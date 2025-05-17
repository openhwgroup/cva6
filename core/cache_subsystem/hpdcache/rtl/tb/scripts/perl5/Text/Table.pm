# Text::Table - Organize Data in Tables
package Text::Table;

use strict;
use warnings;

use 5.008;

use List::Util qw(sum max);

use Text::Aligner qw(align);

our $VERSION = '1.133';

use overload (
    # Don't stringify when only doing boolean tests, since stringification can
    # be expensive for large tables:
    bool => sub { return 1; },
    # Stringify when Table instances are used in most other scalar cases:
    '""' => 'stringify',
);

### User interface:  How to specify columns and column separators

sub _is_sep {
    my $datum = shift;

    return
    (
        defined($datum)
            and
        (
            (ref($datum) eq 'SCALAR')
                    or
            (ref($datum) eq 'HASH' and $datum->{is_sep})
        )
    );
}

sub _get_sep_title_body
{
    my $sep = shift;

    return
        +( ref($sep) eq 'HASH' )
        ? @{ $sep }{qw(title body)}
        : split( /\n/, ${$sep}, -1 ) ;
}

sub _parse_sep {
    my $sep = shift;

    if (!defined($sep))
    {
        $sep = '';
    }

    my ($title, $body) = _get_sep_title_body($sep);

    if (!defined($body))
    {
        $body = $title;
    }

    ($title, $body) = align( 'left', $title, $body);

    return
    {
        is_sep => 1,
        title  => $title,
        body   => $body,
    };
}

sub _default_if_empty
{
    my ($ref, $default) = @_;

    if (! (defined($$ref) && length($$ref)))
    {
        $$ref = $default;
    }

    return;
}

sub _is_align
{
    my $align = shift;

    return $align =~ /\A(?:left|center|right)/;
}

sub _parse_spec {
    my $spec = shift;

    if (!defined($spec))
    {
        $spec = '';
    }

    my $alispec = qr/^ *(?:left|center|right|num|point|auto)/;
    my ( $title, $align, $align_title, $align_title_lines, $sample);
    if ( ref ($spec) eq 'HASH' ) {
        ( $title, $align, $align_title, $align_title_lines, $sample) =
            @{$spec}{qw( title align align_title align_title_lines sample )};
    } else {
        my $alispec = qr/&(.*)/;
        if ( $spec =~ $alispec ) {
            ($title, $align, $sample) = ($spec =~ /(.*)^$alispec\n?(.*)/sm);
        } else {
            $title = $spec;
        }
        for my $s ($title, $sample)
        {
            if (defined($s))
            {
                chomp($s);
            }
        }
    }

    # Assign default values.
    foreach my $x ($title, $sample)
    {
        if (!defined($x))
        {
            $x = [];
        }
        elsif (ref($x) ne 'ARRAY')
        {
            $x = [ split /\n/, $x, -1];
        }
    }

    _default_if_empty(\$align, 'auto');

    unless (
        ref $align eq 'Regexp' or
        $align =~ /^(?:left|center|right|num\(?|point\(?|auto)/
    ) {
        _warn( "Invalid align specification: '$align', using 'auto'");
        $align = 'auto';
    }

    _default_if_empty(\$align_title, 'left');

    if ( ! _is_align($align_title) ) {
        _warn( "Invalid align_title specification: " .
            "'$align_title', using 'left'",
        );
        $align_title = 'left';
    }

    _default_if_empty(\$align_title_lines, $align_title);

    if ( ! _is_align($align_title_lines) ) {
        _warn( "Invalid align_title_lines specification: " .
            "'$align_title_lines', using 'left'",
        );
        $align_title_lines = 'left';
    }

    return
    {
        title             => $title,
        align             => $align,
        align_title       => $align_title,
        align_title_lines => $align_title_lines,
        sample            => $sample,
    };
}

### table creation

sub new
{
    my $tb = bless {}, shift;

    return $tb->_entitle( [ @_ ] );
}

sub _blank
{
    my $self = shift;

    if (@_)
    {
        $self->{blank} = shift;
    }

    return $self->{blank};
}

sub _cols
{
    my $self = shift;

    if (@_)
    {
        $self->{cols} = shift;
    }

    return $self->{cols};
}

sub _forms
{
    my $self = shift;

    if (@_)
    {
        $self->{forms} = shift;
    }

    return $self->{forms};
}

sub _lines
{
    my $self = shift;

    if (@_)
    {
        $self->{lines} = shift;
    }

    return $self->{lines};
}

sub _spec
{
    my $self = shift;

    if (@_)
    {
        $self->{spec} = shift;
    }

    return $self->{spec};
}

sub _titles
{
    my $self = shift;

    if (@_)
    {
        $self->{titles} = shift;
    }

    return $self->{titles};
}

sub _entitle {
    my ($tb, $sep_list) = @_; # will be completely overwritten
    # find active separators and, well separate them from col specs.
    # n+1 separators for n cols
    my ( @seps, @spec); # separators and column specifications
    my $sep;
    foreach my $sep_item ( @{$sep_list} ) {
        if ( _is_sep ($sep_item) ) {
            $sep = _parse_sep($sep_item);
        } else {
            push @seps, $sep;
            push @spec, _parse_spec($sep_item);
            undef $sep;
        }
    }
    push @seps, $sep;
    # build sprintf formats from separators
    my $title_form = _compile_field_format('title', \@seps);
    my $body_form = _compile_field_format('body', \@seps);

    # pre_align titles
    my @titles = map { [ @{ $_->{title} } ] } @spec;

    my $title_height = max(0, map { scalar(@$_) } @titles);

    foreach my $title (@titles)
    {
        push @{$title}, ( '') x ( $title_height - @{$title});
    }

    foreach my $t_idx (0 .. $#titles)
    {
        align($spec[$t_idx]->{align_title_lines}, @{$titles[$t_idx]});
    }

    # build data structure
    $tb->_spec(\@spec);
    $tb->_cols([ map [], 1 .. @spec]);
    $tb->_forms([ $title_form, $body_form]); # separators condensed
    $tb->_titles(\@titles);

    $tb->_clear_cache;

    return $tb;
}

# sprintf-format for line assembly, using separators
sub _compile_format {
   my $seps = shift; # mix of strings and undef (for default)

   for my $idx (0 .. $#$seps)
   {
        if (!defined($seps->[$idx]))
        {
            $seps->[$idx] = ($idx == 0 or $idx == $#$seps) ? '' : q{ };
        }
        else
        {
            # protect against sprintf
            $seps->[$idx] =~ s/%/%%/g;
        }
   }
   return join '%s', @$seps;
}

sub _compile_field_format
{
    my ($field, $seps) = @_;

    return _compile_format(
        [map { defined($_) ? $_->{$field} : undef } @$seps]
    );
}

# reverse format compilation (used by colrange())
sub _recover_separators {
    my $format = shift;
    my @seps = split /(?<!%)%s/, $format, -1;
    for my $s (@seps)
    {
        $s =~ s/%%/%/g;
    }
    return \@seps;
}

# select some columns, (optionally if in [...]), and add new separators
# (the other table creator)
sub select {
    my $tb = shift;
    my @args = map $tb->_select_group( $_), @_;
    # get column selection, checking indices (some have been checked by
    # _select_group, but not all)
    my @sel = map $tb->_check_index( $_), grep !_is_sep( $_), @args;
    # replace indices with column spec to create subtable
    for my $arg (@args)
    {
        if (! _is_sep($arg))
        {
            $arg = $tb->_spec->[ $arg];
        }
    }
    my $sub = ref( $tb)->new( @args);
    # sneak in data columns
    @{ $sub->{ cols}} = map { [ @$_ ] } @{ $tb->_cols}[ @sel];
    $sub;
}

# the first non-separator column in the group is tested if it has any data
# if so, the group is returned, else nothing
sub _select_group {
    my ( $tb, $group) = @_;
    return $group unless ref $group eq 'ARRAY';
    GROUP_LOOP:
    for my $g ( @$group ) {
        if (_is_sep($g))
        {
            next GROUP_LOOP;
        }
        $tb->_check_index($g);

        if (grep { $_} @{ $tb->_cols->[$g] })
        {
            return @$group;
        }
        return; # no more tries after non-sep was found
    }
    return; # no column index in group, no select
}

# check index for validity, return arg if returns at all
sub _check_index {
    my $tb = shift;
    my ( $i) = @_;
    my $n = $tb->n_cols;
    my $ok = eval {
        use warnings FATAL => 'numeric';
        -$n <= $i and $i < $n; # in range of column array?
    };
    _warn( "Invalid column index '$_'") if $@ or not $ok;
    shift;
}

### data entry

sub _clear_cache {
    my ($tb) = @_;

    $tb->_blank(undef());
    $tb->_lines(undef());

    return;
}

# add one data line or split the line into follow-up lines
sub add {
    my $tb = shift;

    if (! $tb->n_cols) {
        $tb->_entitle( [ ('') x @_] );
    }

    foreach my $row (
        _transpose(
            [
                map { [ defined() ? split( /\n/ ) : '' ] } @_
            ]
        )
    )
    {
        $tb->_add(@$row);
    }
    $tb->_clear_cache;

    return $tb;
}

# add one data line
sub _add {
    my $tb = shift;

    foreach my $col ( @{ $tb->_cols} ) {
        push @{$col}, shift(@_);
    }

    $tb->_clear_cache;

    return $tb;
}

# add one or more data lines
sub load {
    my $tb = shift;
    foreach my $row ( @_ ) {
        if (!defined($row)) {
            $row = '';
        }
        $tb->add(
            (ref($row) eq 'ARRAY') ? (@$row) : (split ' ',$row)
        )
    }
    $tb;
}

sub clear {
    my $tb = shift;

    foreach my $col (@{ $tb->_cols} )
    {
        $col = [];
    }

    $tb->_clear_cache;

    return $tb;
}

### access to output area

## sizes

# number of table columns
sub n_cols { scalar @{ $_[0]->{ spec}} }

# number of title lines
sub title_height { $_[ 0]->n_cols and scalar @{ $_[ 0]->_titles->[ 0]} }

# number of data lines
sub body_height
{
    my ($tb) = @_;

    return ($tb->n_cols && scalar @{ $tb->_cols->[0] });
}

# total height
sub table_height
{
    my $tb = shift;
    return $tb->title_height + $tb->body_height;
}

BEGIN { *height = \&table_height; } # alias

# number of characters in each table line. need to build the table to know
sub width
{
    my ($tb) = @_;

    return $tb->height && (length( ($tb->table(0))[0] ) - 1);
}

sub _normalize_col_index
{
    my ($tb, $col_index) = @_;

    $col_index ||= 0;

    if ($col_index < 0)
    {
        $col_index += $tb->n_cols;
    }

    if ($col_index < 0)
    {
        $col_index = 0;
    }
    elsif ($col_index > $tb->n_cols)
    {
        $col_index = $tb->n_cols;
    }

    return $col_index;
}

# start and width of each column
sub colrange {
    my ( $tb, $proto_col_index) = @_;

    my $col_index = $tb->_normalize_col_index($proto_col_index);

    return ( 0, 0) unless $tb->width; # width called, $tb->_blank() exists now
    my @widths = map { length } @{ $tb->_blank}, '';
    @widths = @widths[ 0 .. $col_index];

    my $width = pop @widths;
    my $pos = sum(@widths) || 0;

    my $seps_aref = _recover_separators( $tb->_forms->[ 0]);

    my $sep_sum = 0;
    foreach my $sep (@$seps_aref[ 0 .. $col_index])
    {
        $sep_sum += length($sep);
    }

    return ( $pos+$sep_sum, $width ) ;
}

## printable output

# whole table
sub table {
    my $tb = shift;

    return $tb->_table_portion( $tb->height, 0, @_);
}

# only titles
sub title {
    my $tb = shift;

    return $tb->_table_portion( $tb->title_height, 0, @_);
}

# only body
sub body {
    my $tb = shift;

    return $tb->_table_portion( $tb->body_height, $tb->title_height, @_);
}

sub stringify
{
    my ($tb) = @_;

    return (scalar ( $tb->table() ));
}

### common internals

# common representation of table(), title() and body()

sub _table_portion_as_aref
{
    my $tb = shift;

    my $total = shift;
    my $offset = shift;

    my ( $from, $n) = ( 0, $total); # if no parameters

    if ( @_ ) {
        $from = shift;
        $n = @_ ? shift : 1; # one line if not given
    }

    ( $from, $n) = _limit_range( $total, $from, $n);

    my $limit = $tb->title_height; # title format below
    $from += $offset;

    return
    [
        map $tb->_assemble_line( $_ >= $limit, $tb->_table_line( $_), 0),
        $from .. $from + $n - 1
    ];
}

sub _table_portion
{
    my $tb = shift;

    my $lines_aref = $tb->_table_portion_as_aref(@_);

    return (wantarray ? @$lines_aref : join('', @$lines_aref));
}

sub _limit_range
{
    my ( $total, $from, $n) = @_;

    $from ||= 0;
    $from += $total if $from < 0;
    $n = $total unless defined $n;

    return ( 0, 0) if $from + $n < 0 or $from >= $total;

    $from = 0 if $from < 0;
    $n = $total - $from if $n > $total - $from;

    return( $from, $n);
}

# get table line (formatted, including titles). fill cache if needed
sub _table_line {
    my ($tb, $idx) = @_;

    if (! $tb->_lines)
    {
        $tb->_lines([ $tb->_build_table_lines ]);
    }

    return $tb->_lines->[$idx];
}

# build array of lines of justified data items
sub _build_table_lines {
    my $tb = shift;

    # copy data columns, replacing undef with ''
    my @cols =
        map
        { [ map { defined($_) ? $_ : '' } @$_ ] }
        @{ $tb->_cols() } ;

    # add set of empty strings for blank line (needed to build horizontal rules)
    foreach my $col (@cols)
    {
        push @$col, '';
    }

    # add samples for minimum alignment
    foreach my $col_idx (0 .. $#cols)
    {
        push @{$cols[$col_idx]}, @{$tb->_spec->[$col_idx]->{sample}};
    }

    # align to style
    foreach my $col_idx (0 .. $#cols)
    {
        align($tb->_spec->[$col_idx]->{align}, @{$cols[$col_idx]});
    }

    # trim off samples, but leave blank line
    foreach my $col (@cols)
    {
        splice( @{$col}, 1 + $tb->body_height );
    }

    # include titles
    foreach my $col_idx (0 .. $#cols)
    {
        unshift @{$cols[$col_idx]}, @{$tb->_titles->[$col_idx]};
    }

    # align title and body portions of columns
    # blank line will be there even with no data
    foreach my $col_idx (0 .. $#cols)
    {
        align($tb->_spec->[$col_idx]->{align_title}, @{$cols[$col_idx]});
    }

    # deposit a blank line, pulling it off the columns.
    # *_rule() knows this is done
    my @blank;

    foreach my $col (@cols)
    {
        push @blank, pop(@$col);
    }

    $tb->_blank(\@blank);

    return _transpose_n( $tb->height, \@cols); # bye-bye, @cols
}

# destructively transpose a number of lines/cols from an array of arrayrefs
sub _transpose_n {
    my ($n, $cols) = @_;

    return map { [ map { shift @$_ } @$cols] } 1 .. $n;
}

# like _transpose_n, but find the number to transpose from max of given
sub _transpose
{
    my ($cols) = @_;

    my $m = max ( map { scalar(@$_) } @$cols, []);

    return _transpose_n( $m, $cols);
}

# make a line from a number of formatted data elements
sub _assemble_line {
    my ($tb, $in_body, $line_aref, $replace_spaces) = @_;

    my $format = $tb->_forms->[ !!$in_body];

    if ($replace_spaces)
    {
        $format =~ s/\s/=/g;
    }

    return sprintf($format, @$line_aref) . "\n";
}

sub _text_rule
{
    my ($tb, $rule, $char, $alt) = @_;

    # replace blanks with $char. If $alt is given, replace nonblanks
    # with $alt
    if ( defined $alt )
    {
        $rule =~ s/(.)/$1 eq ' ' ? $char : $alt/ge;
    }
    else
    {
        $rule =~ s/ /$char/g if $char ne ' ';
    }

    return $rule;
}

# build a rule line
sub _rule {
    my $tb = shift;

    return + (!$tb->width) ? '' : $tb->_positive_width_rule(@_);
}

sub _positive_width_rule
{
    my ($tb, $in_body, $char, $alt) = @_;

    my $rule = $tb->_assemble_line( $in_body, $tb->_blank,
        ((ref($char) eq "CODE") ? 1 : 0),
    );

    return $tb->_render_rule($rule, $char, $alt);
}

sub _render_rule
{
    my ($tb, $rule, $char, $alt) = @_;

    if (ref($char) eq "CODE")
    {
        return $tb->_render_rule_with_callbacks($rule, $char, $alt);
    }
    else
    {
        _default_if_empty(\$char, ' ');

        return $tb->_text_rule($rule, $char, $alt);
    }
}

sub _get_fixed_len_string
{
    my ($s, $len) = @_;

    $s  = substr($s, 0, $len);
    $s .= ' ' x ($len - length($s));

    return $s;
}

sub _render_rule_with_callbacks
{
    my ($tb, $rule, $char, $alt) = @_;

    my %callbacks =
    (
        'char' => { cb => $char, idx => 0, },
        'alt' => { cb => $alt, idx => 0, },
    );

    my $calc_substitution = sub {
        my $s = shift;

        my $len = length($s);

        my $which = (($s =~ /\A /) ? 'char' : 'alt');
        my $rec = $callbacks{$which};

        return _get_fixed_len_string(
            scalar ($rec->{cb}->($rec->{idx}++, $len)),
            $len,
        );
    };

    $rule =~ s/((.)\2*)/$calc_substitution->($1)/ge;

    return $rule;
}

sub rule {
    my $tb = shift;
    return $tb->_rule( 0, @_);
}

sub body_rule {
    my $tb = shift;
    return $tb->_rule( 1, @_);
}

### warning behavior
use Carp;

{
    my ( $warn, $fatal) = ( 0, 0);

    sub warnings
    {
        # Ignore the class/object.
        my (undef, $toggle) = @_;

        $toggle ||= 'on';
        if ( $toggle eq 'off' )
        {
            ($warn, $fatal) = (0, 0);
        }
        elsif ( $toggle eq 'fatal' )
        {
            ($warn, $fatal) = (1, 1);
        }
        else
        {
            ($warn, $fatal) = (1, 0);
        }
        return $fatal ? 'fatal' : $warn ? 'on' : 'off';
    }

    sub _warn
    {
        my $msg = shift;

        return unless $warn;

        if ($fatal)
        {
            croak( $msg)
        }

        carp( $msg);

        return;
    }
}

=pod

=encoding UTF-8

=head1 NAME

Text::Table - Organize Data in Tables

=head1 VERSION

version 1.133

=head1 SYNOPSIS

    use Text::Table;
    my $tb = Text::Table->new(
        "Planet", "Radius\nkm", "Density\ng/cm^3"
    );
    $tb->load(
        [ "Mercury", 2360, 3.7 ],
        [ "Venus", 6110, 5.1 ],
        [ "Earth", 6378, 5.52 ],
        [ "Jupiter", 71030, 1.3 ],
    );
    print $tb;

This prints a table from the given title and data like this:

  Planet  Radius Density
          km     g/cm^3
  Mercury  2360  3.7
  Venus    6110  5.1
  Earth    6378  5.52
  Jupiter 71030  1.3

Note that two-line titles work, and that the planet names are aligned
differently than the numbers.

=head1 DESCRIPTION

Organization of data in table form is a time-honored and useful
method of data representation.  While columns of data are trivially
generated by computer through formatted output, even simple tasks
like keeping titles aligned with the data columns are not trivial,
and the one-shot solutions one comes up with tend to be particularly
hard to maintain.  Text::Table allows you to create and maintain
tables that adapt to alignment requirements as you use them.

=head2 Overview

The process is simple: you create a table (a Text::Table object) by
describing the columns the table is going to have.  Then you load
lines of data into the table, and finally print the resulting output
lines.  Alignment of data and column titles is handled dynamically
in dependence on the data present.

=head2 Table Creation

In the simplest case, if all you want is a number of (untitled) columns,
you create an unspecified table and start adding data to it.  The number
of columns is taken from the first line of data.

To specify a table you specify its columns.  A column description
can contain a title and alignment requirements for the data, both
optional.  Additionally, you can specify how the title is aligned with
the body of a column, and how the lines of a multiline title are
aligned among themselves.

The columns are collected in the table in the
order they are given.  On data entry, each column corresponds to
one data item, and in column selection columns are indexed left to
right, starting from 0.

Each title can be a multiline string which will be blank-filled to
the length of the longest partial line.  The largest number of title
lines in a column determines how many title lines the table has as a
whole, including the case that no column has any titles.

On output, columns are separated by a single blank.  You can control
what goes between columns by specifying separators between (or before,
or after) columns.  Separators don't contain any data and don't count
in column indexing.  They also don't accumulate: in a sequence of only
separators and no columns, only the last one counts.

=head2 Status Information

The width (in characters), height (in lines), number of columns, and
similar data about the table is available.

=head2 Data Loading

Table data is entered line-wise, each time specifying data entries
for all table columns.  A bulk loader for many lines at once is also
available.  You can clear the data from the table for re-use (though
you will more likely just create another table).

Data can contain colorizing escape sequences (as provided by
C<Term::AnsiColor>) without upsetting the alignment.

=head2 Table Output

The output area of a table is divided in the title and the body.

The title contains the combined titles from the table columns, if
any.  Its content never changes with a given table, but it may be
spread out differently on the page through alignment with the data.

The body contains the data lines, aligned column-wise as specified,
and left-aligned with the column title.

Each of these is arranged like a Perl array (counting from 0) and can
be accessed in portions by specifying a first line and the number
of following lines.  Also like an array, giving a negative first line
counts from the end of the area.  The whole table, the title followed
by the body, can also be accessed in this manner.

The subdivisions are there so you can repeat the title (or parts of
it) along with parts of the body on output, whether for screen paging
or printout.

A rule line is also available, which is the horizontal counterpart to
the separator columns you specify with the table.
It is basically a table line as it would appear if all data entries
in the line were empty, that is, a blank line except for where the
column separators have non-blank entries.  If you print it between
data lines, it will not disrupt the vertical separator structure
as a plain blank line would.  You can also request a solid rule
consisting of any character, and even one with the non-blank column
separators replaced by a character of your choice.  This way you can
get the popular representation of line-crossings like so:

      |
  ----+---
      |

=head2 Warning Control

On table creation, some parameters are checked and warnings issued
if you allow warnings.  You can also turn warnings into fatal errors.

=head1 SPECIFICATIONS

=head2 Column Specification

Each column specification is a single scalar.  Columns can be either proper
data columns or column separators.  Both can be specified either as
(possibly multi-line) strings, or in a more explicit form as hash-refs.
In the string form, proper columns are given as plain strings, and
separators are given as scalar references to strings.  In hash form,
separators have a true value in the field C<is_sep> while proper columns
don't have this field.

=over 4

=item Columns as strings

A column is given as a column title (any number of lines),
optionally followed by alignment requirements.  Alignment requirements
start with a line that begins with an ampersand "&".  However, only the
last such line counts as such, so if you have title lines that begin
with "&", just append an ampersand on a line by itself as a dummy
alignment section if you don't have one anyway.

What follows the ampersand on its line is the alignment style (like
I<left>, I<right>, ... as described in L<"Alignment">), you want for
the data in this column.  If nothing follows, the general default I<auto>
is used.  If you specify an invalid alignment style, it falls back to
left alignment.

The lines that follow can contain sample data for this column.  These
are considered for alignment in the column, but never actually appear
in the output.  The effect is to guarantee a minimum width for the
column even if the current data doesn't require it.  This helps dampen
the oscillations in the appearance of dynamically aligned tables.

=item Columns as Hashes

The format is

    {
        title   => $title,
        align   => $align,
        sample  => $sample,
        align_title => $align_title,
        align_title_lines => $align_title_lines,
    }

$title contains the title lines and $sample the sample data.  Both can
be given as a string or as an array-ref to the list of lines.  $align contains
the alignment style (without a leading ampersand), usually as a string.
You can also give a regular expression here, which specifies regex alignment.
A regex can only be specified in the hash form of a column specification.

In hash form you can also specify how the title of a column is aligned
with its body.  To do this, you specify the keyword C<align_title> with
C<left>, C<right> or C<center>.  Other alignment specifications are not
valid here.  The default is C<left>.

C<align_title> also specifies how the lines of a multiline title are
aligned among themselves.  If you want a different alignment, you
can specify it with the key C<align_title_lines>.  Again, only C<left>,
C<right> or C<center> are allowed.

Do not put other keys than those mentioned above (I<title>, I<align>,
I<align_title>, I<align_title_lines>, and I<sample>) into a hash that
specifies a column.  Most would be ignored, but some would confuse the
interpreter (in particular, I<is_sep> has to be avoided).

=item Separators as strings

A separator must be given as a reference to a string (often a literal,
like C<\' | '>), any string that is given directly describes a column.

It is usually just a (short) string that will be printed between
table columns on all table lines instead of the default single
blank.  If you specify two separators (on two lines), the first one
will be used in the title and the other in the body of the table.

=item Separators as Hashes

The hash representation of a separator has the format

    {
        is_sep => 1,
        title  => $title,
        body   => $body,
    }

$title is the separator to be used in the title area and $body
the one for the body.  If only one is given, it will be used for
both.  If none is given, a blank is used.  If one is shorter than
the other, it is blank filled on the right.

The value of C<is_sep> must be set to a true value, this is the
distinguishing feature of a separator.

=back

=head2 Alignment

The original documentation to L<Text::Aligner> contains all the details
on alignment specification, but here is the rundown:

The possible alignment specifications are I<left>, I<right>, I<center>,
I<num> and I<point> (which are synonyms), and I<auto>.  The first
three explain themselves.

I<num> (and I<point>) align the decimal point in the data, which is
assumed to the right if none is present.  Strings that aren't
numbers are treated the same way, that is, they appear aligned
with the integers unless they contain a ".".  Instead of the
decimal point ".", you can also specify any other string in
the form I<num(,)>, for instance.  The string in parentheses
is aligned in the data.  The synonym I<point> for I<num> may be
more appropriate in contexts that deal with arbitrary
strings, as in I<point(=E<gt>)> (which might be used to align certain
bits of Perl code).

I<regex alignment> is a more sophisticated form of point alignment.
If you specify a regular expression, as delivered by C<qr//>, the start
of the match is used as the alignment point.  If the regex contains
capturing parentheses, the last submatch counts.  [The usefulness of
this feature is under consideration.]

I<auto> alignment combines numeric alignment with left alignment.
Data items that look like numbers, and those that don't, form two
virtual columns and are aligned accordingly: C<num> for numbers and
C<left> for other strings.  These columns are left-aligned with
each other (i.e. the narrower one is blank-filled) to form the
final alignment.

This way, a column that happens to have only numbers in the data gets
I<num> alignment, a column with no numbers appears I<left>-aligned,
and mixed data is presented in a reasonable way.

=head2 Column Selection

Besides creating tables from scratch, they can be created by
selecting columns from an existing table.  Tables created this
way contain the data from the columns they were built from.

This is done by specifying the columns to select by their index
(where negative indices count backward from the last column).
The same column can be selected more than once and the sequence
of columns can be arbitrarily changed.  Separators don't travel
with columns, but can be specified between the columns at selection
time.

You can make the selection of one or more columns dependent on
the data content of one of them.  If you specify some of the columns
in angle brackets [...], the whole group is only included in the
selection if the first column in the group contains any data that
evaluates to boolean true.  That way you can de-select parts of a
table if it contains no interesting data.  Any column separators
given in brackets are selected or deselected along with the rest
of it.

=head1 PUBLIC METHODS

=head2 Table Creation

=over 4

=item new()

    my $tb = Text::Table->new( $column, ... );

creates a table with the columns specified.  A column can be proper column
which contains and displays data, or a separator which tells how to fill
the space between columns.  The format of the parameters is described under
L<"Column Specification">. Specifying an invalid alignment for a column
results in a warning if these are allowed.

If no columns are specified, the number of columns is taken from the first
line of data added to the table.  The effect is as if you had specified
C<Text::Table-E<gt>new( ( '') x $n)>, where C<$n> is the number of
columns.

=item select()

    my $sub = $tb->select( $column, ...);

creates a table from the listed columns of the table $tb, including
the data.  Columns are specified as integer indices which refer to
the data columns of $tb.  Columns can be repeated and specified in any
order.  Negative indices count from the last column.  If an invalid
index is specified, a warning is issued, if allowed.

As with L<"new()">, separators can be interspersed among the column
indices and will be used between the columns of the new table.

If you enclose some of the arguments (column indices or separators) in
angle brackets C<[...]> (technically, you specify them inside an
arrayref), they form a group for conditional selection.  The group is
only included in the resulting table if the first actual column inside
the group contains any data that evaluate to a boolean true.  This way
you can exclude groups of columns that wouldn't contribute anything
interesting.  Note that separators are selected and de-selected with
their group.  That way, more than one separator can appear between
adjacent columns.  They don't add up, but only the rightmost separator
is used.  A group that contains only separators is never selected.
[Another feature whose usefulness is under consideration.]

=back

=head2 Status Information

=over 4

=item n_cols()

    $tb->n_cols

returns the number of columns in the table.

=item width()

    $tb->width

returns the width (in characters) of the table.  All table lines have
this length (not counting a final "\n" in the line), as well as the
separator lines returned by $tb->rule() and $b->body_rule().
The width of a table can potentially be influenced by any data item
in it.

=item height()

    $tb->height

returns the total number of lines in a table, including title lines
and body lines. For orthogonality, the synonym table_height() also
exists.

=item table_height()

Same as C<< $table->height() >>.

=item title_height()

    $tb->title_height

returns the number of title lines in a table.

=item body_height()

    $tb->body_height

returns the number of lines in the table body.

=item colrange()

    $tb->colrange( $i)

returns the start position and width of the $i-th column (counting from 0)
of the table.  If $i is negative, counts from the end of the table.  If $i
is larger than the greatest column index, an imaginary column of width 0
is assumed right of the table.

=back

=head2 Data Loading

=over 4

=item add()

    $tb->add( $col1, ..., $colN)

adds a data line to the table, returns the table.

C<$col1>, ..., C<$colN> are scalars that
correspond to the table columns.  Undefined entries are converted to '',
and extra data beyond the number of table columns is ignored.

Data entries can be multi-line strings.  The partial strings all go into
the same column.  The corresponding fields of other columns remain empty
unless there is another multi-line entry in that column that fills the
fields.  Adding a line with multi-line entries is equivalent to adding
multiple lines.

Every call to C<add()> increases the body height of the table by the
number of effective lines, one in the absence of multiline entries.

=item load()

    $tb->load( $line, ...)

loads the data lines given into the table, returns the table.

Every argument to C<load()> represents a data line to be added to the
table.  The line can be given as an array(ref) containing the data
items, or as a string, which is split on whitespace to retrieve the
data.  If an undefined argument is given, it is treated as an
empty line.

=item clear()

    $tb->clear;

deletes all data from the table and resets it to the state after
creation.  Returns the table.  The body height of a table is 0 after
C<clear()>.

=back

=head2 Table Output

The three methods C<table()>, C<title()>, and C<body()> are very similar.
They access different parts of the printable output lines of a table with
similar methods.  The details are described with the C<table()> method.

=over 4

=item table()

The C<table()> method returns lines from the entire table, starting
with the first title line and ending with the last body line.

In array context, the lines are returned separately, in scalar context
they are joined together in a single string.

    my @lines = $tb->table;
    my $line  = $tb->table( $line_number);
    my @lines = $tb->table( $line_number, $n);

The first call returns all the lines in the table.  The second call
returns one line given by $line_number.  The third call returns $n
lines, starting with $line_number.  If $line_number is negative, it
counts from the end of the array.  Unlike the C<select()> method,
C<table()> (and its sister methods C<title()> and C<body()>) is
protected against large negative line numbers, it truncates the
range described by $line_number and $n to the existing lines.  If
$n is 0 or negative, no lines are returned (an empty string in scalar
context).

=item stringify()

Returns a string representation of the table. This method is called for
stringification by overload.

    my @table_strings = map { $_->stringify() } @tables;

=item title()

Returns lines from the title area of a table, where the column titles
are rendered.  Parameters and response to context are as with C<table()>,
but no lines are returned from outside the title area.

=item body()

Returns lines from the body area of a table, that is the part where
the data content is rendered, so that $tb->body( 0) is the first data
line.  Parameters and response to context are as with C<table()>.

=item rule()

    $tb->rule;
    $tb->rule( $char);
    $tb->rule( $char, $char1);
    $tb->rule( sub { my ($index, $len) = @_; },
               sub { my ($index, $len) = @_; },
    );

Returns a rule for the table.

A rule is a line of table width that can be used between table lines
to provide visual horizontal divisions, much like column separators
provide vertical visual divisions.  In its basic form (returned by the
first call) it looks like a table line with no data, hence a blank
line except for the non-blank parts of any column-separators.  If
one character is specified (the second call), it replaces the blanks
in the first form, but non-blank column separators are retained.  If
a second character is specified, it replaces the non-blank parts of
the separators.  So specifying the same character twice gives a solid
line of table width.  Another useful combo is C<$tb-E<gt>rule( '-', '+')>,
together with separators that contain a single nonblank "|", for a
popular representation of line crossings.

C<rule()> uses the column separators for the title section if there
is a difference.

If callbacks are specified instead of the characters, then they receive the
index of the section of the rule they need to render and its desired length in
characters, and should return the string to put there. The indexes given
are 0 based (where 0 is either the left column separator or the leftmost
cell) and the strings will be trimmed or extended in the replacement.

=item body_rule()

C<body_rule()> works like <rule()>, except the rule is generated using
the column separators for the table body.

=back

=head2 Warning Control

=over 4

=item warnings()

    Text::Table->warnings();
    Text::Table->warnings( 'on');
    Text::Table->warnings( 'off'):
    Text::Table->warnings( 'fatal'):

The C<warnings()> method is used to control the appearance of warning
messages while tables are manipulated.  When Text::Table starts, warnings
are disabled.  The default action of C<warnings()> is to turn warnings
on.  The other possible arguments are self-explanatory.  C<warnings()>
can also be called as an object method (C<$tb-E<gt>warnings( ...)>).

=back

=head1 VERSION

This document pertains to Text::Table version 1.127

=head1 BUGS

=over 4

=item o

I<auto> alignment doesn't support alternative characters for the decimal
point.  This is actually a bug in the underlying Text::Aligner by the
same author.

=back

=head1 AUTHOR

=head2 MAINTAINER

Shlomi Fish, L<http://www.shlomifish.org/> - CPAN ID: "SHLOMIF".

=head2 ORIGINAL AUTHOR

    Anno Siegel
    CPAN ID: ANNO
    siegel@zrz.tu-berlin.de
    http://www.tu-berlin.de/~siegel

=head1 COPYRIGHT

Copyright (c) 2002 Anno Siegel. All rights reserved.
This program is free software; you can redistribute
it and/or modify it under the terms of the ISC license.

(This program had been licensed under the same terms as Perl itself up to
version 1.118 released on 2011, and was relicensed by permission of its
originator).

The full text of the license can be found in the
LICENSE file included with this module.

=head1 SEE ALSO

L<Text::Aligner>, L<perl(1)> .

=head1 AUTHOR

Shlomi Fish <shlomif@cpan.org>

=head1 COPYRIGHT AND LICENSE

This software is Copyright (c) 2002 by Anno Siegel and others.

This is free software, licensed under:

  The ISC License

=head1 BUGS

Please report any bugs or feature requests on the bugtracker website
L<http://rt.cpan.org/NoAuth/Bugs.html?Dist=Text-Table> or by email to
L<bug-text-table@rt.cpan.org|mailto:bug-text-table@rt.cpan.org>.

When submitting a bug or request, please include a test-file or a
patch to an existing test-file that illustrates the bug or desired
feature.

=for :stopwords cpan testmatrix url annocpan anno bugtracker rt cpants kwalitee diff irc mailto metadata placeholders metacpan

=head1 SUPPORT

=head2 Perldoc

You can find documentation for this module with the perldoc command.

  perldoc Text::Table

=head2 Websites

The following websites have more information about this module, and may be of help to you. As always,
in addition to those websites please use your favorite search engine to discover more resources.

=over 4

=item *

MetaCPAN

A modern, open-source CPAN search engine, useful to view POD in HTML format.

L<http://metacpan.org/release/Text-Table>

=item *

Search CPAN

The default CPAN search engine, useful to view POD in HTML format.

L<http://search.cpan.org/dist/Text-Table>

=item *

RT: CPAN's Bug Tracker

The RT ( Request Tracker ) website is the default bug/issue tracking system for CPAN.

L<https://rt.cpan.org/Public/Dist/Display.html?Name=Text-Table>

=item *

AnnoCPAN

The AnnoCPAN is a website that allows community annotations of Perl module documentation.

L<http://annocpan.org/dist/Text-Table>

=item *

CPAN Ratings

The CPAN Ratings is a website that allows community ratings and reviews of Perl modules.

L<http://cpanratings.perl.org/d/Text-Table>

=item *

CPAN Forum

The CPAN Forum is a web forum for discussing Perl modules.

L<http://cpanforum.com/dist/Text-Table>

=item *

CPANTS

The CPANTS is a website that analyzes the Kwalitee ( code metrics ) of a distribution.

L<http://cpants.cpanauthors.org/dist/Text-Table>

=item *

CPAN Testers

The CPAN Testers is a network of smokers who run automated tests on uploaded CPAN distributions.

L<http://www.cpantesters.org/distro/T/Text-Table>

=item *

CPAN Testers Matrix

The CPAN Testers Matrix is a website that provides a visual overview of the test results for a distribution on various Perls/platforms.

L<http://matrix.cpantesters.org/?dist=Text-Table>

=item *

CPAN Testers Dependencies

The CPAN Testers Dependencies is a website that shows a chart of the test results of all dependencies for a distribution.

L<http://deps.cpantesters.org/?module=Text::Table>

=back

=head2 Bugs / Feature Requests

Please report any bugs or feature requests by email to C<bug-text-table at rt.cpan.org>, or through
the web interface at L<https://rt.cpan.org/Public/Bug/Report.html?Queue=Text-Table>. You will be automatically notified of any
progress on the request by the system.

=head2 Source Code

The code is open to the world, and available for you to hack on. Please feel free to browse it and play
with it, or whatever. If you want to contribute patches, please send me a diff or prod me to pull
from your repository :)

L<https://github.com/shlomif/Text-Table>

  git clone ssh://git@github.com:shlomif/Text-Table.git

=cut

__END__
########################################### main pod documentation begin ##


1;
