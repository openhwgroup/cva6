# Text::Aligner - Align text in columns
package Text::Aligner;

use strict;
use warnings;

use 5.008;

BEGIN    {
    use Exporter ();
    use vars qw ($VERSION @ISA @EXPORT @EXPORT_OK %EXPORT_TAGS);
    $VERSION     = '0.13';
    @ISA         = qw (Exporter);
    @EXPORT      = qw ();
    @EXPORT_OK   = qw ( align);
    %EXPORT_TAGS = ();
}

# this is a non-method, and currently the only user interface
sub align ($@) {
    my $ali = Text::Aligner->new( shift);
    $ali->_alloc( map ref eq 'SCALAR' ? $$_ : $_, @_);
    if ( defined wantarray ) {
        my @just = map $ali->_justify( ref eq 'SCALAR' ? $$_ : $_), @_;
        return @just if wantarray;
        return join "\n", @just, '';
    } else {
        for ( @_ ) {
            $_ = $ali->_justify( $_) for ref eq 'SCALAR' ? $$_ : $_; # one-shot
        }
    }
}

### class Text::Aligner

sub _new { # internal constructor
    my $class = shift;
    my ( $width, $pos) = @_; # both method-or-coderef (this is very general)
    bless {
        width => $width,
        pos => $pos,
        left => Text::Aligner::MaxKeeper->new,
        right => Text::Aligner::MaxKeeper->new,
    }, $class;
}

# Construct an aligner
sub new {
    my ( $class, $spec) = @_;
    $spec ||= 0; # left alignment is default
    my $al;
    if ( !ref( $spec) and $spec =~ s/^auto/num/ ) {
        $al = Text::Aligner::Auto->_new( $spec);
    } else {
        $al = $class->_new( _compile_alispec( $spec));
    }
    $al;
}

# return left and right field widths for an object
sub _measure0 {
    my $al = shift;
    my $obj = shift;
    $obj = '' unless defined $obj;
    my ( $w, $p);
    if ( ref $obj ) {
        ( $w, $p) = ( $obj->$al->{ width}->(), $obj->$al->{ pos}->() );
    } else {
        ( $w, $p) = ( $al->{ width}->( $obj), $al->{ pos}->( $obj) );
    }
    $_ ||= 0 for $w, $p;
    ( $p, $w - $p);
}

use Term::ANSIColor 2.02;

# return left and right field widths for an object
sub _measure {
    my $al = shift;
    my $obj = shift;
    $obj = '' unless defined $obj;
    my ( $wmeth, $pmeth) = @{ $al}{ qw( width pos)};

    # support colorized strings
    $obj = Term::ANSIColor::colorstrip($obj) unless ref $obj;

    my $w = ref $wmeth ? $wmeth->( $obj) : $obj->$wmeth;
    my $p = ref $pmeth ? $pmeth->( $obj) : $obj->$pmeth;
    $_ ||= 0 for $w, $p;
    ( $p, $w - $p);
}

# Return left and right maxima, or nothing if the aligner is empty
sub _status {
    my @lr = ( $_[ 0]->{ left}->max, $_[ 0]->{ right}->max);
    # $l and $r should be both defined or undefined, unless the
    # MaxKeeper memory is corrupted by forgetting unremembered things.
    return unless defined( $lr[ 0]) and defined( $lr[ 1]);
    @lr;
}

# remember alignment requirements
sub _alloc {
    my $al = shift;
    for ( @_ ) {
#       $_ ||= ''; print "allocing '$_'\n";
        my ( $l, $r) = $al->_measure( $_);
        $al->{ left}->remember( $l); # space needed left of pos
        $al->{ right}->remember( $r); # ...and right of pos
    }
    $al;
}

# release alignment requirement.  it disturbs an aligner deeply to forget
# things it hasn't remembered.  the effects may be delayed.
sub _forget {
    my $al = shift;
    for ( map defined() ? $_ : '', @_ ) {
#       print "forgetting '$_'\n";
        my ( $l, $r) = $al->_measure( $_);
        $al->{ left}->forget( $l);
        $al->{ right}->forget( $r);
    }
    $al;
}

sub _spaces {
    my ($repeat_count) = @_;
    return (($repeat_count > 0) ? (' ' x $repeat_count) : '');
}

# justify a string.  a string is aligned within the aligner's field, and
# filled with blanks or cut to size, as appropriate.  a string that has
# been allocated will never be trimmed (that is the point of allocation).
# if the aligner is empty it returns the string unaltered.
sub _justify {
    my $al = shift;
    my $str  = shift;
#   print "justifying '$str'\n";
    $str .= ''; # stringify (objects, numbers, undef)
    my ( $l_pad, $r_pad) = $al->_padding( $str);
    substr( $str, 0, -$l_pad) = '' if $l_pad < 0; # trim if negative
    substr( $str, $r_pad) = '' if $r_pad < 0; # ... both ends
    return _spaces($l_pad) . $str . _spaces($r_pad); # pad if positive
}

# return two numbers that indicate how many blanks are needed on each side
# of a string to justify it.  Negative values mean trim that many characters.
# an empty aligner returns ( 0, 0), so doesn't change anything.
sub _padding {
    my $al = shift;
    my $str = shift;
    my ( $this_l, $this_r) = $al->_measure( $str);
    my ( $l_pad, $r_pad) = ( 0, 0);
    if ( $al->_status ) {
        ( $l_pad, $r_pad) = $al->_status;
        $l_pad -= $this_l;
        $r_pad -= $this_r;
    }
    ( $l_pad, $r_pad);
}

# _compile_alispec() returns positioners according to specification.  In
# effect, it is the interpreter for alignment specifications.

sub _compile_alispec { # it's a dirty job...
    my $width = sub { length shift }; # this is always so for string aligners
    my $pos; # the positioner we actually compile
    local $_ = shift || ''; # alignment specification
    if ( ref() eq 'Regexp' ) {
        my $regex = $_; # lexical copy!
        $pos = sub {
            local $_ = shift;
            return m/$regex/ ? $-[ 0] : length; # assume match after string
        };
    } else {
        s/^left/0/;
        s/^center/0.5/;
        s/^right/1/;
        if ( _is_number( $_) ) {
            my $proportion = $_; # use lexical copy
            $pos = sub { int( $proportion*length shift) };
        } elsif ( $_ =~ /^(?:num|point)(?:\((.*))?/ ) {
            my $point = defined $1 ? $1 : '';
            $point =~ s/\)$//; # ignore trailing paren, if present
            length $point or $point = '.';
            $pos = sub { index( shift() . $point, $point) }
        } else {
            $pos = sub { 0 };
        }
    }
    ( $width, $pos);
}

# decide if a string is a number. (see perlfaq4).
sub _is_number {
    my ($x) = @_;
    return 0 unless defined $x;
    return 0 if $x !~ /\d/;
    return 1 if $x =~ /^-?\d+\.?\d*$/;
    $x = Term::ANSIColor::colorstrip($x);
    $x =~ /^-?\d+\.?\d*$/
}

package Text::Aligner::Auto;
# Combined numeric and left alignment.  Numbers are aligned numerically,
# other strings are left-aligned.  The resulting columns are interleaved
# flush left and filled on the right if necessary.

sub _new { # only called by Text::Aligner->new()
    my $class = shift;
    my $numspec = shift; # currently ignored
    bless {
        num => Text::Aligner->new( 'num'),    # align numbers among themselves
        other => Text::Aligner->new,          # left-align anything else
    }, $class;
}

sub _alloc {
    my $aa = shift;
    my @num = grep _is_number( $_), @_;
    my @other = grep !_is_number( $_), @_;
    $aa->{ num}->_alloc( @num);
    $aa->{ other}->_alloc( @other);
    $aa;
}

sub _forget {
    my $aa = shift;
    $aa->{ num}->_forget( grep _is_number( $_), @_);
    $aa->{ other}->_forget( grep !_is_number( $_), @_);
    $aa;
}

# Justify as required
sub _justify {
    my ( $aa, $str) = @_;
    # align according to type
    $str = $aa->{ _is_number( $str) ? 'num' : 'other'}->_justify( $str);
    my $combi = Text::Aligner->new; # left-justify pre-aligned string
    # initialise to size of partial aligners.  (don't initialise from
    # empty aligner)
    $combi->_alloc( $aa->{ num}->_justify( '')) if $aa->{ num}->_status;
    $combi->_alloc( $aa->{ other}->_justify( '')) if $aa->{ other}->_status;
    $combi->_justify( $str);
}

# for convenience
BEGIN { # import _is_number()
    *_is_number = \ &Text::Aligner::_is_number;
}

package Text::Aligner::MaxKeeper;
# Keep the maximum of a dynamic set of numbers.  Optimized for the case of
# a relatively small range of numbers that may occur repeatedly.

sub new {
    bless {
        max => undef,
        seen => {},
    }, shift;
}

sub max { $_[ 0]->{ max} }

sub remember {
    my ( $mk, $val) = @_;
    _to_max( $mk->{ max}, $val);
    $mk->{ seen}->{ $val}++;
    $mk;
}

sub forget {
    my ( $mk, $val) = @_;
    if ( exists $mk->{ seen}->{ $val} ) {
        my $seen = $mk->{ seen};
        unless ( --$seen->{ $val} ) {
            delete $seen->{ $val};
            if ( $mk->{ max} == $val ) {
                # lost the maximum, recalculate
                undef $mk->{ max};
                _to_max( $mk->{ max}, keys %$seen);
            }
        }
    }
    $mk;
}

sub _to_max {
    my $var = \ shift;
    defined $_ and ( not defined $$var or $$var < $_) and $$var = $_ for @_;
    $$var;
}

########################################### main pod documentation begin ##


1; #this line is important and will help the module return a true value

__END__

=pod

=encoding UTF-8

=head1 NAME

Text::Aligner

=head1 VERSION

version 0.13

=head1 SYNOPSIS

  use Text::Aligner qw( align );

  # Print the words "just a test!" right-justified each on a line:

  my @lines = align( 'right', qw( just a test!);
  print "$_\n" for @lines;

=head1 DESCRIPTION

Text::Aligner exports a single function, align(), which is
used to justify strings to various alignment styles.  The
alignment specification is the first argument, followed by
any number of scalars which are subject to alignment.

The operation depends on context.  In list context, a list of
the justified scalars is returned.  In scalar context, the
justified arguments are joined into a single string with newlines
appended.  The original arguments remain unchanged.  In void
context, in-place justification is attempted.  In this case, all
arguments must be lvalues.

Align() also does one level of scalar dereferencing.  That is,
whenever one of the arguments is a scalar reference, the scalar
pointed to is aligned instead.  Other references are simply stringified.
An undefined argument is interpreted as an empty string without
complaint.

Alignment respects colorizing escape sequences a la L<Term::ANSIColor>
which means it knows that these sequences don't take up space on
the screen.

=head1 NAME

Text::Aligner - module to align text.

=head1 ALIGNMENT

The first argument of the align() function is an alignment style, a
single scalar.

It can be one of the strings "left", "right", "center", "num", "point",
or "auto", or a regular expression (qr/.../), or a coderef.

A default style of "left" is assumed for every other value, including
"" and undef.

"left", "right" and "center" have the obvious meanings.  These can
also be given as numbers 0, 1, and 0.5 respectively. (Other numbers
are also possible, but probably not very useful).

"num", and its synonym "point", specify that the decimal points be
aligned (assumed on the right, unless present).  Arbitrary (non-numeric)
strings are also aligned in this manner, so they end up one column left
of the (possibly assumed) decimal point, flush right with any integers.
For the occasional string like "inf", or "-" for missing values, this
may be the right place.  A string-only column ends up right-aligned
(unless there are points present).

The "auto" style separates numeric strings (that are composed of
"-", ".", and digits in the usual manner) and aligns them numerically.
Other strings are left aligned with the number that sticks out
farthest to the left.  This gives left alignment for string-only
columns and numeric alignment for columns of numbers.  In mixed
columns, strings are reasonably placed to serve as column headings
or intermediate titles.

With "num" (and "point") it is possible to specify another character
for the decimal point in the form "num(,)".  In fact, you can specify
any string after a leading "(", and the closing ")" is optional.
"point(=>)" could be used to align certain pieces of Perl code.  This
option is currently not available with "auto" alignment (because
recognition of numbers is Anglo-centric).

If a regular expression is specified, the points are aligned where
the first match of the regex starts.  A match is assumed immediately
after the string if it doesn't match.

A regular expression is a powerful way of alignment specification.  It
can replace most others easily, except center alignment and, of course,
the double action of "auto".

=head1 POSITIONERS

For entirely self-defined forms of alignment, a coderef, also known
as a positioner, can be given instead of an alignment style.  This
code will be called once or more times with the string to be aligned
as its argument.  It must return two numbers, a width and a position,
that describe how to align a string with other strings.

The width should normally be the length of the string.  The position
defines a point relative to the beginning of the string, which is
aligned with the positions given for other strings.

A zero position for all strings results in left alignment, positioning
to the end of the string results in right alignment, and returning
half the length gives center alignment.  "num" alignment is realized
by marking the position of the decimal point.

Note that the position you return is a relative measure.  Adding a
constant value to all positions results in no change in alignment.
It doesn't have to point inside the string (as in right alignment,
where it points one character past the end of the string).

The first return value of a positioner should almost always be the
length of the given string.  However, it may be useful to lie about
the string length if the string contains escape sequences that occupy
no place on screen.

=head1 SUBROUTINES

=head2 align($style, $str)

See above.

=head2 new(...)

For internal use.

=head1 USAGE

  use Text::Aligner qw( align );

  align( $style, $str, ...);

  $style must be given and must be an alignment specification.
  Any number of scalars can follow.  An argument that contains a
  scalar reference is dereferenced before it is used.  In scalar
  and list context, the aligned strings are returned.  In void
  context, the values are aligned in place and must be lvalues.

=head1 BUGS

None known as of release, but...

=head1 AUTHOR

    Anno Siegel
    CPAN ID: ANNO

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

perl(1)

L<Text::Table> .

=head1 AUTHOR

Shlomi Fish <shlomif@cpan.org>

=head1 COPYRIGHT AND LICENSE

This software is Copyright (c) 2002 by Anno Siegel.

This is free software, licensed under:

  The MIT (X11) License

=cut
