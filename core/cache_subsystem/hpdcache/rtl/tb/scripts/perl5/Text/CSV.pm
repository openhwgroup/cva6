package Text::CSV;


use strict;
use Exporter;
use Carp ();
use vars qw( $VERSION $DEBUG @ISA @EXPORT_OK );
@ISA = qw( Exporter );
@EXPORT_OK = qw( csv );

BEGIN {
    $VERSION = '1.97';
    $DEBUG   = 0;
}

# if use CSV_XS, requires version
my $Module_XS  = 'Text::CSV_XS';
my $Module_PP  = 'Text::CSV_PP';
my $XS_Version = '1.02';

my $Is_Dynamic = 0;

my @PublicMethods = qw/
    version error_diag error_input
    known_attributes csv
    PV IV NV
/;
#

# Check the environment variable to decide worker module.

unless ($Text::CSV::Worker) {
    $Text::CSV::DEBUG and  Carp::carp("Check used worker module...");

    if ( exists $ENV{PERL_TEXT_CSV} ) {
        if ($ENV{PERL_TEXT_CSV} eq '0' or $ENV{PERL_TEXT_CSV} eq 'Text::CSV_PP') {
            _load_pp() or Carp::croak $@;
        }
        elsif ($ENV{PERL_TEXT_CSV} eq '1' or $ENV{PERL_TEXT_CSV} =~ /Text::CSV_XS\s*,\s*Text::CSV_PP/) {
            _load_xs() or _load_pp() or Carp::croak $@;
        }
        elsif ($ENV{PERL_TEXT_CSV} eq '2' or $ENV{PERL_TEXT_CSV} eq 'Text::CSV_XS') {
            _load_xs() or Carp::croak $@;
        }
        else {
            Carp::croak "The value of environmental variable 'PERL_TEXT_CSV' is invalid.";
        }
    }
    else {
        _load_xs() or _load_pp() or Carp::croak $@;
    }

}

sub new { # normal mode
    my $proto = shift;
    my $class = ref($proto) || $proto;

    unless ( $proto ) { # for Text::CSV_XS/PP::new(0);
        return eval qq| $Text::CSV::Worker\::new( \$proto ) |;
    }

    #if (ref $_[0] and $_[0]->{module}) {
    #    Carp::croak("Can't set 'module' in non dynamic mode.");
    #}

    if ( my $obj = $Text::CSV::Worker->new(@_) ) {
        $obj->{_MODULE} = $Text::CSV::Worker;
        bless $obj, $class;
        return $obj;
    }
    else {
        return;
    }


}


sub require_xs_version { $XS_Version; }


sub module {
    my $proto = shift;
    return   !ref($proto)            ? $Text::CSV::Worker
           :  ref($proto->{_MODULE}) ? ref($proto->{_MODULE}) : $proto->{_MODULE};
}

*backend = *module;


sub is_xs {
    return $_[0]->module eq $Module_XS;
}


sub is_pp {
    return $_[0]->module eq $Module_PP;
}


sub is_dynamic { $Is_Dynamic; }

sub _load_xs { _load($Module_XS, $XS_Version) }

sub _load_pp { _load($Module_PP) }

sub _load {
    my ($module, $version) = @_;
    $version ||= '';

    $Text::CSV::DEBUG and Carp::carp "Load $module.";

    eval qq| use $module $version |;

    return if $@;

    push @Text::CSV::ISA, $module;
    $Text::CSV::Worker = $module;

    local $^W;
    no strict qw(refs);

    for my $method (@PublicMethods) {
        *{"Text::CSV::$method"} = \&{"$module\::$method"};
    }
    return 1;
}



1;
__END__

=pod

=head1 NAME

Text::CSV - comma-separated values manipulator (using XS or PurePerl)


=head1 SYNOPSIS

 use Text::CSV;

 my @rows;
 my $csv = Text::CSV->new ( { binary => 1 } )  # should set binary attribute.
                 or die "Cannot use CSV: ".Text::CSV->error_diag ();

 open my $fh, "<:encoding(utf8)", "test.csv" or die "test.csv: $!";
 while ( my $row = $csv->getline( $fh ) ) {
     $row->[2] =~ m/pattern/ or next; # 3rd field should match
     push @rows, $row;
 }
 $csv->eof or $csv->error_diag();
 close $fh;

 $csv->eol ("\r\n");

 open $fh, ">:encoding(utf8)", "new.csv" or die "new.csv: $!";
 $csv->print ($fh, $_) for @rows;
 close $fh or die "new.csv: $!";

 #
 # parse and combine style
 #

 $status = $csv->combine(@columns);    # combine columns into a string
 $line   = $csv->string();             # get the combined string

 $status  = $csv->parse($line);        # parse a CSV string into fields
 @columns = $csv->fields();            # get the parsed fields

 $status       = $csv->status ();      # get the most recent status
 $bad_argument = $csv->error_input (); # get the most recent bad argument
 $diag         = $csv->error_diag ();  # if an error occurred, explains WHY

 $status = $csv->print ($io, $colref); # Write an array of fields
                                       # immediately to a file $io
 $colref = $csv->getline ($io);        # Read a line from file $io,
                                       # parse it and return an array
                                       # ref of fields
 $csv->column_names (@names);          # Set column names for getline_hr ()
 $ref = $csv->getline_hr ($io);        # getline (), but returns a hashref
 $eof = $csv->eof ();                  # Indicate if last parse or
                                       # getline () hit End Of File

 $csv->types(\@t_array);               # Set column types

=head1 DESCRIPTION

Text::CSV is a thin wrapper for L<Text::CSV_XS>-compatible modules now.
All the backend modules provide facilities for the composition and
decomposition of comma-separated values. Text::CSV uses Text::CSV_XS
by default, and when Text::CSV_XS is not available, falls back on
L<Text::CSV_PP>, which is bundled in the same distribution as this module.

=head1 CHOOSING BACKEND

This module respects an environmental variable called C<PERL_TEXT_CSV>
when it decides a backend module to use. If this environmental variable
is not set, it tries to load Text::CSV_XS, and if Text::CSV_XS is not
available, falls back on Text::CSV_PP;

If you always don't want it to fall back on Text::CSV_PP, set the variable
like this (C<export> may be C<setenv>, C<set> and the likes, depending
on your environment):

  > export PERL_TEXT_CSV=Text::CSV_XS

If you prefer Text::CSV_XS to Text::CSV_PP (default), then:

  > export PERL_TEXT_CSV=Text::CSV_XS,Text::CSV_PP

You may also want to set this variable at the top of your test files, in order
not to be bothered with incompatibilities between backends (you need to wrap
this in C<BEGIN>, and set before actually C<use>-ing Text::CSV module, as it
decides its backend as soon as it's loaded):

  BEGIN { $ENV{PERL_TEXT_CSV}='Text::CSV_PP'; }
  use Text::CSV;

=head1 NOTES

This section is taken from Text::CSV_XS.

=head2 Embedded newlines

B<Important Note>:  The default behavior is to accept only ASCII characters
in the range from C<0x20> (space) to C<0x7E> (tilde).   This means that the
fields can not contain newlines. If your data contains newlines embedded in
fields, or characters above C<0x7E> (tilde), or binary data, you B<I<must>>
set C<< binary => 1 >> in the call to L</new>. To cover the widest range of
parsing options, you will always want to set binary.

But you still have the problem  that you have to pass a correct line to the
L</parse> method, which is more complicated from the usual point of usage:

 my $csv = Text::CSV->new ({ binary => 1, eol => $/ });
 while (<>) {		#  WRONG!
     $csv->parse ($_);
     my @fields = $csv->fields ();
     }

this will break, as the C<while> might read broken lines:  it does not care
about the quoting. If you need to support embedded newlines,  the way to go
is to  B<not>  pass L<C<eol>|/eol> in the parser  (it accepts C<\n>, C<\r>,
B<and> C<\r\n> by default) and then

 my $csv = Text::CSV->new ({ binary => 1 });
 open my $fh, "<", $file or die "$file: $!";
 while (my $row = $csv->getline ($fh)) {
     my @fields = @$row;
     }

The old(er) way of using global file handles is still supported

 while (my $row = $csv->getline (*ARGV)) { ... }

=head2 Unicode

Unicode is only tested to work with perl-5.8.2 and up.

See also L</BOM>.

The simplest way to ensure the correct encoding is used for  in- and output
is by either setting layers on the filehandles, or setting the L</encoding>
argument for L</csv>.

 open my $fh, "<:encoding(UTF-8)", "in.csv"  or die "in.csv: $!";
or
 my $aoa = csv (in => "in.csv",     encoding => "UTF-8");

 open my $fh, ">:encoding(UTF-8)", "out.csv" or die "out.csv: $!";
or
 csv (in => $aoa, out => "out.csv", encoding => "UTF-8");

On parsing (both for  L</getline> and  L</parse>),  if the source is marked
being UTF8, then all fields that are marked binary will also be marked UTF8.

On combining (L</print>  and  L</combine>):  if any of the combining fields
was marked UTF8, the resulting string will be marked as UTF8.  Note however
that all fields  I<before>  the first field marked UTF8 and contained 8-bit
characters that were not upgraded to UTF8,  these will be  C<bytes>  in the
resulting string too, possibly causing unexpected errors.  If you pass data
of different encoding,  or you don't know if there is  different  encoding,
force it to be upgraded before you pass them on:

 $csv->print ($fh, [ map { utf8::upgrade (my $x = $_); $x } @data ]);

For complete control over encoding, please use L<Text::CSV::Encoded>:

 use Text::CSV::Encoded;
 my $csv = Text::CSV::Encoded->new ({
     encoding_in  => "iso-8859-1", # the encoding comes into   Perl
     encoding_out => "cp1252",     # the encoding comes out of Perl
     });

 $csv = Text::CSV::Encoded->new ({ encoding  => "utf8" });
 # combine () and print () accept *literally* utf8 encoded data
 # parse () and getline () return *literally* utf8 encoded data

 $csv = Text::CSV::Encoded->new ({ encoding  => undef }); # default
 # combine () and print () accept UTF8 marked data
 # parse () and getline () return UTF8 marked data

=head2 BOM

BOM  (or Byte Order Mark)  handling is available only inside the L</header>
method.   This method supports the following encodings: C<utf-8>, C<utf-1>,
C<utf-32be>, C<utf-32le>, C<utf-16be>, C<utf-16le>, C<utf-ebcdic>, C<scsu>,
C<bocu-1>, and C<gb-18030>. See L<Wikipedia|https://en.wikipedia.org/wiki/Byte_order_mark>.

If a file has a BOM, the easiest way to deal with that is

 my $aoh = csv (in => $file, detect_bom => 1);

All records will be encoded based on the detected BOM.

This implies a call to the  L</header>  method,  which defaults to also set
the L</column_names>. So this is B<not> the same as

 my $aoh = csv (in => $file, headers => "auto");

which only reads the first record to set  L</column_names>  but ignores any
meaning of possible present BOM.

=head1 METHODS

This section is also taken from Text::CSV_XS.

=head2 version

(Class method) Returns the current module version.

=head2 new

(Class method) Returns a new instance of class Text::CSV. The attributes
are described by the (optional) hash ref C<\%attr>.

 my $csv = Text::CSV->new ({ attributes ... });

The following attributes are available:

=head3 eol

 my $csv = Text::CSV->new ({ eol => $/ });
           $csv->eol (undef);
 my $eol = $csv->eol;

The end-of-line string to add to rows for L</print> or the record separator
for L</getline>.

When not passed in a B<parser> instance,  the default behavior is to accept
C<\n>, C<\r>, and C<\r\n>, so it is probably safer to not specify C<eol> at
all. Passing C<undef> or the empty string behave the same.

When not passed in a B<generating> instance,  records are not terminated at
all, so it is probably wise to pass something you expect. A safe choice for
C<eol> on output is either C<$/> or C<\r\n>.

Common values for C<eol> are C<"\012"> (C<\n> or Line Feed),  C<"\015\012">
(C<\r\n> or Carriage Return, Line Feed),  and C<"\015">  (C<\r> or Carriage
Return). The L<C<eol>|/eol> attribute cannot exceed 7 (ASCII) characters.

If both C<$/> and L<C<eol>|/eol> equal C<"\015">, parsing lines that end on
only a Carriage Return without Line Feed, will be L</parse>d correct.

=head3 sep_char

 my $csv = Text::CSV->new ({ sep_char => ";" });
         $csv->sep_char (";");
 my $c = $csv->sep_char;

The char used to separate fields, by default a comma. (C<,>).  Limited to a
single-byte character, usually in the range from C<0x20> (space) to C<0x7E>
(tilde). When longer sequences are required, use L<C<sep>|/sep>.

The separation character can not be equal to the quote character  or to the
escape character.

=head3 sep

 my $csv = Text::CSV->new ({ sep => "\N{FULLWIDTH COMMA}" });
           $csv->sep (";");
 my $sep = $csv->sep;

The chars used to separate fields, by default undefined. Limited to 8 bytes.

When set, overrules L<C<sep_char>|/sep_char>.  If its length is one byte it
acts as an alias to L<C<sep_char>|/sep_char>.

=head3 quote_char

 my $csv = Text::CSV->new ({ quote_char => "'" });
         $csv->quote_char (undef);
 my $c = $csv->quote_char;

The character to quote fields containing blanks or binary data,  by default
the double quote character (C<">).  A value of undef suppresses quote chars
(for simple cases only). Limited to a single-byte character, usually in the
range from  C<0x20> (space) to  C<0x7E> (tilde).  When longer sequences are
required, use L<C<quote>|/quote>.

C<quote_char> can not be equal to L<C<sep_char>|/sep_char>.

=head3 quote

 my $csv = Text::CSV->new ({ quote => "\N{FULLWIDTH QUOTATION MARK}" });
             $csv->quote ("'");
 my $quote = $csv->quote;

The chars used to quote fields, by default undefined. Limited to 8 bytes.

When set, overrules L<C<quote_char>|/quote_char>. If its length is one byte
it acts as an alias to L<C<quote_char>|/quote_char>.

=head3 escape_char

 my $csv = Text::CSV->new ({ escape_char => "\\" });
         $csv->escape_char (":");
 my $c = $csv->escape_char;

The character to  escape  certain characters inside quoted fields.  This is
limited to a  single-byte  character,  usually  in the  range from  C<0x20>
(space) to C<0x7E> (tilde).

The C<escape_char> defaults to being the double-quote mark (C<">). In other
words the same as the default L<C<quote_char>|/quote_char>. This means that
doubling the quote mark in a field escapes it:

 "foo","bar","Escape ""quote mark"" with two ""quote marks""","baz"

If  you  change  the   L<C<quote_char>|/quote_char>  without  changing  the
C<escape_char>,  the  C<escape_char> will still be the double-quote (C<">).
If instead you want to escape the  L<C<quote_char>|/quote_char> by doubling
it you will need to also change the  C<escape_char>  to be the same as what
you have changed the L<C<quote_char>|/quote_char> to.

Setting C<escape_char> to <undef> or C<""> will disable escaping completely
and is greatly discouraged. This will also disable C<escape_null>.

The escape character can not be equal to the separation character.

=head3 binary

 my $csv = Text::CSV->new ({ binary => 1 });
         $csv->binary (0);
 my $f = $csv->binary;

If this attribute is C<1>,  you may use binary characters in quoted fields,
including line feeds, carriage returns and C<NULL> bytes. (The latter could
be escaped as C<"0>.) By default this feature is off.

If a string is marked UTF8,  C<binary> will be turned on automatically when
binary characters other than C<CR> and C<NL> are encountered.   Note that a
simple string like C<"\x{00a0}"> might still be binary, but not marked UTF8,
so setting C<< { binary => 1 } >> is still a wise option.

=head3 strict

 my $csv = Text::CSV->new ({ strict => 1 });
         $csv->strict (0);
 my $f = $csv->strict;

If this attribute is set to C<1>, any row that parses to a different number
of fields than the previous row will cause the parser to throw error 2014.

=head3 formula_handling

=head3 formula

 my $csv = Text::CSV->new ({ formula => "none" });
         $csv->formula ("none");
 my $f = $csv->formula;

This defines the behavior of fields containing I<formulas>. As formulas are
considered dangerous in spreadsheets, this attribute can define an optional
action to be taken if a field starts with an equal sign (C<=>).

For purpose of code-readability, this can also be written as

 my $csv = Text::CSV->new ({ formula_handling => "none" });
         $csv->formula_handling ("none");
 my $f = $csv->formula_handling;

Possible values for this attribute are

=over 2

=item none

Take no specific action. This is the default.

 $csv->formula ("none");

=item die

Cause the process to C<die> whenever a leading C<=> is encountered.

 $csv->formula ("die");

=item croak

Cause the process to C<croak> whenever a leading C<=> is encountered.  (See
L<Carp>)

 $csv->formula ("croak");

=item diag

Report position and content of the field whenever a leading  C<=> is found.
The value of the field is unchanged.

 $csv->formula ("diag");

=item empty

Replace the content of fields that start with a C<=> with the empty string.

 $csv->formula ("empty");
 $csv->formula ("");

=item undef

Replace the content of fields that start with a C<=> with C<undef>.

 $csv->formula ("undef");
 $csv->formula (undef);

=back

All other values will give a warning and then fallback to C<diag>.

=head3 decode_utf8

 my $csv = Text::CSV->new ({ decode_utf8 => 1 });
         $csv->decode_utf8 (0);
 my $f = $csv->decode_utf8;

This attributes defaults to TRUE.

While I<parsing>,  fields that are valid UTF-8, are automatically set to be
UTF-8, so that

  $csv->parse ("\xC4\xA8\n");

results in

  PV("\304\250"\0) [UTF8 "\x{128}"]

Sometimes it might not be a desired action.  To prevent those upgrades, set
this attribute to false, and the result will be

  PV("\304\250"\0)

=head3 auto_diag

 my $csv = Text::CSV->new ({ auto_diag => 1 });
         $csv->auto_diag (2);
 my $l = $csv->auto_diag;

Set this attribute to a number between C<1> and C<9> causes  L</error_diag>
to be automatically called in void context upon errors.

In case of error C<2012 - EOF>, this call will be void.

If C<auto_diag> is set to a numeric value greater than C<1>, it will C<die>
on errors instead of C<warn>.  If set to anything unrecognized,  it will be
silently ignored.

Future extensions to this feature will include more reliable auto-detection
of  C<autodie>  being active in the scope of which the error occurred which
will increment the value of C<auto_diag> with  C<1> the moment the error is
detected.

=head3 diag_verbose

 my $csv = Text::CSV->new ({ diag_verbose => 1 });
         $csv->diag_verbose (2);
 my $l = $csv->diag_verbose;

Set the verbosity of the output triggered by C<auto_diag>.   Currently only
adds the current  input-record-number  (if known)  to the diagnostic output
with an indication of the position of the error.

=head3 blank_is_undef

 my $csv = Text::CSV->new ({ blank_is_undef => 1 });
         $csv->blank_is_undef (0);
 my $f = $csv->blank_is_undef;

Under normal circumstances, C<CSV> data makes no distinction between quoted-
and unquoted empty fields.  These both end up in an empty string field once
read, thus

 1,"",," ",2

is read as

 ("1", "", "", " ", "2")

When I<writing>  C<CSV> files with either  L<C<always_quote>|/always_quote>
or  L<C<quote_empty>|/quote_empty> set, the unquoted  I<empty> field is the
result of an undefined value.   To enable this distinction when  I<reading>
C<CSV>  data,  the  C<blank_is_undef>  attribute will cause  unquoted empty
fields to be set to C<undef>, causing the above to be parsed as

 ("1", "", undef, " ", "2")

note that this is specifically important when loading  C<CSV> fields into a
database that allows C<NULL> values,  as the perl equivalent for C<NULL> is
C<undef> in L<DBI> land.

=head3 empty_is_undef

 my $csv = Text::CSV->new ({ empty_is_undef => 1 });
         $csv->empty_is_undef (0);
 my $f = $csv->empty_is_undef;

Going one  step  further  than  L<C<blank_is_undef>|/blank_is_undef>,  this
attribute converts all empty fields to C<undef>, so

 1,"",," ",2

is read as

 (1, undef, undef, " ", 2)

Note that this effects only fields that are  originally  empty,  not fields
that are empty after stripping allowed whitespace. YMMV.

=head3 allow_whitespace

 my $csv = Text::CSV->new ({ allow_whitespace => 1 });
         $csv->allow_whitespace (0);
 my $f = $csv->allow_whitespace;

When this option is set to true,  the whitespace  (C<TAB>'s and C<SPACE>'s)
surrounding  the  separation character  is removed when parsing.  If either
C<TAB> or C<SPACE> is one of the three characters L<C<sep_char>|/sep_char>,
L<C<quote_char>|/quote_char>, or L<C<escape_char>|/escape_char> it will not
be considered whitespace.

Now lines like:

 1 , "foo" , bar , 3 , zapp

are parsed as valid C<CSV>, even though it violates the C<CSV> specs.

Note that  B<all>  whitespace is stripped from both  start and  end of each
field.  That would make it  I<more> than a I<feature> to enable parsing bad
C<CSV> lines, as

 1,   2.0,  3,   ape  , monkey

will now be parsed as

 ("1", "2.0", "3", "ape", "monkey")

even if the original line was perfectly acceptable C<CSV>.

=head3 allow_loose_quotes

 my $csv = Text::CSV->new ({ allow_loose_quotes => 1 });
         $csv->allow_loose_quotes (0);
 my $f = $csv->allow_loose_quotes;

By default, parsing unquoted fields containing L<C<quote_char>|/quote_char>
characters like

 1,foo "bar" baz,42

would result in parse error 2034.  Though it is still bad practice to allow
this format,  we  cannot  help  the  fact  that  some  vendors  make  their
applications spit out lines styled this way.

If there is B<really> bad C<CSV> data, like

 1,"foo "bar" baz",42

or

 1,""foo bar baz"",42

there is a way to get this data-line parsed and leave the quotes inside the
quoted field as-is.  This can be achieved by setting  C<allow_loose_quotes>
B<AND> making sure that the L<C<escape_char>|/escape_char> is  I<not> equal
to L<C<quote_char>|/quote_char>.

=head3 allow_loose_escapes

 my $csv = Text::CSV->new ({ allow_loose_escapes => 1 });
         $csv->allow_loose_escapes (0);
 my $f = $csv->allow_loose_escapes;

Parsing fields  that  have  L<C<escape_char>|/escape_char>  characters that
escape characters that do not need to be escaped, like:

 my $csv = Text::CSV->new ({ escape_char => "\\" });
 $csv->parse (qq{1,"my bar\'s",baz,42});

would result in parse error 2025.   Though it is bad practice to allow this
format,  this attribute enables you to treat all escape character sequences
equal.

=head3 allow_unquoted_escape

 my $csv = Text::CSV->new ({ allow_unquoted_escape => 1 });
         $csv->allow_unquoted_escape (0);
 my $f = $csv->allow_unquoted_escape;

A backward compatibility issue where L<C<escape_char>|/escape_char> differs
from L<C<quote_char>|/quote_char>  prevents  L<C<escape_char>|/escape_char>
to be in the first position of a field.  If L<C<quote_char>|/quote_char> is
equal to the default C<"> and L<C<escape_char>|/escape_char> is set to C<\>,
this would be illegal:

 1,\0,2

Setting this attribute to C<1>  might help to overcome issues with backward
compatibility and allow this style.

=head3 always_quote

 my $csv = Text::CSV->new ({ always_quote => 1 });
         $csv->always_quote (0);
 my $f = $csv->always_quote;

By default the generated fields are quoted only if they I<need> to be.  For
example, if they contain the separator character. If you set this attribute
to C<1> then I<all> defined fields will be quoted. (C<undef> fields are not
quoted, see L</blank_is_undef>). This makes it quite often easier to handle
exported data in external applications.

=head3 quote_space

 my $csv = Text::CSV->new ({ quote_space => 1 });
         $csv->quote_space (0);
 my $f = $csv->quote_space;

By default,  a space in a field would trigger quotation.  As no rule exists
this to be forced in C<CSV>,  nor any for the opposite, the default is true
for safety.   You can exclude the space  from this trigger  by setting this
attribute to 0.

=head3 quote_empty

 my $csv = Text::CSV->new ({ quote_empty => 1 });
         $csv->quote_empty (0);
 my $f = $csv->quote_empty;

By default the generated fields are quoted only if they I<need> to be.   An
empty (defined) field does not need quotation. If you set this attribute to
C<1> then I<empty> defined fields will be quoted.  (C<undef> fields are not
quoted, see L</blank_is_undef>). See also L<C<always_quote>|/always_quote>.

=head3 quote_binary

 my $csv = Text::CSV->new ({ quote_binary => 1 });
         $csv->quote_binary (0);
 my $f = $csv->quote_binary;

By default,  all "unsafe" bytes inside a string cause the combined field to
be quoted.  By setting this attribute to C<0>, you can disable that trigger
for bytes >= C<0x7F>.

=head3 escape_null

 my $csv = Text::CSV->new ({ escape_null => 1 });
         $csv->escape_null (0);
 my $f = $csv->escape_null;

By default, a C<NULL> byte in a field would be escaped. This option enables
you to treat the  C<NULL>  byte as a simple binary character in binary mode
(the C<< { binary => 1 } >> is set).  The default is true.  You can prevent
C<NULL> escapes by setting this attribute to C<0>.

When the C<escape_char> attribute is set to undefined,  this attribute will
be set to false.

The default setting will encode "=\x00=" as

 "="0="

With C<escape_null> set, this will result in

 "=\x00="

The default when using the C<csv> function is C<false>.

For backward compatibility reasons,  the deprecated old name  C<quote_null>
is still recognized.

=head3 keep_meta_info

 my $csv = Text::CSV->new ({ keep_meta_info => 1 });
         $csv->keep_meta_info (0);
 my $f = $csv->keep_meta_info;

By default, the parsing of input records is as simple and fast as possible.
However,  some parsing information - like quotation of the original field -
is lost in that process.  Setting this flag to true enables retrieving that
information after parsing with  the methods  L</meta_info>,  L</is_quoted>,
and L</is_binary> described below.  Default is false for performance.

If you set this attribute to a value greater than 9,   than you can control
output quotation style like it was used in the input of the the last parsed
record (unless quotation was added because of other reasons).

 my $csv = Text::CSV->new ({
    binary         => 1,
    keep_meta_info => 1,
    quote_space    => 0,
    });

 my $row = $csv->parse (q{1,,"", ," ",f,"g","h""h",help,"help"});

 $csv->print (*STDOUT, \@row);
 # 1,,, , ,f,g,"h""h",help,help
 $csv->keep_meta_info (11);
 $csv->print (*STDOUT, \@row);
 # 1,,"", ," ",f,"g","h""h",help,"help"

=head3 undef_str

 my $csv = Text::CSV->new ({ undef_str => "\\N" });
         $csv->undef_str (undef);
 my $s = $csv->undef_str;

This attribute optionally defines the output of undefined fields. The value
passed is not changed at all, so if it needs quotation, the quotation needs
to be included in the value of the attribute.  Use with caution, as passing
a value like  C<",",,,,""">  will for sure mess up your output. The default
for this attribute is C<undef>, meaning no special treatment.

This attribute is useful when exporting  CSV data  to be imported in custom
loaders, like for MySQL, that recognize special sequences for C<NULL> data.

=head3 verbatim

 my $csv = Text::CSV->new ({ verbatim => 1 });
         $csv->verbatim (0);
 my $f = $csv->verbatim;

This is a quite controversial attribute to set,  but makes some hard things
possible.

The rationale behind this attribute is to tell the parser that the normally
special characters newline (C<NL>) and Carriage Return (C<CR>)  will not be
special when this flag is set,  and be dealt with  as being ordinary binary
characters. This will ease working with data with embedded newlines.

When  C<verbatim>  is used with  L</getline>,  L</getline>  auto-C<chomp>'s
every line.

Imagine a file format like

 M^^Hans^Janssen^Klas 2\n2A^Ja^11-06-2007#\r\n

where, the line ending is a very specific C<"#\r\n">, and the sep_char is a
C<^> (caret).   None of the fields is quoted,   but embedded binary data is
likely to be present. With the specific line ending, this should not be too
hard to detect.

By default,  Text::CSV'  parse function is instructed to only know about
C<"\n"> and C<"\r">  to be legal line endings,  and so has to deal with the
embedded newline as a real C<end-of-line>,  so it can scan the next line if
binary is true, and the newline is inside a quoted field. With this option,
we tell L</parse> to parse the line as if C<"\n"> is just nothing more than
a binary character.

For L</parse> this means that the parser has no more idea about line ending
and L</getline> C<chomp>s line endings on reading.

=head3 types

A set of column types; the attribute is immediately passed to the L</types>
method.

=head3 callbacks

See the L</Callbacks> section below.

=head3 accessors

To sum it up,

 $csv = Text::CSV->new ();

is equivalent to

 $csv = Text::CSV->new ({
     eol                   => undef, # \r, \n, or \r\n
     sep_char              => ',',
     sep                   => undef,
     quote_char            => '"',
     quote                 => undef,
     escape_char           => '"',
     binary                => 0,
     decode_utf8           => 1,
     auto_diag             => 0,
     diag_verbose          => 0,
     blank_is_undef        => 0,
     empty_is_undef        => 0,
     allow_whitespace      => 0,
     allow_loose_quotes    => 0,
     allow_loose_escapes   => 0,
     allow_unquoted_escape => 0,
     always_quote          => 0,
     quote_empty           => 0,
     quote_space           => 1,
     escape_null           => 1,
     quote_binary          => 1,
     keep_meta_info        => 0,
     verbatim              => 0,
     undef_str             => undef,
     types                 => undef,
     callbacks             => undef,
     });

For all of the above mentioned flags, an accessor method is available where
you can inquire the current value, or change the value

 my $quote = $csv->quote_char;
 $csv->binary (1);

It is not wise to change these settings halfway through writing C<CSV> data
to a stream. If however you want to create a new stream using the available
C<CSV> object, there is no harm in changing them.

If the L</new> constructor call fails,  it returns C<undef>,  and makes the
fail reason available through the L</error_diag> method.

 $csv = Text::CSV->new ({ ecs_char => 1 }) or
     die "".Text::CSV->error_diag ();

L</error_diag> will return a string like

 "INI - Unknown attribute 'ecs_char'"

=head2 known_attributes

 @attr = Text::CSV->known_attributes;
 @attr = Text::CSV::known_attributes;
 @attr = $csv->known_attributes;

This method will return an ordered list of all the supported  attributes as
described above.   This can be useful for knowing what attributes are valid
in classes that use or extend Text::CSV.

=head2 print

 $status = $csv->print ($fh, $colref);

Similar to  L</combine> + L</string> + L</print>,  but much more efficient.
It expects an array ref as input  (not an array!)  and the resulting string
is not really  created,  but  immediately  written  to the  C<$fh>  object,
typically an IO handle or any other object that offers a L</print> method.

For performance reasons  C<print>  does not create a result string,  so all
L</string>, L</status>, L</fields>, and L</error_input> methods will return
undefined information after executing this method.

If C<$colref> is C<undef>  (explicit,  not through a variable argument) and
L</bind_columns>  was used to specify fields to be printed,  it is possible
to make performance improvements, as otherwise data would have to be copied
as arguments to the method call:

 $csv->bind_columns (\($foo, $bar));
 $status = $csv->print ($fh, undef);

A short benchmark

 my @data = ("aa" .. "zz");
 $csv->bind_columns (\(@data));

 $csv->print ($fh, [ @data ]);   # 11800 recs/sec
 $csv->print ($fh,  \@data  );   # 57600 recs/sec
 $csv->print ($fh,   undef  );   # 48500 recs/sec

=head2 say

 $status = $csv->say ($fh, $colref);

Like L<C<print>|/print>, but L<C<eol>|/eol> defaults to C<$\>.

=head2 print_hr

 $csv->print_hr ($fh, $ref);

Provides an easy way  to print a  C<$ref>  (as fetched with L</getline_hr>)
provided the column names are set with L</column_names>.

It is just a wrapper method with basic parameter checks over

 $csv->print ($fh, [ map { $ref->{$_} } $csv->column_names ]);

=head2 combine

 $status = $csv->combine (@fields);

This method constructs a C<CSV> record from  C<@fields>,  returning success
or failure.   Failure can result from lack of arguments or an argument that
contains an invalid character.   Upon success,  L</string> can be called to
retrieve the resultant C<CSV> string.  Upon failure,  the value returned by
L</string> is undefined and L</error_input> could be called to retrieve the
invalid argument.

=head2 string

 $line = $csv->string ();

This method returns the input to  L</parse>  or the resultant C<CSV> string
of L</combine>, whichever was called more recently.

=head2 getline

 $colref = $csv->getline ($fh);

This is the counterpart to  L</print>,  as L</parse>  is the counterpart to
L</combine>:  it parses a row from the C<$fh>  handle using the L</getline>
method associated with C<$fh>  and parses this row into an array ref.  This
array ref is returned by the function or C<undef> for failure.  When C<$fh>
does not support C<getline>, you are likely to hit errors.

When fields are bound with L</bind_columns> the return value is a reference
to an empty list.

The L</string>, L</fields>, and L</status> methods are meaningless again.

=head2 getline_all

 $arrayref = $csv->getline_all ($fh);
 $arrayref = $csv->getline_all ($fh, $offset);
 $arrayref = $csv->getline_all ($fh, $offset, $length);

This will return a reference to a list of L<getline ($fh)|/getline> results.
In this call, C<keep_meta_info> is disabled.  If C<$offset> is negative, as
with C<splice>, only the last  C<abs ($offset)> records of C<$fh> are taken
into consideration.

Given a CSV file with 10 lines:

 lines call
 ----- ---------------------------------------------------------
 0..9  $csv->getline_all ($fh)         # all
 0..9  $csv->getline_all ($fh,  0)     # all
 8..9  $csv->getline_all ($fh,  8)     # start at 8
 -     $csv->getline_all ($fh,  0,  0) # start at 0 first 0 rows
 0..4  $csv->getline_all ($fh,  0,  5) # start at 0 first 5 rows
 4..5  $csv->getline_all ($fh,  4,  2) # start at 4 first 2 rows
 8..9  $csv->getline_all ($fh, -2)     # last 2 rows
 6..7  $csv->getline_all ($fh, -4,  2) # first 2 of last  4 rows

=head2 getline_hr

The L</getline_hr> and L</column_names> methods work together  to allow you
to have rows returned as hashrefs.  You must call L</column_names> first to
declare your column names.

 $csv->column_names (qw( code name price description ));
 $hr = $csv->getline_hr ($fh);
 print "Price for $hr->{name} is $hr->{price} EUR\n";

L</getline_hr> will croak if called before L</column_names>.

Note that  L</getline_hr>  creates a hashref for every row and will be much
slower than the combined use of L</bind_columns>  and L</getline> but still
offering the same ease of use hashref inside the loop:

 my @cols = @{$csv->getline ($fh)};
 $csv->column_names (@cols);
 while (my $row = $csv->getline_hr ($fh)) {
     print $row->{price};
     }

Could easily be rewritten to the much faster:

 my @cols = @{$csv->getline ($fh)};
 my $row = {};
 $csv->bind_columns (\@{$row}{@cols});
 while ($csv->getline ($fh)) {
     print $row->{price};
     }

Your mileage may vary for the size of the data and the number of rows. With
perl-5.14.2 the comparison for a 100_000 line file with 14 rows:

            Rate hashrefs getlines
 hashrefs 1.00/s       --     -76%
 getlines 4.15/s     313%       --

=head2 getline_hr_all

 $arrayref = $csv->getline_hr_all ($fh);
 $arrayref = $csv->getline_hr_all ($fh, $offset);
 $arrayref = $csv->getline_hr_all ($fh, $offset, $length);

This will return a reference to a list of   L<getline_hr ($fh)|/getline_hr>
results.  In this call, L<C<keep_meta_info>|/keep_meta_info> is disabled.

=head2 parse

 $status = $csv->parse ($line);

This method decomposes a  C<CSV>  string into fields,  returning success or
failure.   Failure can result from a lack of argument  or the given  C<CSV>
string is improperly formatted.   Upon success, L</fields> can be called to
retrieve the decomposed fields. Upon failure calling L</fields> will return
undefined data and  L</error_input>  can be called to retrieve  the invalid
argument.

You may use the L</types>  method for setting column types.  See L</types>'
description below.

The C<$line> argument is supposed to be a simple scalar. Everything else is
supposed to croak and set error 1500.

=head2 fragment

This function tries to implement RFC7111  (URI Fragment Identifiers for the
text/csv Media Type) - http://tools.ietf.org/html/rfc7111

 my $AoA = $csv->fragment ($fh, $spec);

In specifications,  C<*> is used to specify the I<last> item, a dash (C<->)
to indicate a range.   All indices are C<1>-based:  the first row or column
has index C<1>. Selections can be combined with the semi-colon (C<;>).

When using this method in combination with  L</column_names>,  the returned
reference  will point to a  list of hashes  instead of a  list of lists.  A
disjointed  cell-based combined selection  might return rows with different
number of columns making the use of hashes unpredictable.

 $csv->column_names ("Name", "Age");
 my $AoH = $csv->fragment ($fh, "col=3;8");

If the L</after_parse> callback is active,  it is also called on every line
parsed and skipped before the fragment.

=over 2

=item row

 row=4
 row=5-7
 row=6-*
 row=1-2;4;6-*

=item col

 col=2
 col=1-3
 col=4-*
 col=1-2;4;7-*

=item cell

In cell-based selection, the comma (C<,>) is used to pair row and column

 cell=4,1

The range operator (C<->) using C<cell>s can be used to define top-left and
bottom-right C<cell> location

 cell=3,1-4,6

The C<*> is only allowed in the second part of a pair

 cell=3,2-*,2    # row 3 till end, only column 2
 cell=3,2-3,*    # column 2 till end, only row 3
 cell=3,2-*,*    # strip row 1 and 2, and column 1

Cells and cell ranges may be combined with C<;>, possibly resulting in rows
with different number of columns

 cell=1,1-2,2;3,3-4,4;1,4;4,1

Disjointed selections will only return selected cells.   The cells that are
not  specified  will  not  be  included  in the  returned set,  not even as
C<undef>.  As an example given a C<CSV> like

 11,12,13,...19
 21,22,...28,29
 :            :
 91,...97,98,99

with C<cell=1,1-2,2;3,3-4,4;1,4;4,1> will return:

 11,12,14
 21,22
 33,34
 41,43,44

Overlapping cell-specs will return those cells only once, So
C<cell=1,1-3,3;2,2-4,4;2,3;4,2> will return:

 11,12,13
 21,22,23,24
 31,32,33,34
 42,43,44

=back

L<RFC7111|http://tools.ietf.org/html/rfc7111> does  B<not>  allow different
types of specs to be combined   (either C<row> I<or> C<col> I<or> C<cell>).
Passing an invalid fragment specification will croak and set error 2013.

=head2 column_names

Set the "keys" that will be used in the  L</getline_hr>  calls.  If no keys
(column names) are passed, it will return the current setting as a list.

L</column_names> accepts a list of scalars  (the column names)  or a single
array_ref, so you can pass the return value from L</getline> too:

 $csv->column_names ($csv->getline ($fh));

L</column_names> does B<no> checking on duplicates at all, which might lead
to unexpected results.   Undefined entries will be replaced with the string
C<"\cAUNDEF\cA">, so

 $csv->column_names (undef, "", "name", "name");
 $hr = $csv->getline_hr ($fh);

Will set C<< $hr->{"\cAUNDEF\cA"} >> to the 1st field,  C<< $hr->{""} >> to
the 2nd field, and C<< $hr->{name} >> to the 4th field,  discarding the 3rd
field.

L</column_names> croaks on invalid arguments.

=head2 header

This method does NOT work in perl-5.6.x

Parse the CSV header and set L<C<sep>|/sep>, column_names and encoding.

 my @hdr = $csv->header ($fh);
 $csv->header ($fh, { sep_set => [ ";", ",", "|", "\t" ] });
 $csv->header ($fh, { detect_bom => 1, munge_column_names => "lc" });

The first argument should be a file handle.

This method resets some object properties,  as it is supposed to be invoked
only once per file or stream.  It will leave attributes C<column_names> and
C<bound_columns> alone of setting column names is disabled. Reading headers
on previously process objects might fail on perl-5.8.0 and older.

Assuming that the file opened for parsing has a header, and the header does
not contain problematic characters like embedded newlines,   read the first
line from the open handle then auto-detect whether the header separates the
column names with a character from the allowed separator list.

If any of the allowed separators matches,  and none of the I<other> allowed
separators match,  set  L<C<sep>|/sep>  to that  separator  for the current
CSV instance and use it to parse the first line, map those to lowercase,
and use that to set the instance L</column_names>:

 my $csv = Text::CSV->new ({ binary => 1, auto_diag => 1 });
 open my $fh, "<", "file.csv";
 binmode $fh; # for Windows
 $csv->header ($fh);
 while (my $row = $csv->getline_hr ($fh)) {
     ...
     }

If the header is empty,  contains more than one unique separator out of the
allowed set,  contains empty fields,   or contains identical fields  (after
folding), it will croak with error 1010, 1011, 1012, or 1013 respectively.

If the header contains embedded newlines or is not valid  CSV  in any other
way, this method will croak and leave the parse error untouched.

A successful call to C<header>  will always set the  L<C<sep>|/sep>  of the
C<$csv> object. This behavior can not be disabled.

=head3 return value

On error this method will croak.

In list context,  the headers will be returned whether they are used to set
L</column_names> or not.

In scalar context, the instance itself is returned.  B<Note>: the values as
found in the header will effectively be  B<lost> if  C<set_column_names> is
false.

=head3 Options

=over 2

=item sep_set

 $csv->header ($fh, { sep_set => [ ";", ",", "|", "\t" ] });

The list of legal separators defaults to C<[ ";", "," ]> and can be changed
by this option.  As this is probably the most often used option,  it can be
passed on its own as an unnamed argument:

 $csv->header ($fh, [ ";", ",", "|", "\t", "::", "\x{2063}" ]);

Multi-byte  sequences are allowed,  both multi-character and  Unicode.  See
L<C<sep>|/sep>.

=item detect_bom

 $csv->header ($fh, { detect_bom => 1 });

The default behavior is to detect if the header line starts with a BOM.  If
the header has a BOM, use that to set the encoding of C<$fh>.  This default
behavior can be disabled by passing a false value to C<detect_bom>.

Supported encodings from BOM are: UTF-8, UTF-16BE, UTF-16LE, UTF-32BE,  and
UTF-32LE. BOM's also support UTF-1, UTF-EBCDIC, SCSU, BOCU-1,  and GB-18030
but L<Encode> does not (yet). UTF-7 is not supported.

If a supported BOM was detected as start of the stream, it is stored in the
abject attribute C<ENCODING>.

 my $enc = $csv->{ENCODING};

The encoding is used with C<binmode> on C<$fh>.

If the handle was opened in a (correct) encoding,  this method will  B<not>
alter the encoding, as it checks the leading B<bytes> of the first line. In
case the stream starts with a decode BOM (C<U+FEFF>), C<{ENCODING}> will be
C<""> (empty) instead of the default C<undef>.

=item munge_column_names

This option offers the means to modify the column names into something that
is most useful to the application.   The default is to map all column names
to lower case.

 $csv->header ($fh, { munge_column_names => "lc" });

The following values are available:

  lc     - lower case
  uc     - upper case
  none   - do not change
  \%hash - supply a mapping
  \&cb   - supply a callback

Literal:

 $csv->header ($fh, { munge_column_names => "none" });

Hash:

 $csv->header ($fh, { munge_column_names => { foo => "sombrero" });

if a value does not exist, the original value is used unchanged

Callback:

 $csv->header ($fh, { munge_column_names => sub { fc } });
 $csv->header ($fh, { munge_column_names => sub { "column_".$col++ } });
 $csv->header ($fh, { munge_column_names => sub { lc (s/\W+/_/gr) } });

As this callback is called in a C<map>, you can use C<$_> directly.

=item set_column_names

 $csv->header ($fh, { set_column_names => 1 });

The default is to set the instances column names using  L</column_names> if
the method is successful,  so subsequent calls to L</getline_hr> can return
a hash. Disable setting the header can be forced by using a false value for
this option.

As described in L</return value> above, content is lost in scalar context.

=back

=head3 Validation

When receiving CSV files from external sources,  this method can be used to
protect against changes in the layout by restricting to known headers  (and
typos in the header fields).

 my %known = (
     "record key" => "c_rec",
     "rec id"     => "c_rec",
     "id_rec"     => "c_rec",
     "kode"       => "code",
     "code"       => "code",
     "vaule"      => "value",
     "value"      => "value",
     );
 my $csv = Text::CSV->new ({ binary => 1, auto_diag => 1 });
 open my $fh, "<", $source or die "$source: $!";
 $csv->header ($fh, { munge_column_names => sub {
     s/\s+$//;
     s/^\s+//;
     $known{lc $_} or die "Unknown column '$_' in $source";
     }});
 while (my $row = $csv->getline_hr ($fh)) {
     say join "\t", $row->{c_rec}, $row->{code}, $row->{value};
     }

=head2 bind_columns

Takes a list of scalar references to be used for output with  L</print>  or
to store in the fields fetched by L</getline>.  When you do not pass enough
references to store the fetched fields in, L</getline> will fail with error
C<3006>.  If you pass more than there are fields to return,  the content of
the remaining references is left untouched.

 $csv->bind_columns (\$code, \$name, \$price, \$description);
 while ($csv->getline ($fh)) {
     print "The price of a $name is \x{20ac} $price\n";
     }

To reset or clear all column binding, call L</bind_columns> with the single
argument C<undef>. This will also clear column names.

 $csv->bind_columns (undef);

If no arguments are passed at all, L</bind_columns> will return the list of
current bindings or C<undef> if no binds are active.

Note that in parsing with  C<bind_columns>,  the fields are set on the fly.
That implies that if the third field of a row causes an error  (or this row
has just two fields where the previous row had more),  the first two fields
already have been assigned the values of the current row, while the rest of
the fields will still hold the values of the previous row.  If you want the
parser to fail in these cases, use the L<C<strict>|/strict> attribute.

=head2 eof

 $eof = $csv->eof ();

If L</parse> or  L</getline>  was used with an IO stream,  this method will
return true (1) if the last call hit end of file,  otherwise it will return
false ('').  This is useful to see the difference between a failure and end
of file.

Note that if the parsing of the last line caused an error,  C<eof> is still
true.  That means that if you are I<not> using L</auto_diag>, an idiom like

 while (my $row = $csv->getline ($fh)) {
     # ...
     }
 $csv->eof or $csv->error_diag;

will I<not> report the error. You would have to change that to

 while (my $row = $csv->getline ($fh)) {
     # ...
     }
 +$csv->error_diag and $csv->error_diag;

=head2 types

 $csv->types (\@tref);

This method is used to force that  (all)  columns are of a given type.  For
example, if you have an integer column,  two  columns  with  doubles  and a
string column, then you might do a

 $csv->types ([Text::CSV::IV (),
               Text::CSV::NV (),
               Text::CSV::NV (),
               Text::CSV::PV ()]);

Column types are used only for I<decoding> columns while parsing,  in other
words by the L</parse> and L</getline> methods.

You can unset column types by doing a

 $csv->types (undef);

or fetch the current type settings with

 $types = $csv->types ();

=over 4

=item IV

Set field type to integer.

=item NV

Set field type to numeric/float.

=item PV

Set field type to string.

=back

=head2 fields

 @columns = $csv->fields ();

This method returns the input to   L</combine>  or the resultant decomposed
fields of a successful L</parse>, whichever was called more recently.

Note that the return value is undefined after using L</getline>, which does
not fill the data structures returned by L</parse>.

=head2 meta_info

 @flags = $csv->meta_info ();

This method returns the "flags" of the input to L</combine> or the flags of
the resultant  decomposed fields of  L</parse>,   whichever was called more
recently.

For each field,  a meta_info field will hold  flags that  inform  something
about  the  field  returned  by  the  L</fields>  method or  passed to  the
L</combine> method. The flags are bit-wise-C<or>'d like:

=over 2

=item C< >0x0001

The field was quoted.

=item C< >0x0002

The field was binary.

=back

See the C<is_***> methods below.

=head2 is_quoted

 my $quoted = $csv->is_quoted ($column_idx);

Where  C<$column_idx> is the  (zero-based)  index of the column in the last
result of L</parse>.

This returns a true value  if the data in the indicated column was enclosed
in L<C<quote_char>|/quote_char> quotes.  This might be important for fields
where content C<,20070108,> is to be treated as a numeric value,  and where
C<,"20070108",> is explicitly marked as character string data.

This method is only valid when L</keep_meta_info> is set to a true value.

=head2 is_binary

 my $binary = $csv->is_binary ($column_idx);

Where  C<$column_idx> is the  (zero-based)  index of the column in the last
result of L</parse>.

This returns a true value if the data in the indicated column contained any
byte in the range C<[\x00-\x08,\x10-\x1F,\x7F-\xFF]>.

This method is only valid when L</keep_meta_info> is set to a true value.

=head2 is_missing

 my $missing = $csv->is_missing ($column_idx);

Where  C<$column_idx> is the  (zero-based)  index of the column in the last
result of L</getline_hr>.

 $csv->keep_meta_info (1);
 while (my $hr = $csv->getline_hr ($fh)) {
     $csv->is_missing (0) and next; # This was an empty line
     }

When using  L</getline_hr>,  it is impossible to tell if the  parsed fields
are C<undef> because they where not filled in the C<CSV> stream  or because
they were not read at all, as B<all> the fields defined by L</column_names>
are set in the hash-ref.    If you still need to know if all fields in each
row are provided, you should enable L<C<keep_meta_info>|/keep_meta_info> so
you can check the flags.

If  L<C<keep_meta_info>|/keep_meta_info>  is C<false>,  C<is_missing>  will
always return C<undef>, regardless of C<$column_idx> being valid or not. If
this attribute is C<true> it will return either C<0> (the field is present)
or C<1> (the field is missing).

A special case is the empty line.  If the line is completely empty -  after
dealing with the flags - this is still a valid CSV line:  it is a record of
just one single empty field. However, if C<keep_meta_info> is set, invoking
C<is_missing> with index C<0> will now return true.

=head2 status

 $status = $csv->status ();

This method returns the status of the last invoked L</combine> or L</parse>
call. Status is success (true: C<1>) or failure (false: C<undef> or C<0>).

=head2 error_input

 $bad_argument = $csv->error_input ();

This method returns the erroneous argument (if it exists) of L</combine> or
L</parse>,  whichever was called more recently.  If the last invocation was
successful, C<error_input> will return C<undef>.

=head2 error_diag

 Text::CSV->error_diag ();
 $csv->error_diag ();
 $error_code               = 0  + $csv->error_diag ();
 $error_str                = "" . $csv->error_diag ();
 ($cde, $str, $pos, $rec, $fld) = $csv->error_diag ();

If (and only if) an error occurred,  this function returns  the diagnostics
of that error.

If called in void context,  this will print the internal error code and the
associated error message to STDERR.

If called in list context,  this will return  the error code  and the error
message in that order.  If the last error was from parsing, the rest of the
values returned are a best guess at the location  within the line  that was
being parsed. Their values are 1-based.  The position currently is index of
the byte at which the parsing failed in the current record. It might change
to be the index of the current character in a later release. The records is
the index of the record parsed by the csv instance. The field number is the
index of the field the parser thinks it is currently  trying to  parse. See
F<examples/csv-check> for how this can be used.

If called in  scalar context,  it will return  the diagnostics  in a single
scalar, a-la C<$!>.  It will contain the error code in numeric context, and
the diagnostics message in string context.

When called as a class method or a  direct function call,  the  diagnostics
are that of the last L</new> call.

=head2 record_number

 $recno = $csv->record_number ();

Returns the records parsed by this csv instance.  This value should be more
accurate than C<$.> when embedded newlines come in play. Records written by
this instance are not counted.

=head2 SetDiag

 $csv->SetDiag (0);

Use to reset the diagnostics if you are dealing with errors.

=head1 ADDITIONAL METHODS

=over

=item backend

Returns the backend module name called by Text::CSV.
C<module> is an alias.

=item is_xs

Returns true value if Text::CSV uses an XS backend.

=item is_pp

Returns true value if Text::CSV uses a pure-Perl backend.

=back

=head1 FUNCTIONS

This section is also taken from Text::CSV_XS.

=head2 csv

This function is not exported by default and should be explicitly requested:

 use Text::CSV qw( csv );

This is an high-level function that aims at simple (user) interfaces.  This
can be used to read/parse a C<CSV> file or stream (the default behavior) or
to produce a file or write to a stream (define the  C<out>  attribute).  It
returns an array- or hash-reference on parsing (or C<undef> on fail) or the
numeric value of  L</error_diag>  on writing.  When this function fails you
can get to the error using the class call to L</error_diag>

 my $aoa = csv (in => "test.csv") or
     die Text::CSV->error_diag;

This function takes the arguments as key-value pairs. This can be passed as
a list or as an anonymous hash:

 my $aoa = csv (  in => "test.csv", sep_char => ";");
 my $aoh = csv ({ in => $fh, headers => "auto" });

The arguments passed consist of two parts:  the arguments to L</csv> itself
and the optional attributes to the  C<CSV>  object used inside the function
as enumerated and explained in L</new>.

If not overridden, the default option used for CSV is

 auto_diag   => 1
 escape_null => 0

The option that is always set and cannot be altered is

 binary      => 1

As this function will likely be used in one-liners,  it allows  C<quote> to
be abbreviated as C<quo>,  and  C<escape_char> to be abbreviated as  C<esc>
or C<escape>.

Alternative invocations:

 my $aoa = Text::CSV::csv (in => "file.csv");

 my $csv = Text::CSV->new ();
 my $aoa = $csv->csv (in => "file.csv");

In the latter case, the object attributes are used from the existing object
and the attribute arguments in the function call are ignored:

 my $csv = Text::CSV->new ({ sep_char => ";" });
 my $aoh = $csv->csv (in => "file.csv", bom => 1);

will parse using C<;> as C<sep_char>, not C<,>.

=head3 in

Used to specify the source.  C<in> can be a file name (e.g. C<"file.csv">),
which will be  opened for reading  and closed when finished,  a file handle
(e.g.  C<$fh> or C<FH>),  a reference to a glob (e.g. C<\*ARGV>),  the glob
itself (e.g. C<*STDIN>), or a reference to a scalar (e.g. C<\q{1,2,"csv"}>).

When used with L</out>, C<in> should be a reference to a CSV structure (AoA
or AoH)  or a CODE-ref that returns an array-reference or a hash-reference.
The code-ref will be invoked with no arguments.

 my $aoa = csv (in => "file.csv");

 open my $fh, "<", "file.csv";
 my $aoa = csv (in => $fh);

 my $csv = [ [qw( Foo Bar )], [ 1, 2 ], [ 2, 3 ]];
 my $err = csv (in => $csv, out => "file.csv");

If called in void context without the L</out> attribute, the resulting ref
will be used as input to a subsequent call to csv:

 csv (in => "file.csv", filter => { 2 => sub { length > 2 }})

will be a shortcut to

 csv (in => csv (in => "file.csv", filter => { 2 => sub { length > 2 }}))

where, in the absence of the C<out> attribute, this is a shortcut to

 csv (in  => csv (in => "file.csv", filter => { 2 => sub { length > 2 }}),
      out => *STDOUT)

=head3 out

 csv (in => $aoa, out => "file.csv");
 csv (in => $aoa, out => $fh);
 csv (in => $aoa, out =>   STDOUT);
 csv (in => $aoa, out =>  *STDOUT);
 csv (in => $aoa, out => \*STDOUT);
 csv (in => $aoa, out => \my $data);
 csv (in => $aoa, out =>  undef);
 csv (in => $aoa, out => \"skip");

In output mode, the default CSV options when producing CSV are

 eol       => "\r\n"

The L</fragment> attribute is ignored in output mode.

C<out> can be a file name  (e.g.  C<"file.csv">),  which will be opened for
writing and closed when finished,  a file handle (e.g. C<$fh> or C<FH>),  a
reference to a glob (e.g. C<\*STDOUT>),  the glob itself (e.g. C<*STDOUT>),
or a reference to a scalar (e.g. C<\my $data>).

 csv (in => sub { $sth->fetch },            out => "dump.csv");
 csv (in => sub { $sth->fetchrow_hashref }, out => "dump.csv",
      headers => $sth->{NAME_lc});

When a code-ref is used for C<in>, the output is generated  per invocation,
so no buffering is involved. This implies that there is no size restriction
on the number of records. The C<csv> function ends when the coderef returns
a false value.

If C<out> is set to a reference of the literal string C<"skip">, the output
will be suppressed completely,  which might be useful in combination with a
filter for side effects only.

 my %cache;
 csv (in    => "dump.csv",
      out   => \"skip",
      on_in => sub { $cache{$_[1][1]}++ });

Currently,  setting C<out> to any false value  (C<undef>, C<"">, 0) will be
equivalent to C<\"skip">.

=head3 encoding

If passed,  it should be an encoding accepted by the  C<:encoding()> option
to C<open>. There is no default value. This attribute does not work in perl
5.6.x.  C<encoding> can be abbreviated to C<enc> for ease of use in command
line invocations.

If C<encoding> is set to the literal value C<"auto">, the method L</header>
will be invoked on the opened stream to check if there is a BOM and set the
encoding accordingly.   This is equal to passing a true value in the option
L<C<detect_bom>|/detect_bom>.

=head3 detect_bom

If  C<detect_bom>  is given, the method  L</header>  will be invoked on the
opened stream to check if there is a BOM and set the encoding accordingly.

C<detect_bom> can be abbreviated to C<bom>.

This is the same as setting L<C<encoding>|/encoding> to C<"auto">.

Note that as the method  L</header> is invoked,  its default is to also set
the headers.

=head3 headers

If this attribute is not given, the default behavior is to produce an array
of arrays.

If C<headers> is supplied,  it should be an anonymous list of column names,
an anonymous hashref, a coderef, or a literal flag:  C<auto>, C<lc>, C<uc>,
or C<skip>.

=over 2

=item skip

When C<skip> is used, the header will not be included in the output.

 my $aoa = csv (in => $fh, headers => "skip");

=item auto

If C<auto> is used, the first line of the C<CSV> source will be read as the
list of field headers and used to produce an array of hashes.

 my $aoh = csv (in => $fh, headers => "auto");

=item lc

If C<lc> is used,  the first line of the  C<CSV> source will be read as the
list of field headers mapped to  lower case and used to produce an array of
hashes. This is a variation of C<auto>.

 my $aoh = csv (in => $fh, headers => "lc");

=item uc

If C<uc> is used,  the first line of the  C<CSV> source will be read as the
list of field headers mapped to  upper case and used to produce an array of
hashes. This is a variation of C<auto>.

 my $aoh = csv (in => $fh, headers => "uc");

=item CODE

If a coderef is used,  the first line of the  C<CSV> source will be read as
the list of mangled field headers in which each field is passed as the only
argument to the coderef. This list is used to produce an array of hashes.

 my $aoh = csv (in      => $fh,
                headers => sub { lc ($_[0]) =~ s/kode/code/gr });

this example is a variation of using C<lc> where all occurrences of C<kode>
are replaced with C<code>.

=item ARRAY

If  C<headers>  is an anonymous list,  the entries in the list will be used
as field names. The first line is considered data instead of headers.

 my $aoh = csv (in => $fh, headers => [qw( Foo Bar )]);
 csv (in => $aoa, out => $fh, headers => [qw( code description price )]);

=item HASH

If C<headers> is an hash reference, this implies C<auto>, but header fields
for that exist as key in the hashref will be replaced by the value for that
key. Given a CSV file like

 post-kode,city,name,id number,fubble
 1234AA,Duckstad,Donald,13,"X313DF"

using

 csv (headers => { "post-kode" => "pc", "id number" => "ID" }, ...

will return an entry like

 { pc     => "1234AA",
   city   => "Duckstad",
   name   => "Donald",
   ID     => "13",
   fubble => "X313DF",
   }

=back

See also L<C<munge_column_names>|/munge_column_names> and
L<C<set_column_names>|/set_column_names>.

=head3 munge_column_names

If C<munge_column_names> is set,  the method  L</header>  is invoked on the
opened stream with all matching arguments to detect and set the headers.

C<munge_column_names> can be abbreviated to C<munge>.

=head3 key

If passed,  will default  L<C<headers>|/headers>  to C<"auto"> and return a
hashref instead of an array of hashes.

 my $ref = csv (in => "test.csv", key => "code");

with test.csv like

 code,product,price,color
 1,pc,850,gray
 2,keyboard,12,white
 3,mouse,5,black

will return

  { 1   => {
        code    => 1,
        color   => 'gray',
        price   => 850,
        product => 'pc'
        },
    2   => {
        code    => 2,
        color   => 'white',
        price   => 12,
        product => 'keyboard'
        },
    3   => {
        code    => 3,
        color   => 'black',
        price   => 5,
        product => 'mouse'
        }
    }

The C<key> attribute can be combined with L<C<headers>|/headers> for C<CSV>
date that has no header line, like

 my $ref = csv (
     in      => "foo.csv",
     headers => [qw( c_foo foo bar description stock )],
     key     =>     "c_foo",
     );

=head3 keep_headers

When using hashes,  keep the column names into the arrayref passed,  so all
headers are available after the call in the original order.

 my $aoh = csv (in => "file.csv", keep_headers => \my @hdr);

This attribute can be abbreviated to C<kh> or passed as C<keep_column_names>.

This attribute implies a default of C<auto> for the C<headers> attribute.

=head3 fragment

Only output the fragment as defined in the L</fragment> method. This option
is ignored when I<generating> C<CSV>. See L</out>.

Combining all of them could give something like

 use Text::CSV qw( csv );
 my $aoh = csv (
     in       => "test.txt",
     encoding => "utf-8",
     headers  => "auto",
     sep_char => "|",
     fragment => "row=3;6-9;15-*",
     );
 say $aoh->[15]{Foo};

=head3 sep_set

If C<sep_set> is set, the method L</header> is invoked on the opened stream
to detect and set L<C<sep_char>|/sep_char> with the given set.

C<sep_set> can be abbreviated to C<seps>.

Note that as the  L</header> method is invoked,  its default is to also set
the headers.

=head3 set_column_names

If  C<set_column_names> is passed,  the method L</header> is invoked on the
opened stream with all arguments meant for L</header>.

If C<set_column_names> is passed as a false value, the content of the first
row is only preserved if the output is AoA:

With an input-file like

 bAr,foo
 1,2
 3,4,5

This call

 my $aoa = csv (in => $file, set_column_names => 0);

will result in

 [[ "bar", "foo"     ],
  [ "1",   "2"       ],
  [ "3",   "4",  "5" ]]

and

 my $aoa = csv (in => $file, set_column_names => 0, munge => "none");

will result in

 [[ "bAr", "foo"     ],
  [ "1",   "2"       ],
  [ "3",   "4",  "5" ]]

=head2 Callbacks

Callbacks enable actions triggered from the I<inside> of Text::CSV.

While most of what this enables  can easily be done in an  unrolled loop as
described in the L</SYNOPSIS> callbacks can be used to meet special demands
or enhance the L</csv> function.

=over 2

=item error

 $csv->callbacks (error => sub { $csv->SetDiag (0) });

the C<error>  callback is invoked when an error occurs,  but  I<only>  when
L</auto_diag> is set to a true value. A callback is invoked with the values
returned by L</error_diag>:

 my ($c, $s);

 sub ignore3006
 {
     my ($err, $msg, $pos, $recno, $fldno) = @_;
     if ($err == 3006) {
         # ignore this error
         ($c, $s) = (undef, undef);
         Text::CSV->SetDiag (0);
         }
     # Any other error
     return;
     } # ignore3006

 $csv->callbacks (error => \&ignore3006);
 $csv->bind_columns (\$c, \$s);
 while ($csv->getline ($fh)) {
     # Error 3006 will not stop the loop
     }

=item after_parse

 $csv->callbacks (after_parse => sub { push @{$_[1]}, "NEW" });
 while (my $row = $csv->getline ($fh)) {
     $row->[-1] eq "NEW";
     }

This callback is invoked after parsing with  L</getline>  only if no  error
occurred.  The callback is invoked with two arguments:   the current C<CSV>
parser object and an array reference to the fields parsed.

The return code of the callback is ignored  unless it is a reference to the
string "skip", in which case the record will be skipped in L</getline_all>.

 sub add_from_db
 {
     my ($csv, $row) = @_;
     $sth->execute ($row->[4]);
     push @$row, $sth->fetchrow_array;
     } # add_from_db

 my $aoa = csv (in => "file.csv", callbacks => {
     after_parse => \&add_from_db });

This hook can be used for validation:

=over 2

=item FAIL

Die if any of the records does not validate a rule:

 after_parse => sub {
     $_[1][4] =~ m/^[0-9]{4}\s?[A-Z]{2}$/ or
         die "5th field does not have a valid Dutch zipcode";
     }

=item DEFAULT

Replace invalid fields with a default value:

 after_parse => sub { $_[1][2] =~ m/^\d+$/ or $_[1][2] = 0 }

=item SKIP

Skip records that have invalid fields (only applies to L</getline_all>):

 after_parse => sub { $_[1][0] =~ m/^\d+$/ or return \"skip"; }

=back

=item before_print

 my $idx = 1;
 $csv->callbacks (before_print => sub { $_[1][0] = $idx++ });
 $csv->print (*STDOUT, [ 0, $_ ]) for @members;

This callback is invoked  before printing with  L</print>  only if no error
occurred.  The callback is invoked with two arguments:  the current  C<CSV>
parser object and an array reference to the fields passed.

The return code of the callback is ignored.

 sub max_4_fields
 {
     my ($csv, $row) = @_;
     @$row > 4 and splice @$row, 4;
     } # max_4_fields

 csv (in => csv (in => "file.csv"), out => *STDOUT,
     callbacks => { before print => \&max_4_fields });

This callback is not active for L</combine>.

=back

=head3 Callbacks for csv ()

The L</csv> allows for some callbacks that do not integrate in XS internals
but only feature the L</csv> function.

  csv (in        => "file.csv",
       callbacks => {
           filter       => { 6 => sub { $_ > 15 } },    # first
           after_parse  => sub { say "AFTER PARSE";  }, # first
           after_in     => sub { say "AFTER IN";     }, # second
           on_in        => sub { say "ON IN";        }, # third
           },
       );

  csv (in        => $aoh,
       out       => "file.csv",
       callbacks => {
           on_in        => sub { say "ON IN";        }, # first
           before_out   => sub { say "BEFORE OUT";   }, # second
           before_print => sub { say "BEFORE PRINT"; }, # third
           },
       );

=over 2

=item filter

This callback can be used to filter records.  It is called just after a new
record has been scanned.  The callback accepts a:

=over 2

=item hashref

The keys are the index to the row (the field name or field number, 1-based)
and the values are subs to return a true or false value.

 csv (in => "file.csv", filter => {
            3 => sub { m/a/ },       # third field should contain an "a"
            5 => sub { length > 4 }, # length of the 5th field minimal 5
            });

 csv (in => "file.csv", filter => { foo => sub { $_ > 4 }});

If the keys to the filter hash contain any character that is not a digit it
will also implicitly set L</headers> to C<"auto">  unless  L</headers>  was
already passed as argument.  When headers are active, returning an array of
hashes, the filter is not applicable to the header itself.

All sub results should match, as in AND.

The context of the callback sets  C<$_> localized to the field indicated by
the filter. The two arguments are as with all other callbacks, so the other
fields in the current row can be seen:

 filter => { 3 => sub { $_ > 100 ? $_[1][1] =~ m/A/ : $_[1][6] =~ m/B/ }}

If the context is set to return a list of hashes  (L</headers> is defined),
the current record will also be available in the localized C<%_>:

 filter => { 3 => sub { $_ > 100 && $_{foo} =~ m/A/ && $_{bar} < 1000  }}

If the filter is used to I<alter> the content by changing C<$_>,  make sure
that the sub returns true in order not to have that record skipped:

 filter => { 2 => sub { $_ = uc }}

will upper-case the second field, and then skip it if the resulting content
evaluates to false. To always accept, end with truth:

 filter => { 2 => sub { $_ = uc; 1 }}

=item coderef

 csv (in => "file.csv", filter => sub { $n++; 0; });

If the argument to C<filter> is a coderef,  it is an alias or shortcut to a
filter on column 0:

 csv (filter => sub { $n++; 0 });

is equal to

 csv (filter => { 0 => sub { $n++; 0 });

=item filter-name

 csv (in => "file.csv", filter => "not_blank");
 csv (in => "file.csv", filter => "not_empty");
 csv (in => "file.csv", filter => "filled");

These are predefined filters

Given a file like (line numbers prefixed for doc purpose only):

 1:1,2,3
 2:
 3:,
 4:""
 5:,,
 6:, ,
 7:"",
 8:" "
 9:4,5,6

=over 2

=item not_blank

Filter out the blank lines

This filter is a shortcut for

 filter => { 0 => sub { @{$_[1]} > 1 or
             defined $_[1][0] && $_[1][0] ne "" } }

Due to the implementation,  it is currently impossible to also filter lines
that consists only of a quoted empty field. These lines are also considered
blank lines.

With the given example, lines 2 and 4 will be skipped.

=item not_empty

Filter out lines where all the fields are empty.

This filter is a shortcut for

 filter => { 0 => sub { grep { defined && $_ ne "" } @{$_[1]} } }

A space is not regarded being empty, so given the example data, lines 2, 3,
4, 5, and 7 are skipped.

=item filled

Filter out lines that have no visible data

This filter is a shortcut for

 filter => { 0 => sub { grep { defined && m/\S/ } @{$_[1]} } }

This filter rejects all lines that I<not> have at least one field that does
not evaluate to the empty string.

With the given example data, this filter would skip lines 2 through 8.

=back

=back

=item after_in

This callback is invoked for each record after all records have been parsed
but before returning the reference to the caller.  The hook is invoked with
two arguments:  the current  C<CSV>  parser object  and a  reference to the
record.   The reference can be a reference to a  HASH  or a reference to an
ARRAY as determined by the arguments.

This callback can also be passed as  an attribute without the  C<callbacks>
wrapper.

=item before_out

This callback is invoked for each record before the record is printed.  The
hook is invoked with two arguments:  the current C<CSV> parser object and a
reference to the record.   The reference can be a reference to a  HASH or a
reference to an ARRAY as determined by the arguments.

This callback can also be passed as an attribute  without the  C<callbacks>
wrapper.

This callback makes the row available in C<%_> if the row is a hashref.  In
this case C<%_> is writable and will change the original row.

=item on_in

This callback acts exactly as the L</after_in> or the L</before_out> hooks.

This callback can also be passed as an attribute  without the  C<callbacks>
wrapper.

This callback makes the row available in C<%_> if the row is a hashref.  In
this case C<%_> is writable and will change the original row. So e.g. with

  my $aoh = csv (
      in      => \"foo\n1\n2\n",
      headers => "auto",
      on_in   => sub { $_{bar} = 2; },
      );

C<$aoh> will be:

  [ { foo => 1,
      bar => 2,
      }
    { foo => 2,
      bar => 2,
      }
    ]

=item csv

The I<function>  L</csv> can also be called as a method or with an existing
Text::CSV object. This could help if the function is to be invoked a lot
of times and the overhead of creating the object internally over  and  over
again would be prevented by passing an existing instance.

 my $csv = Text::CSV->new ({ binary => 1, auto_diag => 1 });

 my $aoa = $csv->csv (in => $fh);
 my $aoa = csv (in => $fh, csv => $csv);

both act the same. Running this 20000 times on a 20 lines CSV file,  showed
a 53% speedup.

=back

=head1 DIAGNOSTICS

This section is also taken from Text::CSV_XS.

Still under construction ...

If an error occurs,  C<< $csv->error_diag >> can be used to get information
on the cause of the failure. Note that for speed reasons the internal value
is never cleared on success,  so using the value returned by L</error_diag>
in normal cases - when no error occurred - may cause unexpected results.

If the constructor failed, the cause can be found using L</error_diag> as a
class method, like C<< Text::CSV->error_diag >>.

The C<< $csv->error_diag >> method is automatically invoked upon error when
the contractor was called with  L<C<auto_diag>|/auto_diag>  set to  C<1> or
C<2>, or when L<autodie> is in effect.  When set to C<1>, this will cause a
C<warn> with the error message,  when set to C<2>, it will C<die>. C<2012 -
EOF> is excluded from L<C<auto_diag>|/auto_diag> reports.

Errors can be (individually) caught using the L</error> callback.

The errors as described below are available. I have tried to make the error
itself explanatory enough, but more descriptions will be added. For most of
these errors, the first three capitals describe the error category:

=over 2

=item *
INI

Initialization error or option conflict.

=item *
ECR

Carriage-Return related parse error.

=item *
EOF

End-Of-File related parse error.

=item *
EIQ

Parse error inside quotation.

=item *
EIF

Parse error inside field.

=item *
ECB

Combine error.

=item *
EHR

HashRef parse related error.

=back

And below should be the complete list of error codes that can be returned:

=over 2

=item *
1001 "INI - sep_char is equal to quote_char or escape_char"

The  L<separation character|/sep_char>  cannot be equal to  L<the quotation
character|/quote_char> or to L<the escape character|/escape_char>,  as this
would invalidate all parsing rules.

=item *
1002 "INI - allow_whitespace with escape_char or quote_char SP or TAB"

Using the  L<C<allow_whitespace>|/allow_whitespace>  attribute  when either
L<C<quote_char>|/quote_char> or L<C<escape_char>|/escape_char>  is equal to
C<SPACE> or C<TAB> is too ambiguous to allow.

=item *
1003 "INI - \r or \n in main attr not allowed"

Using default L<C<eol>|/eol> characters in either L<C<sep_char>|/sep_char>,
L<C<quote_char>|/quote_char>,   or  L<C<escape_char>|/escape_char>  is  not
allowed.

=item *
1004 "INI - callbacks should be undef or a hashref"

The L<C<callbacks>|/Callbacks>  attribute only allows one to be C<undef> or
a hash reference.

=item *
1005 "INI - EOL too long"

The value passed for EOL is exceeding its maximum length (16).

=item *
1006 "INI - SEP too long"

The value passed for SEP is exceeding its maximum length (16).

=item *
1007 "INI - QUOTE too long"

The value passed for QUOTE is exceeding its maximum length (16).

=item *
1008 "INI - SEP undefined"

The value passed for SEP should be defined and not empty.

=item *
1010 "INI - the header is empty"

The header line parsed in the L</header> is empty.

=item *
1011 "INI - the header contains more than one valid separator"

The header line parsed in the  L</header>  contains more than one  (unique)
separator character out of the allowed set of separators.

=item *
1012 "INI - the header contains an empty field"

The header line parsed in the L</header> is contains an empty field.

=item *
1013 "INI - the header contains nun-unique fields"

The header line parsed in the  L</header>  contains at least  two identical
fields.

=item *
1014 "INI - header called on undefined stream"

The header line cannot be parsed from an undefined sources.

=item *
1500 "PRM - Invalid/unsupported argument(s)"

Function or method called with invalid argument(s) or parameter(s).

=item *
1501 "PRM - The key attribute is passed as an unsupported type"

The C<key> attribute is of an unsupported type.

=item *
2010 "ECR - QUO char inside quotes followed by CR not part of EOL"

When  L<C<eol>|/eol>  has  been  set  to  anything  but the  default,  like
C<"\r\t\n">,  and  the  C<"\r">  is  following  the   B<second>   (closing)
L<C<quote_char>|/quote_char>, where the characters following the C<"\r"> do
not make up the L<C<eol>|/eol> sequence, this is an error.

=item *
2011 "ECR - Characters after end of quoted field"

Sequences like C<1,foo,"bar"baz,22,1> are not allowed. C<"bar"> is a quoted
field and after the closing double-quote, there should be either a new-line
sequence or a separation character.

=item *
2012 "EOF - End of data in parsing input stream"

Self-explaining. End-of-file while inside parsing a stream. Can happen only
when reading from streams with L</getline>,  as using  L</parse> is done on
strings that are not required to have a trailing L<C<eol>|/eol>.

=item *
2013 "INI - Specification error for fragments RFC7111"

Invalid specification for URI L</fragment> specification.

=item *
2014 "ENF - Inconsistent number of fields"

Inconsistent number of fields under strict parsing.

=item *
2021 "EIQ - NL char inside quotes, binary off"

Sequences like C<1,"foo\nbar",22,1> are allowed only when the binary option
has been selected with the constructor.

=item *
2022 "EIQ - CR char inside quotes, binary off"

Sequences like C<1,"foo\rbar",22,1> are allowed only when the binary option
has been selected with the constructor.

=item *
2023 "EIQ - QUO character not allowed"

Sequences like C<"foo "bar" baz",qu> and C<2023,",2008-04-05,"Foo, Bar",\n>
will cause this error.

=item *
2024 "EIQ - EOF cannot be escaped, not even inside quotes"

The escape character is not allowed as last character in an input stream.

=item *
2025 "EIQ - Loose unescaped escape"

An escape character should escape only characters that need escaping.

Allowing  the escape  for other characters  is possible  with the attribute
L</allow_loose_escape>.

=item *
2026 "EIQ - Binary character inside quoted field, binary off"

Binary characters are not allowed by default.    Exceptions are fields that
contain valid UTF-8,  that will automatically be upgraded if the content is
valid UTF-8. Set L<C<binary>|/binary> to C<1> to accept binary data.

=item *
2027 "EIQ - Quoted field not terminated"

When parsing a field that started with a quotation character,  the field is
expected to be closed with a quotation character.   When the parsed line is
exhausted before the quote is found, that field is not terminated.

=item *
2030 "EIF - NL char inside unquoted verbatim, binary off"

=item *
2031 "EIF - CR char is first char of field, not part of EOL"

=item *
2032 "EIF - CR char inside unquoted, not part of EOL"

=item *
2034 "EIF - Loose unescaped quote"

=item *
2035 "EIF - Escaped EOF in unquoted field"

=item *
2036 "EIF - ESC error"

=item *
2037 "EIF - Binary character in unquoted field, binary off"

=item *
2110 "ECB - Binary character in Combine, binary off"

=item *
2200 "EIO - print to IO failed. See errno"

=item *
3001 "EHR - Unsupported syntax for column_names ()"

=item *
3002 "EHR - getline_hr () called before column_names ()"

=item *
3003 "EHR - bind_columns () and column_names () fields count mismatch"

=item *
3004 "EHR - bind_columns () only accepts refs to scalars"

=item *
3006 "EHR - bind_columns () did not pass enough refs for parsed fields"

=item *
3007 "EHR - bind_columns needs refs to writable scalars"

=item *
3008 "EHR - unexpected error in bound fields"

=item *
3009 "EHR - print_hr () called before column_names ()"

=item *
3010 "EHR - print_hr () called with invalid arguments"

=back

=head1 SEE ALSO

L<Text::CSV_PP>, L<Text::CSV_XS> and L<Text::CSV::Encoded>.


=head1 AUTHORS and MAINTAINERS

Alan Citterman F<E<lt>alan[at]mfgrtl.comE<gt>> wrote the original Perl
module. Please don't send mail concerning Text::CSV to Alan, as
he's not a present maintainer.

Jochen Wiedmann F<E<lt>joe[at]ispsoft.deE<gt>> rewrote the encoding and
decoding in C by implementing a simple finite-state machine and added
the variable quote, escape and separator characters, the binary mode
and the print and getline methods. See ChangeLog releases 0.10 through
0.23.

H.Merijn Brand F<E<lt>h.m.brand[at]xs4all.nlE<gt>> cleaned up the code,
added the field flags methods, wrote the major part of the test suite,
completed the documentation, fixed some RT bugs. See ChangeLog releases
0.25 and on.

Makamaka Hannyaharamitu, E<lt>makamaka[at]cpan.orgE<gt> wrote Text::CSV_PP
which is the pure-Perl version of Text::CSV_XS.

New Text::CSV (since 0.99) is maintained by Makamaka, and Kenichi Ishigaki
since 1.91.


=head1 COPYRIGHT AND LICENSE

Text::CSV

Copyright (C) 1997 Alan Citterman. All rights reserved.
Copyright (C) 2007-2015 Makamaka Hannyaharamitu.
Copyright (C) 2017- Kenichi Ishigaki
A large portion of the doc is taken from Text::CSV_XS. See below.

Text::CSV_PP:

Copyright (C) 2005-2015 Makamaka Hannyaharamitu.
Copyright (C) 2017- Kenichi Ishigaki
A large portion of the code/doc are also taken from Text::CSV_XS. See below.

Text:CSV_XS:

Copyright (C) 2007-2016 H.Merijn Brand for PROCURA B.V.
Copyright (C) 1998-2001 Jochen Wiedmann. All rights reserved.
Portions Copyright (C) 1997 Alan Citterman. All rights reserved.


This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself.

=cut
