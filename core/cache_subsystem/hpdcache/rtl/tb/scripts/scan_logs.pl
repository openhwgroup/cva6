#!/usr/bin/env perl
################################################################################
# ----------------------------------------------------------------------------
#Copyright 2024 CEA*
#*Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
#
#Licensed under the Apache License, Version 2.0 (the "License");
#you may not use this file except in compliance with the License.
#You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
#Unless required by applicable law or agreed to in writing, software
#distributed under the License is distributed on an "AS IS" BASIS,
#WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#See the License for the specific language governing permissions and
#limitations under the License.
#[END OF HEADER]
# ----------------------------------------------------------------------------
#   Description : Simulation log file scan script.
################################################################################

=encoding utf8

=head1 NAME

scanlogs -  parser for log files

=head1 SYNOPSIS

    scanlogs [-pat pattern_file ] [-waiver waiver_file ] [ -format txt|xml|csv ] -out [outfile] [-nowarn ] [-nopreresetwarn] [-notime] [-noendcheck] [-listwarnings] [-listerrors] [-nogroup] [-suppresswaived] [-suppressprereset] logfile1 [ logfile2 ... ]

=head1 DESCRIPTION

=head2 Overview

In a regressionable work environment, it is important that the pass/fail status
of tasks can be assessed in an automated fashion. In complex environments,
there may be many sources of errors or warnings and these may generate messages
with different formats (UVM messages, legacy messages, model specific messages,
timing violations, etc.). The purpose of this script is to be able to read one
(or multiple) log files and to extract the warning and error messages. The
script will return a pass (zero) status if no errors or warnings are detected.
Otherwise, it will return a non-zero status corresponding to the number of
error or warning messages.

The script can also check for timing violations in the log file and fail
the test if one occurs. Often, one only wants to consider timing violations
that occur after reset has been de-asserted. If the user defines a message
to indicate the time of reset, then only those timing violations after reset
are considered. If no reset message is detected, then all timing violations
are considered.

It is essential not to produce false positives. For this reason, this script
will always check for an explicit message indicating that the job has
completed. This helps ensure that a false positive is not produced if
a truncated (or potentially empty) log file is provided as input.

The script has a set of default rules which are used to identify warnings,
errors and successful test completion. These rules can be customized using
configuration files. The user specifies the name of the pattern configuration
file with the '-pat' command line option.

In some cases, it is helpful to provide a list of waivers, for known and
accepted warnings. An optional waiver file can be provided on the command line
with the '-waiver' option.

The user can provide one or multiple log files. These files are parsed and
a summary is produced. By default, a text summary is output to stdout.
Alternatively, the summary can be output in a csv or XML form (not yet
implemented). Command line options can be abbreviated, as long as they are not
ambiguous.

In a randomized simulation environment, it is common for the same test to be
run with different random seeds. The script can extract the seed (using
a defined pattern). If no SEED is found, the seed information is not displayed.

=head1 OPTIONS

=over

=item B<-h>

Displays man page.

=item B<-pat pattern_file>

Specify an input pattern file. Multiple input pattern files can be
specified. Details about the format of the pattern file are provided
later.

=item B<-waiver waiver_file>

Specify an input waiver file. Multiple input waiver files can be
specified. Details about the format of the waiver file are provided
later.

=item B<-att attribute_file>

Specify an input attribute file. Multiple attribute files can be
specified. Details about the format of the attribute file are provided
later.

=item B<-format txt|xml|csv>

Specify the output format for the report. Default is txt.

=item B<-out outfile>

Specify the name of an output file. Default is to output to stdout.

=item B<-nowarn>

By default, if there are any warnings, the return status is non-zero. If
this option is specified, warnings will not affect the output status.

=item B<-nopreresetwarn>

By default, if there are any warnings, the return status is non-zero. If
this option is specified, warnings that occur before the reset message
will not cause the test to fail.

=item B<-notime>

By default, if there are any timing violations, the return status is non-zero. If
this option is specified, timing violations will not affect the output status.

=item B<-noendcheck>

By default, a fail status is returned, if the the log does not have an
explicit end of test message. This is to avoid truncated logs producing a
pass status. Using this option, the check for the end message can be
surpressed.

=item B<-silent>

Even when an output file is specified, the script outputs some information
to the console. Using this option, all messages can be surpressed.

=item B<-listwarnings>

When this option is specified, the report will include a list of all the
warnings that were found, including in which file, the line number and 
whether it was wavied.

=item B<-listerrors>

When this option is specified, the report will include a list of all the
errors that were found, including in which file, the line number and 
whether it was wavied.

=item B<-nogroup>

By default, the warnings and error messages are grouped and a table is
output showing the number of messages corresponding to each group. This
table can be suppresseed using this option.

=item B<-suppresswaived>

This option applies when the -listerrors or -listwarnings is used. By
default these options will list all the errors/warnings, including those
that were waived. With the additional -suppresswaived option, only those
errors/warnings that were not waived are displayed.

=item B<-suppressprereset>

This option applies when the -listwarnings is used. By default this option will
list all the warnings, including those that were prior to reset. With the
additional -suppressprepreset option, only those warnings that are after reset
are displayed.

=back

=head1 EXIT STATUS

An exit status of 0 indicates the log has passed.
A non-zero positive exit status indicates the log has failures and the value is
the total number of errors and warnings (plus 1 if the end of test
check has failed). If the script fails to actually read and process the
pattern or log files, it returns the exit value 255.

=head1 PATTERN FILE FORMAT

A pattern file is simply a CSV file with two columns. The first column
specifies the type of pattern
(ERROR|ERROR_NUM|WARNING|WARNING_NUM|EOT|SEED|GROUP). The second column
contains a perl regular expression. For the ERROR, WARNING and EOT types, the
script simply checks whether the line matches or not. For the ERROR_NUM,
WARNING_NUM, SEED and GROUP types, it is expected that the regular expression
contains a capture group that extracts an argument. For example the log might
contain a line such as "NUMER ERRORS : 3". The regular expression could extract
the numeric value '3'. When scanning a log, the total number of errors (or
warnings) is summed. Thus for a log file to pass, all the ERROR_NUM messages
must report zero errors.

The GROUP pattern has a third argument which is the name of the grouping. For
example, if we group all the messages from a given tool (simulator...), this
could be the name of the tool. For example, a rule to group all messages from
vsim, might look like "GROUP,(vsim-[0-9]+),QUESTA_SIMULATE".

=head1 WAIVER FILE FORMAT

A waiver file is simply  a CSV file with two columns. The first column
specifies the type of waiver (NOERROR|NOWARNING). The text after the column
serves as a reg-ex. If a given line in a log file first matches an
error or a warning pattern, then the script checks if it matches a waiver
pattern. If it matches a waiver pattern, then the warning or error is
not reported. At the end of a scan, the number of waivers is reported.

=head1 ATTRIBUTE FILE FORMAT

An attribute file is a CSV file with 5 columns. The first column contains
either the keyword 'ATT' or 'META'. Lines with 'ATT' specify an attribute,
which is a raw value that is extracted from a log file. Lines with 'META'
specify 'meta-attribute'. A meta-attribute is an expression based on
attributes. For example, a meta-atribute might the ratio between two attributes.

The second column contains a name for the attribute. This is the name that
is displayed in the column header in the final report. Generally, it should
be kept relatively short, otherwise the resulting table can become too wide.

The thid column contains a type (s=string,d=decimal, f=float,t=time h:m:s).
The fourth column contains a regular expression for detecting the attribute in
a log file. Finally, the fifth column contains a format string which, if
present, is used with sformatf to print the result. For example, a %3.1f 
specifier might be used to indicate that only one decimal point should be
printed.

=cut

use Getopt::Long qw(:config no_auto_abbrev no_ignore_case);
use Pod::Usage;
use strict;
use Text::Table;
use warnings;
#  use Switch;    # not using switch, appears not to be installed

$| = 1 ; # force flushing of stdout

# ###########################################################################
# Subroutine prototypes
# ###########################################################################
sub text_report($ );
sub csv_report( );
sub string_repeat($$);
sub extract_common_prefix(@);
sub extract_common_suffix(@);

# ###########################################################################
# # Declare Global Variables
# ###########################################################################

# Command options
my @pat_files_A = ( );
my @att_files_A = ( );
my @waiver_files_A = ( );
my $format = "TXT";     # outputf format
my $outfile = "";       # default to STDOUT
my $noendcheck = 0;     # don't fail if missing EOT
my $nowarn = 0;         # don't fail if there are warnings
my $list_warning = 0;   # list all the warnings 
my $list_error = 0;     # list all the errors 
my $nopreresetwarn = 0; # don't fail if there are warnings pre reset
my $notime = 0;         # don't fail if there are timing violations
my $no_groups = 0;      # flag to suppresss group by table report
my $suppresswaived = 0; # flag to prevent waived errors/warnings being reported
my $suppressprereset = 0; # flag to prevent waived errors/warnings being reported
my $help_flag = 0;
my @log_files_A = ( );

my $debug = 0;
my $silent = 0;

# Internal data structures
my @pattern_DB_AoH = ( ); # Array containging patterns. Each entry contains a
                          # hash with keys REGEXP|TYPE. REGEXP is a regexp
                          # to match against. 
                          # TYPE is "ERROR|ERROR_NUM|SEED|WARNING|WARNING_NUM|EOT|RESET|GROUP

my @waiver_DB_AoH = ( ); # Array containging waiver  patterns. Each entry contains a
                          # hash with keys REGEXP|TYPE. REGEXP is a regexp
                          # to match against. 
                          # TYPE is "NOERROR|NOWARNING"

my @attribute_DB_AoH = ( ); # Array containing patterns. Each entry contains a
                            # hash with keys NAME|TYPE|REGEXP

my %present_attributes_H; # Hash which is indexed by attribute NAMEs. An
                          # entry is present, if that attribute has been
                          # seen. Used to avoid printing attributes that
                          # were not see in the current logs

my %found_attributes_DB_HoH; # Holds the attributes that were found
                             #  First index is the log file name
                             #  Second Index is {ATT_NAME}

my @valid_types_A = "GROUP|ERROR|ERROR_NUM|WARNING|SEED|WARNING_NUM|EOT|RESET|TIMING";
my @valid_waiver_types_A = "NOERROR|NOWARNING";
my @valid_attribute_types_A   = "ATT|META";
my @valid_attribute_formats_A = "s|d|f|t";

my %msg_DB_HoH;   # Holds summary of results after parsing each log file
                  #
                  # First index is the filename
                  # Second index is {ERROR|SEED|WARNING|EOT}

my %group_DB_HoH; # First Index is filename
                  # Second is Group Name ( eg. QUESTA_MSG)
                  # Third is Key  (eg. vlog-1234)
                  # Content is the count

# General behaviour
my $dot_interval = 1000;                     # One dot on the STD out after this many lines of log file
my $debug_prefix = "<<< DEBUG >>> ";
my $warning_prefix = "*** WARNING ***";
my $numeric_RE = "[0-9]+";
my $max_log_file_name_len = 0;
my $common_length_start_log_file_names = 0;  # part at start of log file names
                                             # that is common and thus not printed
my $common_length_end_log_file_names = 0;    # same and end of file name

# Summary variables
my $total_errors=0;        # total errors in all logs
my $total_waived_errors=0; # total errors wavied in all logs
my $total_warnings=0;      # total warnings in all logs
my $total_waived_warnings=0;      # total warnings in all logs
my $total_timing=0;        # total timing violations in all logs
my $total_seed = 0;        # total # of seed messages
my $missing_eot=0;         # total logs missing an EOT
my $final_ret_value = 255; # 
my $num_passing_tests = 0; # Count how many tests passed
my %warnings_DB_HoHoH;     # Stores all the warning lines. Indexed by (i) file (ii) line number (iii) WAIVED|TEXT-> Contains the warning text
my %errors_DB_HoHoH;       # Stores all the error lines. Index by (i) file (ii) line number, (iii) WAIVED|TEXT

# File handle for output
my $outfile_FH;

# ###########################################################################
# Read Command Options
# ###########################################################################
GetOptions(
    'pat=s'             => \@pat_files_A,
    'waiver=s'          => \@waiver_files_A,
    'att=s'             => \@att_files_A,
    'format=s'          => \$format,
    'out=s'             => \$outfile,
    'noendcheck'        => \$noendcheck,
    'listwarnings'      => \$list_warning,
    'listerrors'        => \$list_error,
    'suppresswaived'    => \$suppresswaived,
    'suppressprereset'  => \$suppressprereset,
    'nowarn'            => \$nowarn,
    'nopreresetwarn'    => \$nopreresetwarn,
    'help'              => \$help_flag,
    'debug'             => \$debug,
    'nogroup'           => \$no_groups,
    'silent'            => \$silent,
  ) or pod2usage( -verbose => 1,  -exitval => 1);
  if ($help_flag) { pod2usage( -verbose => 3, -exitval => 0); };

# Basic checks on arguments
$format = uc($format);
if ( ( $format ne "TXT" ) && ( $format ne "CSV" ) && ( $format ne "XML" ) ) {
   proc_err("Invalid output file format : $format");
}

# Check there is at least one log file (no vacuous pass!)
if ( $#ARGV < 0 ) {
   proc_err( "No log files specified." );
}

# ###########################################################################
# Read the pattern files
# ###########################################################################
foreach my $pat_file ( @pat_files_A ) {
   my $l=0; # line counter for error messages
   open (my $FH,"<", $pat_file ) or proc_err("Unable to open pattern file $pat_file");
   while (<$FH>) {
      $l++;
      next if (/^#/);
      next if (/^$/);
      my @csv_fields = split(",");
      my $type   = $csv_fields[0];
      my $regexp = $csv_fields[1];
      my $group_name;
      if ( grep ( /$type/, @valid_types_A ) != 1 ) {
         proc_err("Invalid pattern type ($type) at line $l of file $pat_file.\n$_" );
      }
      chomp $regexp;
      if ( $regexp eq "" ) {
         proc_err( "Regular expression ($regexp) at line $l of file $pat_file is empty" );
      }
      if ( $type eq "GROUP" ) {
         $group_name = $csv_fields[2];
         chomp $group_name;
         if ( !defined $group_name ) {
            proc_err("Group pattern at line $l of file $pat_file is missing a group name.\n$_");
         }
      }
      my %rec;
      $rec{TYPE}     = $type;
      $rec{REGEXP}   = $regexp;
      $rec{GROUPNAME}= $group_name;
      $rec{FILE}     = $pat_file;       # for debug only
      $rec{LINE_NUM} = $l;              # for debug only
      push @pattern_DB_AoH, { %rec };
      if ( $debug ) {
         print $debug_prefix, "Reading pattern of type $type in $pat_file with this pattern : $regexp \n";
      }
   }
   close $FH;
}

# ###########################################################################
# Read the waiver files
# ###########################################################################
foreach my $waiver_file ( @waiver_files_A ) {
   my $l=0; # line counter for error messages
   open (my $FH,"<", $waiver_file ) or proc_err("Unable to open pattern file $waiver_file");
   while (<$FH>) {
      $l++;
      next if (/^#/);
      next if (/^$/);
      my ( $type, $regexp ) = split(",");
      if ( grep ( /$type/, @valid_waiver_types_A ) != 1 ) {
         proc_err("Invalid pattern type ($type) at line $l of file $waiver_file.\n$_" );
      }
      chomp $regexp;
      if ( $regexp eq "" ) {
         proc_err( "Regular expression ($regexp) at line $l of file $waiver_file is empty" );
      }
      my %rec;
      $rec{TYPE}     = $type;
      $rec{REGEXP}   = $regexp;
      $rec{FILE}     = $waiver_file;       # for debug only
      $rec{LINE_NUM} = $l;              # for debug only
      push @waiver_DB_AoH, { %rec };
      if ( $debug ) {
         print $debug_prefix, "Reading pattern of type $type in $waiver_file with this pattern : $regexp \n";
      }
   }
   close $FH;
}

# ###########################################################################
# Read the attributes files
# ###########################################################################
foreach my $att_file ( @att_files_A ) {
   my $l=0; # line counter for error messages
   open (my $FH,"<", $att_file ) or proc_err("Unable to open pattern file $att_file");
   while (<$FH>) {
      $l++;
      next if (/^#/);
      next if (/^$/);
      my ( $att_type, $att_name, $type, $regexp, $format_string ) = split(",");
      if ( grep ( /$att_type/, @valid_attribute_types_A ) != 1 ) {
         proc_err("Invalid attribute type ($type) at line $l of file $att_file.\n$_" );
      }
      if ( grep ( /$type/, @valid_attribute_formats_A ) != 1 ) {
         proc_err("Invalid attribute format ($type) at line $l of file $att_file.\n$_" );
      }
      chomp $regexp;
      if ( $regexp eq "" ) {
         proc_err( "Regular expression ($regexp) at line $l of file $att_file is empty" );
      }
      if ( ! defined $format_string ) { $format_string = ""; }
      my %rec;
      $rec{ATT_TYPE} = $att_type;
      $rec{ATT_NAME} = $att_name;
      $rec{TYPE}     = $type;
      $rec{REGEXP}   = $regexp;
      $rec{FORMAT}   = $format_string;
      $rec{FILE}     = $att_file;       # for debug only
      $rec{LINE_NUM} = $l;              # for debug only
      push @attribute_DB_AoH, { %rec };
      if ( $debug ) {
         print $debug_prefix, "Reading attribute of type $type in $att_file with this pattern : $regexp \n";
      }
   }
   close $FH;
}

# ###########################################################################
# Install some default patterns, if no pattern file provided.
# 
# These patterns are very broad and might trigger on 
# ###########################################################################
if ( $#pattern_DB_AoH eq -1 ) {
   @pattern_DB_AoH = (  {
                           TYPE     => "ERROR",
                           REGEXP   => ".*[Ee][Rr][Rr][Oo][Rr]",
                           BUILTIN  => 1,
                        },
                        {
                           TYPE     => "WARNING",
                           REGEXP   => ".*[Ww][Aa][Rr][Nn]",
                           BUILTIN  => 1,
                        },
                        {
                           TYPE     => "EOT",
                           REGEXP   => ".*[Cc][Oo][Mm][Pp][Ll][Ee][Tt][Ee]",
                           BUILTIN  => 1,
                        },
                        {
                           TYPE     => "SEED",
                           REGEXP   => "SEED=([0-9]+)",
                           BUILTIN  => 1,
                        },
                        {
                           TYPE     => "RESET",
                           REGEXP   => "RESET_DONE",
                           BUILTIN  => 1,
                        },
                        {
                           TYPE     => "TIMING",
                           REGEXP   => "Timing Violation",
                           BUILTIN  => 1,
                        },
                     );
}

# ###########################################################################
# For debug - dump all the patterns
# ###########################################################################
if ( $debug ) {
  my $n=0;
  foreach my $pat_href ( @pattern_DB_AoH ) {
     print "$debug_prefix Pattern #$n (",$pat_href->{TYPE},") = ", $pat_href->{REGEXP};
     if ( $pat_href->{BUILTIN} ) {
        print " (default pattern)";
     } else {
        print ". Found on line ",$pat_href->{LINE_NUM}, " of ", $pat_href->{FILE};
     }
     print "\n";
     $n++;
  }
  $n=0;
  foreach my $pat_href ( @waiver_DB_AoH ) {
     print "$debug_prefix Waiver Pattern #$n (",$pat_href->{TYPE},") = ", $pat_href->{REGEXP};
     if ( $pat_href->{BUILTIN} ) {
        print " (default pattern)";
     } else {
        print ". Found on line ",$pat_href->{LINE_NUM}, " of ", $pat_href->{FILE};
     }
     print "\n";
     $n++;
  }
}

# ###########################################################################
# Read and Parse the log files
# ###########################################################################
if ( $#ARGV > 0 ) {
   $common_length_start_log_file_names = extract_common_prefix( @ARGV );
   $common_length_end_log_file_names   = extract_common_suffix( @ARGV );
}
foreach my $log ( @ARGV ) {
   open (my $FH,"<", $log) or proc_err( "Unable to open $log for reading.");
   if (!$silent) {
      print "Scanning $log";
      if ( $debug ) { print "\n"; }
   }

   my $l=0;                # line counter

   my $num_errors = 0;              # no. errors in current log
   my $num_pre_reset_warnings = 0;  # no. pre-reset warnings in current log
   my $num_post_reset_warnings = 0; # no. post-reset warnings in current log
   my $num_pre_reset_timing = 0;    # no. pre-reset timing viol in current log
   my $num_post_reset_timing = 0;   # no. post-reset timing viol in current log
   my $num_timing = 0;              # either all timing violns or jus post-reset
   my $num_warnings = 0;             # either all warnings or jus post-reset
   my $num_waived_warnings = 0;     # number of warnings that were waived
   my $num_waived_errors = 0;       # number of errors that were waived
   my $got_eot = 0;                 # check we got an EOT message
   my $seed = "";

   my $got_bad_msg = 0 ;   # indicates badly formated ERROR_NUM, WARNING_NUM
   my $reset_done_flag = 0;
   my $bad_msg_line;

   while (<$FH>) {


      $l++;
      my $logit=0;            # something matched ; print it in debug mode

      my $waive_error_on_this_line = 0;
      my $waive_warning_on_this_line = 0;

      my %groups_H;

      # First check if the line matches a waiver
      foreach my $pat_href ( @waiver_DB_AoH ) {
         my $regex = $pat_href->{REGEXP} ;
         my $type  = $pat_href->{TYPE} ;

         if (/$regex/) {
            if ( $type eq "NOWARNING" ) { $waive_warning_on_this_line = 1; }
            if ( $type eq "NOERROR"   ) { $waive_error_on_this_line   = 1; }
         }
      }

      # Second - check for groups
      foreach my $pat_href ( @pattern_DB_AoH ) {
         my $regex = $pat_href->{REGEXP} ;
         my $type  = $pat_href->{TYPE} ;

         if ( $type eq "GROUP" ) {
            my $group_name = $pat_href->{GROUPNAME};
            if (/$regex/) {
               if ( !( defined $1 ) ) {
                  print "\n $warning_prefix At line $l of $log, found a group expression ($regex) which didn't yield a valid string.\n";
               } else {
                  $groups_H{$group_name} = $1;
               } # endif
            } # endif
         } # endif
      } # endforeach


      # Now check if the line matches a warning/error/eot/seed pattern
      foreach my $pat_href ( @pattern_DB_AoH ) {
         my $regex = $pat_href->{REGEXP} ;
         my $type  = $pat_href->{TYPE} ;

         if ( $type ne "GROUP" ) {
            if (/$regex/) {

               if ( $type eq "TIMING" ) {
                  $logit=1;  # for debug only
                  if ( $reset_done_flag ) {
                     $num_post_reset_timing++;
                  } else {
                     $num_pre_reset_timing++;
                  }
               } elsif ( $type eq "ERROR" ) {
                  $logit=1; # for debug only
                  $errors_DB_HoHoH{$log}{$l}{TEXT} = $_;
                  if ( $waive_error_on_this_line ) {
                     $errors_DB_HoHoH{$log}{$l}{WAIVED} = 1;
                     $num_waived_errors++;
                  } else {
                     $errors_DB_HoHoH{$log}{$l}{WAIVED} = 0;
                     $num_errors +=1;
                     # Record which groups this error belonged to
                     foreach my $group ( keys %groups_H ) {
                        if ( defined $group_DB_HoH{$log}{ $group }{ $groups_H{$group} } ) {
                           $group_DB_HoH{$log}{ $group }{ $groups_H{$group} }++;
                        } else {
                           $group_DB_HoH{$log}{ $group }{ $groups_H{$group} }=1;
                        }
                     }
                  }
               } elsif ( $type eq "ERROR_NUM" ) {
                   $logit=1; # for debug only
                   my $num_err = $1;
                   if ( ( ! defined $1 ) || ! ( $1 =~ $numeric_RE ) ) {
                      $num_errors++;
                      $got_bad_msg = 1;
                      $bad_msg_line = $l; 
                   } else {
                      $num_errors += $num_err;
                   }
               } elsif ( $type eq "WARNING" ) {
                  $logit=1; # for debug only
                  $warnings_DB_HoHoH{$log}{$l}{TEXT} = $_;
                  $warnings_DB_HoHoH{$log}{$l}{POSTRESET} = $reset_done_flag;
                  if ( $waive_warning_on_this_line ) {
                     $warnings_DB_HoHoH{$log}{$l}{WAIVED} = 1;
                     $num_waived_warnings++;
                  } else {
                     $warnings_DB_HoHoH{$log}{$l}{WAIVED} = 0;
                     if ( $reset_done_flag ) {
                        $num_post_reset_warnings +=1;
                     } else {
                        $num_pre_reset_warnings +=1;
                     }
                     # Record which groups this warnings belonged to
                     if ( ($reset_done_flag) || ( !($nopreresetwarn) ) && (!$nowarn) ) {
                        foreach my $group ( keys %groups_H ) {
                           if ( defined $group_DB_HoH{$log}{ $group }{ $groups_H{$group} } ) {
                              $group_DB_HoH{$log}{ $group }{ $groups_H{$group} }++;
                           } else {
                              $group_DB_HoH{$log}{ $group }{ $groups_H{$group} }=1;
                           }
                        }
                     }
                  }
               } elsif ( $type eq "WARNING_NUM" ) {
                  $logit=1;  # for debug only
                  my $num_warn = $1;
                  if ( ( ! defined $1 ) || ! ( $1 =~ $numeric_RE ) ) {
                     $num_warnings++;
                     $got_bad_msg = 1;
                     $bad_msg_line = $l; 
                  } else {
                     if ( $reset_done_flag ) {
                        $num_post_reset_warnings += $num_warn;
                     } else {
                        $num_pre_reset_warnings += $num_warn;
                     }
                  }
               } elsif ( $type eq "EOT" ) {
                  $logit=1; # for debug only
                  $got_eot = 1;
               } elsif ( $type eq "SEED" ) {
                  $logit=1;  # for debug only
                  if ( defined $1 ) {
                     $seed = $1;
                     $total_seed++;
                  }
               } elsif ( $type eq "RESET" ) {
                  $logit=1;  # for debug only
                  $reset_done_flag = 1;
               }
            } # endif REGEXP
         } # endif !GROUP
      } # end foreach

      # Now check if the line matches an attribute
      foreach my $att_href ( @attribute_DB_AoH ) {
         my $att_type  = $att_href->{ATT_TYPE} ;
         my $regex     = $att_href->{REGEXP} ;
         my $type      = $att_href->{TYPE} ;
         my $att_name  = $att_href->{ATT_NAME} ;

         # If it's an attribute - search for the regexp in this line
         if ( $att_type eq "ATT" ) {
            if (/$regex/) {
               my $att_value = $1;
               if (defined $att_value) {
                  if ( $debug ) {
                     print $debug_prefix, "Matched attribute $att_name = $att_value at line $l\n";
                  }
               }
               $found_attributes_DB_HoH{$log}{$att_name} = $att_value;
               $present_attributes_H{$att_name} = $type;
            }
         }
      }

      # Timing violations
      # Safety check - if there are timing violations but no reset indication - fail the test
      if ($reset_done_flag ) {
         $num_timing = $num_post_reset_timing;
      } else {
         $num_timing = $num_pre_reset_timing + $num_pre_reset_timing;
      }

      # Safety check - if there are timing violations but no reset indication - fail the test
      if ( ($reset_done_flag) && ( $nopreresetwarn ) ) {
         $num_warnings = $num_post_reset_warnings;
      } else {
         $num_warnings = $num_pre_reset_warnings + $num_post_reset_warnings;
      }

      if ( $debug ) {
         if ( $logit ) {
            print "$debug_prefix : Line $l in $log matched.";
            print "ERRORS=$num_errors ( $num_waived_errors were wavied ).\n";
            print "PRE RESET WARNINGS=$num_pre_reset_warnings. POST RESET WARNINGS=$num_post_reset_warnings. $num_waived_warnings were waived.\n";
            print "EOT=$got_eot.\n";
            print "PRE RESET TIMING=$num_pre_reset_timing. POST RESET TIMING=$num_post_reset_timing\n";
            print "RESET_DONE=$reset_done_flag. NUM_TIMING=$num_timing\n";
            print "GOT BAD MSG=$got_bad_msg. SEED=$seed\n"
         }
      } else {
         # Print dots to show progress for long log files
         if ( ( $l % $dot_interval ) == 0 ) {
            print ".";
        }
     }
   }
   close $FH;
if(!$silent) {
   print "\n";
   }

   # If there was a message with a number of errors/warnings that could not
   #  be parsed cleanly - report it now
   if ( $got_bad_msg ) {
      print "$warning_prefix : On line $bad_msg_line of $log ";
      print "unable to determine number of messages - assuming 1.\n";
   }

   # Store results for current file in the DB
   $msg_DB_HoH{$log}{ERROR}          = $num_errors;
   $msg_DB_HoH{$log}{WAIVED_ERROR}   = $num_waived_errors;
   $msg_DB_HoH{$log}{WARNING}        = $num_warnings;
   $msg_DB_HoH{$log}{WAIVED_WARNING} = $num_waived_warnings;
   $msg_DB_HoH{$log}{TIMING}         = $num_timing;
   $msg_DB_HoH{$log}{EOT}            = $got_eot;
   $msg_DB_HoH{$log}{SEED}           = $seed;

}

# ###########################################################################
# Compute the META Attributes
# ###########################################################################
foreach my $log ( @ARGV ) {
   foreach my $att_href ( @attribute_DB_AoH ) {
      if ( $att_href->{ATT_TYPE} eq "META" ) {
         my $expression = $att_href->{REGEXP} ;
         my $type       = $att_href->{TYPE} ;
         my $att_name   = $att_href->{ATT_NAME} ;
         my $format     = $att_href->{FORMAT} ;

         my $vars_defined = 1;

         # Perform variable substitution
         while ( $expression =~ /\$([A-Za-z_]+)/ ) {
            my $var_name = $1;
            my $var_type = $present_attributes_H{$var_name};
            if ( !defined $var_type ) { $var_type = "d"; }
            my $value = $found_attributes_DB_HoH{$log}{$var_name};
            if ( defined $value ) {
               if ( $var_type eq "t" ) {
                 $value = time2sec($value);
               }
               $expression =~ s/\$$var_name/$value/g;
            } else {
               $expression =~ s/\$$var_name/0/g;
               $vars_defined = 0;
            }
         }
         # Only evaluate if all variables were defined
         if ( $vars_defined ) {
            my $raw_result = eval($expression);
            my $formatted_result = $raw_result;
            # If a format specified was defined, apply it now
            if ( ( defined $raw_result ) && ( defined $format ) ) {
                 $formatted_result = sprintf($format,$raw_result);
            }
            $present_attributes_H{$att_name} = 1;
            $found_attributes_DB_HoH{$log}{$att_name} = $formatted_result;
         }
      }
   }
}

# ###########################################################################
# Count total errors and check that each test got an EOT
# ###########################################################################
foreach my $log ( @ARGV ) {
   my $status = "FAIL";              # start by assuming test failed

   # Track length of longest log file name to format report
   if ( length ($log) > $max_log_file_name_len ) {
      $max_log_file_name_len = length($log);
   }

   if ( (                  $msg_DB_HoH{$log}{ERROR} == 0 ) &&
        ( $nowarn     || ( $msg_DB_HoH{$log}{WARNING} == 0 ) ) &&
        ( $notime     || ( $msg_DB_HoH{$log}{TIMING} == 0 ) ) &&
        ( $noendcheck || ( $msg_DB_HoH{$log}{EOT} != 0 ) ) ) {
      $status = "PASS";
      $num_passing_tests++;
   }
   $total_errors          += $msg_DB_HoH{$log}{ERROR};
   $total_waived_errors   += $msg_DB_HoH{$log}{WAIVED_ERROR};
   $total_timing          += $msg_DB_HoH{$log}{TIMING};
   $total_warnings        += $msg_DB_HoH{$log}{WARNING};
   $total_waived_warnings += $msg_DB_HoH{$log}{WAIVED_WARNING};
   $missing_eot++ unless ( $msg_DB_HoH{$log}{EOT} > 0 ) ;
   $msg_DB_HoH{$log}{STATUS} = $status;
}

# ###########################################################################
# Compute final status
# ###########################################################################
$final_ret_value = $total_errors;                 # always report errors
$final_ret_value += $total_warnings unless $nowarn; # normally include warnings
$final_ret_value += $total_timing unless $notime; # normally include warnings
$final_ret_value += $missing_eot  unless $noendcheck;     # and missing eots
if ( $final_ret_value > 255 ) { $final_ret_value = 255; } # don't try return values >255

# ###########################################################################
# Report Generation
# ###########################################################################

# Open the outputfile ( or point to STDOUT)
if ( $outfile ) {
   open ($outfile_FH,">", $outfile ) or 
       proc_err("Unable to open output file $outfile for writing");
} else {
   $outfile_FH = *STDOUT;
}

# Create a summary
my $final_summary = "Scanned " . ($#ARGV+1) . " log file(s).\n" .
                    "Number passing logs           : $num_passing_tests\n\n" .

                    "Total number of errors        : $total_errors" .
                    ( ( $total_waived_errors > 0 ) ? " ($total_waived_errors more were waived)\n" : "\n" ) .
                    "Total number of warnings      : $total_warnings" .
                    ( ( $total_waived_warnings > 0 ) ? " ($total_waived_warnings more were waived)\n" : "\n" ) .
                    "Total number of timing violns : $total_timing\n" .
                    "Total missing end of test mgs : $missing_eot\n";

if ( $outfile ne "" ) {
   $final_summary .= "Wrote detailed report to $outfile";
}

if ( $format eq "TXT" ) {
   if (!$silent) {
      text_report( $final_summary );
   }
} elsif ( $format eq "CSV" ) {
   csv_report( );
} else {
   proc_error("XML report not yet implemented");
}
print STDERR $final_summary unless $outfile eq "";

# ###########################################################################
# Banner Output
# ###########################################################################
if (!$silent) {
  if ( $final_ret_value != 0 ) {
     banner_fail();
  } else {
     banner_pass();
  }
}
# ###########################################################################
# That's it
# ###########################################################################
exit($final_ret_value);

# ###########################################################################
# ###########################################################################
# Subroutines
# ###########################################################################
# ###########################################################################

# ###########################################################################
# sub proc_err
#
# Report a fatal error msg and exit.
# ###########################################################################
sub proc_err {
   my $msg    = shift;


   print STDERR "*** ERROR scanlogs failed ***\n";
   print STDERR $msg,"\n";
   exit(255);
}

# ###########################################################################
# sub banner_pass
# ###########################################################################
sub banner_pass {
   print STDERR "\n\n";
   print STDERR "          PPPPP    AAAA     SSSS     SSSS   \n";
   print STDERR "          P    P  A    A   S    S   S    S  \n";
   print STDERR "          P    P  A    A    S        S      \n";
   print STDERR "          PPPPP   AAAAAA     SS       SS    \n";
   print STDERR "          P       A    A       S        S   \n";
   print STDERR "          P       A    A   S    S   S    S  \n";
   print STDERR "          P       A    A    SSSS     SSSS   \n";
}

# ###########################################################################
# sub banner_fail
# ###########################################################################
sub banner_fail {
   print STDERR "\n\n";
   print STDERR "          FFFFFF   AAAA    III  L       \n";
   print STDERR "          F       A    A    I   L       \n";
   print STDERR "          F       A    A    I   L       \n";
   print STDERR "          FFFF    AAAAAA    I   L       \n";
   print STDERR "          F       A    A    I   L       \n";
   print STDERR "          F       A    A    I   L       \n";
   print STDERR "          F       A    A   III  LLLLL   \n";
}


# ###########################################################################
# sub text_report
# ###########################################################################
sub text_report( $ ) {
   my $final_summary = shift;

   # Figure out width of the column for the log file names
   my $log_col_width = $max_log_file_name_len 
                       - $common_length_start_log_file_names 
                       - $common_length_end_log_file_names;

   if ( $log_col_width < 20 ) { $log_col_width = 20; }

   my $total_width = $log_col_width + 20;

   Text::Table->warnings('on');

   my @headings_A = (
   \'|', 
   {  title => "Log file",
      align => "left",
      align_title => "center" },
   \'|' );
   if ( $total_seed > 0 ) {
      push @headings_A, (
      {  title => "Seed",
         align => "center",
         align_title => "center" },
      \'|',
      ) 
   };
   push @headings_A, (
   { title => "Errors",
      align => "center",
      align_title => "center" },
   \'|', 
   { title => "Warnings",
     align => "center",
     align_title => "center" },
   \'|' );

   if ( $total_timing > 0 ) {
      push @headings_A,  (
      { title => "Timing\nViolations",
        align => "center",
        align_title => "center" },
      \'|',
      );
   }
   push @headings_A, (
   { title => "EOT",
     align => "center",
     align_title => "center" },
   \'|',
   { title => "STATUS",
     align => "center",
     align_title => "center" },
   \'|' );
   foreach my $att ( sort keys  %present_attributes_H  ) {
      push @headings_A, (
     { title => $att,
       align => "center",
       align_title => "center" },
     \'|' );
   }

   my $tb = Text::Table->new( @headings_A );

   foreach my $log ( @ARGV ) {
      my @record_A;
      my $log_to_print = substr($log, $common_length_start_log_file_names );

      $log_to_print = substr( $log_to_print, 0, $log_col_width );
      push @record_A, $log_to_print;

      if ( $total_seed > 0 ) {
         if ( $msg_DB_HoH{$log}{SEED} ne "" ) {
            push @record_A, $msg_DB_HoH{$log}{SEED};
         } else {
            push @record_A, "";
         }
      }

      # Print errors and possibly waived errors
      my $err_string = $msg_DB_HoH{$log}{ERROR};
      if ( $msg_DB_HoH{$log}{WAIVED_ERROR} > 0 ) {
         $err_string .= sprintf("(%dW)", $msg_DB_HoH{$log}{WAIVED_ERROR} );
      }
      push @record_A, $err_string;

      # Print warnings and possibly waived warnings
      my $warn_string = $msg_DB_HoH{$log}{WARNING};
      if ( $msg_DB_HoH{$log}{WAIVED_WARNING} > 0 ) {
         $warn_string .= sprintf("%7s", sprintf("(%dW)", $msg_DB_HoH{$log}{WAIVED_WARNING} ) ) ;
      }
      push @record_A, $warn_string;

      if ($total_timing > 0 ) {
         push @record_A, $msg_DB_HoH{$log}{TIMING};
      }

      push @record_A, ( $msg_DB_HoH{$log}{EOT} ? "YES" : "NO" );

      push @record_A, $msg_DB_HoH{$log}{STATUS};


      foreach my $att ( sort keys  %present_attributes_H ) {
         my $att_value;
         $att_value = $found_attributes_DB_HoH{$log}{$att};
         push @record_A, $att_value;
      }

      $tb->add( @record_A );
   }

   # Output the table
   print $outfile_FH "\n";
   print $outfile_FH $tb->rule( '-','+');
   print $outfile_FH $tb->title;
   print $outfile_FH $tb->rule( '-','+');
   print $outfile_FH $tb->body;
   print $outfile_FH $tb->rule( '-','+');
   print $outfile_FH "\n\n";

   if ( $list_warning ) {
      my %warning_report_H; # Temporarily hold the warning report - prior to sorting

      print $outfile_FH " START WARNING SUMMARY\n";
      foreach my $log_file ( keys %warnings_DB_HoHoH ) {
         foreach my $line_num ( keys %{ $warnings_DB_HoHoH{$log_file} } ) {


            my $t = $warnings_DB_HoHoH{$log_file}{$line_num}{TEXT};
            chomp $t;
            my $w        = $warnings_DB_HoHoH{$log_file}{$line_num}{WAIVED}    ? "WAIVED" : "" ;
            my $prereset = $warnings_DB_HoHoH{$log_file}{$line_num}{POSTRESET} ? "" : "PRE_RESET" ;
            my $msg_prefix = " WARNING $w $prereset at $log_file ($line_num)";

            # If suppresswaived flag is true - don't display waived messages
            #   If use doesn't want to see pre-reset warnings - skip them
            if ( ( $w eq "" ) || ( !$suppresswaived ) ) {
               if ( ( !$suppressprereset ) || ( $prereset ne "PRE_RESET" ) ) {
                  my $key = $log_file . sprintf("%07d", $line_num ); # sort report by file and then line numbe
                  $warning_report_H{$key} = sprintf("%-30s : %s\n", $msg_prefix, $t );
               }
            }
         }
      }
      # Sort and print the warning report
      foreach my $k ( sort keys %warning_report_H ) {
         print $outfile_FH $warning_report_H{$k};
      }
      print $outfile_FH " END WARNING SUMMARY\n\n";
   }

   if ( $list_error ) {
      my %error_report_H; # Temporarily hold the warning report - prior to sorting

      print $outfile_FH " START ERROR SUMMARY\n";
      foreach my $log_file ( keys %errors_DB_HoHoH ) {
         foreach my $line_num ( keys %{ $errors_DB_HoHoH{$log_file} } ) {
            my $t = $errors_DB_HoHoH{$log_file}{$line_num}{TEXT};
            chomp $t;
            my $w = $errors_DB_HoHoH{$log_file}{$line_num}{WAIVED} ? "WAIVED" : "" ;
            my $msg_prefix = " ERROR $w at $log_file ($line_num)";

            # If suppresswaived flag is true - don't display waived messages
            if ( ( $w eq "" ) || ( !$suppresswaived ) ) {
               my $key = $log_file . sprintf("%07d", $line_num ); # sort report by file and then line numbe
               $error_report_H{$key} = sprintf("%-30s : %s\n", $msg_prefix, $t );
            }
         }
      }
      # Sort and print the error report
      foreach my $k ( sort keys %error_report_H ) {
         print $outfile_FH $error_report_H{$k};
      }
      print $outfile_FH " END ERROR SUMMARY\n\n";
   }

   # Print report by group
   if ( !$no_groups ) {

     my %unique_group_H;
     my @unique_group_A;
     my %unique_messages_group_HoH; # Indexed by group name, message
     my @headings_A ;

     # Identify a unique list of groups and their messages
     foreach my $log_i ( keys %group_DB_HoH ) {
        foreach my $group_i ( keys %{ $group_DB_HoH{$log_i} } ) {
           foreach my $msg ( keys %{ $group_DB_HoH{$log_i}{$group_i} } ) {
              $unique_group_H{$group_i} = 1;
              $unique_messages_group_HoH{$group_i}{ $msg } = 1;
           }
        }
     }

     # Adding log file to headings
     @headings_A = (
     \'|', 
     {  title => "Log file",
        align => "left",
        align_title => "center" },
     \'|' );
     if ( $total_seed > 0 ) {
        push @headings_A, (
        {  title => "Seed",
           align => "center",
           align_title => "center" },
        \'|',
        ) 
     };
     push @headings_A,\'|';

     # Add List of groups to Headings
     my $found_a_group_flag = 0;
     @unique_group_A = sort keys %unique_group_H;
     foreach my $group ( @unique_group_A ) {
        foreach my $msg ( sort keys %{ $unique_messages_group_HoH{$group} } ) {
           push @headings_A, {
               title => ( $group . "\n" . $msg ),
               align => "center",
               align_title => "center" };
           push @headings_A,\'|';
           $found_a_group_flag = 1;
        }
     }

     if ( $found_a_group_flag ) {
        my $group_tb = Text::Table->new( @headings_A );
   
        # Add each row
        foreach my $log ( @ARGV ) {
           my @record_A;
           my $log_to_print = substr($log, $common_length_start_log_file_names );
           my $num_groups = 0; # number of groups found for this row
   
           $log_to_print = substr( $log_to_print, 0, $log_col_width );
           push @record_A, $log_to_print;
   
           if ( $total_seed > 0 ) {
              if ( $msg_DB_HoH{$log}{SEED} ne "" ) {
                 push @record_A, $msg_DB_HoH{$log}{SEED};
              } else {
                 push @record_A, "";
              }
           }
   
           foreach my $group ( @unique_group_A ) {
              foreach my $msg ( sort keys %{ $unique_messages_group_HoH{$group} } ) {
                 my $v = $group_DB_HoH{$log}{$group}{$msg};
                 if ( !defined $v ) { $v = ""; } else { $num_groups++; }
                 push @record_A, $v;
              }
           }
   
           # Add the row to the table
           if ($num_groups>0) {
              $group_tb->add( @record_A );
           }
        }
   
        # Output the table
        print $outfile_FH "Summary by Message Group\n";
        print $outfile_FH "\n";
        print $outfile_FH $group_tb->rule( '-','+');
        print $outfile_FH $group_tb->title;
        print $outfile_FH $group_tb->rule( '-','+');
        print $outfile_FH $group_tb->body;
        print $outfile_FH $group_tb->rule( '-','+');
        print $outfile_FH "\n\n";
     }

  }

   print $outfile_FH $final_summary;
}

# ###########################################################################
# sub csv_report
#
# Output a report in CSV format.
# ###########################################################################
sub csv_report( ) {

   print $outfile_FH "TEST NAME,SEED,NUM ERRORS,NUM WARNINGS,TIMING,MISSING EOT,STATUS\n";
   foreach my $log ( @ARGV ) {
      print $outfile_FH $log,",";
      print $outfile_FH $msg_DB_HoH{$log}{SEED},",";
      print $outfile_FH $msg_DB_HoH{$log}{ERROR},",";
      print $outfile_FH $msg_DB_HoH{$log}{WARNING},",";
      print $outfile_FH $msg_DB_HoH{$log}{TIMING},",";
      print $outfile_FH ( $msg_DB_HoH{$log}{EOT} ? "YES" : "NO" ),",";
      print $outfile_FH $msg_DB_HoH{$log}{STATUS};
      print $outfile_FH "\n";
   }
}

# ###########################################################################
# sub string_repeat
# 
# Takes an input string and returns N copies concatenated together.
# ###########################################################################
sub string_repeat($$) {
   my $s = shift;
   my $n = shift;
   my $r = "";
   while ($n>0) { $r .= $s; $n-- };
   return $r;
}

# ###########################################################################
# sub extract_common prefix
#
# Takes in an array of strings. 
# Returns the number of characters that are common at the start of all
# the strings - or -1 if there is no common prefix.
# ###########################################################################
sub extract_common_prefix(@) {
   my @strings_A = @_;

   my $n=-1; 
   my $f=1;

   while ( $f ) {
      $n++;
      if ( length($strings_A[0]) <= $n ) { 
         $f=0;
      } else {
         my $c = substr($strings_A[0],$n,1);
         for( my $i=1 ; ( ( $f ) && ( $i <= $#strings_A ) ) ; $i++ ) {
            if ( substr($strings_A[$i], $n, 1 ) ne $c ) { $f=0; }
         }
      }
   }
   return $n;
}


# ###########################################################################
# sub extract_common suffix
#
# Takes in an array of strings. 
# Returns the number of characters that are common at the start of all
# the strings - or -1 if there is no common prefix.
# ###########################################################################
sub extract_common_suffix(@) {
   my @strings_A = @_;

   my $n=-1; 
   my $f=1;

   while ( $f ) {
      $n++;
      if ( length($strings_A[0]) <= $n ) { 
         $f=0;
      } else {
         my $c = substr($strings_A[0],-$n,1);
         for( my $i=1 ; ( ( $f ) && ( $i <= $#strings_A ) ) ; $i++ ) {
            if ( substr($strings_A[$i], -$n, 1 ) ne $c ) { $f=0; }
         }
      }
   }
   return $n-1;
}

# ###########################################################################
# time2sec
# ###########################################################################
sub time2sec {
   my $s = shift;

   $s =~ /([0-9]+):([0-9]+):([0-9]+)/;
   my $hour = $1;
   my $min  = $2;
   my $sec  = $3;
   if (!defined $hour) { $hour = 0; }
   if (!defined $min ) { $hour = 0; }
   if (!defined $sec ) { $hour = 0; }
   return ($sec + 60*$min + 60*60*$hour);
}


