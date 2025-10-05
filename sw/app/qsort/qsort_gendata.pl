#!/usr/bin/perl -w
#==========================================================================
# qsort_gendata.pl
#
# Author : Christopher Batten (cbatten@mit.edu)
# Date   : April 29, 2005
#
(our $usageMsg = <<'ENDMSG') =~ s/^\#//gm;
#
# Simple script which creates an input data set and the reference data
# for the qsort benchmark.
#
ENDMSG

use strict "vars";
use warnings;
no  warnings("once");
use Getopt::Long;

#--------------------------------------------------------------------------
# Command line processing
#--------------------------------------------------------------------------

our %opts;

sub usage()
{

  print "\n";
  print " Usage: qsort_gendata.pl [options] \n";
  print "\n";
  print " Options:\n";
  print "  --help  print this message\n";
  print "  --size  size of input data [250]\n";
  print "  --seed  random seed [1]\n";
  print "$usageMsg";

  exit();
}

sub processCommandLine()
{

  $opts{"help"} = 0;
  $opts{"size"} = 250;
  $opts{"seed"} = 1;
  Getopt::Long::GetOptions( \%opts, 'help|?', 'size:i', 'seed:i' ) or usage();
  $opts{"help"} and usage();

}

#--------------------------------------------------------------------------
# Helper Functions
#--------------------------------------------------------------------------

sub printArray
{
  my $arrayName = $_[0];
  my $arrayRef  = $_[1];

  my $numCols = 20;
  my $arrayLen = scalar(@{$arrayRef});

  print "type ".$arrayName."[DATA_SIZE] = \n";
  print "{\n";

  if ( $arrayLen <= $numCols ) {
    print "  ";
    for ( my $i = 0; $i < $arrayLen; $i++ ) {
      print sprintf("%3d",$arrayRef->[$i]);
      if ( $i != $arrayLen-1 ) {
        print ", ";
      }
    }
    print "\n";
  }

  else {
    my $numRows = int($arrayLen/$numCols);
    for ( my $j = 0; $j < $numRows; $j++ ) {
      print "  ";
      for ( my $i = 0; $i < $numCols; $i++ ) {
        my $index = $j*$numCols + $i;
        print sprintf("%3d",$arrayRef->[$index]);
        if ( $index != $arrayLen-1 ) {
          print ", ";
        }
      }
      print "\n";
    }

    if ( $arrayLen > ($numRows*$numCols) ) {
      print "  ";
      for ( my $i = 0; $i < ($arrayLen-($numRows*$numCols)); $i++ ) {
        my $index = $numCols*$numRows + $i;
        print sprintf("%3d",$arrayRef->[$index]);
        if ( $index != $arrayLen-1 ) {
          print ", ";
        }
      }
      print "\n";
    }

  }

  print  "};\n\n";
}

#--------------------------------------------------------------------------
# Main
#--------------------------------------------------------------------------

sub main()
{

  processCommandLine();
  srand($opts{"seed"});

  my @values;
  for ( my $i = 0; $i < $opts{"size"}; $i++ ) {
    push( @values, int(rand((1<<31)-1)) );
  }
  my @sorted = sort { $a <=> $b } @values;

  print "\n\#define DATA_SIZE ".$opts{"size"}." \n\n";
  printArray( "input_data", \@values );
  printArray( "verify_data", \@sorted );

}

main();

