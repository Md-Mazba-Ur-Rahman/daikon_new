#!/usr/bin/env perl

# colony-runmatches.pl:  runs a set of matches.
# See "usage()" routine for usage information.

sub usage () {
  return
    "$0 [OPTIONS] match-file result-file [parameters]\n"
    . "See colony-README for file formats\n"
    . "Options:\n"
    . "  --debug\n"
    . "  --distribute[=machine1,machine2,...]\n"
    . "  --duplicate[=machine1,machine2,...]\n"
    . "  --loadlimit=N\n"
    . "  --firstline=N\n"
    . "  --lastline=N\n";
}

use strict;
use English;
$WARNING = 1;
use checkargs;
use util_daikon;
use colony_simconf;
use POSIX;                      # for ceil
require Cwd;		# make Cwd:: accessible

my $debug = "";
my $distribute = 0;
my $duplicate = 0;
my $loadlimit = 0;
my $firstline = 0;
my $lastline = 0;
my @machines = ('parsnip', 'peanut',
                'beet', 'daikon', 'manioc', 'rutabaga', 'turnip',
                'yam', 'scallion',
                'shallot',
                # These are so slow it's hardly worthwhile to include them
                # 'potato',
                # 'meoptiplex'
                );
my $current_dir;


cleanup();

while ((scalar(@ARGV) > 0) && ($ARGV[0] =~ /^-/)) {
  my $arg = shift @ARGV;
  if ($arg eq "--debug") {
    $debug = $arg;
  } elsif ($arg =~ /^--distribute(=(.*))?$/) {
    $distribute = 1;
    if (defined($2)) {
      @machines = split(',', $1);
    }
  } elsif ($arg =~ /^--duplicate(=(.*))?$/) {
    $duplicate = 1;
    if (defined($2)) {
      @machines = split(',', $1);
    }
  } elsif ($arg =~ "--loadlimit=(.*)") {
    $loadlimit = $1;
  } elsif ($arg =~ "--firstline=(.*)") {
    $firstline = $1;
  } elsif ($arg =~ "--lastline=(.*)") {
    $lastline = $1;
  } else {
    die "unrecognized argument $arg";
  }
}

if (0 && $debug) {
  print "args:\n";
  print " distribute  $distribute\n";
  print " duplicate  $duplicate\n";
  print " loadlimit  $loadlimit\n";
  print " firstline  $firstline\n";
  print " lastline  $lastline\n";
}

if (scalar(@ARGV) < 2) {
  die "$0: not enough arguments; needs match-file and result-file\n" . usage();
}
my $input_filename = shift(@ARGV);
my $output_filename = shift(@ARGV);
my $parameters = join(' ', @ARGV);


###########################################################################
### Subroutines
###

#Clean up old temp files
sub cleanup () {
    my $tmpdir = "/tmp/$ENV{'USER'}";
    opendir (DIR, $tmpdir);
    my @files = readdir DIR;
    close DIR;
    # look through the directory for files matching the pattern
    # runmatch-[digits]
    foreach my $file (@files) {
	if ($file =~ /runmatch.\d+/) {
	    system_or_die("rm -rf $tmpdir/$file");    
	}
    }    
}


# Filter out elements of @machines whose load is greater than $loadlimit.
# If this would filter out all machines, run on all machines anyway.
sub obey_loadlimit () {
  check_args(0);
  if ($loadlimit == 0) {
    return;
  }
  die "--loadlimit argument not yet implemented";
}

# From the Perl FAQ.
sub file_lines ( $ ) {
  my ($filename) = check_args(1, @_);
  my $lines = 0;
  my $buffer;
  open(FILE, $filename) or die "Can't open `$filename': $!";
  while (sysread FILE, $buffer, 4096) {
    $lines += ($buffer =~ tr/\n//);
  }
  close FILE;
  return $lines;
}

sub absolutify_filenames () {
  check_args(0);
  $current_dir = Cwd::getcwd();
  $input_filename = absolutify_filename($input_filename);
  $output_filename = absolutify_filename($output_filename);
}

sub absolutify_filename ( $ ) {
  my ($filename) = check_args(1, @_);
  if ($filename =~ /^\//) {
    return $filename;
  }
  return "$current_dir/$filename";
}


###########################################################################
### Main processing
###

### The --distribute and --duplicate options run multiple jobs on multiple
### processors, by recursively invoking this same script.

if ($duplicate) {
  obey_loadlimit();
  absolutify_filenames();
  if (scalar(@machines) == 0) {
    die "No machines specified";
  }
  for my $host (@machines) {
    my $command = "ssh -f $host.lcs.mit.edu nice $0 $debug $input_filename $output_filename-$host $parameters";
    # print "$command\n";
    system_or_die($command);
  }
  exit(0);
}

if ($distribute) {
  obey_loadlimit();
  absolutify_filenames();
  my $num_matches = file_lines($input_filename);
  my $num_machines = scalar(@machines);
  my $num_matches_per_machine = ceil($num_matches/$num_machines);
  if ($num_machines == 0) {
    die "No machines specified";
  }
  for (my $hostnum=0; $hostnum<$num_machines; $hostnum++) {
    my $this_firstline = $hostnum*$num_matches_per_machine;
    my $this_lastline = $this_firstline + $num_matches_per_machine - 1;
    my $host = $machines[$hostnum];
    my $command = "ssh -f $host.lcs.mit.edu nice $0 $debug --firstline=$this_firstline --lastline=$this_lastline $input_filename $output_filename-$host $parameters";
    # print "$command\n";
    system_or_die($command);
  }
  exit(0);
}


### BASE CASE
### Simply run the job locally.
open (IN, $input_filename) || die "Cannot read $input_filename";
my $line;
my $lineno = 0;
while (defined($line = <IN>)) {
  $lineno++;
  if (($firstline && ($lineno < $firstline))
      || ($lastline && ($lineno > $lastline))) {
    next;
  }
  chomp($line);
  my ($team1, $team2) = split(' ', $line, 2);
  my $command = "colony-runmatch.pl $team1 $team2 $output_filename $parameters";
  if ($debug) {
    # system_or_die will print the command if it fails.
    # print "\ncommand: $command\n";
    system_or_die($command);
  } else {
    # Not system_or_die; it's OK if it dies (we'll notice the missing run
    # and come back to it later).
    system("colony-runmatch.pl $team1 $team2 $output_filename $parameters");
  }
}
close(IN);

exit(0);
