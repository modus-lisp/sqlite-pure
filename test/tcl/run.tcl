# test/tcl/run.tcl TESTFILE — run one of SQLite's *.test files against
# sqlite-pure: the [sqlite3] command of sqlite3.tcl, then the file itself,
# which sources SQLite's own tester.tcl from its directory.
set here [file dirname [file normalize [info script]]]
source $here/sqlite3.tcl
set argv0 [file normalize [lindex $argv 0]]
set argv [lrange $argv 1 end]
set rc [catch {source $argv0} msg]
if {$rc} { puts "ERROR: $msg" }
set s [lsort [array names ::sqlp::stubs]]
if {[llength $s]} { puts "STUBS: $s" }
exit 0
