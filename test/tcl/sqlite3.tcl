# test/tcl/sqlite3.tcl — the [sqlite3] command of SQLite's TCL interface
# (tclsqlite.c), implemented over test/tcl/server.lisp, plus the handful of
# testfixture commands tester.tcl needs.  Sourced before a test file, so
# that SQLite's tester.tcl and *.test files run unmodified.
#
# Each database handle is its own server process ($::env(SQLP_SERVER)).
# Values keep their types across the pipe: integers and doubles become Tcl
# numbers, blobs byte arrays; bound variables are typed by their Tcl
# internal representation, as tclsqlite binds them.

if {[info exists ::sqlp::loaded]} return

namespace eval ::sqlp {
  variable loaded 1
  variable chan    ;# handle -> channel
  variable null    ;# handle -> nullvalue
  variable fn      ;# id -> script
  variable nextid 0
  variable stubs   ;# testfixture commands called that only exist as stubs
  array set stubs {}
}

# ---------------------------------------------------------------- framing

proc ::sqlp::item {v {type ""}} {
  if {$type eq ""} { set type [::sqlp::typeof $v] }
  switch -- $type {
    n { return "n0:" }
    b { set bytes $v }
    default { set bytes [encoding convertto utf-8 $v] }
  }
  return "$type[string length $bytes]:$bytes"
}

# The storage class tclsqlite would bind a Tcl value as.
proc ::sqlp::typeof {v} {
  set r [tcl::unsupported::representation $v]
  if {[string match "value is a bytearray*" $r] && [string match "*no string representation*" $r]} {
    return b
  }
  if {[string match "value is a int *" $r] || [string match "value is a wideInt *" $r]
      || [string match "value is a boolean *" $r]} {
    if {[string is entier -strict $v]} { return i }
    if {[string is boolean -strict $v]} { return i }
  }
  if {[string match "value is a double *" $r]} { return f }
  return s
}

proc ::sqlp::send {ch items} {
  set out "[llength $items]\n"
  foreach it $items { append out $it }
  puts -nonewline $ch $out
  flush $ch
}

proc ::sqlp::readframe {ch} {
  if {[gets $ch n] < 0} { error "database server died" }
  set items {}
  for {set i 0} {$i < $n} {incr i} {
    set type [read $ch 1]
    set len ""
    while {[set c [read $ch 1]] ne ":"} {
      if {$c eq ""} { error "database server died" }
      append len $c
    }
    set bytes [read $ch $len]
    switch -- $type {
      n { lappend items [list n {}] }
      i { lappend items [list i [expr {wide($bytes)}]] }
      f { lappend items [list f [expr {double($bytes)}]] }
      s { lappend items [list s [encoding convertfrom utf-8 $bytes]] }
      b { lappend items [list b $bytes] }
    }
  }
  return $items
}

# A value from the server, as tclsqlite hands it to scripts.
proc ::sqlp::val {it {null ""}} {
  lassign $it type v
  if {$type eq "n"} { return $null }
  return $v
}

# Send a request and serve callbacks until the answer arrives.
proc ::sqlp::request {db items} {
  variable chan
  set ch $chan($db)
  ::sqlp::send $ch $items
  while 1 {
    set reply [::sqlp::readframe $ch]
    set op [::sqlp::val [lindex $reply 0]]
    switch -- $op {
      vars {
        set vals {}
        foreach it [lrange $reply 1 end] {
          set name [::sqlp::val $it]
          set var [string range $name 1 end]
          if {[uplevel #[::sqlp::level] [list info exists $var]]} {
            set v [uplevel #[::sqlp::level] [list set $var]]
            lappend vals [::sqlp::item $v]
          } else {
            lappend vals [::sqlp::item {} n]
          }
        }
        ::sqlp::send $ch [concat [list [::sqlp::item ret]] $vals]
      }
      call {
        set id [::sqlp::val [lindex $reply 1]]
        set args {}
        foreach it [lrange $reply 2 end] { lappend args [::sqlp::val $it $::sqlp::null($db)] }
        if {[catch {uplevel #0 [concat $::sqlp::fn($id) $args]} res]} {
          ::sqlp::send $ch [list [::sqlp::item err] [::sqlp::item $res s]]
        } else {
          ::sqlp::send $ch [list [::sqlp::item ret] [::sqlp::item $res]]
        }
      }
      coll {
        set id [::sqlp::val [lindex $reply 1]]
        set a [::sqlp::val [lindex $reply 2]]
        set b [::sqlp::val [lindex $reply 3]]
        if {[catch {uplevel #0 [concat $::sqlp::fn($id) [list $a $b]]} res] || ![string is integer -strict $res]} {
          ::sqlp::send $ch [list [::sqlp::item ret] [::sqlp::item 0 i]]
        } else {
          ::sqlp::send $ch [list [::sqlp::item ret] [::sqlp::item $res i]]
        }
      }
      default { return $reply }
    }
  }
}

# The stack level of the script that called the db command (for variables).
proc ::sqlp::level {} { return $::sqlp::callerlevel }
set ::sqlp::callerlevel 0

# ---------------------------------------------------------------- sqlite3

proc sqlite3 {args} {
  switch -- [lindex $args 0] {
    -sourceid { return "2022-12-28 14:03:47 sqlite-pure" }
    -version  { return 3.40.1 }
    -has-codec { return 0 }
  }
  set name [lindex $args 0]
  set file [lindex $args 1]
  set readonly 0
  foreach {opt val} [lrange $args 2 end] {
    switch -- $opt {
      -readonly { set readonly [expr {$val ? 1 : 0}] }
      default {}
    }
  }
  if {[info commands ::$name] ne ""} { catch {::$name close} }
  set ch [open "|$::env(SQLP_SERVER)" r+]
  fconfigure $ch -translation binary -encoding binary -buffering full
  set ::sqlp::chan($name) $ch
  set ::sqlp::null($name) ""
  set r [::sqlp::request $name [list [::sqlp::item open s] [::sqlp::item $file s] [::sqlp::item $readonly i]]]
  if {[::sqlp::val [lindex $r 0]] ne "ok"} {
    catch {close $ch}
    unset ::sqlp::chan($name)
    return -code error [::sqlp::val [lindex $r 1]]
  }
  # an alias adds no stack frame, so [uplevel 1] in a method is the caller
  interp alias {} ::$name {} ::sqlp::method $name
  return ""
}

# Run SQL; returns {error-message code results} where results is a list
# of {columns rows} per statement that ran.
proc ::sqlp::run {db sql level} {
  set ::sqlp::callerlevel $level
  set r [::sqlp::request $db [list [::sqlp::item eval s] [::sqlp::item $sql s]]]
  set ok [expr {[::sqlp::val [lindex $r 0]] eq "ok"}]
  set msg [::sqlp::val [lindex $r 1]]
  set code [::sqlp::val [lindex $r 2]]
  set nstmt [::sqlp::val [lindex $r 3]]
  set k 4
  set results {}
  for {set s 0} {$s < $nstmt} {incr s} {
    set ncol [::sqlp::val [lindex $r $k]]; incr k
    set cols {}
    for {set c 0} {$c < $ncol} {incr c} { lappend cols [::sqlp::val [lindex $r $k]]; incr k }
    set nrow [::sqlp::val [lindex $r $k]]; incr k
    set rows {}
    for {set i 0} {$i < $nrow} {incr i} {
      set row {}
      for {set c 0} {$c < $ncol} {incr c} { lappend row [lindex $r $k]; incr k }
      lappend rows $row
    }
    lappend results [list $cols $rows]
  }
  return [list [expr {$ok ? "" : $msg}] $ok $results]
}

# tclsqlite's method names; like Tcl_GetIndexFromObj, a unique prefix names one
set ::sqlp::methods {authorizer backup bind_fallback busy cache changes close collate
  collation_needed commit_hook complete config copy deserialize enable_load_extension
  errorcode eval exists function incrblob interrupt last_insert_rowid nullvalue
  onecolumn preupdate profile progress rekey restore rollback_hook serialize status
  timeout total_changes trace trace_v2 transaction unlock_notify update_hook version
  wal_hook func one}

proc ::sqlp::method {db method args} {
  set level [expr {[info level] - 1}]
  if {[lsearch -exact $::sqlp::methods $method] < 0} {
    set hits [lsearch -all -inline -glob $::sqlp::methods "$method*"]
    if {[llength $hits] == 1} {
      set method [lindex $hits 0]
    } else {
      return -code error "bad option \"$method\": must be [join [lrange $::sqlp::methods 0 end-3] {, }], or wal_hook"
    }
  }
  set null $::sqlp::null($db)
  switch -- $method {
    eval {
      set sql [lindex $args 0]
      lassign [::sqlp::run $db $sql $level] msg ok results
      if {[llength $args] == 1} {
        set out {}
        foreach res $results {
          foreach row [lindex $res 1] { foreach v $row { lappend out [::sqlp::val $v $null] } }
        }
        if {!$ok} { return -code error $msg }
        return $out
      }
      if {[llength $args] == 2} { set arr ""; set script [lindex $args 1] } else {
        set arr [lindex $args 1]; set script [lindex $args 2]
      }
      foreach res $results {
        lassign $res cols rows
        foreach row $rows {
          if {$arr ne ""} {
            uplevel 1 [list set ${arr}(*) $cols]
            foreach c $cols v $row { uplevel 1 [list set ${arr}($c) [::sqlp::val $v $null]] }
          } else {
            foreach c $cols v $row { uplevel 1 [list set $c [::sqlp::val $v $null]] }
          }
          set rc [catch {uplevel 1 $script} res2 opts]
          if {$rc == 3} { if {!$ok} {return -code error $msg}; return "" }
          if {$rc == 4} continue
          if {$rc != 0} { return -options $opts -level [expr {[dict get $opts -level] + 1}] $res2 }
        }
      }
      if {!$ok} { return -code error $msg }
      return ""
    }
    one - onecolumn {
      lassign [::sqlp::run $db [lindex $args 0] $level] msg ok results
      if {!$ok} { return -code error $msg }
      foreach res $results {
        set rows [lindex $res 1]
        if {[llength $rows]} { return [::sqlp::val [lindex $rows 0 0] $null] }
      }
      return ""
    }
    exists {
      lassign [::sqlp::run $db [lindex $args 0] $level] msg ok results
      if {!$ok} { return -code error $msg }
      foreach res $results { if {[llength [lindex $res 1]]} { return 1 } }
      return 0
    }
    close {
      catch {::sqlp::request $db [list [::sqlp::item close s]]}
      catch {close $::sqlp::chan($db)}
      unset -nocomplain ::sqlp::chan($db)
      rename ::$db {}
      return ""
    }
    changes - total_changes - last_insert_rowid - errorcode {
      return [::sqlp::val [lindex [::sqlp::request $db [list [::sqlp::item $method s]]] 1]]
    }
    complete {
      return [::sqlp::val [lindex [::sqlp::request $db [list [::sqlp::item complete s] [::sqlp::item [lindex $args 0] s]]] 1]]
    }
    nullvalue {
      if {[llength $args]} { set ::sqlp::null($db) [lindex $args 0] }
      return $::sqlp::null($db)
    }
    func - function {
      set name [lindex $args 0]
      set script [lindex $args end]
      set nargs -1
      foreach {o v} [lrange $args 1 end-1] {
        if {$o eq "-argcount"} { set nargs $v }
      }
      set id [incr ::sqlp::nextid]
      set ::sqlp::fn($id) $script
      ::sqlp::request $db [list [::sqlp::item func s] [::sqlp::item $name s] [::sqlp::item $nargs i] [::sqlp::item $id i]]
      return ""
    }
    collate {
      lassign $args name script
      set id [incr ::sqlp::nextid]
      set ::sqlp::fn($id) $script
      ::sqlp::request $db [list [::sqlp::item collate s] [::sqlp::item $name s] [::sqlp::item $id i]]
      return ""
    }
    transaction {
      set type ""
      if {[llength $args] == 2} { set type [lindex $args 0] }
      set script [lindex $args end]
      set auto [::sqlp::val [lindex [::sqlp::request $db [list [::sqlp::item autocommit s]]] 1]]
      if {$auto} {
        ::sqlp::method $db eval "BEGIN $type"
        set rc [catch {uplevel 1 $script} res opts]
        if {$rc == 0 || $rc == 2 || $rc == 3 || $rc == 4} {
          if {[catch {::sqlp::method $db eval COMMIT} e]} {
            catch {::sqlp::method $db eval ROLLBACK}
            return -code error $e
          }
        } else {
          catch {::sqlp::method $db eval ROLLBACK}
        }
      } else {
        ::sqlp::method $db eval "SAVEPOINT _tcl_transaction"
        set rc [catch {uplevel 1 $script} res opts]
        if {$rc == 0 || $rc == 2 || $rc == 3 || $rc == 4} {
          ::sqlp::method $db eval "RELEASE _tcl_transaction"
        } else {
          catch {::sqlp::method $db eval "ROLLBACK TO _tcl_transaction; RELEASE _tcl_transaction"}
        }
      }
      if {$rc == 1} { return -options $opts $res }
      return $res
    }
    version { return 3.40.1 }
    cache - timeout - busy - config { return "" }
    status { return 0 }
    profile - trace - trace_v2 - progress -
    enable_load_extension - authorizer - commit_hook - rollback_hook - update_hook -
    wal_hook - collation_needed - unlock_notify - preupdate - incrblob - backup - restore -
    serialize - deserialize - interrupt - copy - rekey {
      set ::sqlp::stubs(db:$method) 1
      return -code error "sqlp: \"$method\" is not supported"
    }
    default { return -code error "bad option \"$method\"" }
  }
}

proc sqlite3_get_autocommit {db} {
  return [::sqlp::val [lindex [::sqlp::request $db [list [::sqlp::item autocommit s]]] 1]]
}
proc sqlite3_connection_pointer {db} { return $db }
proc sqlite3_complete {sql} {
  # any open handle can answer; open a scratch one if none is
  foreach h [array names ::sqlp::chan] {
    return [::sqlp::method $h complete $sql]
  }
  return 0
}

# ------------------------------------------------------ testfixture stubs

set sqlite_open_file_count 0
foreach v {sqlite_search_count sqlite_sort_count sqlite_like_count sqlite_current_time
           sqlite_io_error_pending sqlite_io_error_hit sqlite_io_error_hardhit
           sqlite_io_error_persist sqlite_diskfull_pending sqlite_diskfull
           sqlite_max_blobsize sqlite_found_count sqlite_interrupt_count
           sqlite_open_file_count sqlite_sync_count sqlite_fullsync_count} {
  set $v 0
}
proc working_64bit_int {} { return 1 }

# testfixture's [md5 STRING] (test_md5.c), computed by a server
proc md5 {s} {
  if {![info exists ::sqlp::md5chan]} {
    set ::sqlp::md5chan [open "|$::env(SQLP_SERVER)" r+]
    fconfigure $::sqlp::md5chan -translation binary -encoding binary -buffering full
    set ::sqlp::chan(__md5) $::sqlp::md5chan
  }
  set r [::sqlp::request __md5 [list [::sqlp::item md5 s] [::sqlp::item $s s]]]
  return [::sqlp::val [lindex $r 1]]
}

# test_config.c's compile-time constants (the values of SQLite 3.40.1's
# defaults), and the lock page this library uses
foreach {v n} {
  SQLITE_MAX_LENGTH 1000000000  SQLITE_MAX_COLUMN 2000  SQLITE_MAX_SQL_LENGTH 1000000000
  SQLITE_MAX_EXPR_DEPTH 1000  SQLITE_MAX_COMPOUND_SELECT 500  SQLITE_MAX_VDBE_OP 250000000
  SQLITE_MAX_FUNCTION_ARG 127  SQLITE_MAX_VARIABLE_NUMBER 32766  SQLITE_MAX_PAGE_SIZE 65536
  SQLITE_MAX_PAGE_COUNT 1073741823  SQLITE_MAX_LIKE_PATTERN_LENGTH 50000
  SQLITE_MAX_TRIGGER_DEPTH 1000  SQLITE_DEFAULT_CACHE_SIZE -2000  SQLITE_DEFAULT_PAGE_SIZE 4096
  SQLITE_DEFAULT_FILE_FORMAT 4  SQLITE_DEFAULT_SYNCHRONOUS 2  SQLITE_DEFAULT_WAL_SYNCHRONOUS 2
  SQLITE_MAX_ATTACHED 10  SQLITE_MAX_DEFAULT_PAGE_SIZE 8192  SQLITE_MAX_WORKER_THREADS 8
  TEMP_STORE 1  longdouble_size 16  bitmask_size 64  sqlite_pending_byte 1073741824
} { set ::$v $n }
proc sqlite3_memory_used {args} { return 0 }
proc sqlite3_memory_highwater {args} { return 0 }
proc sqlite3_status {args} { return {0 0 0} }
proc sqlite3_db_status {args} { return {0 0 0} }
proc sqlite3_libversion_number {} { return 3040001 }
proc sqlite3_sourceid {} { return "2022-12-28 14:03:47 sqlite-pure" }
proc sqlite3_extended_result_codes {args} { return 0 }
proc vfs_unlink_test {} {}
proc run_thread_tests {args} {}

# Anything else a test calls that testfixture provides in C (test hooks,
# fault injection, VFS shims, memory statistics...): record it and answer
# "".  A test that depends on one is not meaningful here; each file's
# summary lists the stubs it reached.
# tester.tcl's own setup and teardown call these on every run
set ::sqlp::setup {autoinstall_test_functions database_never_corrupt extra_schema_checks
  install_malloc_faultsim sqlite3_config_memstatus sqlite3_hard_heap_limit64
  sqlite3_initialize sqlite3_memdebug_settitle sqlite3_reset_auto_extension
  sqlite3_shutdown sqlite3_soft_heap_limit64 sqlite3_test_control_pending_byte
  unregister_demovfs unregister_devsim unregister_jt_vfs}
rename unknown ::sqlp::tcl_unknown
proc unknown {args} {
  set cmd [lindex $args 0]
  if {[catch {uplevel 1 [list ::sqlp::tcl_unknown {*}$args]} res opts]} {
    # a closed or never-opened database handle stays an error
    if {[string match "invalid command name*" $res] && ![regexp {^:*db[0-9]*$} $cmd]} {
      if {[lsearch -exact $::sqlp::setup $cmd] < 0} { set ::sqlp::stubs($cmd) 1 }
      # testfixture's C commands mostly answer a result code: SQLITE_OK
      return 0
    }
    return -options $opts $res
  }
  return $res
}

# What this build is: SQLite 3.40 with the extensions sqlite-pure has, and
# none of the machinery it does not (no C API test hooks, shared cache,
# loadable extensions, UTF-16 APIs, incremental blob I/O, hooks ...).
array set sqlite_options {}
foreach o {
  altertable analyze attach autoinc autoindex autovacuum between_opt bloblit cast check
  columnmetadata complete compound conflict cte datetime decltype explain floatingpoint
  foreignkey fts3 fts3_unicode fts4_deferred fts5 geopoly hiddencolumns integrityck json1
  like_opt localtime mathlib memorydb or_opt pager_pragmas pragma reindex rtree
  schema_pragmas schema_version secure_delete subquery tempdb trigger truncate_opt
  vacuum view vtab wal windowfunc diskio long_double lfs gettable offset_sql_func
  normalize direct_read default_ckptfullfsync default_autovacuum atomicwrite
} { set sqlite_options($o) 1 }
foreach o {
  8_3_names api_armor auth autoreset builtin_test compileoption_diags crashtest curdir
  cursorhints debug deprecated deserialize dirsync fast_secure_delete fts1 fts2 has_codec
  icu icu_collations incrblob legacyformat like_match_blobs load_ext lookaside
  malloc_usable_size mem3 mem5 memdebug memorymanage mergesort mmap multiplex_ext_overwrite
  mutex mutex_noop null_trim oversize_cell_check pagecache_overflow_stats preupdate
  progress rbu rowid32 rtree_int_only scanstatus session shared_cache snapshot sqllog
  stat4 stmtvtab tclvar threadsafe threadsafe1 threadsafe2 trace unlock_notify
  update_delete_limit uri_00_error userauth utf16 win32malloc worker_threads wsd
  yytrackmaxstackdepth
} { set sqlite_options($o) 0 }

# A capability this list does not name is one this build does not have.
proc ::sqlp::optdefault {name elem op} {
  if {$elem ne "" && ![info exists ::sqlite_options($elem)]} { set ::sqlite_options($elem) 0 }
}
trace add variable ::sqlite_options read ::sqlp::optdefault

# tester.tcl ends the process itself; report the stubs reached first.
rename exit ::sqlp::exit
proc exit {args} {
  set s [lsort [array names ::sqlp::stubs]]
  if {[llength $s]} { puts "STUBS: $s" }
  flush stdout
  ::sqlp::exit {*}$args
}
