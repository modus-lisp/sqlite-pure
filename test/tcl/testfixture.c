/* test/tcl/testfixture.c — tclsh that sources $SQLP_SHIM (test/tcl/sqlite3.tcl)
** at startup, standing in for SQLite's testfixture: test scripts that start
** another testfixture with [info nameofexecutable] get the same [sqlite3]. */
#include <stdlib.h>
#include <tcl.h>

static int AppInit(Tcl_Interp *interp){
  const char *shim;
  if( Tcl_Init(interp)==TCL_ERROR ) return TCL_ERROR;
  shim = getenv("SQLP_SHIM");
  if( shim && Tcl_EvalFile(interp, shim)!=TCL_OK ) return TCL_ERROR;
  return TCL_OK;
}

int main(int argc, char **argv){
  Tcl_Main(argc, argv, AppInit);
  return 0;
}
