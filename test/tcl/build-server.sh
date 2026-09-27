#!/bin/sh
# Save a core running test/tcl/server.lisp's MAIN; prints its path.
here=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
core=${TMPDIR:-/tmp}/sqlite-pure-tclserver.core
sbcl --noinform --no-userinit --non-interactive \
  --eval '(require :sb-posix)' --eval '(require :sb-md5)' --eval '(require :asdf)' \
  --eval "(push #p\"$here/\" asdf:*central-registry*)" \
  --eval '(let ((*error-output* (make-broadcast-stream)) (*standard-output* (make-broadcast-stream))) (asdf:load-system "sqlite-pure/shell"))' \
  --eval "(let ((*error-output* (make-broadcast-stream))) (load (compile-file \"$here/test/tcl/server.lisp\" :output-file \"${TMPDIR:-/tmp}/sqlite-pure-tclserver.fasl\")))" \
  --eval "(sb-ext:save-lisp-and-die \"$core\" :toplevel #'sqlite-pure.tclserver:main)" >/dev/null 2>&1
echo "$core"
