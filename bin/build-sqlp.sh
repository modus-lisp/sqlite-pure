#!/bin/sh
# Build bin/sqlp.core (used by bin/sqlp) or, with --executable, a standalone
# bin/sqlp-bin that needs nothing but itself.
here=$(cd "$(dirname "$0")/.." && pwd)
exe=nil; out="$here/bin/sqlp.core"
if [ "$1" = "--executable" ]; then exe=t; out="$here/bin/sqlp-bin"; fi
sbcl --noinform --no-userinit --non-interactive \
  --eval '(require :asdf)' \
  --eval "(push #p\"$here/\" asdf:*central-registry*)" \
  --eval '(let ((*error-output* (make-broadcast-stream)) (*standard-output* (make-broadcast-stream))) (asdf:load-system "sqlite-pure/shell"))' \
  --eval "(sb-ext:save-lisp-and-die \"$out\" :toplevel #'sqlite-pure.shell:toplevel :executable $exe :save-runtime-options $exe)"
