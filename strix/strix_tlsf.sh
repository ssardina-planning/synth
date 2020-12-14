#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
NO_ARGS=$#   # Get the number of arguments passed in the command line


FILE_TLSF=$1
FILE_DOT="`basename $FILE_TLSF .tlsf`.dot" 


LTL=$(syfco -f ltl -q double -m fully $FILE_TLSF)
INS=$(syfco -f ltl --print-input-signals $FILE_TLSF)
OUTS=$(syfco -f ltl --print-output-signals $FILE_TLSF)

strix_options=( -m -k --dot -f "$LTL" --ins "$INS" --outs "$OUTS")
#strix_options=( -k --dot -f "$LTL" --ins "$INS" --outs "$OUTS")
echo "strix ${strix_options[@]}"

if [ "$NO_ARGS" -ge 2 ]; then
  strix "${strix_options[@]}" > $FILE_DOT

  head -n1 $FILE_DOT
  sed  -i '1d' $FILE_DOT
  exit
fi
strix "${strix_options[@]}"



