NO_ARGS=$#   # Get the number of arguments passed in the command line

FILE=$1
FILE_DOT=`basename $FILE .ltl`.dot 

INS=`sed -n '1p' $FILE | tr -d '\n'`
OUTS=`sed -n '2p' $FILE | tr -d '\n'`
LTL=`tail -n +3 $FILE | tr -d '\n'`

#echo $INPUT
#echo $OUTPUT
#echo $LTL


strix_options=( -m -k --dot -f "$LTL" --ins "$INS" --outs "$OUTS")
echo "strix ${strix_options[@]}"

if [ "$NO_ARGS" -ge 2 ]; then
  strix "${strix_options[@]}" > $FILE_DOT

  head -n1 $FILE_DOT
  sed  -i '1d' $FILE_DOT
  exit
fi
strix "${strix_options[@]}"

