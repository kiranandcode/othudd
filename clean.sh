# remove generated ml files
rm $(ls lib/*.v | sed 's/\(.*\)\.v/\1.ml/') > /dev/null 2>&1

# remove generated mli files
rm $(ls lib/*.v | sed 's/\(.*\)\.v/\1.mli/') > /dev/null 2>&1

exit 0
