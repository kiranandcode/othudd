# generates _CoqProject

if [ -f "./_CoqProject" ]; then
    rm ./_CoqProject
fi

touch _CoqProject

# add all folders of coqproject 
echo '-Q lib Lib' >> _CoqProject

# add individual files
ls **/*.v | cat >> _CoqProject
