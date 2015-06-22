cd ../src
make clean
make
cd isabelle
isabelle jedit -d $lem/lem/isabelle-lib -l LEM BtreeLemmas.thy
# note that this will pull Lem theory files from the LEM heap,
# regardless of their paths in the .thy files
