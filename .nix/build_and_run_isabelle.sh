cd ../src
make clean
make
cd isabelle
isabelle jedit -d $lem/lem/isabelle-lib -l LEM tr/Abstract_tree.thy
# note that this will pull Lem theory files from the LEM heap,
# regardless of their paths in the .thy files
#
# in docker, this may fail with Exception in thread "main" java.lang.NoClassDefFoundError: Could not initialize class java.awt.Toolkit
# (even though xeyes works); this seems related to http://stackoverflow.com/questions/18099614/java-lang-noclassdeffounderror-could-not-initialize-class-java-awt-toolkit, 

# trying in docker:
# sudo dpkg --add-architecture i386
# sudo apt-get update
# sudo apt-get install libxtst-dev:i386
# (doesn't work)
