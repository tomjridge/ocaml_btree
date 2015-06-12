{ }:
let 
    pkgs = import <nixpkgs> {};
    stdenv = pkgs.stdenv;
    fetchgit = pkgs.fetchgit;
    ocaml = pkgs.ocaml_4_02_1;
    git = pkgs.git;
    findlib = pkgs.ocamlPackages_4_02_1.findlib;
in stdenv.mkDerivation {
    name = "lem";
  
    src = fetchgit {
      url = https://bitbucket.org/Peter_Sewell/lem.git;
      rev = "d3326d5"; # a commit which builds on 2015-06-12
      sha256 = "3dbec35806b5e4d81a9f00f3876bc230d70cea8c8cda7d85e91b296e148d8d26";
    };
  
    buildInputs = [ ocaml findlib git pkgs.pkgconfig pkgs.perl pkgs.ocamlPackages_4_02_1.zarith pkgs.gmp]; # note that lem tries to build zarith as well
  
    configurePhase = "true"; 	# Skip configure
    
    buildPhase = ''
      export LD_LIBRARY_PATH=`pwd`/ocaml-lib/dependencies/zarith:$LD_LIBRARY_PATH  # complete hack - need to find dllzarith.so
      echo 'let v="d3326d5"' >src/version.ml  # complete hack - the source code isn't a git repo after fetchgit
      echo "!!!"
      make

      echo "!!!"
      make ocaml-libs
      '';
  
    installPhase = "mkdir -p $out/lem && cp -R -L * $out/lem"; # so we can inspect the result
    # note that we need to export LEM_LIBRARY_PATH=<absolute path to lem directory>/library before invoking lem

    createFindlibDestdir = true;

}
