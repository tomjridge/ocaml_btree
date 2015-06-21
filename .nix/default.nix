{ }:
let 
    pkgs = import <nixpkgs> {};
    stdenv = pkgs.stdenv;
    fetchgit = pkgs.fetchgit;
    perl = pkgs.perl;
    isabelle = import ./isabelle { };
    lem = import ./lem { };
in stdenv.mkDerivation {
    name = "lemenv";

    lem = lem;
    isabelle = isabelle;
  
    src = lem;  
    buildInputs = [ perl isabelle lem ]; 
  
    configurePhase = "true"; 	# Skip configure
    
    # curPhase=buildPhase
    # export out=/tmp
    # eval "${!curPhase:-$curPhase}"
    buildPhase = ''
      echo lemenv execute the following using buildPhase from nix-shell
      cd ${lem}/lem
      echo pwd is $PWD
      export USER_HOME=$out
      echo USER_HOME: $USER_HOME
      isabelle build -d isabelle-lib -b LEM
      '';
  
    installPhase = "true"; # don't want to install


shellHook = ''
    export LEMPATH=${lem}/lem
    export PATH=$PATH:${lem}/lem
    export LEMLIB=${lem}/lem/library
    #export ISABELLE_LOGIC=LEM
    curPhase=buildPhase
    export out=/tmp/isa
    
  '';
    #eval "${!curPhase:-$curPhase}"

}
