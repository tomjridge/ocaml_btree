{ }:
let 
    pkgs = import <nixpkgs> {};
    stdenv = pkgs.stdenv;
    fetchgit = pkgs.fetchgit;
    isabelle = import ./isabelle { };
    lem = import ./lem { };
in stdenv.mkDerivation {
    name = "lemenv";
  
    src = fetchgit {
      url = https://github.com/tomjridge/p3.git;
      rev = "0f6c732";
      sha256 = "5ea4a2486876b2bd382dcdada57593233ac6b1e681539e72d5e144e630aaf1ff";
    };
#    src = ./.;  
    buildInputs = [ isabelle lem ]; 
  
    configurePhase = "true"; 	# Skip configure
    
    buildPhase = ''
      echo lemenv! execute the following using buildPhase() from nix-shell
      cd ${lem}/lem
      isabelle build -d isabelle-lib -b LEM
      '';
  
    installPhase = "false"; # don't want to install

}
