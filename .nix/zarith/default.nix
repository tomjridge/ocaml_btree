{ }:
let
    pkgs = import <nixpkgs> {};
    stdenv = pkgs.stdenv;
    fetchurl = pkgs.fetchurl;
    perl = pkgs.perl;
    ocaml = pkgs.ocaml_4_02_1;
    findlib = pkgs.ocamlPackages_4_02_1.findlib;
    gmp = pkgs.gmp;
in stdenv.mkDerivation {
    name = "ocaml_zarith";

    src = fetchurl {
      url = https://forge.ocamlcore.org/frs/download.php/1471/zarith-1.3.tgz;
      sha256 = "946687d6f032b96ab9db9661d876e39437bff783e0ad473ac463c06259b7a3d7";
    };

    buildInputs = [ ocaml findlib pkgs.which perl gmp];
    dontAddPrefix = true;
    createFindlibDestdir = true;


}
