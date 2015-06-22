# LEM B+tree

A LEM model of B+ trees, based on Sexton and Thielecke

OCaml packages required:

bisect (only for running unit tests recipee of Makefile)




# Instructions for installing via nix

  - Install nix: https://nixos.org/nix/
  - `cd .nix`
  - `nix-shell`
    - this builds isabelle and lem
  - `make`
    - this builds isabelle heap images for HOL and LEM
  - `source build_and_run_isabelle.sh`
    - this builds everything using Lem, then runs an interactive
      isabelle session using previously built heaps
