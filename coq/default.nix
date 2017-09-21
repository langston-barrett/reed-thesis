{ pkgs ? import ./pinned-pkgs.nix { } }:

# TODO: build my files :)

pkgs.callPackage ./hott.nix { coq = pkgs.coq_8_6; }
