{ pkgs ? import <nixpkgs> { } }:

# This commit added HoTT to nixpkgs
import (pkgs.fetchFromGitHub {
  owner  = "NixOS";
  repo   = "nixpkgs";
  rev    = "48a49fc12e0b6e28c46fcb0a7c52bac26f8bc05d";
  sha256 = "1vxk0mi0qb6syv6afb04li0bvdgxg60dxi35xq1khcy71d214ch1";
}) { }
