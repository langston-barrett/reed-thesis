{ pkgs ? import <nixpkgs> { } }:

import (pkgs.fetchFromGitHub {
  owner  = "NixOS";
  repo   = "nixpkgs";
  rev    = "17.09-beta";
  sha256 = "1psff8lpp5kmihsg7xv46a0d3rmhsb4kyb9w8r213gn8ggigwg57";
}) { }
