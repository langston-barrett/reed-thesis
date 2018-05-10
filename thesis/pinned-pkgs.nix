{ pkgs ? import <nixpkgs> { } }:

import (pkgs.fetchFromGitHub {
  owner    = "NixOS";
  repo     = "nixpkgs";
  rev      = "18.03-beta";
  sha256   = "00gd96p7yz3rgpjjkizp397y2syfc272yvwxqixbjd1qdshbizmj";
}) { }
