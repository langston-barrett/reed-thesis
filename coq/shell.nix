{ pkgs ? import ./pinned-pkgs.nix { } }:

let
  # Current HoTT master branch (Sep 2017) pins Coq v8.6. See HoTT/HoTT
  # (48c048123fe82504dfaaa3739bc5e9dbc77a4b03).
  hott = with pkgs; callPackage ./hott.nix { coq = coq_8_6; };
in with pkgs; stdenv.mkDerivation rec {
  name = "thesis";
  src = if lib.inNixShell then null else ./.;

  shellHook = ''
    # Trick Emacs/Proof General into finding the right coqtop binary
    rm -f $PWD/coqtop
    ln -s ${hott}/bin/hoqtop coqtop
    export PATH=$PATH:$PWD

    # export COQPATH=$COQPATH:/result/share/hott
  '';

  # We don't want coq_8_6 in scope while working with hoqtop, hoqc, etc
  # buildInputs = hott.buildInputs;
}
