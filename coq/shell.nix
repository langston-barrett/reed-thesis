{ pkgs ? import ./pinned-pkgs.nix { } }:

with pkgs; stdenv.mkDerivation rec {
  name = "thesis";
  src = if lib.inNixShell then null else ./.;

  shellHook = ''
    # Trick Emacs/Proof General into finding the right coqtop binary
    rm -f $PWD/coqtop
    ln -s ${coqPackages_8_6.HoTT}/bin/hoqtop coqtop
    export PATH=$PWD:$PATH
  '';

  buildInputs = [ coqPackages_8_6.HoTT ];
}
