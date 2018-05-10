{ pkgs ? import ./pinned-pkgs.nix { } }:

let
  # https://github.com/NixOS/nixpkgs/pull/37730
  # Copy contents of symlink'd ./tex-preamble to store
  derefPath = { name, src }:
    pkgs.runCommand name {} "cp -aL ${toString src}/ $out/";

  # https://github.com/NixOS/nixpkgs/issues/24485
  fontconfig_file = with pkgs; makeFontsConf {
    fontDirectories = [
      lmodern
      latinmodern-math
      tex-gyre-pagella-math
    ];
  };
  # We include a lot of cached files so the build is faster
  tex_exts = [
    "tex" "cls" "aux" "bbl" "fdb" "fdb_latexmk" "fls" "log" "out"
    "pdf" "run.xml" "synctex.gz" "toc"
  ];
in with pkgs; stdenv.mkDerivation rec {
  name = "thesis";
  version = "0.1.0";

  src =
    if lib.inNixShell
    then null
    else derefPath {
      name = "${name}-src17";
      src  =  ./.;
    };

  FONTCONFIG_FILE = fontconfig_file;

  shellHook = ''
    export FONTCONFIG_FILE="${fontconfig_file}"
    buildPhase
  '';

  installPhase = ''
    mkdir -p "$out"
    for file in *.pdf *.md; do
      echo "Copying ${file}..."
      cp "$file" "$out"
    done
  '';

  buildPhase = ''
    mkdir -p TMP && export TEXMFCACHE=$PWD/TMP

    # TODO: this is a bad way to do this, but works
    cp ${tex-gyre-pagella-math}/share/fonts/opentype/*.otf .
    # cp ${gyre-fonts}/share/fonts/truetype/*.otf .

    # TODO: use latexmk to compile with citations, toc, etc
    lualatex thesis.tex
  '';

  buildInputs = [
    # amsthm_to_anki
    (aspellWithDicts (ps : [ ps.en ])) # spell checking for emacs
    latinmodern-math             # latex math font
    # gyre-fonts                   # TeX Gyre Pagella
    tex-gyre-pagella-math        # latex math font
    (texlive.combine {
      inherit (texlive)
      # Core
      scheme-basic euenc fontspec latexmk luatex lualibs luaotfload # luatex-def
      # General
      booktabs datetime2 environ epigraph esint cleveref enumitem etoolbox
      filehook float hyperref setspace subfiles tex-gyre tracklang trimspaces
      ucharcat xkeyval
      # Math
      amsmath lualatex-math mathtools prftree unicode-math
      # Graphics
      pgf tikz-cd relsize xcolor;
    })

    # Font tools
    fontconfig
  ];
}
