# Tell latexmk to just use nix to build the PDF

$pdf_mode = 1;

@default_files = ("*.tex");

$pdflatex = 'nix-shell . --pure --run "lualatex --halt-on-error %O %B"';

$clean_ext = 'aux bbl dvi fdb fdb_latexmk fls log out run.xml synctex.gz toc -blx.bib';