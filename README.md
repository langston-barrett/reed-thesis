# Undergraduate Thesis

<!-- [![Build Status](https://travis-ci.org/siddharthist/reed-thesis.svg?branch=master)](https://travis-ci.org/siddharthist/reed-thesis) -->

This repo is mostly for backup right now, it holds my notes and plans for my undergraduate thesis. The topic will hopefully be something in Homotopy Type Theory.

## Directory Structure

 - `archive/` contains things I thought I would need, but didn't.
 - `coq/` contains formalized mathematics
    * `coq/Exercises` contains solutions to exercises in the HoTT book.
 - `exercises/` contains informal solutions to exercises in the HoTT book (scanned from handwritten versions).
 - `notes/` contains LaTeX notes on various subjects at the level of detail I required at the time (no attempt to be comprehensive nor expository has been made).
 - `tex-preamble/` is a collection of LaTeX files that are useful to `\input{}` at the beginning of documents.

## A Note on Continuous Integration

While I would've loved to use Travis CI to check Coq files and compile LaTeX, the time it takes to download and compile _either_ [HoTT/HoTT](https://github.com/HoTT/HoTT) _or_ TeXLive is prohibitive.
