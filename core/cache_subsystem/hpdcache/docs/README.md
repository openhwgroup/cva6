# Build instructions

The documents in this directory are written in reStructuredText and compiled to HTML using Sphinx. For more information, check https://www.sphinx-doc.org/en/master/usage/restructuredtext/index.html.

## Prerequisites

This section outlines the necessary steps to build the document on Linux (tested on Debian-based distributions).

Sphinx is based on Python and requires at least version 3.8. Additionally, `make` is required and can be installed through build-essential.

```bash
sudo apt update
sudo apt install python3
sudo apt install build-essential
```

Please verify your Python version using

```bash
python3 --version
```

Sphinx requires certain packages to build these documents. These are listed in `requirements.txt`. They can be installed using

```bash
pip install -r requirements.txt
```

## Building the documents

Build is invoked via the `make` command. Typically, an HTML should be build.

```bash
make html
```

A secondary build target is pdf. To build the pdf, additional prerequisites need to be met. To install `pdflatex`, run

```bash
sudo apt-get install texlive-latex-base
```

A pdf document can be built using the command

```bash
make latexpdf
```

Simply type `make` to view other available targets.
