[//]: # (Copyright 2022 Thales Silicon Security)
[//]: # (SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0.)
[//]: # (Original Author: Zbigniew CHAMSKI <zbigniew.chamski@thalesgroup.com>)

# HOWTO use VPTOOL to edit and export DV plans

## Introduction

New features pertaining to Verification Plan exports are currently being developed and tested within the CVA6 ecosystem.  They will be integrated in the `master` branch at a later date.  Hence, the instructions below assume that you are working on the `cva6/dev` branch of the `core-v-verif` repository, or on a branch derived from it.

## Requirements for Markdown output generation

* VPTOOL (included in the `core-v-verif` distribution under `tools/vptool`) with its dependencies installed, as per instructions in file `core-v-verif/tools/vptool/VPTOOL-readme.txt`.
* Python packages related to the processing of markdown files (listed in file `requirements.txt`).
* Verification Plan directories, one per subsystem.

## Installation

### Step 1: Install the required packages

To generate DV plans in the form of viewable HTML/PDF/ePub documents, `VPTOOL` uses the `Sphinx` documentation generator.
Furthermore, to generate PDF and ePub output formats, VPTOOL relies on the `LaTeX` typesetting program with the `latexmk` wrapper add-on.

#### Semi-automated installation

If your system can access a Python package repository (either on the Internet, or local to your site), the Bash shell script `install-prerequisites.sh` will install the necessary Python packages and check for the availability of basic LaTeX-related commands.  Run it with
```
. install-prerequisites.sh
```

If LaTeX distribution or the `latexmk` wrapper is missing, the script will inform your about the steps to follow.  *Please take note that these steps may require superuser privileges.*

#### Manual installation
If your system has access to the internet, you can install the packages using your preferred Python installer.  Under Bash shell, you can do this using PIP and the command

```
  for REQT in `cat requirements.txt` ; do python3 -m pip install $REQT ; done
```

Otherwise, up-to-date versions of the packages listed in file `requirements.txt` and their dependencies need to be installed manually.

### Step 2: Configure per-subsystem databases

Currently, the verification plan for each subsystem is stored in a separate VPTOOL database.  The per-subsystem configuration consists of the following information:

* shell variable `PLATFORM_TOP_DIR` which indicates the root location of the database files. It is recommended to use an absolute path; a good choice is the *effective* location of the database as returned by `dirname $(readlink -f <path_to_vp_config.py>)`.
* shell variable `PROJECT_NAME` which specifies the human-friendly name of the subsystem (a free-form string containing no newline characters).  The value of this variable will serve as the name of the subsystem in the generated documentation.
* shell variable `PROJECT_IDENT` which specifies the file name stem to use in Markdown processing (no path separators, spaces nor special characters allowed).  This string will be used to construct the name of the output Markdown file, and must be unique across all subsystems of a design.
* shell variable `MARKDOWN_OUTPUT_DIR` which designates the directory in which to place the generated per-subsystem Markdown files.  The Markdown rendering tools that produce human-friendly output (e.g. HTML) for CVA6 Verification Plans are configured to take Markdown input from directory `core-v-verif/cva6/docs/VerifPlans/source`.  It is recommended to use an absolute path; a good choice is the *effective* location of the database (`readlink -f $PLATFORM_TOP_DIR`) suffixed with the *relative* path to `source` as this avoids hardcoded absolute paths.)

To ensure consistent configurations between consecutive runs of VPTOOL on a given database, it is recommended to set these variables within a shell script (see `core-v-verif/cva6/docs/VerifPlans/FRONTEND/runme.sh` for an example.)

Typically, creating a new database could be as simple as:

* Create a directory for a new per-subsystem DV plan, say `cva6/docs/VerifPlans/NEW_ARCH_VARIANT/NEW_SUBSYSTEM`.
* Copy existing `vp_config.py` and `runme.sh` files from an existing per-subsystem Verification Plan directory to the newly created directory.
* Edit the `runme.sh` in the new directory to adjust the vaue of variable `PROJECT_NAME`, `PROJECT_IDENT` and `MARKDOWN_OUTPUT_DIR`.
* Using the adjusted `runme.sh` script, launch VPTOOL to interactively create the new database:
  ```
  . cva6/docs/VerifPlans/NEW_ARCH_VARIANT/NEW_SUBSYSTEM/runme.sh
  ```

### Step 3: Provide initial content of the database(s)

In VPTOOL, modify the Verification Plan database of the new subsystem as appropriate.

## Generation of DV plan documents

### Step 1: Export database content to Markdown document(s)

Currently, the generation of Markdown output is directly coupled to the action of saving database content of a project.  When saving a database, VPTOOL will also create a Markdown file containing a human readable version of the DV plan in file `dvplan_${PROJECT_IDENT}.md` in directory designated by the shell variable `MARKDOWN_OUTPUT_DIR` set in the `runme.sh` script of the given subsystem.

After editing the databases for projects `FRONTEND` and `NEW_ARCH_VARIANT/NEW_SUBSYSTEM` the directory layout will thus be:

* `cva6/docs/VerifPlans`
  * `FRONTEND`
    * `runme.sh` : wrapper script
    * `vp_config.py` : database configuration file for subsystem `FRONTEND`
    * `VP_IPnnn.pck` : Verification Plan database files for subsystem `FRONTEND`
    * ...
  * `NEW_ARCH_VARIANT`
    * `NEW_SUBSYSTEM` 
      * `runme.sh` : wrapper script for `NEW_SUBSYSTEM` (Let's assume that it sets `PROJECT_NAME="New Subsystem"` and `PROJECT_IDENT="NEW_SUBSYS"`.)
      * `vp_config.py` : database configuration file for `NEW_SUBSYSTEM`
      * `VP_IPnnn.pck` : files of the Verification Plan database for `NEW_SUBSYSTEM`
    * ...
  * `source`
    * `conf.py` : configuration file for document generator
    * `dvplan_FRONTEND.md` : Markdown version of verification plan for  that `PROJECT_IDENT` for 
    * `dvplan_NEW_SUBSYS.md` : Markdown version of `NEW_SUBSYSTEM` verification plan (since the wrapper script set `PROJECT_IDENT` to `"NEW_SUBSYS"`.)
    * `dvplan_intro.rst` : Markdown version of the introduction to the overall verification plan
    * `dvplan_index.rst` : Markdown version of the overall verification plan document.

### Step 2: Generate final DV plan documents

In order to include the newly generated `NEW_SUBSYSTEM` verification plan into the overall DV Plan document, the file `source/dvplan_index.rst` needs to be modified so that it includes `dvplan_NEW_SUBSYS.md`.  This is achieved by simply adding the name of the new DV plan Markdown document (without the `.md` extension) at the appropriate location in the document structure, e.g. after the line containing 'dvplan_FRONTEND`.

Once the index file has been adjusted, the final document can generated in a variety of formats by invoking `make` in the directory `core-v-verif/cva6/docs/VerifPlans` with the desired output format as argument.  The list of formats supported by your local Sphinx installation can be obtained by invoking `make` without arguments:

```
me@ariane:cva6/docs/VerifPlans$ make
Sphinx v1.8.4
Please use `make target' where target is one of
  html        to make standalone HTML files
  dirhtml     to make HTML files named index.html in directories
  singlehtml  to make a single large HTML file
  pickle      to make pickle files
  json        to make JSON files
  htmlhelp    to make HTML files and an HTML help project
  qthelp      to make HTML files and a qthelp project
  devhelp     to make HTML files and a Devhelp project
  epub        to make an epub
  latex       to make LaTeX files, you can set PAPER=a4 or PAPER=letter
  latexpdf    to make LaTeX and PDF files (default pdflatex)
  latexpdfja  to make LaTeX files and run them through platex/dvipdfmx
  text        to make text files
  man         to make manual pages
  texinfo     to make Texinfo files
  info        to make Texinfo files and run them through makeinfo
  gettext     to make PO message catalogs
  changes     to make an overview of all changed/added/deprecated items
  xml         to make Docutils-native XML files
  pseudoxml   to make pseudoxml-XML files for display purposes
  linkcheck   to check all external links for integrity
  doctest     to run all doctests embedded in the documentation (if enabled)
  coverage    to run coverage check of the documentation (if enabled)
me@ariane:cva6/docs/VerifPlans$
```

The recommended target during the development of the verification plans is `singlehtml` as it offers the shortest turnaround time and interactive output with good readability.  Also, some of the other formatting targets may depend on the availability of additional tools that may or may not be installed (or even installable) on your system.

```
me@ariane:cva6/docs/VerifPlans$ make singlehtml
Running Sphinx v1.8.4
loading translations [en]... done
loading pickled environment... done
building [mo]: targets for 0 po files that are out of date
building [singlehtml]: all documents
updating environment: 0 added, 0 changed, 0 removed
looking for now-outdated files... none found
preparing documents... done
assembling single document... dvplan_intro dvplan_FRONTEND dvplan_NEW_SUBSYS
writing... done
writing additional files...
copying static files... done
copying extra files... done
dumping object inventory... done
build succeeded.

The HTML page is in build/singlehtml.
me@ariane:cva6/docs/VerifPlans$
```

The resulting document can be viewed by pointing your browser at the file `core-v-verif/cva6/docs/VerifPlans/build/singlehtml/index.html`.
