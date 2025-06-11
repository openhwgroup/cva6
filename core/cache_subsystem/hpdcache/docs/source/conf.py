#
# Copyright 2024 CEA*
# *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#
# Licensed under the Solderpad Hardware License v 2.1 (the “License”); you
# may not use this file except in compliance with the License, or, at your
# option, the Apache License version 2.0. You may obtain a copy of the
# License at
#
# https://solderpad.org/licenses/SHL-2.1/
#
# Unless required by applicable law or agreed to in writing, any work
# distributed under the License is distributed on an “AS IS” BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
# License for the specific language governing permissions and limitations
# under the License.
#
# Authors       : Cesar Fuguet
# Description   : Configuration file for the Sphinx documentation builder
#

# -- Project information -----------------------------------------------------

project = 'HPDcache User Guide'
copyright = '2023-present Commissariat a l\'Energie Atomique et aux Energies Alternatives (CEA)'
author = 'César Fuguet'

# The full version, including alpha/beta/rc tags
release = 'v1.0.1'


# -- General configuration ---------------------------------------------------

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.
extensions = [
    'sphinx.ext.todo',
    'sphinx.ext.ifconfig',
    'sphinx.ext.graphviz',
    'sphinx.ext.autosectionlabel'
]

# Add any paths that contain templates here, relative to this directory.
templates_path = ['_templates']

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This pattern also affects html_static_path and html_extra_path.
exclude_patterns = []

# Number figures, tables and code-blocks automatically
numfig = True


# -- Options for HTML output -------------------------------------------------

# The theme to use for HTML and HTML Help pages.  See the documentation for
# a list of builtin themes.
#
html_theme = 'sphinx_rtd_theme'

# Add any paths that contain custom static files (such as style sheets) here,
# relative to this directory. They are copied after the builtin static files,
# so a file named "default.css" will overwrite the builtin "default.css".
html_static_path = ['_static']

def setup(app):
   app.add_css_file("theme_overrides.css")
