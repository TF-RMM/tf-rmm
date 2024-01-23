# -*- coding: utf-8 -*-
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#
# Configuration file for the Sphinx documentation builder.
#
# See the options documentation at http://www.sphinx-doc.org/en/master/config

import os
import re
from subprocess import check_output

# -- Project information -----------------------------------------------------

project = 'Realm Management Monitor'
copyright = 'TF-RMM Contributors'
author = 'TF-RMM Contributors'
title = 'User Guide'

try:
  vregx = re.compile(r'tf-rmm-(?P<RMM_VERSION>v.+?)'
                     r'(-[0-9]+-)?(?P<GIT_SHA>g[a-f0-9]{7,})?$')
  git_result = check_output("git describe --tags --always",
                            shell = True, encoding = 'UTF-8')
  _v = vregx.match(git_result)
  version = _v.group('RMM_VERSION')
  if _v.group('GIT_SHA'):
    version += "+" + _v.group('GIT_SHA')[:7]
except:
  version = 'Unknown'

# -- General configuration ---------------------------------------------------

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.
extensions = ['sphinx.ext.autosectionlabel']

# Add any paths that contain templates here, relative to this directory.
templates_path = ['_templates']

# The suffix(es) of source filenames.
source_suffix = ['.rst']

# The master toctree document.
master_doc = 'index'

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This pattern also affects html_static_path and html_extra_path .
exclude_patterns = []

# The name of the Pygments (syntax highlighting) style to use.
pygments_style = 'sphinx'

# Load the contents of the global substitutions file into the 'rst_prolog'
# variable. This ensures that the substitutions are all inserted into each page.
with open('global_substitutions.txt', 'r') as subs:
  rst_prolog = subs.read()

# Minimum version of sphinx required
needs_sphinx = '5.3.0'

# -- Options for HTML output -------------------------------------------------

# Don't show the "Built with Sphinx" footer
html_show_sphinx = False

# Show copyright info in the footer
html_show_copyright = True

# The theme to use for HTML and HTML Help pages.  See the documentation for
# a list of builtin themes.
html_theme = "sphinx_rtd_theme"

# The logo to display in the sidebar
html_logo = '_static/images/TrustedFirmware-Logo_standard-white.png'

# Options for the "sphinx-rtd-theme" theme
html_theme_options = {
    'collapse_navigation': False, # Can expand and collapse sidebar entries
    'prev_next_buttons_location': 'both', # Top and bottom of the page
    'style_external_links': True # Display an icon next to external links
}

# Path to _static directory
html_static_path = ['_static']

# Path to css file relative to html_static_path
html_css_files = ['css/rmm_custom.css',]

# -- Options for autosectionlabel --------------------------------------------

# Only generate automatic section labels for document titles
autosectionlabel_maxdepth = 1

# -- Options for plantuml ----------------------------------------------------

plantuml_output_format = 'svg_img'
