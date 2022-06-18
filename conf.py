# -*- coding: utf-8 -*-
#
# Configuration file for the Sphinx documentation builder.
#
# This file does only contain a selection of the most common options. For a
# full list see the documentation:
# http://www.sphinx-doc.org/en/master/config

def setup(app):
    app.add_stylesheet('src/_static/custom.css')
    app.add_stylesheet('src/_static/mathconf.js')

# -- Path setup --------------------------------------------------------------

# If extensions (or modules to document with autodoc) are in another directory,
# add these directories to sys.path here. If the directory is relative to the
# documentation root, use os.path.abspath to make it absolute, like shown here.
#
import os
import sys
sys.path.insert(0, os.path.abspath('.'))
sys.path.append(os.path.abspath('src'))
sys.path.append(os.path.abspath('src/_includes'))
sys.path.append(os.path.abspath('src/_static'))

# -- Project information -----------------------------------------------------

project = 'agda-algebras'
copyright = u'''2019–2022 remains with the authors.'''
author = u'the agda-algebras team'

# The short X.Y version
version = '2.1.0'
# The full version, including alpha/beta/rc tags
release = version


# -- General configuration ---------------------------------------------------

# If your documentation needs a minimal Sphinx version, state it here.
#
needs_sphinx = '1.8.3'

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.
extensions = [
    'sphinx.ext.imgmath',
    'sphinx.ext.ifconfig',
    'sphinx.ext.imgconverter',
    'sphinx.ext.mathjax',
    'sphinx.ext.ifconfig',
    'sphinx.ext.viewcode',
    'sphinx.ext.githubpages',
    'sphinxcontrib.bibtex',
    'sphinxcontrib.proof' #, 'sphinxcontrib.tikz'
]

bibtex_bibfiles = ['ualib_refs.bib']

proof_theorem_types = {
    "axiom": "Axiom",
    "conjecture": "Conjecture",
    "corollary": "Corollary",
    "definition": "Definition",
    "example": "Example",
    "examples": "Examples",
    "exercise": "Exercise",
    "lemma": "Lemma",
    "notation": "Notation",
    "observation": "Observation",
    "proof": "Proof",
    "property": "Property",
    "question": "Question",
    "prop": "Proposition",
    "theorem": "Theorem",
    "agda": "Agda Artifact",
    "agda-note": "Agda Note",
}



# use numbering for section references with :numref:, e.g. 'Section 3.2'.
numfig = True

# Add any paths that contain templates here, relative to this directory.
templates_path = ['src/_templates']

# The suffix(es) of source filenames.
# You can specify multiple suffix as a list of string:
#
source_suffix = ['.lagda.rst', '.rst']

# The master toctree document.
master_doc = 'index'

# The language for content autogenerated by Sphinx. Refer to documentation
# for a list of supported languages.
#
# This is also used if you do content translation via gettext catalogs.
# Usually you set "language" from the command line for these cases.
language = None

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This pattern also affects html_static_path and html_extra_path.
exclude_patterns = ['_build', 'agda', 'auto', '.DS_Store', '.venv', '_exclude', 'Thumbs.db', 'links.rst']


# The name of the Pygments (syntax highlighting) style to use.
pygments_style = 'sphinx'
highlight_language = 'Agda'

# If true, `todo` and `todoList` produce output, else they produce nothing.
todo_include_todos = True

# -- Options for HTML output -------------------------------------------------

import sphinx_rtd_theme

# The theme to use for HTML and HTML Help pages.  See the documentation for
# a list of builtin themes.
#
#html_theme = 'alabaster'
html_theme = 'sphinx_rtd_theme'

html_theme_path = [sphinx_rtd_theme.get_html_theme_path()]

# Theme options are theme-specific and customize the look and feel of a theme
# further.  For a list of options available for each theme, see the
# documentation.
#
# html_theme_options = {}
html_theme_options = {
    # 'logo_name': True,
    #'logo_only': False,
    # 'font_family': 'Times New Roman, Times, serif',
    # 'head_font_family': 'Times New Roman, Times, serif',
    # 'code_bg': 'white',

    # navigation options
    # 'collapse_navigation': True,
    # 'sticky_navigation': True,
    'navigation_depth': 3
    # 'extra_nav_links': {
    #     'PDF version (coming soon)': 'document.pdf'
    # },
    # 'prev_next_buttons_location': 'bottom',
    # 'style_nav_header_background': 'white',

    # 'sidebar_width' : '200px',
    # 'page_width' : '960px',
    # 'fixed_sidebar' : True
    # 'analytics_id': 'G-XXXXXXXXXX',  #  Provided by Google in your dashboard
    # 'analytics_anonymize_ip': False,

    # 'display_version': True,
    # 'style_external_links': False,
    # 'vcs_pageview_mode': '',

    # Toc options
    # 'includehidden': True,
    # 'titles_only': False    # , 'donate_url': 'https://www.gofundme.com/formal-foundations-for-informal-mathematics',
}

# Add any paths that contain custom static files (such as style sheets) here,
# relative to this directory. They are copied after the builtin static files,
# so a file named "default.css" will overwrite the builtin "default.css".
html_static_path = ['src/_static']

#html_logo = '_static/lambda.jpg'
html_favicon = 'src/_static/favicon.ico'
html_show_sourcelink = True

#html_output_encoding = 'ascii'
# Custom sidebar templates, must be a dictionary that maps document names
# to template names.
#
# The default sidebars (for documents that don't match any pattern) are
# defined by theme itself.  Builtin themes are using these templates by
# default: ``['localtoc.html', 'relations.html', 'sourcelink.html',
# 'searchbox.html']``.
#
# html_sidebars = {}


# -- Options for HTMLHelp output ---------------------------------------------

# Output file base name for HTML help builder.
htmlhelp_basename = 'ualib-docs'


# -- Options for LaTeX output ------------------------------------------------

latex_engine = 'xelatex'
latex_additional_files = ['unixode.sty', 'bussproofs.sty', 'mylogic.sty', "unicode-symbols-sphinx.tex.txt"]

latex_elements = {

    # The paper size ('letterpaper' or 'a4paper').
    #
    # 'papersize': 'letterpaper',

    # The font size ('10pt', '11pt' or '12pt').
    #
    # 'pointsize': '10pt',

    # Additional stuff for the LaTeX preamble.
    #
    # 'preamble': '',

    'makeindex': '',
    'printindex': '',
    'preamble': r'''
\usepackage{amsmath,mathtools,amssymb}
\usepackage{mathrsfs}
\usepackage{stmaryrd}
\usepackage[cal=boondox]{mathalfa}
\usepackage[titles]{tocloft}
\usepackage{unixode}
\usepackage{bussproofs}
\usepackage{mylogic}
\usepackage{tikz,tikz-cd}
\usetikzlibrary{backgrounds}
'''
    # \definecolor{VerbatimBorderColor}{rgb}{0.7, 0.7, 0.7}
    # \usepackage{tikz, tikz-cd}
    # 'fncychap': r'\usepackage[Bjornstrup]{fncychap}',
    #    'printindex': r'\footnotesize\raggedright\printindex',

    # Latex figure (float) alignment
    #
    # 'figure_align': 'htbp',

    # Latex figure (float) alignment
    #
    # 'figure_align': 'htbp',
}

# Grouping the document tree into LaTeX files. List of tuples
# (source start file, target name, title,
#  author, documentclass [howto, manual, or own class]).
latex_documents = [
    (master_doc, 'agda-algebras.tex', u'Agda Universal Algebra Library',
     u'William DeMeo and Jacques Carette', 'manual'),
]


# -- Options for manual page output ------------------------------------------

# One entry per manual page. List of tuples
# (source start file, name, description, authors, manual section).
man_pages = [(master_doc, 'agda-algebras', u'Agda Universal Algebra Library', [author], 1)]

# -- Options for Texinfo output ----------------------------------------------

# Grouping the document tree into Texinfo files. List of tuples
# (source start file, target name, title, author,
#  dir menu entry, description, category)
texinfo_documents = [
    (master_doc, 'agda-algebras', u'Agda Universal Algebra Library',
     author, 'agda-algebras', 'A library of Agda types and programs (theorems and proofs) for general (universal) algebra.', 'Miscellaneous'),
]


# -- Options for Epub output -------------------------------------------------

# make rst_epilog a variable, so you can add other epilog parts to it
rst_epilog =""
# Read link all targets from file
with open('links.rst') as f:
     rst_epilog += f.read()

# Bibliographic Dublin Core info.
epub_title = """

# The unique identifier of the text. This can be a ISBN number
# or the project homepage.
#
# epub_identifier = ''

# A unique identification for the text.
#
# epub_uid = ''

# A list of files that should not be packed into the epub file.
epub_exclude_files = ['search.html']


# -- Extension configuration -------------------------------------------------


.. raw:: html

    Please email comments, suggestions, and corrections to <a href="mailto:williamdemeo@gmail.com">williamdemeo@gmail.com</a>
"""


