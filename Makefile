# Minimal makefile for Sphinx documentation
#

# You can set these variables from the command line.
SPHINXOPTS    = # -E -W --keep-going
SPHINXBUILD   = sphinx-build
SPHINXPROJ    = agda-algebras #ualib-docs
SOURCEDIR     = .
BUILDDIR      = _build

# Put it first so that "make" without argument is like "make help".
help:
	@$(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

VENVDIR := .venv
export PATH := $(VENVDIR)/bin:$(PATH)

install-deps:
	#test -f $(VENVDIR)/bin/pip || python3 -m venv $(VENVDIR)
	pip3 install sphinx
	pip3 install sphinxcontrib-bibtex sphinxcontrib-proof sphinxcontrib-tikz
	pip3 install https://bitbucket.org/gebner/pygments-main/get/default.tar.gz#egg=Pygments

.PHONY: help Makefile

# Catch-all target: route all unknown targets to Sphinx using the new
# "make mode" option.  $(O) is meant as a shortcut for $(SPHINXOPTS).
%: Makefile
	@$(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)
