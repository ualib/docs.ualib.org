.. FILE    : index.lagda.rst
.. AUTHOR  : "William DeMeo <williamdemeo@gmail.com>"
.. DATE    : 18 Jun 2022
.. LICENSE : See the LICENSE file at https://github.com/ualib/agda-algebras/raw/master/LICENSE

.. agda-algebras documentation master file, created by
   sphinx-quickstart on Mon May 23 14:31:03 2022.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

..
   LICENSE:

   The software in this file is subject to the GNU General Public License v3.0.

   The `LICENSE file <https://github.com/ualib/agda-algebras/raw/master/LICENSE>`__
   is available in the repository at
   `github.com/ualib/agda-algebras <https://github.com/ualib/agda-algebras/blob/master/LICENSE>`__.

   The text other than software is copyright of the author. It can be
   used for scholarly purposes subject to the usual academic conventions
   of citation.

   * The *.lagda files are not meant to be read by people, but rather to be
     type-checked by the Agda proof assistant and to automatically generate html files
     (which are meant to be read by people).

   * This is done with the generate-html file to generate markdown and html files from the
     literate Agda (.lagda) files, and then using jekyll to convert markdown into html.

..
   .. image:: lambda.jpg
     :width: 400
     :alt: The official agda-algebras logo


The Agda Universal Algebra Library
==================================

(Version 2.04 of |today|)

.. {{ "now" \| date: "%d %b %Y" }})

Abstract
--------

The `Agda Universal Algebra Library`_ is a collection of
types and programs (theorems and proofs) that formalizes the foundations
of universal algebra in dependent type theory using the Agda_ proof
assistant language.

The library contains definitions of many new types for representing
important constructs and theorems comprising a substantial part of the
foundations of general (universal) algebra and equational logic. These
types are implemented in so called “literate” Agda files (with the
``.lagda`` extension), and they are grouped into modules which can be
easily imported and integrated into other Agda developments.

To get an idea of the current scope of the library, note that it now
includes a formal proof of Birkhoff’s `HSP
Theorem <https://en.wikipedia.org/wiki/Variety_(universal_algebra)#Birkhoff's_theorem>`__,
which asserts that every *variety* is an *equational class*. That is, if
𝒦 is a class of algebras which is closed under the taking of homomorphic
images, subalgebras, and arbitrary products, then 𝒦 is the class of all
algebras satisfying some set of identities. To our knowledge, ours is
the first formal, machine-checked proof of Birkhoff’s Theorem. (If you
have evidence refuting this claim, we would love to hear about it;
please `email us <mailto:williamdemeo@gmail.com>`__!)

We hope the library is useful to mathematicians and computer scientists
who wish to formalize their work in dependent type theory and verify
their results with a proof assistant. Indeed, the agda-algebras_
library aims to become an indispensable companion on our mathematical
journeys, helping us authenticate the discoveries we make along the way.

**Keywords and phrases**. Universal algebra, Equational logic,
Martin-Löf Type Theory, Birkhoff’s HSP Theorem, Formalization of
mathematics, Agda

**Software Repository**.
`github.com/ualib/agda-algebras <https://github.com/ualib/agda-algebras>`__

**Citing this work**. See the instructions at
`agda-algebras/Preface.html <https://ualib.github.io/agda-algebras/Preface.html#citing-the-agda-algebras-library>`__.

**Primary Contributors**. `William DeMeo <https://williamdemeo.gitlab.io>`__ and
`Jacques Carette <http://www.cas.mcmaster.ca/~carette/>`__

.. _organization:

Organization
------------

We have organized the library into a number of modules, called
Overture_, Base_, Setoid_, Demos_, and Examples_, which are imported
below. The modules Base_ and Setoid_ are essentially independent. The
Base_ module contains submodules that comprise the first
version of the library. The Setoid_ contains an alternative version of
the library based on setoids.

The `Demos.HSP`_ module presents a fairly self-contained formal proof
of Birkhoff's HSP Theorem in a single module. In contrast, an alternative version of the proof
is contained in the `Setoid.Varieties.HSP`_ module.  Instead of duplicating everything
needed to be self-contained (as in done in `Demos.HSP`_), the proof in `Setoid.Varieties.HSP`_
imports what it needs from other parts of the agda-algebras_ library.

.. toctree::
   :maxdepth: 2

   Overture
   Base
   Setoid
   Demos
   Examples


::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module index where

  open import Overture  -- preliminaries
  open import Base      -- version 1 of the library (based on standard dependent types)
  open import Setoid    -- version 2 of the library (based on setoids)
  open import Demos     -- demonstrations (e.g., proof of the HSP Theorem in a single module)
  open import Examples



References
==========

.. bibliography:: src/_includes/ualib_refs.bib

Indices
=======

* :ref:`genindex`
* :ref:`search`


License
========

The agda-algebras_ library and its documentation, by William DeMeo and
the agda algebras team, is licensed under a Creative Commons
Attribution-ShareAlike 4.0 International License. BibTeX citation
information. Based on the work at
https://gitlab.com/ualib/ualib.gitlab.io.

..
   Indices and tables
   ==================
   * :ref:`genindex`
   * :ref:`modindex`
   * :ref:`search`

..
   appendix_prerequisites.rst
   misc_notes.lagda.rst
   alternatives.lagda.rst
   acronyms_and_symbols.rst
   glossary
   genindex

