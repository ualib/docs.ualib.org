.. FILE      : Base/Categories.lagda.rst
.. AUTHOR    : Jacques Carette and William DeMeo
.. DATE      : 12 Dec 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-categories:

Categories
----------

This is the `Base.Categories`_ module of the `Agda Universal Algebra Library`_.

This module is intended, not to replace or override anything in the
agda-categories_ library, but rather to collect some experiments in the use of
category theory to re-express some of the basic concepts from universal algebra
developed in other modules of the agda-algebras_ library.

The purpose of this effort twofold. First, we hope it makes the types defined in
the agda-algebras_ library more modular and reusable. Second, we hope that the more
general language of category theory will make metaprogramming easier. Somewhat
ironically, one of our main motivations for metaprogramming is to help automate
the task of recognizing when we have multiple alternative definitions (or proofs)
of a single concept (or theorem) in the library and to potentially remove or
consolidate such redundancy.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Categories where

  open import Base.Categories.Functors public


.. toctree::
   :maxdepth: 2

   Categories/Functors

