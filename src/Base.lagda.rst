.. FILE      : Base.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 12 Dec 2021
.. UPDATED   : 02 Jun 2022
.. COPYRIGHT : (c) 2022 Jacques Carette, William DeMeo, and the agda-algebras team

.. highlight:: agda
.. role:: code

.. _basic-types-for-general-algebra:

Basic Types for General Algebra
===============================

This module collects all submodules of the agda-algebras_ library that use "bare" types (cf. the Setoid_ module which collects analogous submodules based on Setoids).

.. toctree::
   :maxdepth: 2

   Base/Overture
   Base/Equality
   Base/Relations
   Base/Algebras
   Base/Homomorphisms
   Base/Terms
   Base/Subalgebras
   Base/Varieties
   Base/Structures
   Base/Adjunction
   Base/Categories
   Base/Complexity

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base where

  open import Base.Overture
  open import Base.Relations
  open import Base.Algebras
  open import Base.Equality
  open import Base.Homomorphisms
  open import Base.Terms
  open import Base.Subalgebras
  open import Base.Varieties
  open import Base.Structures
  open import Base.Adjunction
  open import Base.Categories
  open import Base.Complexity






