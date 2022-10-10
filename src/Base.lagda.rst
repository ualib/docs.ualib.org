.. FILE      : Base.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 12 Dec 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-basic-types-for-general-algebra:

Basic Types for General Algebra
===============================

This module collects all submodules of the agda-algebras_ library that use "bare" types (cf. the Setoid_ module which collects analogous submodules based on Setoids).

.. toctree::
   :maxdepth: 2

   Base/Relations
   Base/Functions
   Base/Equality
   Base/Adjunction
   Base/Algebras
   Base/Homomorphisms
   Base/Terms
   Base/Subalgebras
   Base/Varieties
   Base/Structures
   Base/Categories
   Base/Complexity

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base where

  open import Base.Relations
  open import Base.Functions
  open import Base.Equality
  open import Base.Adjunction
  open import Base.Algebras
  open import Base.Homomorphisms
  open import Base.Terms
  open import Base.Subalgebras
  open import Base.Varieties
  open import Base.Structures
  open import Base.Categories
  open import Base.Complexity






