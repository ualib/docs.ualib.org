.. FILE      : Setoid/Homomorphisms.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 17 Sep 2021
.. UPDATED   : 09 Jun 2022
.. COPYRIGHT : (c) 2022 Jacques Carette, William DeMeo

.. highlight:: agda
.. role:: code

.. _homomorphism-of-setoid-algebras:

Homomorphism of Setoid Algebras
-------------------------------

This is the `Setoid.Homomorphisms`_ module of the `Agda Universal Algebra Library`_.

.. toctree::
   :maxdepth: 2

   Setoid/Homomorphisms/Basic
   Setoid/Homomorphisms/Properties
   Setoid/Homomorphisms/Kernels
   Setoid/Homomorphisms/Products
   Setoid/Homomorphisms/Noether
   Setoid/Homomorphisms/Factor
   Setoid/Homomorphisms/Isomorphisms
   Setoid/Homomorphisms/HomomorphicImages


::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Setoid.Homomorphisms where

  open import Setoid.Homomorphisms.Basic              public
  open import Setoid.Homomorphisms.Properties         public
  open import Setoid.Homomorphisms.Kernels            public
  open import Setoid.Homomorphisms.Products           public
  open import Setoid.Homomorphisms.Noether            public
  open import Setoid.Homomorphisms.Factor             public
  open import Setoid.Homomorphisms.Isomorphisms       public
  open import Setoid.Homomorphisms.HomomorphicImages  public
