.. FILE      : Base/Homomorphisms.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 03 Jun 2022
.. UPDATED   : 03 Jun 2022
.. COPYRIGHT : (c) 2022 William DeMeo

.. _homomorphism:

Homomorphisms
-------------

This is the `Base.Homomorphisms`_ module of the `Agda Universal Algebra Library`_.

.. toctree::
   :maxdepth: 2

   Homomorphisms/Basic
   Homomorphisms/Properties
   Homomorphisms/Kernels
   Homomorphisms/Products
   Homomorphisms/Noether
   Homomorphisms/Factor
   Homomorphisms/Isomorphisms
   Homomorphisms/HomomorphicImages

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Homomorphisms where

  open import Base.Homomorphisms.Basic              public
  open import Base.Homomorphisms.Properties         public
  open import Base.Homomorphisms.Kernels            public
  open import Base.Homomorphisms.Products           public
  open import Base.Homomorphisms.Noether            public
  open import Base.Homomorphisms.Factor             public
  open import Base.Homomorphisms.Isomorphisms       public
  open import Base.Homomorphisms.HomomorphicImages  public

