.. FILE      : Base/Structures.lagda.rst
.. DATE      : 26 Jul 2021
.. UPDATED   : 04 Jun 2022
.. COPYRIGHT : (c) 2022 Jacques Carette and William DeMeo

.. _structures:

Structures
----------

This is the `Base.Structures`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Structures where

  open import Base.Structures.Basic            public
  open import Base.Structures.Products         public
  open import Base.Structures.Congruences      public
  open import Base.Structures.Homs             public
  open import Base.Structures.Graphs           public
  open import Base.Structures.Graphs0          public
  open import Base.Structures.Isos             public
  open import Base.Structures.Terms            public
  open import Base.Structures.Substructures    public
  open import Base.Structures.EquationalLogic  public
  open import Base.Structures.Sigma            public

.. toctree::
   :maxdepth: 2

   Structures/Basic
   Structures/Graphs
   Structures/Graphs0
   Structures/Products
   Structures/Congruences
   Structures/Homs
   Structures/Isos
   Structures/Terms
   Structures/Substructures
   Structures/EquationalLogic
   Structures/Sigma


