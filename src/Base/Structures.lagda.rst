.. FILE      : Base/Structures.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 26 Jul 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-structures:

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
  open import Base.Structures.Graphs0
  open import Base.Structures.Isos             public
  open import Base.Structures.Terms            public
  open import Base.Structures.Substructures    public
  open import Base.Structures.EquationalLogic  public

.. toctree::
   :maxdepth: 2

   Structures/Basic
   Structures/Products
   Structures/Congruences
   Structures/Homs
   Structures/Graphs
   Structures/Graphs0
   Structures/Isos
   Structures/Terms
   Structures/Substructures
   Structures/EquationalLogic


