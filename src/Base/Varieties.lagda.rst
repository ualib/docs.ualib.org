.. FILE      : Base/Varieties.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 03 Jun 2022
.. UPDATED   : 03 Jun 2022
.. COPYRIGHT : (c) 2022 William DeMeo

.. _varieties:

Varieties
---------

This is the `Base.Varieties`_ module of the `Agda Universal Algebra Library`_,
where we define types for theories and their models, and for equational logic,
and we prove properties of these types.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Varieties where

  open import Base.Varieties.EquationalLogic
  open import Base.Varieties.Closure
  open import Base.Varieties.Properties
  open import Base.Varieties.Preservation
  open import Base.Varieties.FreeAlgebras

.. toctree::
   :maxdepth: 2

   Varieties/EquationalLogic
   Varieties/Closure
   Varieties/Properties
   Varieties/Preservation
   Varieties/FreeAlgebras
