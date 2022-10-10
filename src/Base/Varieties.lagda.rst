.. FILE      : Base/Varieties.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 14 Jan 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-varieties:

Varieties
---------

This is the `Base.Varieties`_ module of the `Agda Universal Algebra Library`_,
where we define types for theories and their models, and for equational logic,
and we prove properties of these types.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using ( Signature ; 𝓞 ; 𝓥 )

  module Base.Varieties {𝑆 : Signature 𝓞 𝓥} where

  open import Base.Varieties.EquationalLogic  {𝑆 = 𝑆} public
  open import Base.Varieties.Closure          {𝑆 = 𝑆} public
  open import Base.Varieties.Properties       {𝑆 = 𝑆} public
  open import Base.Varieties.Preservation     {𝑆 = 𝑆} public

  open import Level using ( Level )

  module _ {α : Level} where

   open import Base.Varieties.FreeAlgebras  {α = α} {𝑆 = 𝑆} public

.. toctree::
   :maxdepth: 2

   Varieties/EquationalLogic
   Varieties/Closure
   Varieties/Properties
   Varieties/Preservation
   Varieties/FreeAlgebras

