.. FILE      : Setoid/Varieties.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 26 Jul 2021
.. UPDATED   : 18 Jun 2022

.. highlight:: agda
.. role:: code

.. _setoid-equations-and-varieties-for-setoids:

Equations and Varieties for Setoids
-----------------------------------

This is the `Setoid.Varieties`_ module of the `Agda Universal Algebra Library`_.


.. toctree::
   :maxdepth: 2

   Varieties/EquationalLogic
   Varieties/SoundAndComplete
   Varieties/Closure
   Varieties/Properties
   Varieties/Preservation
   Varieties/FreeAlgebras
   Varieties/HSP

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (𝓞 ; 𝓥 ; Signature)

  module Setoid.Varieties {𝑆 : Signature 𝓞 𝓥} where

  open import Setoid.Varieties.EquationalLogic   {𝑆 = 𝑆} public
  open import Setoid.Varieties.SoundAndComplete  {𝑆 = 𝑆} public
  open import Setoid.Varieties.Closure           {𝑆 = 𝑆} public
  open import Setoid.Varieties.Properties        {𝑆 = 𝑆} public
  open import Setoid.Varieties.Preservation      {𝑆 = 𝑆} public
  open import Setoid.Varieties.FreeAlgebras      {𝑆 = 𝑆} public
  open import Setoid.Varieties.HSP               {𝑆 = 𝑆} public
