.. FILE      : Setoid/Algebras.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 12 Dec 2021
.. UPDATED   : 09 Jun 2022
.. COPYRIGHT : (c) 2022 Jacques Carette, William DeMeo

.. highlight:: agda
.. role:: code

.. _setoid-representation-of-algebras:

Setoid Representation of Algebras
---------------------------------

.. toctree::
   :maxdepth: 2

   Setoid/Algebras/Basic
   Setoid/Algebras/Products
   Setoid/Algebras/Congruences

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Base.Algebras.Basic using (𝓞 ; 𝓥 ; Signature)

  module Setoid.Algebras {𝑆 : Signature 𝓞 𝓥} where

  open import Setoid.Algebras.Basic        {𝑆  = 𝑆} public
  open import Setoid.Algebras.Products     {𝑆  = 𝑆} public
  open import Setoid.Algebras.Congruences  {𝑆  = 𝑆} public

