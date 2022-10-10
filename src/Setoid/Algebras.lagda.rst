.. FILE     : Setoid/Algebras.lagda.rst
.. AUTHOR   : William DeMeo
.. DATE     : 17 Spe 2021
.. UPDATED  : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _setoid-setoid-representation-of-algebras:

Setoid Representation of Algebras
---------------------------------

.. toctree::
   :maxdepth: 2

   Algebras/Basic
   Algebras/Products
   Algebras/Congruences

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (𝓞 ; 𝓥 ; Signature)

  module Setoid.Algebras {𝑆 : Signature 𝓞 𝓥} where

  open import Setoid.Algebras.Basic        {𝑆 = 𝑆} public
  open import Setoid.Algebras.Products     {𝑆 = 𝑆} public
  open import Setoid.Algebras.Congruences  {𝑆 = 𝑆} public
