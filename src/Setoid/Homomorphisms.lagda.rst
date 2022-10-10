.. FILE      : Setoid/Homomorphisms.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 17 Sep 2021
.. UPDATED   : 09 Jun 2022

.. highlight:: agda
.. role:: code

.. _homomorphism-of-setoid-algebras:

Homomorphism of Setoid Algebras
-------------------------------

This is the `Setoid.Homomorphisms`_ module of the `Agda Universal Algebra Library`_.

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

  open import Overture using (𝓞 ; 𝓥 ; Signature)

  module Setoid.Homomorphisms {𝑆 : Signature 𝓞 𝓥} where

  open import Setoid.Homomorphisms.Basic              {𝑆 = 𝑆} public
  open import Setoid.Homomorphisms.Properties         {𝑆 = 𝑆} public
  open import Setoid.Homomorphisms.Kernels            {𝑆 = 𝑆} public
  open import Setoid.Homomorphisms.Products           {𝑆 = 𝑆} public
  open import Setoid.Homomorphisms.Noether            {𝑆 = 𝑆} public
  open import Setoid.Homomorphisms.Factor             {𝑆 = 𝑆} public
  open import Setoid.Homomorphisms.Isomorphisms       {𝑆 = 𝑆} public
  open import Setoid.Homomorphisms.HomomorphicImages  {𝑆 = 𝑆} public
