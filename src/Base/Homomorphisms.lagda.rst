.. FILE      : Base/Homomorphisms.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 12 Jan 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-homomorphisms:

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

  open import Overture using (Signature ; 𝓞 ; 𝓥 )

  module Base.Homomorphisms {𝑆 : Signature 𝓞 𝓥} where

  open import Base.Homomorphisms.Basic              {𝑆 = 𝑆} public
  open import Base.Homomorphisms.Properties         {𝑆 = 𝑆} public
  open import Base.Homomorphisms.Kernels            {𝑆 = 𝑆} public
  open import Base.Homomorphisms.Products           {𝑆 = 𝑆} public
  open import Base.Homomorphisms.Noether            {𝑆 = 𝑆} public
  open import Base.Homomorphisms.Factor             {𝑆 = 𝑆} public
  open import Base.Homomorphisms.Isomorphisms       {𝑆 = 𝑆} public
  open import Base.Homomorphisms.HomomorphicImages  {𝑆 = 𝑆} public
