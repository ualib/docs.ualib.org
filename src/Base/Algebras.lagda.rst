.. FILE      : Base/Algebras.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 12 Jan 2021
.. UPDATED   : 18 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-algebras:

Algebras
--------

This is the `Base.Algebras`_ module of the agda-algebras_ library in which we use type theory
and Agda_ to codify the most basic objects of universal algebra, such as *signatures*, *algebras*,
*product algebras*, *congruence relations*, and *quotient algebras*.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture  using ( 𝓞 ; 𝓥 ; Signature )

  module Base.Algebras {𝑆 : Signature 𝓞 𝓥 } where

  open import Base.Algebras.Basic        {𝑆 = 𝑆} public
  open import Base.Algebras.Products     {𝑆 = 𝑆} public
  open import Base.Algebras.Congruences  {𝑆 = 𝑆} public

.. toctree::
   :maxdepth: 2

   Algebras/Basic
   Algebras/Products
   Algebras/Congruences

