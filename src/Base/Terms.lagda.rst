.. FILE      : Base/Terms.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 14 Jan 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-terms:

Terms
-----

This is the `Base.Terms`_ module of the `Agda Universal Algebra Library`_

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (Signature ; 𝓞 ; 𝓥 )

  module Base.Terms {𝑆 : Signature 𝓞 𝓥} where

  open import Base.Terms.Basic       {𝑆 = 𝑆} public
  open import Base.Terms.Properties  {𝑆 = 𝑆} public
  open import Base.Terms.Operations  {𝑆 = 𝑆} public

.. toctree::
   :maxdepth: 2

   Terms/Basic
   Terms/Properties
   Terms/Operations




