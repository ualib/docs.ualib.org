.. FILE      : Setoid/Terms.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 18 Sep 2021
.. UPDATED   : 18 Jun 2022

.. highlight:: agda
.. role:: code

.. _setoid-terms-on-setoids:

Terms on setoids
----------------

This is the `Setoid.Terms`_ module of the `Agda Universal Algebra Library`_.


.. toctree::
   :maxdepth: 2

   Terms/Basic
   Terms/Properties
   Terms/Operations

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (𝓞 ; 𝓥 ; Signature)

  module Setoid.Terms {𝑆 : Signature 𝓞 𝓥} where

  open import Setoid.Terms.Basic       {𝑆 = 𝑆} public
  open import Setoid.Terms.Properties  {𝑆 = 𝑆} public
  open import Setoid.Terms.Operations  {𝑆 = 𝑆} public
