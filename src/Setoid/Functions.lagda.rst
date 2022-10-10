.. FILE      : Setoid/Functions.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 08 Sep 2021
.. UPDATED   : 05 Jun 2022

.. highlight:: agda
.. role:: code

.. _setoid-functions:

Setoid functions
-----------------

This is the `Setoid.Functions`_ module of the `Agda Universal Algebra Library`_.

.. toctree::
   :maxdepth: 2

   Functions/Basic
   Functions/Inverses
   Functions/Injective
   Functions/Surjective
   Functions/Bijective

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Setoid.Functions where

  open import Setoid.Functions.Basic       public
  open import Setoid.Functions.Inverses    public
  open import Setoid.Functions.Injective   public
  open import Setoid.Functions.Surjective  public
  open import Setoid.Functions.Bijective   public

