.. FILE      : Setoid/Functions.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 12 Dec 2021
.. UPDATED   : 05 Jun 2022
.. COPYRIGHT : (c) 2022 Jacques Carette and William DeMeo

.. highlight:: agda
.. role:: code

.. _setoid-functions:

Setoid functions
-----------------

This is the `Setoid.Functions`_ module of the `Agda Universal Algebra Library`_.

.. toctree::
   :maxdepth: 2

   Setoid/Functions/Basic
   Setoid/Functions/Inverses
   Setoid/Functions/Injective
   Setoid/Functions/Surjective
   Setoid/Functions/Bijective

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Setoid.Functions where

  open import Setoid.Functions.Basic       public
  open import Setoid.Functions.Inverses    public
  open import Setoid.Functions.Injective   public
  open import Setoid.Functions.Surjective  public
  open import Setoid.Functions.Bijective   public

