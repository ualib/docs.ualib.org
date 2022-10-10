.. FILE      : Base/Adjunction.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 30 Aug 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-adjunction:

Adjunction
----------

This is the `Base.Adjunction`_ module of the `Agda Universal Algebra Library`_.

.. toctree::
   :maxdepth: 2

   Adjunction/Closure
   Adjunction/Galois
   Adjunction/Residuation

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Adjunction where

  open import Base.Adjunction.Closure      public
  open import Base.Adjunction.Galois       public
  open import Base.Adjunction.Residuation  public


