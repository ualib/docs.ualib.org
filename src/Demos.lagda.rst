.. FILE      : Demos.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 27 Apr 2022
.. UPDATED   : 22 Jun 2022

.. highlight:: agda
.. role:: code

.. _demos-demonstrations-of-the-agda-algebras-library:

Demonstrations of the Agda Algebras Library
===========================================

This is the `Demos`_ module of the `Agda Universal Algebra Library`_.

.. toctree::
   :maxdepth: 2

   Demos/HSP
   Demos/ContraX

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Demos where

  open import Demos.HSP
  open import Demos.ContraX
