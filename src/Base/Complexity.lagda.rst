.. FILE      : Base/Complexity.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 26 Jul 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-complexity:

Complexity
----------

This is the `Base.Complexity`_ module of the `Agda Universal Algebra Library`_.

.. toctree::
   :maxdepth: 2

   Complexity/Basic
   Complexity/CSP

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Complexity where

  open import Base.Complexity.Basic public
  open import Base.Complexity.CSP public


