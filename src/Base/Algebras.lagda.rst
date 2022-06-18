.. FILE      : Base/Algebras.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 02 Jun 2022
.. UPDATED   : 02 Jun 2022
.. COPYRIGHT : (c) 2022 William DeMeo

.. highlight:: agda
.. role:: code

.. _algebras:

Algebras
--------

This is the `Base.Algebras`_ module of the agda-algebras_ library in which we use type theory
and Agda_ to codify the most basic objects of universal algebra, such as *signatures*, *algebras*,
*product algebras*, *congruence relations*, and *quotient algebras*.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Algebras where

  open import Base.Algebras.Basic        public
  open import Base.Algebras.Products     public
  open import Base.Algebras.Congruences  public

.. toctree::
   :maxdepth: 2

   Algebras/Basic
   Algebras/Products
   Algebras/Congruences

