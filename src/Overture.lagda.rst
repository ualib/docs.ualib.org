.. FILE      : Overture.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 12 Dec 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _overture:

Overture
========

This is the Overture_ module of the `Agda Universal Algebra Library`_.

.. toctree::
   :maxdepth: 2

   Overture/Preface
   Overture/Basic
   Overture/Levels
   Overture/Signatures
   Overture/Operations

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Overture where

  open import Overture.Preface     public
  open import Overture.Basic       public
  open import Overture.Levels      public
  open import Overture.Signatures  public
  open import Overture.Operations  public
