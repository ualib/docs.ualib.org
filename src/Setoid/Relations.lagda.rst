.. FILE     : Setoid/Relations.lagda.rst
.. AUTHOR   : William DeMeo
.. DATE     : 17 Sep 2021
.. UPDATED  : 09 Jun 2022

.. highlight:: agda
.. role:: code

.. _setoid-relations:

Setoid relations
----------------

This is the `Setoid.Relations`_ module of the `Agda Universal Algebra Library`_.

.. toctree::
   :maxdepth: 2

   Relations/Discrete
   Relations/Quotients

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Setoid.Relations where

  open import Setoid.Relations.Discrete   public
  open import Setoid.Relations.Quotients  public

