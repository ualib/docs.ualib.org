.. FILE      : Base/Complexity/Basic.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 13 Jul 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-complexity-theory:

Complexity Theory
~~~~~~~~~~~~~~~~~

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Complexity.Basic where

.. _base-complexity-words:

Words
^^^^^

Let 𝑇ₙ be a totally ordered set of size 𝑛. Let 𝐴 be a set (the alphabet). We can
model the set 𝑊ₙ, of *words* (strings of letters from 𝐴) of length 𝑛 by the type
𝑇ₙ → 𝐴 of functions from 𝑇ₙ to 𝐴.

The set of all (finite length) words is then 𝕎 = ⋃[𝑛 ∈ ℕ] 𝑊ₙ.

The *length* of a word ``x`` is given by the function ``size x``, defined later.

An *algorithm* is a computer program with infinite memory (i.e., a
Turing machine).

A function 𝑓 : 𝑊 → 𝑊 is *computable in polynomial time* if there exist
an algorithm and numbers 𝑐, 𝑑 ∈ ℕ such that for each word 𝑥 ∈ 𝑊 the
algorithm stops in at most (size 𝑥) 𝑐 + 𝑑 steps and computes 𝑓 𝑥.

At first we will simplify by assuming 𝑇ₙ is ``Fin n``.



