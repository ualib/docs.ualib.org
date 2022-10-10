.. FILE      : Setoid/Subalgebras.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 26 Jul 2021
.. UPDATED   : 18 Jun 2022

.. highlight:: agda
.. role:: code

.. _subalgebras-over-setoids:

Subalgebras over setoids
~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Subalgebras`_ module of the `Agda Universal Algebra Library`_.


.. toctree::
   :maxdepth: 2

   Subalgebras/Subuniverses
   Subalgebras/Subalgebras
   Subalgebras/Properties


::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (𝓞 ; 𝓥 ; Signature)

  module Setoid.Subalgebras {𝑆 : Signature 𝓞 𝓥} where

  open import Setoid.Subalgebras.Subuniverses  {𝑆 = 𝑆} public
  open import Setoid.Subalgebras.Subalgebras   {𝑆 = 𝑆} public
  open import Setoid.Subalgebras.Properties    {𝑆 = 𝑆} public
