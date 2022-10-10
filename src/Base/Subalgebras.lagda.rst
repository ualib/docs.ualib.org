.. FILE      : Base/Subalgebras.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 14 Jan 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-subalgebras:

Subalgebras
-----------

This is the `Base.Subalgebras`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using ( Signature ; 𝓞 ; 𝓥 )

  module Base.Subalgebras {𝑆 : Signature 𝓞 𝓥} where

  open import Base.Subalgebras.Subuniverses  {𝑆 = 𝑆} public
  open import Base.Subalgebras.Subalgebras   {𝑆 = 𝑆} public
  open import Base.Subalgebras.Properties    {𝑆 = 𝑆} public

.. toctree::
   :maxdepth: 2

   Subalgebras/Subuniverses
   Subalgebras/Subalgebras
   Subalgebras/Properties


