.. FILE      : Overture/Levels.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 06 Jan 2022
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _overture-type-universes:

Type Universes
--------------

This is the `Overture.Levels`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Overture.Levels where

  -- Imports from Agda and the Agda Standard Library
  open import Agda.Primitive       using () renaming ( Set to Type )
  open import Function             using ( _∘_ )
  open import Level                using ( Level ; lift ; lower ; Lift )
  open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ )

  open import Overture.Basic       using ( 𝑖𝑑 )

  private variable α β : Level


The hierarchy of universes in Agda is structured as follows:

.. code:: agda

   Type α : Type (lsuc α) ,   Type (lsuc α) : Type (lsuc (lsuc α)) , etc.

and so on. This means that the universe ``Type α`` has type ``Type(lsuc α)``, and
``Type(lsuc α)`` has type ``Type(lsuc (lsuc α))``, and so on. It is important to
note, however, this does *not* imply that ``Type α : Type(lsuc(lsuc α))``. In other
words, Agda's universe hierarchy is *non-cumulative*. This makes it possible to treat universe
levels more precisely, which is nice. On the other hand, a non-cumulative hierarchy can
sometimes make for a non-fun proof assistant. Specifically, in certain situations, the
non-cumulativity makes it unduly difficult to convince Agda that a program or proof is correct.


.. _overture-universe-level-casting:

Universe level casting
~~~~~~~~~~~~~~~~~~~~~~

Here we describe a general ``Lift`` operation which casts a universe up to a higher
level and is used to overcome the technical hurdle described in the previous subsection.

In the :ref:`Lifts of algebras section`_ of the `Base.Algebras.Basic`_ module we will
define a couple domain-specific lifting types which have certain properties that make
them useful for resolving universe level errors when working with algebra types.

Let us be more concrete about what is at issue here by considering a
typical example. Agda will often complain with errors like the following:

.. code:: agda

   Birkhoff.lagda:498,20-23
   α != 𝓞 ⊔ 𝓥 ⊔ (lsuc α) when checking that the expression... has type...

This error message means that Agda encountered the universe level
``lsuc α``, on line 498 (columns 20–23) of the file ``Birkhoff.lagda``,
but was expecting a type at level ``𝓞 ⊔ 𝓥 ⊔ lsuc α`` instead.

The general ``Lift`` record type that we now describe makes such
problems easier to deal with. It takes a type inhabiting some universe
and embeds it into a higher universe and, apart from syntax and
notation, it is equivalent to the ``Lift`` type one finds in the
``Level`` module of the `Agda Standard Library`_.

.. code:: agda

   record Lift {𝓦 α : Level} (A : Set α) : Set (α ⊔ 𝓦) where
       constructor lift
       field lower : A

The point of having a ramified hierarchy of universes is to avoid
Russell's paradox, and this would be subverted if we were to lower the
universe of a type that wasn't previously lifted. However, we can prove
that if an application of ``lower`` is immediately followed by an
application of ``lift``, then the result is the identity transformation.
Similarly, ``lift`` followed by ``lower`` is the identity.

::

  lift∼lower : {A : Type α} → lift ∘ lower ≡ 𝑖𝑑 (Lift β A)
  lift∼lower = ≡.refl

  lower∼lift : {A : Type α} → (lower {α}{β}) ∘ lift ≡ 𝑖𝑑 A
  lower∼lift = ≡.refl

The proofs are trivial. Nonetheless, we'll come across some holes these lemmas can fill.
