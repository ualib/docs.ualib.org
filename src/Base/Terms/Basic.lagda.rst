.. FILE      : Base/Terms.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 14 Jan 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-terms-basic-definitions:

Basic Definitions
~~~~~~~~~~~~~~~~~

This is the `Base.Terms.Basic`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (Signature ; š ; š„ )

  module Base.Terms.Basic {š : Signature š š„} where

  -- Imports from Agda and the Agda Standard Library ----------------
  open import Agda.Primitive         using () renaming ( Set to Type )
  open import Data.Product           using ( _,_ )
  open import Level                  using ( Level )

  -- Imports from the Agda Universal Algebra Library ----------------
  open import Overture          using ( ā£_ā£ ; ā„_ā„ )
  open import Base.Algebras {š = š}  using ( Algebra ; ov )

  private variable Ļ : Level

.. _base-terms-the-type-of-terms:

The type of terms
^^^^^^^^^^^^^^^^^

Fix a signature ``š`` and let ``X`` denote an arbitrary nonempty collection of
variable symbols. Assume the symbols in ``X`` are distinct from the operation
symbols of ``š``, that is ``X ā© ā£ š ā£ = ā``.

By a *word* in the language of ``š``, we mean a nonempty, finite sequence of
members of ``X āŖ ā£ š ā£``. We denote the concatenation of such sequences by simple
juxtaposition. 

Let ``Sā`` denote the set of nullary operation symbols of ``š``. We define by
induction on ``n`` the sets ``šā`` of *words* over ``X āŖ ā£ š ā£`` as follows
(cf.Ā :ref:`Bergman (2012) Def. 4.19 <XXXX>`__ ):

``šā := X āŖ Sā`` and ``šāāā := šā āŖ šÆā``

where ``šÆā`` is the collection of all ``f t`` such that ``f : ā£ š ā£`` and
``t : ā„ š ā„ f ā šā``. (Recall, ``ā„ š ā„ f`` is the arity of the operation symbol
``f``.)

We define the collection of *terms* in the signature ``š`` over ``X`` by
``Term X := āā šā``. By an š-\ *term* we mean a term in the language of ``š``.

The definition of ``Term X`` is recursive, indicating that an inductive type could
be used to represent the semantic notion of terms in type theory. Indeed, such a
representation is given by the following inductive type.

::

  data Term (X : Type Ļ ) : Type (ov Ļ)  where
   ā : X ā Term X    -- (ā for "generator")
   node : (f : ā£ š ā£)(t : ā„ š ā„ f ā Term X) ā Term X

  open Term

This is a very basic inductive type that represents each term as a tree with an
operation symbol at each ``node`` and a variable symbol at each leaf (``generator``).

**Notation**. As usual, the type ``X`` represents an arbitrary collection of
variable symbols. Recall, ``ov Ļ`` is our shorthand notation for the universe
level ``š ā š„ ā suc Ļ``.

.. _base-terms-the-term-algebra:

The term algebra
^^^^^^^^^^^^^^^^

For a given signature ``š``, if the type ``Term X`` is nonempty (equivalently, if
``X`` or ``ā£ š ā£`` is nonempty), then we can define an algebraic structure,
denoted by ``š» X`` and called the *term algebra in the signature* ``š`` *over*
``X``. Terms are viewed as acting on other terms, so both the domain and basic
operations of the algebra are the terms themselves.

-  For each operation symbol ``f : ā£ š ā£``, denote by ``f Ģ (š» X)`` the operation
   on ``Term X`` that maps a tuple ``t : ā„ š ā„ f ā ā£ š» X ā£`` to the formal term
   ``f t``.
-  Define ``š» X`` to be the algebra with universe ``ā£ š» X ā£ := Term X`` and
   operations ``f Ģ (š» X)``, one for each symbol ``f`` in ``ā£ š ā£``.

In Agda_ the term algebra can be defined as simply as one could hope.

::

  š» : (X : Type Ļ ) ā Algebra (ov Ļ)
  š» X = Term X , node



