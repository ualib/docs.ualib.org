.. FILE      : Base/Varieties.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 14 Jan 2021
.. UPDATED   : 03 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-varieties-equational-logic:

Equational Logic
~~~~~~~~~~~~~~~~

This is the `Base.Varieties.EquationalLogic`_ module of the
`Agda Universal Algebra Library`_ where the binary "models" relation ``β§``,
relating algebras (or classes of algebras) to the identities that they
satisfy, is defined.

Let ``π`` be a signature. By an *identity* or *equation* in ``π`` we mean an
ordered pair of terms, written ``p β q``, from the term algebra ``π» X``. If ``π¨``
is an ``π``-algebra we say that π¨ *satisfies* π β π provided π Μ π¨ β‘ π Μ π¨ holds.
In this situation, we write π¨ β§ π β π and say that π¨ *models* the
identity π β q. If π¦ is a class of algebras, all of the same signature,
we write π¦ β§ p β q if, for every π¨ β π¦, π¨ β§ π β π.

Because a class of structures has a different type than a single structure, we must use a slightly different syntax to avoid overloading the relations ``β§`` and ``β``. As a reasonable alternative to what we would normally express informally as ``π¦ β§ p β q``, we have settled on ``π¦ β« p β q`` to denote this relation.  To reiterate, if ``π¦`` is a class of ``π``-algebras, we write ``π¦ β« p β q`` iff every ``π¨ β π¦`` satisfies ``π¨ β§ p β q``.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using ( π ; π₯ ; Signature )

  module Base.Varieties.EquationalLogic {π : Signature π π₯} where

  -- Imports from Agda and the Agda Standard Library ----------------
  open import Agda.Primitive  using () renaming ( Set to Type )
  open import Data.Product    using ( _Γ_ ; _,_ ; Ξ£-syntax)
                              renaming ( projβ to fst ; projβ to snd )
  open import Level           using ( Level ;  _β_ )
  open import Relation.Unary  using ( Pred ; _β_ )

  -- Imports from the Agda Universal Algebra Library ----------------
  open import Overture                using ( _β_ )
  open import Base.Algebras  {π = π}  using ( Algebra ; ov )
  open import Base.Terms     {π = π}  using ( Term ; π» ; _β¦_β§ )

  private variable
   Ο Ξ± Ο ΞΉ : Level
   X : Type Ο


.. _base-varieties-the-models-relation:

The models relation
^^^^^^^^^^^^^^^^^^^

We define the binary "models" relation ``β§`` using infix syntax so that we may
write, e.g., ``π¨ β§ p β q`` or ``π¦ β« p β q``, relating algebras (or classes of
algebras) to the identities that they satisfy. We also prove a couple of useful
facts about ``β§``.

::

  _β§_β_ : Algebra Ξ± β Term X β Term X β Type _
  π¨ β§ p β q = π¨ β¦ p β§ β π¨ β¦ q β§

  _β«_β_ : Pred(Algebra Ξ±) Ο β Term X β Term X β Type _
  π¦ β« p β q = {π¨ : Algebra _} β π¦ π¨ β π¨ β§ p β q

**Unicode tip**. Type ``\models`` to get ``β§`` ; type ``\||=`` to get ``β«``.

The expression ``π¨ β§ p β q`` represents the assertion that the identity ``p β q``
holds when interpreted in the algebra ``π¨``; syntactically, ``π¨ β¦ p β§ β π¨ β¦ q β§``.

The expression ``π¨ β¦ p β§ β π¨ β¦ q β§`` denotes *extensional equality*; that is, for
each βenvironmentβ ``Ξ· :  X β β£ π¨ β£`` (assigning values in the domain of ``π¨`` to
the variable symbols in ``X``) the (intensional) equality ``π¨ β¦ p β§ Ξ· β‘ π¨ β¦ q β§ Ξ·``
holds.

.. _base-varieties-equational-theories-and-models:

Equational theories and models
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If ``π¦`` denotes a class of structures, then ``Th π¦`` represents the set of
identities modeled by the members of ``π¦``.

::

  Th : Pred (Algebra Ξ±) (ov Ξ±) β Pred(Term X Γ Term X) _
  Th π¦ = Ξ» (p , q) β π¦ β« p β q

We represent ``Th π¦`` as an indexed collection of algebras by taking ``Th π¦``,
itself, to be the index set.

::

  module _ {X : Type Ο}{π¦ : Pred (Algebra Ξ±) (ov Ξ±)} where

   β : Type (ov(Ξ± β Ο))
   β = Ξ£[ (p , q) β (Term X Γ Term X) ] π¦ β« p β q

   β° : β β Term X Γ Term X
   β° ((p , q) , _) = (p , q)

If ``β°`` denotes a set of identities, then ``Mod β°`` is the class of
structures satisfying the identities in ``β°``.

::

  Mod : Pred(Term X Γ Term X) (ov Ξ±) β Pred(Algebra Ξ±) _
  Mod β° = Ξ» π¨ β β p q β (p , q) β β° β π¨ β§ p β q
  -- (tupled version)
  Modα΅ : {I : Type ΞΉ} β (I β Term X Γ Term X) β {Ξ± : Level} β Pred(Algebra Ξ±) _
  Modα΅ β° = Ξ» π¨ β β i β π¨ β§ (fst (β° i)) β (snd (β° i))


