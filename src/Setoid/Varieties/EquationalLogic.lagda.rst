.. FILE      : Setoid/Varieties/EquationalLogic.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 24 Jul 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _setoid-varieties-equational-logic-and-varieties-of-setoid-algebras:

Equational logic and varieties of setoid algebras
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Varieties.EquationalLogic`_ module of the `Agda Universal
Algebra Library`_ where the binary "models" relation β§, relating algebras (or
classes of algebras) to the identities that they satisfy, is defined.

Let π be a signature. By an *identity* or *equation* in π we mean an ordered
pair of terms, written π β π, from the term algebra π» X. If π¨ is an π-algebra
we say that π¨ *satisfies* π β π provided π Μ π¨ β‘ π Μ π¨ holds. In this
situation, we write π¨ β§ π β π and say that π¨ *models* the identity π β q.
If π¦ is a class of algebras, all of the same signature, we write
π¦ β§ p β q if, for every π¨ β π¦, π¨ β§ π β π.

Because a class of structures has a different type than a single structure,
we must use a slightly different syntax to avoid overloading the relations
β§ and β. As a reasonable alternative to what we would normally express
informally as π¦ β§ π β π, we have settled on π¦ β« p β q to denote this
relation. To reiterate, if π¦ is a class of π-algebras, we write
π¦ β« π β π if every π¨ β π¦ satisfies π¨ β§ π β π.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (π ; π₯ ; Signature)

  module Setoid.Varieties.EquationalLogic {π : Signature π π₯} where

  -- Imports from Agda and the Agda Standard Library -------------------------------
  open import Agda.Primitive   using () renaming ( Set to Type )
  open import Data.Product     using ( _Γ_ ; _,_ ; Ξ£-syntax)
                               renaming ( projβ to fst ; projβ to snd )
  open import Function         using () renaming ( Func to _βΆ_ )
  open import Level            using ( _β_ ; Level )
  open import Relation.Binary  using ( Setoid )
  open import Relation.Unary   using ( Pred ; _β_ )

  -- Imports from the Agda Universal Algebra Library -------------------------------
  open import Setoid.Algebras  {π = π} using ( Algebra ; ov )
  open import Base.Terms       {π = π} using ( Term )
  open import Setoid.Terms     {π = π} using ( π» ; module Environment )

  private variable Ο Ξ± Οα΅ β ΞΉ : Level


.. _setoid-varieties-the-models-relation:

The models relation
^^^^^^^^^^^^^^^^^^^

We define the binary βmodelsβ relation ``β§`` using infix syntax so that
we may write, e.g., ``π¨ β§ p β q`` or ``π¦ β« p β q``, relating algebras
(or classes of algebras) to the identities that they satisfy. We also
prove a couple of useful facts about β§. More will be proved about β§ in
the next module, Varieties.EquationalLogic.

::

  open _βΆ_ using () renaming ( f to _β¨$β©_ )

  module _  {X : Type Ο} where

   open Setoid   using () renaming (Carrier to β£_β£ )
   open Algebra  using ( Domain )

   _β§_β_ : Algebra Ξ± Οα΅ β Term X β Term X β Type _
   π¨ β§ p β q = β (Ο : β£ Env X β£) β β¦ p β§ β¨$β© Ο β β¦ q β§ β¨$β© Ο
    where
    open Setoid ( Domain π¨ )  using ( _β_ )
    open Environment π¨        using ( Env ; β¦_β§ )

   _β«_β_ : Pred(Algebra Ξ± Οα΅) β β Term X β Term X β Type (Ο β β β ov(Ξ± β Οα΅))
   π¦ β« p β q = {π¨ : Algebra _ _} β π¦ π¨ β π¨ β§ p β q

(**Unicode tip**. Type :raw-latex:`\models `to get ``β§`` ; type \||= to get ``β«``.)

The expression ``π¨ β§ p β q`` represents the assertion that the identity ``p β q``
holds when interpreted in the algebra ``π¨`` for any environment Ο; syntactically,
we write this interpretation as ``β¦ p β§ Ο β β¦ q β§ Ο``. (Recall, and environment
is simply an assignment of values in the domain to variable symbols).



.. _setoid-varieties-equational-theories-and-models-over-setoids:

Equational theories and models over setoids
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If π¦ denotes a class of structures, then ``Th π¦`` represents the set of identities
modeled by the members of π¦.

::

   Th' : Pred (Algebra Ξ± Οα΅) β β Pred(Term X Γ Term X) (Ο β β β ov(Ξ± β Οα΅))
   Th' π¦ = Ξ» (p , q) β π¦ β« p β q

::

  Th'' :  {Ο Ξ± : Level}{X : Type Ο} β Pred (Algebra Ξ± Ξ±) (ov Ξ±)
   β      Pred(Term X Γ Term X) (Ο β ov Ξ±)
  Th'' π¦ = Ξ» (p , q) β π¦ β« p β q

Perhaps we want to represent Th π¦ as an indexed collection. We do so essentially
by taking ``Th π¦`` itself to be the index set, as shown below.

::

  module _ {X : Type Ο}{π¦ : Pred (Algebra Ξ± Οα΅) (ov Ξ±)} where

   β : Type (ov(Ξ± β Οα΅ β Ο))
   β = Ξ£[ (p , q) β (Term X Γ Term X) ] π¦ β« p β q

   β° : β β Term X Γ Term X
   β° ((p , q) , _) = (p , q)

If ``β°`` denotes a set of identities, then ``Mod β°`` is the class of
structures satisfying the identities in ``β°``.

::

   Mod' : Pred(Term X Γ Term X) (ov Ξ±) β Pred(Algebra Ξ± Οα΅) (Οα΅ β ov(Ξ± β Ο))
   Mod' β° = Ξ» π¨ β β p q β (p , q) β β° β π¨ β§ p β q

It is sometimes more convenient to have a βtupledβ version of the
previous definition, which we denote by ``Modα΅`` and define as follows.

::

   Modα΅ : {I : Type ΞΉ} β (I β Term X Γ Term X) β {Ξ± : Level} β Pred(Algebra Ξ± Οα΅) (Ο β Οα΅ β ΞΉ β Ξ±)
   Modα΅ β° = Ξ» π¨ β β i β π¨ β§ fst (β° i) β snd (β° i)
