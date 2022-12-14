.. FILE      : Setoid/Varieties/EquationalLogic.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 14 Jan 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _setoid-varieties-entailment-soundness-and-completeness:

Entailment, soundness and completeness
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Varieties.SoundAndComplete`_ module of the `Agda Universal Algebra Library`_.

This module is based on `Andreas Abelβs Agda formalization of Birkhoffβs
completeness theorem <http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf>`__.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (π ; π₯ ; Signature)

  module Setoid.Varieties.SoundAndComplete {π : Signature π π₯} where

  -- imports from Agda and the Agda Standard Library -------------------------------
  open import Agda.Primitive   using () renaming ( Set to Type )
  open import Data.Product     using ( _,_ ; Ξ£-syntax ; _Γ_ )
                               renaming ( projβ to fst ; projβ to snd )
  open import Function         using ( _β_ ; flip ; id ) renaming ( Func to _βΆ_ )
  open import Level            using ( Level ; _β_ )
  open import Relation.Binary  using ( Setoid ; IsEquivalence )
  open import Relation.Unary   using ( Pred ; _β_ )

  open import Relation.Binary.PropositionalEquality using ( _β‘_ ; refl )

  import Relation.Binary.Reasoning.Setoid as SetoidReasoning

  -- Imports from the Agda Universal Algebra Library -------------------------------
  open import Overture                  using ( β£_β£ )
  open import Base.Terms       {π = π}  using ( Term )
  open import Setoid.Algebras  {π = π}  using ( Algebra ; ov ; β¨_β© )
  open import Setoid.Terms     {π = π}  using ( module Environment ; Sub ; _[_] )

  open Setoid  using ( Carrier ; _β_ ; isEquivalence )
  open _βΆ_     renaming ( f to _β¨$β©_ )
  open Term

  private variable
   Ο Ξ± Οα΅ ΞΉ β : Level
   X Ξ Ξ : Type Ο
   f     : β£ π β£
   I : Type ΞΉ

  -- Equations
  -- An equation is a pair (s , t) of terms in the same context.
  record Eq : Type (ov Ο) where
   constructor _βΜ_
   field
    {cxt}  : Type Ο
    lhs    : Term cxt
    rhs    : Term cxt

  open Eq public

  -- Equation p βΜ q holding in algebra M. (type \~~\^. to get βΜ; type \models to get β§)
  _β§_ : (π¨ : Algebra Ξ± Οα΅)(term-identity : Eq{Ο}) β Type _
  π¨ β§ (p βΜ q) = Equal p q where open Environment π¨

  _β«_ : Pred (Algebra Ξ± Οα΅) β β Eq{Ο} β Type (β β Ο β ov(Ξ± β Οα΅))
  π¦ β« eq = β π¨ β π¦ π¨ β π¨ β§ eq                    -- (type \||= to get β«)

  -- An I-indexed set of equations inhabits the type I β Eq.

  -- For such `β° : I β Eq`...

  -- ...`π¨ β¨ β°` is the assertion that the algebra π¨ models every equation in β°.
  _β¨_ : (π¨ : Algebra Ξ± Οα΅) β (I β Eq{Ο}) β Type _
  π¨ β¨ β° = β i β Equal (lhs (β° i))(rhs (β° i)) where open Environment π¨  --   (type \|= to get β¨)

  -- ...`π¦ β₯β β°` is the assertion that every algebra in π¦ models every equation in β°.
  _β₯β_ : Pred (Algebra Ξ± Οα΅) β β (I β Eq{Ο}) β Type _
  π¦ β₯β β° = β i β π¦ β« β° i

  -- ...`Mod β°` is the class of algebras that model every equation in β°.
  ModTuple : (I β Eq{Ο}) β Pred(Algebra Ξ± Οα΅) _
  ModTuple β° = _β¨ β°

  module _ {Ξ± Οα΅ β : Level} where

   Mod : Pred(Term X Γ Term X) β β Pred (Algebra Ξ± Οα΅) _ -- (π β π₯ β lsuc Ο β β β Ξ± β Οα΅)
   Mod β° π¨ = β {p q} β (p , q) β β° β Equal p q where open Environment π¨

   Th : Pred (Algebra Ξ± Οα΅) β β Pred(Term X Γ Term X) _ -- (β β Ο β ov (Ξ± β Οα΅))
   Th π¦ = Ξ» (p , q) β π¦ β« (p βΜ q)

   βTh : Pred(Term X Γ Term X) (β β Ο β ov (Ξ± β Οα΅)) β Type _ -- (β β ov (Ξ± β Οα΅ β Ο))
   βTh P = Ξ£[ p β (Term _ Γ Term _) ] p β P

   module _ {Ο : Level}{X : Type Ο} where

    ThTuple : (π¦ : Pred (Algebra Ξ± Οα΅) β) β βTh{Ο = Ο} (Th{X = X} π¦) β Eq{Ο}
    ThTuple π¦ = Ξ» i β fst β£ i β£ βΜ snd β£ i β£

  module _ {Ξ±}{Οα΅}{ΞΉ}{I : Type ΞΉ} where
   -- An entailment E β eq holds iff it holds in all models of E.
   _β_ : (E : I β Eq{Ο}) (eq : Eq{Ο}) β Type _
   E β eq = (M : Algebra Ξ± Οα΅) β M β¨ E β M β§ eq

.. _setoid-varieties-derivations-in-a-context:

Derivations in a context
^^^^^^^^^^^^^^^^^^^^^^^^

(Based on `Andreas Abelβs Agda formalization of Birkhoffβs completeness
theorem <http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf>`__.)

::

  module _ {Ο ΞΉ : Level} where

   data _β’_βΉ_β_ {I : Type ΞΉ}(E : I β Eq) : (X : Type Ο)(p q : Term X) β Type (ΞΉ β ov Ο) where
    hyp    : β i β let p βΜ q = E i in E β’ _ βΉ p β q
    app    : β {ps qs} β (β i β E β’ Ξ βΉ ps i β qs i) β E β’ Ξ βΉ (node f ps) β (node f qs)
    sub    : β {p q} β E β’ Ξ βΉ p β q β β (Ο : Sub Ξ Ξ) β E β’ Ξ βΉ (p [ Ο ]) β (q [ Ο ])
    refl   : β {p}              β E β’ Ξ βΉ p β p
    sym    : β {p q : Term Ξ}   β E β’ Ξ βΉ p β q β E β’ Ξ βΉ q β p
    trans  : β {p q r : Term Ξ} β E β’ Ξ βΉ p β q β E β’ Ξ βΉ q β r β E β’ Ξ βΉ p β r

   β’βΉβIsEquiv : {I : Type ΞΉ}{E : I β Eq} β IsEquivalence (E β’ Ξ βΉ_β_)
   β’βΉβIsEquiv = record { refl = refl ; sym = sym ; trans = trans }


.. _setoid-varieties-soundness-of-the-inference-rules:

Soundness of the inference rules
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

(Based on `Andreas Abelβs Agda formalization of Birkhoffβs completeness
theorem <see:%20http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf>`__.)

::

  module Soundness  {Ο Ξ± ΞΉ : Level}{I : Type ΞΉ} (E : I β Eq{Ο})
                    (π¨ : Algebra Ξ± Οα΅)     -- We assume an algebra M
                    (V : π¨ β¨ E)         -- that models all equations in E.
   where
   open Algebra π¨ using ( Interp ) renaming (Domain to A)

   -- In any model M that satisfies the equations E, derived equality is actual equality.
   open SetoidReasoning A

   open Environment π¨ renaming ( β¦_β§s to βͺ_β« )
   open IsEquivalence renaming ( refl to reflβ ; sym to  symβ ; trans to transβ )

   sound : β {p q} β E β’ X βΉ p β q β π¨ β§ (p βΜ q)
   sound (hyp i)                    = V i
   sound (app {f = f} es) Ο         = Interp .cong (refl , Ξ» i β sound (es i) Ο)
   sound (sub {p = p} {q} Epq Ο) Ο  =
    begin
     β¦ p [ Ο ] β§ β¨$β©       Ο ββ¨ substitution p Ο Ο β©
     β¦ p       β§ β¨$β© βͺ Ο β« Ο ββ¨ sound Epq (βͺ Ο β« Ο)  β©
     β¦ q       β§ β¨$β© βͺ Ο β« Ο βΛβ¨ substitution  q Ο Ο β©
     β¦ q [ Ο ] β§ β¨$β©       Ο β

   sound (refl {p = p})                = reflβ   isEquiv {x = p}
   sound (sym {p = p} {q} Epq)         = symβ    isEquiv {x = p}{q}     (sound Epq)
   sound (trans{p = p}{q}{r} Epq Eqr)  = transβ  isEquiv {i = p}{q}{r}  (sound Epq)(sound Eqr)


The deductive closure of a set E is the set of equations modeled by all models
of E; that is, Th Mod E.

The soundness proof above shows β X β E β’ X βΉ p β q β (p , q) β Th Mod
β°. That is, β X β E β’ X βΉ p β q β Mod E β« p β q.

The converse is Birkhoffβs completeness theorem: if Mod E β« p β q, then
E β’ X βΉ p β q.

We will prove that result next.

.. _setoid-varieties-birkhoffs-completeness-theorem:

Birkhoffβs completeness theorem
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The proof proceeds by constructing a relatively free algebra consisting
of term quotiented by derivable equality E β’ X βΉ *β*. It then suffices
to prove that this model satisfies all equations in :math:`E`.

(Based on `Andreas Abelβs Agda formalization of Birkhoffβs completeness
theorem <http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf>`__.)

We denote by ``π½[ X ]`` the *relatively free algebra* over ``X``
(relative to ``E``), which is defined as ``Term X`` modulo
``E β’ X βΉ _β_``. This algebra ``π½[ X ]`` is βfreeβ or βinitialβ in the
variety of algebras satisfying the identities in ``E`` in the sense that
it satisfies the following universal property: for each algebra ``π¨``,
if ``π¨ β§ E``, then there is a unique homomorphism from ``π½[ X ]`` to
``π¨``.

::

  module FreeAlgebra {Ο : Level}{ΞΉ : Level}{I : Type ΞΉ}(E : I β Eq) where
   open Algebra

   -- Domain of the relatively free algebra.
   FreeDomain : Type Ο β Setoid _ _
   FreeDomain X = record  { Carrier       = Term X
                          ; _β_           = E β’ X βΉ_β_
                          ; isEquivalence = β’βΉβIsEquiv
                          }

   -- The interpretation of an operation is simply the operation itself.
   -- This works since E β’ X βΉ_β_ is a congruence.
   FreeInterp : β {X} β (β¨ π β© (FreeDomain X)) βΆ (FreeDomain X)
   FreeInterp β¨$β© (f , ts) = node f ts
   cong FreeInterp (refl , h) = app h

   -- The relatively free algebra
   π½[_] : Type Ο β Algebra (ov Ο) (ΞΉ β ov Ο)
   Domain π½[ X ] = FreeDomain X
   Interp π½[ X ] = FreeInterp

   -- The identity substitution Οβ maps variables to themselves.
   Οβ : {X : Type Ο} β Sub X X
   Οβ x = β x

   -- Οβ acts indeed as identity.
   identity : (t : Term X) β E β’ X βΉ t [ Οβ ] β t
   identity (β x) = refl
   identity (node f ts) = app (identity β ts)


Evaluation in the term model is substitution ``E β’ X βΉ β¦tβ§Ο β t[Ο]``.
(This would hold βon the noseβ if we had function extensionality.)

(We put this and the next two lemmas into their own submodules to
emphasize the fact that these results are independent of the chosen
variable symbol type ``X`` (or ``Ξ``, or ``Ξ``), which is an arbitrary
inhabitant of ``Type Ο``.)

::

   module _ {X : Type Ο} where
    open Environment π½[ X ]
    evaluation : (t : Term Ξ) (Ο : Sub X Ξ) β E β’ X βΉ (β¦ t β§ β¨$β© Ο) β (t [ Ο ])
    evaluation (β x) Ο = refl
    evaluation (node f ts) Ο = app (flip (evaluation β ts) Ο)


   module _ {Ξ : Type Ο} where
    -- The term model satisfies all the equations it started out with.
    satisfies : π½[ Ξ ] β¨ E
    satisfies i Ο =
     begin
      β¦ p β§ β¨$β© Ο  ββ¨ evaluation p Ο β©
      p [ Ο ]      ββ¨ sub (hyp i) Ο β©
      q [ Ο ]      βΛβ¨ evaluation q Ο β©
      β¦ q β§ β¨$β© Ο  β
      where
      open Environment π½[ Ξ ]
      open SetoidReasoning (Domain π½[ Ξ ]) ; p = lhs (E i) ; q = rhs (E i)

We are finally ready to formally state and prove Birkhoffβs Completeness
Theorem, which asserts that every valid consequence is derivable.

::

   module _ {Ξ : Type Ο} where

    completeness : β p q β ModTuple E β« (p βΜ q) β E β’ Ξ βΉ p β q
    completeness p q V =
     begin
      p              βΛβ¨ identity p β©
      p [ Οβ ]       βΛβ¨ evaluation p Οβ β©
      β¦ p β§ β¨$β© Οβ   ββ¨ V π½[ Ξ ] satisfies Οβ β©
      β¦ q β§ β¨$β© Οβ   ββ¨ evaluation q Οβ β©
      q [ Οβ ]       ββ¨ identity q β©
      q              β
     where
     open Environment π½[ Ξ ]
     open SetoidReasoning (Domain π½[ Ξ ])

