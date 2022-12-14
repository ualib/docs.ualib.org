.. FILE      : Setoid/Subalgebras/Subuniverses.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 11 Jul 2021
.. UPDATED   : 18 Jun 2022

.. highlight:: agda
.. role:: code

.. _subuniverses-of-setoid-algebras:

Subuniverses of setoid algebras
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Subalgebras.Subuniverses`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (๐ ; ๐ฅ ; Signature)

  module Setoid.Subalgebras.Subuniverses {๐ : Signature ๐ ๐ฅ} where

  -- Imports from Agda and the Agda Standard Library ----------------------------------
  open import Agda.Primitive   using () renaming ( Set to Type )
  open import Data.Product     using ( _,_ )
  open import Function         using ( _โ_ ; Func )
  open import Level            using (Level ;  _โ_ )
  open import Relation.Binary  using ( Setoid )
  open import Relation.Unary   using ( Pred ; _โ_ ; _โ_ ; โ )

  import Relation.Binary.Reasoning.Setoid as SetoidReasoning
  open import Relation.Binary.PropositionalEquality using ( refl )

  -- Imports from the Agda Universal Algebra Library ----------------------------------
  open import Overture        using ( โฃ_โฃ ; โฅ_โฅ )
  open import Base.Relations  using ( Im_โ_ )

  open import Base.Terms            {๐ = ๐} using ( Term ; โ ; node )
  open import Setoid.Algebras       {๐ = ๐} using ( Algebra ; ๐[_] ; _ฬ_ ; ov )
  open import Setoid.Terms          {๐ = ๐} using ( module Environment )
  open import Setoid.Homomorphisms  {๐ = ๐} using ( hom ; IsHom )

  private variable
   ฮฑ ฮฒ ฮณ ฯแต ฯแต ฯแถ โ ฯ : Level
   X : Type ฯ


We first show how to represent in Agda_ the collection of subuniverses of an
algebra ``๐จ``. Since a subuniverse is viewed as a subset of the domain of
``๐จ``, we define it as a predicate on ``โฃ ๐จ โฃ``. Thus, the collection of
subuniverses is a predicate on predicates on ``โฃ ๐จ โฃ``.

::

  module _ (๐จ : Algebra ฮฑ ฯแต) where
   private A = ๐[ ๐จ ] -- the forgetful functor

   Subuniverses : Pred (Pred A โ) (๐ โ ๐ฅ โ ฮฑ โ โ )
   Subuniverses B = โ f a โ Im a โ B โ (f ฬ ๐จ) a โ B

   -- Subuniverses as a record type
   record Subuniverse : Type(ov (ฮฑ โ โ)) where
    constructor mksub
    field
     sset  : Pred A โ
     isSub : sset โ Subuniverses

   -- Subuniverse Generation
   data Sg (G : Pred A โ) : Pred A (๐ โ ๐ฅ โ ฮฑ โ โ) where
    var : โ {v} โ v โ G โ v โ Sg G
    app : โ f a โ Im a โ Sg G โ (f ฬ ๐จ) a โ Sg G

(The inferred types in the ``app`` constructor are ``f : โฃ ๐ โฃ`` and
``a : โฅ ๐ โฅ ๐ โ โฃ ๐จ โฃ``.)

Given an arbitrary subset ``X`` of the domain ``โฃ ๐จ โฃ`` of an ``๐``-algebra ``๐จ``,
the type ``Sg X`` does indeed represent a subuniverse of ``๐จ``. Proving this using
the inductive type ``Sg`` is trivial, as we see here.

::

   sgIsSub : {G : Pred A โ} โ Sg G โ Subuniverses
   sgIsSub = app

Next we prove by structural induction that ``Sg X`` is the smallest subuniverse
of ``๐จ`` containing ``X``.

::

   sgIsSmallest :  {G : Pred A ฯแต}(B : Pred A ฯแต)
    โ              B โ Subuniverses  โ  G โ B  โ  Sg G โ B

   sgIsSmallest _ _ GโB (var Gx) = GโB Gx
   sgIsSmallest B BโคA GโB {.((f ฬ ๐จ) a)} (app f a SgGa) = Goal
    where
    IH : Im a โ B
    IH i = sgIsSmallest B BโคA GโB (SgGa i)

    Goal : (f ฬ ๐จ) a โ B
    Goal = BโคA f a IH

When the element of ``Sg G`` is constructed as ``app f a SgGa``, we may assume
(the induction hypothesis) that the arguments in the tuple ``a`` belong to ``B``.
Then the result of applying ``f`` to ``a`` also belongs to ``B`` since ``B`` is
a subuniverse.

::

  module _ {๐จ : Algebra ฮฑ ฯแต} where
   private A = ๐[ ๐จ ]

   โs :  {ฮน : Level}(I : Type ฮน){ฯ : Level}{๐ : I โ Pred A ฯ}
    โ    (โ i โ ๐ i โ Subuniverses ๐จ) โ โ I ๐ โ Subuniverses ๐จ

   โs I ฯ f a ฮฝ = ฮป i โ ฯ i f a (ฮป x โ ฮฝ x i)


In the proof above, we assume the following typing judgments:

.. code:: agda

   ฮฝ  : Im a โ โ I ๐
   a  : โฅ ๐ โฅ f โ Setoid.Subalgebras.A ๐จ
   f  : โฃ ๐ โฃ
   ฯ  : (i : I) โ ๐ i โ Subuniverses ๐จ

and we must prove ``(f ฬ ๐จ) a โ โ I ๐``. When we did this with the old Algebra
type, Agda could fill in the proof term ``ฮป i โ ฯ i f a (ฮป x โ ฮฝ x i)``
automatically using ``C-c C-a``, but this doesn't work for Algebra as we've
implemented it. We get the error "Agsy does not support copatterns yet."
We should fix the implementation to resolve this.

::

  module _ {๐จ : Algebra ฮฑ ฯแต} where
   private A = ๐[ ๐จ ]
   open Setoid using ( Carrier )
   open Environment ๐จ
   open Func renaming ( f to _โจ$โฉ_ )

   -- subuniverses are closed under the action of term operations
   sub-term-closed :  (B : Pred A โ)
    โ                 (B โ Subuniverses ๐จ)
    โ                 (t : Term X)
    โ                 (b : Carrier (Env X))
    โ                 (โ x โ (b x โ B)) โ (โฆ t โง โจ$โฉ b) โ B

   sub-term-closed _ _ (โ x) b Bb = Bb x
   sub-term-closed B BโคA (node f t)b ฮฝ =
    BโคA f  (ฮป z โ โฆ t z โง โจ$โฉ b) ฮป x โ sub-term-closed B BโคA (t x) b ฮฝ

In the induction step of the foregoing proof, the typing judgments of
the premise are the following:

.. code:: agda

   ฮฝ  : (x : X) โ b x โ B
   b  : Setoid.Carrier (Env X)
   t  : โฅ ๐ โฅ f โ Term X
   f  : โฃ ๐ โฃ
   ฯ  : B โ Subuniverses ๐จ
   B  : Pred A ฯ
   ฯ  : Level
   ๐จ  : Algebra ฮฑ ฯแต

and the given proof term establishes the goal ``โฆ node f t โง โจ$โฉ b โ B``.

Alternatively, we could express the preceeding fact using an inductive type
representing images of terms.

::

   data TermImage (B : Pred A ฯแต) : Pred A (๐ โ ๐ฅ โ ฮฑ โ ฯแต) where
    var : โ {b : A} โ b โ B โ b โ TermImage B
    app : โ f ts โ  ((i : โฅ ๐ โฅ f) โ ts i โ TermImage B)  โ (f ฬ ๐จ) ts โ TermImage B

   -- `TermImage B` is a subuniverse of ๐จ that contains B.
   TermImageIsSub : {B : Pred A ฯแต} โ TermImage B โ Subuniverses ๐จ
   TermImageIsSub = app

   B-onlyif-TermImageB : {B : Pred A ฯแต} โ B โ TermImage B
   B-onlyif-TermImageB Ba = var Ba

   -- Since `Sg B` is the smallest subuniverse containing B, we obtain the following inclusion.
   SgB-onlyif-TermImageB : (B : Pred A ฯแต) โ Sg ๐จ B โ TermImage B
   SgB-onlyif-TermImageB B = sgIsSmallest ๐จ (TermImage B) TermImageIsSub B-onlyif-TermImageB


A basic but important fact about homomorphisms is that they are uniquely
determined by the values they take on a generating set. This is the
content of the next theorem, which we call ``hom-unique``.

::

   module _ {๐ฉ : Algebra ฮฒ ฯแต} (gh hh : hom ๐จ ๐ฉ) where
    open Algebra ๐ฉ  using ( Interp )  renaming (Domain to B )
    open Setoid B   using ( _โ_ ; sym )
    open Func       using ( cong )    renaming (f to _โจ$โฉ_ )
    open SetoidReasoning B

    private
     g = _โจ$โฉ_ โฃ gh โฃ
     h = _โจ$โฉ_ โฃ hh โฃ

    open IsHom
    open Environment ๐ฉ

    hom-unique :  (G : Pred A โ) โ ((x : A) โ (x โ G โ g x โ h x))
     โ            (a : A) โ (a โ Sg ๐จ G โ g a โ h a)

    hom-unique G ฯ a (var Ga) = ฯ a Ga
    hom-unique G ฯ .((f ฬ ๐จ) a) (app f a SgGa) = Goal
     where
     IH : โ i โ h (a i) โ g (a i)
     IH i = sym (hom-unique G ฯ (a i) (SgGa i))

     Goal : g ((f ฬ ๐จ) a) โ h ((f ฬ ๐จ) a)
     Goal =  begin
             g ((f ฬ ๐จ) a)   โโจ compatible โฅ gh โฅ โฉ
             (f ฬ ๐ฉ)(g โ a ) โหโจ cong Interp (refl , IH) โฉ
             (f ฬ ๐ฉ)(h โ a)  โหโจ compatible โฅ hh โฅ โฉ
             h ((f ฬ ๐จ) a )  โ

In the induction step, the following typing judgments are assumed:

.. code:: agda

   SgGa : Im a โ Sg ๐จ G
   a    : โฅ ๐ โฅ f โ Subuniverses ๐จ
   f    : โฃ ๐ โฃ
   ฯ    : (x : A) โ x โ G โ g x โ h x
   G    : Pred A โ
   hh   : hom ๐จ ๐ฉ
   gh   : hom ๐จ ๐ฉ

and, under these assumptions, we proved ``g ((f ฬ ๐จ) a) โ h ((f ฬ ๐จ) a)``.
