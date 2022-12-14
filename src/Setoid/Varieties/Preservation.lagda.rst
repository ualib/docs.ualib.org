.. FILE      : Setoid/Varieties/Preservation.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 18 Jul 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _setoid-varieties-equation-preservation-for-setoid-algebras:

Equation preservation for setoid algebras
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Varieties.Preservation`_ module of the `Agda Universal Algebra Library`_
where we show that the classes `H π¦`, `S π¦`, `P π¦`, and `V π¦` satisfy the same identities.


.. :raw-latex:`\af `H :raw-latex:`\ab{π¦}`, :raw-latex:`\af `S
   :raw-latex:`\ab{π¦}`, :raw-latex:`\af `P :raw-latex:`\ab{π¦}`, and
   :raw-latex:`\af `V :raw-latex:`\ab{π¦}` satisfy the same identities.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (π ; π₯ ; Signature)

  module Setoid.Varieties.Preservation {π : Signature π π₯} where

  -- Imports from Agda and the Agda Standard Library -------------------------------
  open import Agda.Primitive         using ()       renaming ( Set to Type )
  open import Data.Product           using ( _,_ )
                                     renaming ( projβ to fst ; projβ to snd )
  open import Data.Unit.Polymorphic  using ( β€ )
  open import Function               using ( _β_ )  renaming ( Func to _βΆ_ )
  open import Level                  using ( Level ; _β_ )
  open import Relation.Binary        using ( Setoid )
  open import Relation.Unary         using ( Pred ; _β_ ; _β_ )

  import Relation.Binary.Reasoning.Setoid as SetoidReasoning

  -- Imports from the Agda Universal Algebra Library -------------------------------
  open  import Overture using ( β£_β£ ; β₯_β₯ )
  open  import Setoid.Functions
        using ( IsSurjective ; SurjInv ; SurjInvIsInverseΚ³ )

  open  import Base.Terms {π = π} using ( Term )

  open  import Setoid.Algebras {π = π}
        using ( Algebra ; ov ; π[_] ; Lift-Alg ; β¨ )

  open  import Setoid.Homomorphisms {π = π}
        using ( ββ¨βΊ-refl ; β-refl ; IdHomImage ; β-sym )

  open  import Setoid.Terms {π = π}
        using ( module Environment; comm-hom-term )

  open  import Setoid.Subalgebras {π = π}
        using ( _β€_ ; _β€c_ ; β¨-β€ ; β-trans-β€ ; β€-reflexive )

  open  import Setoid.Varieties.Closure {π = π}
        using ( H ; S ; P ; S-expa ; H-expa ; V ; P-expa ; V-expa ;Level-closure )

  open  import Setoid.Varieties.Properties {π = π}
        using ( β§-H-invar ; β§-S-invar ; β§-P-invar ; β§-I-invar )

  open  import Setoid.Varieties.SoundAndComplete {π = π}
        using ( _β§_ ; _β¨_ ; _β«_ ; Eq ; _βΜ_ ; lhs ; rhs ; _β’_βΉ_β_ ; Th)

  open _βΆ_      using ( cong ) renaming ( f to _β¨$β©_ )
  open Algebra  using ( Domain )


.. _setoid-varieties-closure-properties:

Closure properties
^^^^^^^^^^^^^^^^^^

The types defined above represent operators with useful closure
properties. We now prove a handful of such properties that we need
later.

::

  module _  {Ξ± Οα΅ β : Level}{π¦ : Pred(Algebra Ξ± Οα΅) (Ξ± β Οα΅ β ov β)} where
   private
    a = Ξ± β Οα΅
    oaβ = ov (a β β)

   SβSP : β{ΞΉ} β S β π¦ β S {Ξ² = Ξ±}{Οα΅} (a β β β ΞΉ) (P {Ξ² = Ξ±}{Οα΅} β ΞΉ π¦)
   SβSP {ΞΉ} (π¨ , (kA , Bβ€A )) = π¨ , (pA , Bβ€A)
    where
    pA : π¨ β P β ΞΉ π¦
    pA = β€ , (Ξ» _ β π¨) , (Ξ» _ β kA) , ββ¨βΊ-refl

   PβSP : β{ΞΉ} β P β ΞΉ π¦ β S (a β β β ΞΉ) (P {Ξ² = Ξ±}{Οα΅}β ΞΉ π¦)
   PβSP {ΞΉ} x = S-expa{β = a β β β ΞΉ} x


   PβHSP : β{ΞΉ} β  P {Ξ² = Ξ±}{Οα΅} β ΞΉ π¦
                   β H (a β β β ΞΉ) (S {Ξ² = Ξ±}{Οα΅}(a β β β ΞΉ) (P {Ξ² = Ξ±}{Οα΅}β ΞΉ π¦))
   PβHSP {ΞΉ} x = H-expa{β = a β β β ΞΉ}  (S-expa{β = a β β β ΞΉ} x)

   PβV : β{ΞΉ} β P β ΞΉ π¦ β V β ΞΉ π¦
   PβV = PβHSP

   SPβV : β{ΞΉ} β S{Ξ² = Ξ±}{Οα΅ = Οα΅} (a β β β ΞΉ) (P {Ξ² = Ξ±}{Οα΅} β ΞΉ π¦) β V β ΞΉ π¦
   SPβV {ΞΉ} x = H-expa{β = a β β β ΞΉ} x


Finally, we are in a position to prove that a product of subalgebras of
algebras in a class π¦ is a subalgebra of a product of algebras in π¦.

::

   PSβSP : P (a β β) oaβ (S{Ξ² = Ξ±}{Οα΅} β π¦) β S oaβ (P β oaβ π¦)
   PSβSP {π©} (I , ( π , sA , Bββ¨A )) = Goal
    where
    β¬ : I β Algebra Ξ± Οα΅
    β¬ i = β£ sA i β£
    kB : (i : I) β β¬ i β π¦
    kB i =  fst β₯ sA i β₯
    β¨Aβ€β¨B : β¨ π β€ β¨ β¬
    β¨Aβ€β¨B = β¨-β€ Ξ» i β snd β₯ sA i β₯
    Goal : π© β S{Ξ² = oaβ}{oaβ}oaβ (P {Ξ² = oaβ}{oaβ} β oaβ π¦)
    Goal = β¨ β¬ , (I , (β¬ , (kB , β-refl))) , (β-trans-β€ Bββ¨A β¨Aβ€β¨B)

.. _setoid-varieties-h-preserves-identities:

H preserves identities
^^^^^^^^^^^^^^^^^^^^^^

First we prove that the closure operator H is compatible with identities
that hold in the given class.

::

  module _   {Ξ± Οα΅ β Ο : Level}
             {π¦ : Pred(Algebra Ξ± Οα΅) (Ξ± β Οα΅ β ov β)}
             {X : Type Ο}
             {p q : Term X}
             where

   H-id1 : π¦ β« (p βΜ q) β H {Ξ² = Ξ±}{Οα΅}β π¦ β« (p βΜ q)
   H-id1 Ο π© (π¨ , kA , BimgA) = β§-H-invar{p = p}{q} (Ο π¨ kA) BimgA

The converse of the foregoing result is almost too obvious to bother
with. Nonetheless, we formalize it for completeness.

::

   H-id2 : H β π¦ β« (p βΜ q) β π¦ β« (p βΜ q)
   H-id2 Hpq π¨ kA = Hpq π¨ (π¨ , (kA , IdHomImage))

.. _setoid-varieties-s-preserves-identities:

S preserves identities
^^^^^^^^^^^^^^^^^^^^^^

::

   S-id1 : π¦ β« (p βΜ q) β (S {Ξ² = Ξ±}{Οα΅} β π¦) β« (p βΜ q)
   S-id1 Ο π© (π¨ , kA , Bβ€A) = β§-S-invar{p = p}{q} (Ο π¨ kA) Bβ€A

   S-id2 : S β π¦ β« (p βΜ q) β π¦ β« (p βΜ q)
   S-id2 Spq π¨ kA = Spq π¨ (π¨ , (kA , β€-reflexive))

.. _setoid-varieties-p-preserves-identities:

P preserves identities
^^^^^^^^^^^^^^^^^^^^^^

::

   P-id1 : β{ΞΉ} β π¦ β« (p βΜ q) β P {Ξ² = Ξ±}{Οα΅}β ΞΉ π¦ β« (p βΜ q)
   P-id1 Ο π¨ (I , π , kA , Aββ¨A) = β§-I-invar π¨ p q IH (β-sym Aββ¨A)
    where
    ih : β i β π i β§ (p βΜ q)
    ih i = Ο (π i) (kA i)
    IH : β¨ π β§ (p βΜ q)
    IH = β§-P-invar {p = p}{q} π ih

   P-id2 : β{ΞΉ} β P β ΞΉ π¦ β« (p βΜ q) β π¦ β« (p βΜ q)
   P-id2{ΞΉ} PKpq π¨ kA = PKpq π¨ (P-expa {β = β}{ΞΉ} kA)


.. _setoid-varieties-v-preserves-identities:

V preserves identities
^^^^^^^^^^^^^^^^^^^^^^

Finally, we prove the analogous preservation lemmas for the closure
operator ``V``.

::

  module _  {Ξ± Οα΅ β ΞΉ Ο : Level}
            {π¦ : Pred(Algebra Ξ± Οα΅) (Ξ± β Οα΅ β ov β)}
            {X : Type Ο}
            {p q : Term X} where

   private aβΞΉ = Ξ± β Οα΅ β β β ΞΉ

   V-id1 : π¦ β« (p βΜ q) β V β ΞΉ π¦ β« (p βΜ q)
   V-id1 Ο π© (π¨ , (β¨A , pβ¨A , Aβ€β¨A) , BimgA) =
    H-id1{β = aβΞΉ}{π¦ = S aβΞΉ (P {Ξ² = Ξ±}{Οα΅}β ΞΉ π¦)}{p = p}{q} spKβ§pq π© (π¨ , (spA , BimgA))
     where
     spA : π¨ β S aβΞΉ (P {Ξ² = Ξ±}{Οα΅}β ΞΉ π¦)
     spA = β¨A , (pβ¨A , Aβ€β¨A)
     spKβ§pq : S aβΞΉ (P β ΞΉ π¦) β« (p βΜ q)
     spKβ§pq = S-id1{β = aβΞΉ}{p = p}{q} (P-id1{β = β} {π¦ = π¦}{p = p}{q} Ο)

   V-id2 : V β ΞΉ π¦ β« (p βΜ q) β π¦ β« (p βΜ q)
   V-id2 Vpq π¨ kA = Vpq π¨ (V-expa β ΞΉ kA)

   Lift-id1 : β{Ξ² Οα΅} β π¦ β« (p βΜ q) β Level-closure{Ξ±}{Οα΅}{Ξ²}{Οα΅} β π¦ β« (p βΜ q)
   Lift-id1 pKq π¨ (π© , kB , BβA) Ο = Goal
    where
    open Environment π¨
    open Setoid (Domain π¨) using (_β_)
    Goal : β¦ p β§ β¨$β© Ο β β¦ q β§ β¨$β© Ο
    Goal = β§-I-invar π¨ p q (pKq π© kB) BβA Ο

.. _setoid-varieties-class-identities:

Class identities
^^^^^^^^^^^^^^^^

From ``V-id1`` it follows that if π¦ is a class of structures, then the
set of identities modeled by all structures in ``π¦`` is equivalent to
the set of identities modeled by all structures in ``V π¦``. In other
terms, ``Th (V π¦)`` is precisely the set of identities modeled by ``π¦``.
We formalize this observation as follows.

::

   classIds-β-VIds : π¦ β« (p βΜ q)  β (p , q) β Th (V β ΞΉ π¦)
   classIds-β-VIds pKq π¨ = V-id1 pKq π¨

   VIds-β-classIds : (p , q) β Th (V β ΞΉ π¦) β π¦ β« (p βΜ q)
   VIds-β-classIds Thpq π¨ kA = V-id2 Thpq π¨ kA
