.. FILE      : Setoid/Varieties/Preservation.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 18 Jul 2021
.. UPDATED   : 22 Jun 2022

.. highlight:: agda
.. role:: code

.. _equation-preservation-for-setoid-algebras:

Equation preservation for setoid algebras
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Varieties.Preservation`_ module of the `Agda Universal Algebra Library`_
where we show that the classes `H 𝒦`, `S 𝒦`, `P 𝒦`, and `V 𝒦` satisfy the same identities.


.. :raw-latex:`\af `H :raw-latex:`\ab{𝒦}`, :raw-latex:`\af `S
   :raw-latex:`\ab{𝒦}`, :raw-latex:`\af `P :raw-latex:`\ab{𝒦}`, and
   :raw-latex:`\af `V :raw-latex:`\ab{𝒦}` satisfy the same identities.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (𝓞 ; 𝓥 ; Signature)

  module Setoid.Varieties.Preservation {𝑆 : Signature 𝓞 𝓥} where

  -- Imports from Agda and the Agda Standard Library -------------------------------
  open import Agda.Primitive         using ()       renaming ( Set to Type )
  open import Data.Product           using ( _,_ )
                                     renaming ( proj₁ to fst ; proj₂ to snd )
  open import Data.Unit.Polymorphic  using ( ⊤ )
  open import Function               using ( _∘_ )  renaming ( Func to _⟶_ )
  open import Level                  using ( Level ; _⊔_ )
  open import Relation.Binary        using ( Setoid )
  open import Relation.Unary         using ( Pred ; _⊆_ ; _∈_ )

  import Relation.Binary.Reasoning.Setoid as SetoidReasoning

  -- Imports from the Agda Universal Algebra Library -------------------------------
  open  import Overture using ( ∣_∣ ; ∥_∥ )
  open  import Setoid.Functions
        using ( IsSurjective ; SurjInv ; SurjInvIsInverseʳ )

  open  import Base.Terms {𝑆 = 𝑆} using ( Term )

  open  import Setoid.Algebras {𝑆 = 𝑆}
        using ( Algebra ; ov ; 𝕌[_] ; Lift-Alg ; ⨅ )

  open  import Setoid.Homomorphisms {𝑆 = 𝑆}
        using ( ≅⨅⁺-refl ; ≅-refl ; IdHomImage ; ≅-sym )

  open  import Setoid.Terms {𝑆 = 𝑆}
        using ( module Environment; comm-hom-term )

  open  import Setoid.Subalgebras {𝑆 = 𝑆}
        using ( _≤_ ; _≤c_ ; ⨅-≤ ; ≅-trans-≤ ; ≤-reflexive )

  open  import Setoid.Varieties.Closure {𝑆 = 𝑆}
        using ( H ; S ; P ; S-expa ; H-expa ; V ; P-expa ; V-expa ;Level-closure )

  open  import Setoid.Varieties.Properties {𝑆 = 𝑆}
        using ( ⊧-H-invar ; ⊧-S-invar ; ⊧-P-invar ; ⊧-I-invar )

  open  import Setoid.Varieties.SoundAndComplete {𝑆 = 𝑆}
        using ( _⊧_ ; _⊨_ ; _⊫_ ; Eq ; _≈̇_ ; lhs ; rhs ; _⊢_▹_≈_ ; Th)

  open _⟶_      using ( cong ) renaming ( f to _⟨$⟩_ )
  open Algebra  using ( Domain )


.. _closure-properties:

Closure properties
^^^^^^^^^^^^^^^^^^

The types defined above represent operators with useful closure
properties. We now prove a handful of such properties that we need
later.

::

  module _  {α ρᵃ ℓ : Level}{𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
   private
    a = α ⊔ ρᵃ
    oaℓ = ov (a ⊔ ℓ)

   S⊆SP : ∀{ι} → S ℓ 𝒦 ⊆ S {β = α}{ρᵃ} (a ⊔ ℓ ⊔ ι) (P {β = α}{ρᵃ} ℓ ι 𝒦)
   S⊆SP {ι} (𝑨 , (kA , B≤A )) = 𝑨 , (pA , B≤A)
    where
    pA : 𝑨 ∈ P ℓ ι 𝒦
    pA = ⊤ , (λ _ → 𝑨) , (λ _ → kA) , ≅⨅⁺-refl

   P⊆SP : ∀{ι} → P ℓ ι 𝒦 ⊆ S (a ⊔ ℓ ⊔ ι) (P {β = α}{ρᵃ}ℓ ι 𝒦)
   P⊆SP {ι} x = S-expa{ℓ = a ⊔ ℓ ⊔ ι} x


   P⊆HSP : ∀{ι} →  P {β = α}{ρᵃ} ℓ ι 𝒦
                   ⊆ H (a ⊔ ℓ ⊔ ι) (S {β = α}{ρᵃ}(a ⊔ ℓ ⊔ ι) (P {β = α}{ρᵃ}ℓ ι 𝒦))
   P⊆HSP {ι} x = H-expa{ℓ = a ⊔ ℓ ⊔ ι}  (S-expa{ℓ = a ⊔ ℓ ⊔ ι} x)

   P⊆V : ∀{ι} → P ℓ ι 𝒦 ⊆ V ℓ ι 𝒦
   P⊆V = P⊆HSP

   SP⊆V : ∀{ι} → S{β = α}{ρᵇ = ρᵃ} (a ⊔ ℓ ⊔ ι) (P {β = α}{ρᵃ} ℓ ι 𝒦) ⊆ V ℓ ι 𝒦
   SP⊆V {ι} x = H-expa{ℓ = a ⊔ ℓ ⊔ ι} x


Finally, we are in a position to prove that a product of subalgebras of
algebras in a class 𝒦 is a subalgebra of a product of algebras in 𝒦.

::

   PS⊆SP : P (a ⊔ ℓ) oaℓ (S{β = α}{ρᵃ} ℓ 𝒦) ⊆ S oaℓ (P ℓ oaℓ 𝒦)
   PS⊆SP {𝑩} (I , ( 𝒜 , sA , B≅⨅A )) = Goal
    where
    ℬ : I → Algebra α ρᵃ
    ℬ i = ∣ sA i ∣
    kB : (i : I) → ℬ i ∈ 𝒦
    kB i =  fst ∥ sA i ∥
    ⨅A≤⨅B : ⨅ 𝒜 ≤ ⨅ ℬ
    ⨅A≤⨅B = ⨅-≤ λ i → snd ∥ sA i ∥
    Goal : 𝑩 ∈ S{β = oaℓ}{oaℓ}oaℓ (P {β = oaℓ}{oaℓ} ℓ oaℓ 𝒦)
    Goal = ⨅ ℬ , (I , (ℬ , (kB , ≅-refl))) , (≅-trans-≤ B≅⨅A ⨅A≤⨅B)

.. _h-preserves-identities:

H preserves identities
^^^^^^^^^^^^^^^^^^^^^^

First we prove that the closure operator H is compatible with identities
that hold in the given class.

::

  module _   {α ρᵃ ℓ χ : Level}
             {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)}
             {X : Type χ}
             {p q : Term X}
             where

   H-id1 : 𝒦 ⊫ (p ≈̇ q) → H {β = α}{ρᵃ}ℓ 𝒦 ⊫ (p ≈̇ q)
   H-id1 σ 𝑩 (𝑨 , kA , BimgA) = ⊧-H-invar{p = p}{q} (σ 𝑨 kA) BimgA

The converse of the foregoing result is almost too obvious to bother
with. Nonetheless, we formalize it for completeness.

::

   H-id2 : H ℓ 𝒦 ⊫ (p ≈̇ q) → 𝒦 ⊫ (p ≈̇ q)
   H-id2 Hpq 𝑨 kA = Hpq 𝑨 (𝑨 , (kA , IdHomImage))

.. _s-preserves-identities:

S preserves identities
^^^^^^^^^^^^^^^^^^^^^^

::

   S-id1 : 𝒦 ⊫ (p ≈̇ q) → (S {β = α}{ρᵃ} ℓ 𝒦) ⊫ (p ≈̇ q)
   S-id1 σ 𝑩 (𝑨 , kA , B≤A) = ⊧-S-invar{p = p}{q} (σ 𝑨 kA) B≤A

   S-id2 : S ℓ 𝒦 ⊫ (p ≈̇ q) → 𝒦 ⊫ (p ≈̇ q)
   S-id2 Spq 𝑨 kA = Spq 𝑨 (𝑨 , (kA , ≤-reflexive))

.. _p-preserves-identities:

P preserves identities
^^^^^^^^^^^^^^^^^^^^^^

::

   P-id1 : ∀{ι} → 𝒦 ⊫ (p ≈̇ q) → P {β = α}{ρᵃ}ℓ ι 𝒦 ⊫ (p ≈̇ q)
   P-id1 σ 𝑨 (I , 𝒜 , kA , A≅⨅A) = ⊧-I-invar 𝑨 p q IH (≅-sym A≅⨅A)
    where
    ih : ∀ i → 𝒜 i ⊧ (p ≈̇ q)
    ih i = σ (𝒜 i) (kA i)
    IH : ⨅ 𝒜 ⊧ (p ≈̇ q)
    IH = ⊧-P-invar {p = p}{q} 𝒜 ih

   P-id2 : ∀{ι} → P ℓ ι 𝒦 ⊫ (p ≈̇ q) → 𝒦 ⊫ (p ≈̇ q)
   P-id2{ι} PKpq 𝑨 kA = PKpq 𝑨 (P-expa {ℓ = ℓ}{ι} kA)


.. _v-preserves-identities:

V preserves identities
^^^^^^^^^^^^^^^^^^^^^^

Finally, we prove the analogous preservation lemmas for the closure
operator ``V``.

::

  module _  {α ρᵃ ℓ ι χ : Level}
            {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)}
            {X : Type χ}
            {p q : Term X} where

   private aℓι = α ⊔ ρᵃ ⊔ ℓ ⊔ ι

   V-id1 : 𝒦 ⊫ (p ≈̇ q) → V ℓ ι 𝒦 ⊫ (p ≈̇ q)
   V-id1 σ 𝑩 (𝑨 , (⨅A , p⨅A , A≤⨅A) , BimgA) =
    H-id1{ℓ = aℓι}{𝒦 = S aℓι (P {β = α}{ρᵃ}ℓ ι 𝒦)}{p = p}{q} spK⊧pq 𝑩 (𝑨 , (spA , BimgA))
     where
     spA : 𝑨 ∈ S aℓι (P {β = α}{ρᵃ}ℓ ι 𝒦)
     spA = ⨅A , (p⨅A , A≤⨅A)
     spK⊧pq : S aℓι (P ℓ ι 𝒦) ⊫ (p ≈̇ q)
     spK⊧pq = S-id1{ℓ = aℓι}{p = p}{q} (P-id1{ℓ = ℓ} {𝒦 = 𝒦}{p = p}{q} σ)

   V-id2 : V ℓ ι 𝒦 ⊫ (p ≈̇ q) → 𝒦 ⊫ (p ≈̇ q)
   V-id2 Vpq 𝑨 kA = Vpq 𝑨 (V-expa ℓ ι kA)

   Lift-id1 : ∀{β ρᵇ} → 𝒦 ⊫ (p ≈̇ q) → Level-closure{α}{ρᵃ}{β}{ρᵇ} ℓ 𝒦 ⊫ (p ≈̇ q)
   Lift-id1 pKq 𝑨 (𝑩 , kB , B≅A) ρ = Goal
    where
    open Environment 𝑨
    open Setoid (Domain 𝑨) using (_≈_)
    Goal : ⟦ p ⟧ ⟨$⟩ ρ ≈ ⟦ q ⟧ ⟨$⟩ ρ
    Goal = ⊧-I-invar 𝑨 p q (pKq 𝑩 kB) B≅A ρ

.. _class-identities:

Class identities
^^^^^^^^^^^^^^^^

From ``V-id1`` it follows that if 𝒦 is a class of structures, then the
set of identities modeled by all structures in ``𝒦`` is equivalent to
the set of identities modeled by all structures in ``V 𝒦``. In other
terms, ``Th (V 𝒦)`` is precisely the set of identities modeled by ``𝒦``.
We formalize this observation as follows.

::

   classIds-⊆-VIds : 𝒦 ⊫ (p ≈̇ q)  → (p , q) ∈ Th (V ℓ ι 𝒦)
   classIds-⊆-VIds pKq 𝑨 = V-id1 pKq 𝑨

   VIds-⊆-classIds : (p , q) ∈ Th (V ℓ ι 𝒦) → 𝒦 ⊫ (p ≈̇ q)
   VIds-⊆-classIds Thpq 𝑨 kA = V-id2 Thpq 𝑨 kA
