.. FILE      : Base/Structures/Graphs.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 04 Jun 2022
.. UPDATED   : 04 Jun 2022
.. COPYRIGHT : (c) 2022 William DeMeo

.. _graph-structures:

Graph Structures
~~~~~~~~~~~~~~~~

This is the `Base.Structures.Graphs`_ module of the `Agda Universal Algebra Library`_.


N.B. This module differs from `Base.Structures.0Graphs0`_ in that this module is universe
polymorphic; i.e., we do not restrict universe levels (to, e.g., ``ℓ₀``). This
complicates some things; e.g., we must use lift and lower in some places (cf.
[Base/Structures/Graphs0.lagda][]). 

**Definition** (Graph of a structure). Let ``𝑨`` be an ``(𝑅, 𝐹)``-structure
(relations from ``𝑅`` and operations from ``𝐹``). The *graph* of ``𝑨`` is the
structure ``Gr 𝑨`` with the same domain as ``𝑨`` with relations from ``𝑅``
together with a (``k+1``)-ary relation symbol ``G 𝑓`` for each ``𝑓 ∈ 𝐹`` of arity
``k``, which is interpreted in ``Gr 𝑨`` as all tuples ``(t , y) ∈ Aᵏ⁺¹`` such that
``𝑓 t ≡ y``. (See also Definition 2 of :ref:`this paper <https://arxiv.org/pdf/2010.04958v2.pdf)>`__.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Structures.Graphs where

  -- imports from Agda and the Agda Standard Library -------------------------------------------
  open import Agda.Primitive                         using     ( _⊔_ ; lsuc )
                                                     renaming  ( Set to Type ; lzero  to ℓ₀ )
  open import Data.Product                           using     ( _,_ ; Σ-syntax ; _×_ )
  open import Data.Sum.Base                          using     ( _⊎_ )
                                                     renaming  ( inj₁ to inl ; inj₂ to inr )
  open import Data.Unit.Base                         using     ( ⊤ ; tt )
  open import Level                                  using     ( Level ; Lift ; lift ; lower )
  open import Function.Base                          using     ( _∘_  )
  open import Relation.Binary.PropositionalEquality  using     ( _≡_ ; refl ; module ≡-Reasoning ; cong ; sym )

  -- Imports from the Agda Universal Algebra Library ---------------------------------------------
  open import Base.Overture.Preliminaries     using ( ∣_∣ ; _≈_ ; ∥_∥ ; _∙_ ; lower∼lift ; lift∼lower )
  open import Base.Relations.Continuous       using ( Rel )
  open import Base.Structures.Basic           using ( signature ; structure )
  open import Base.Structures.Homs            using ( hom ; 𝒾𝒹 ; ∘-hom ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; is-hom-rel; is-hom-op)
  open import Examples.Structures.Signatures  using ( S∅ )

  open signature
  open structure
  open _⊎_


  Gr-sig : signature ℓ₀ ℓ₀ → signature ℓ₀ ℓ₀ → signature ℓ₀ ℓ₀

  Gr-sig 𝐹 𝑅 = record { symbol = symbol 𝑅 ⊎ symbol 𝐹
                      ; arity  = ar }
   where
   ar : symbol 𝑅 ⊎ symbol 𝐹 → Type _
   ar (inl 𝑟) = (arity 𝑅) 𝑟
   ar (inr 𝑓) = (arity 𝐹) 𝑓 ⊎ ⊤

  private variable
   𝐹 𝑅 : signature ℓ₀ ℓ₀
   α ρ : Level

  Gr : ∀{α ρ} → structure 𝐹 𝑅 {α} {ρ} → structure S∅ (Gr-sig 𝐹 𝑅) {α} {α ⊔ ρ}
  Gr {𝐹}{𝑅}{α}{ρ} 𝑨 = record { carrier = carrier 𝑨 ; op = λ () ; rel = split }
    where
    split : (s : symbol 𝑅 ⊎ symbol 𝐹) → Rel (carrier 𝑨) (arity (Gr-sig 𝐹 𝑅) s) {α ⊔ ρ}
    split (inl 𝑟) arg = Lift α (rel 𝑨 𝑟 arg)
    split (inr 𝑓) args = Lift ρ (op 𝑨 𝑓 (args ∘ inl) ≡ args (inr tt))


  open ≡-Reasoning

  private variable
   ρᵃ β ρᵇ : Level

  module _ {𝑨 : structure 𝐹 𝑅 {α} {ρᵃ}}
           {𝑩 : structure 𝐹 𝑅 {β} {ρᵇ}} where

   hom→Grhom : hom 𝑨 𝑩 → hom (Gr 𝑨) (Gr 𝑩)
   hom→Grhom (h , hhom) = h , (i , ii)
    where
    i : is-hom-rel (Gr 𝑨) (Gr 𝑩) h
    i (inl 𝑟) a x = lift (∣ hhom ∣ 𝑟 a (lower x))
    i (inr 𝑓) a x = lift goal
     where
     homop : h (op 𝑨 𝑓 (a ∘ inl)) ≡ op 𝑩 𝑓 (h ∘ (a ∘ inl))
     homop = ∥ hhom ∥ 𝑓 (a ∘ inl)

     goal : op 𝑩 𝑓 (h ∘ (a ∘ inl)) ≡ h (a (inr tt))
     goal = op 𝑩 𝑓 (h ∘ (a ∘ inl)) ≡⟨ sym homop ⟩
            h (op 𝑨 𝑓 (a ∘ inl))   ≡⟨ cong h (lower x) ⟩
            h (a (inr tt))         ∎

    ii : is-hom-op (Gr 𝑨) (Gr 𝑩) h
    ii = λ ()

   Grhom→hom : hom (Gr 𝑨) (Gr 𝑩) → hom 𝑨 𝑩
   Grhom→hom (h , hhom) = h , (i , ii)
    where
    i : is-hom-rel 𝑨 𝑩 h
    i R a x = lower (∣ hhom ∣ (inl R) a (lift x))
    ii : is-hom-op 𝑨 𝑩 h
    ii f a = goal -- goal
     where
     split : arity 𝐹 f ⊎ ⊤ → carrier 𝑨
     split (inl x) = a x
     split (inr y) = op 𝑨 f a
     goal : h (op 𝑨 f a) ≡ op 𝑩 f (λ x → h (a x))
     goal = sym (lower (∣ hhom ∣ (inr f) split (lift refl)))

----------------------


