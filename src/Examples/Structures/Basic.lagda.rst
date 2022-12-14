.. FILE      : Examples/Structures/Basic.lagda.rst
.. DATE      : 29 Jul 2021
.. UPDATED   : 18 Jun 2022

.. _examples-of-structures:

Examples of Structures
~~~~~~~~~~~~~~~~~~~~~~

This is the `Examples.Structures.Basic`_ module of the agda-algebras_ library.


::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Examples.Structures.Basic where

  open import Agda.Primitive                  using ( Level ) renaming ( Set to Type ; lzero to ℓ₀ )
  open import Data.Product                    using ( _,_ ; _×_  )
  open import Relation.Unary                  using ( Pred ; _∈_ )

  open import Overture                        using ( 𝟚 ; 𝟛 )
  open import Base.Structures                 using ( signature ; structure )
  open import Examples.Structures.Signatures  using ( S001 ; S∅ ; S0001 )

  -- An example of a (purely) algebraic structure is a 3-element meet semilattice.

  SL : structure  S001   -- (one binary operation symbol)
                  S∅     -- (no relation symbols)
                  {ρ = ℓ₀}

  SL = record { carrier = 𝟛
              ; op = λ _ x → meet (x 𝟚.𝟎) (x 𝟚.𝟏)
              ; rel = λ ()
              } where
                meet : 𝟛 → 𝟛 → 𝟛
                meet 𝟛.𝟎 𝟛.𝟎 = 𝟛.𝟎
                meet 𝟛.𝟎 𝟛.𝟏 = 𝟛.𝟎
                meet 𝟛.𝟎 𝟛.𝟐 = 𝟛.𝟎
                meet 𝟛.𝟏 𝟛.𝟎 = 𝟛.𝟎
                meet 𝟛.𝟏 𝟛.𝟏 = 𝟛.𝟏
                meet 𝟛.𝟏 𝟛.𝟐 = 𝟛.𝟎
                meet 𝟛.𝟐 𝟛.𝟎 = 𝟛.𝟎
                meet 𝟛.𝟐 𝟛.𝟏 = 𝟛.𝟎
                meet 𝟛.𝟐 𝟛.𝟐 = 𝟛.𝟐

An example of a (purely) relational structure is the 2 element structure with
the ternary NAE-3-SAT relation, R = S³ - {(0,0,0), (1,1,1)} (where S = {0, 1}).

::

  data NAE3SAT : Pred (𝟚 × 𝟚 × 𝟚) ℓ₀ where
   r1 : (𝟚.𝟎 , 𝟚.𝟎 , 𝟚.𝟏) ∈ NAE3SAT
   r2 : (𝟚.𝟎 , 𝟚.𝟏 , 𝟚.𝟎) ∈ NAE3SAT
   r3 : (𝟚.𝟎 , 𝟚.𝟏 , 𝟚.𝟏) ∈ NAE3SAT
   r4 : (𝟚.𝟏 , 𝟚.𝟎 , 𝟚.𝟎) ∈ NAE3SAT
   r5 : (𝟚.𝟏 , 𝟚.𝟎 , 𝟚.𝟏) ∈ NAE3SAT
   r6 : (𝟚.𝟏 , 𝟚.𝟏 , 𝟚.𝟎) ∈ NAE3SAT

  nae3sat : structure S∅    -- (no operation symbols)
                      S0001 -- (one ternary relation symbol)

  nae3sat = record { carrier = 𝟚
                   ; op = λ ()
                   ; rel = λ _ x → ((x 𝟛.𝟎) , (x 𝟛.𝟏) , (x 𝟛.𝟐)) ∈ NAE3SAT
                   }
