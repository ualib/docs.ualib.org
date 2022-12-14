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

  open import Agda.Primitive                  using ( Level ) renaming ( Set to Type ; lzero to āā )
  open import Data.Product                    using ( _,_ ; _Ć_  )
  open import Relation.Unary                  using ( Pred ; _ā_ )

  open import Overture                        using ( š ; š )
  open import Base.Structures                 using ( signature ; structure )
  open import Examples.Structures.Signatures  using ( S001 ; Sā ; S0001 )

  -- An example of a (purely) algebraic structure is a 3-element meet semilattice.

  SL : structure  S001   -- (one binary operation symbol)
                  Sā     -- (no relation symbols)
                  {Ļ = āā}

  SL = record { carrier = š
              ; op = Ī» _ x ā meet (x š.š) (x š.š)
              ; rel = Ī» ()
              } where
                meet : š ā š ā š
                meet š.š š.š = š.š
                meet š.š š.š = š.š
                meet š.š š.š = š.š
                meet š.š š.š = š.š
                meet š.š š.š = š.š
                meet š.š š.š = š.š
                meet š.š š.š = š.š
                meet š.š š.š = š.š
                meet š.š š.š = š.š

An example of a (purely) relational structure is the 2 element structure with
the ternary NAE-3-SAT relation, R = SĀ³ - {(0,0,0), (1,1,1)} (where S = {0, 1}).

::

  data NAE3SAT : Pred (š Ć š Ć š) āā where
   r1 : (š.š , š.š , š.š) ā NAE3SAT
   r2 : (š.š , š.š , š.š) ā NAE3SAT
   r3 : (š.š , š.š , š.š) ā NAE3SAT
   r4 : (š.š , š.š , š.š) ā NAE3SAT
   r5 : (š.š , š.š , š.š) ā NAE3SAT
   r6 : (š.š , š.š , š.š) ā NAE3SAT

  nae3sat : structure Sā    -- (no operation symbols)
                      S0001 -- (one ternary relation symbol)

  nae3sat = record { carrier = š
                   ; op = Ī» ()
                   ; rel = Ī» _ x ā ((x š.š) , (x š.š) , (x š.š)) ā NAE3SAT
                   }
