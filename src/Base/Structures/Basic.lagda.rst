.. FILE      : Base/Structures/Basic.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 20 May 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-structures-basic-definitions:

Basic Definitions
~~~~~~~~~~~~~~~~~

This is the `Base.Structures.Basic`_ module of the `Agda Universal Algebra Library`_.
It is a submodule of the `Base.Structures`_ module which presents general
(relational-algebraic) structures as inhabitants of record types.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Structures.Basic  where

  -- Imports from Agda and the Agda Standard Library -----------------------------
  open import Agda.Primitive        using () renaming ( Set to Type )
  open import Function.Base         using ( flip ; _â_ )
  open import Level                 using ( _â_ ; suc ; Level )
  open import Relation.Binary.Core  using () renaming ( Rel to BinRel )

  -- Imports from the Agda Universal Algebra Library -----------------------------
  open import Overture              using ( Op )
  open import Base.Relations        using ( _|:_ ; _preserves_ ; Rel )

  private variable ðâ ð¥â ðâ ð¥â : Level

  -- Signature as a record type
  record signature (ð ð¥ : Level) : Type (suc (ð â ð¥)) where
   field
    symbol : Type ð
    arity : symbol â Type ð¥

  siglË¡ : {ð ð¥ : Level} â signature ð ð¥ â Level
  siglË¡ {ð}{ð¥} _ = ð

  siglÊ³ : {ð ð¥ : Level} â signature ð ð¥ â Level
  siglÊ³ {ð}{ð¥} _ = ð¥

  sigl : {ð ð¥ : Level} â signature ð ð¥ â Level
  sigl {ð}{ð¥} _ = ð â ð¥

  open signature public

  record structure  (ð¹ : signature ðâ ð¥â)
                    (ð : signature ðâ ð¥â)
                    {Î± Ï : Level} : Type (ðâ â ð¥â â ðâ â ð¥â â (suc (Î± â Ï)))
   where
   field
    carrier : Type Î±
    op   : â(f : symbol ð¹) â Op  carrier (arity ð¹ f)      -- interpret. of operations
    rel  : â(r : symbol ð) â Rel carrier (arity ð r) {Ï}  -- interpret. of relations

   -- Forgetful Functor
   ð : Type Î±
   ð = carrier

  open structure public

  module _ {ð¹ : signature ðâ ð¥â}{ð : signature ðâ ð¥â} where
   -- Syntactic sugar for interpretation of operation
   _Ê³_ :  â{Î± Ï} â (r : symbol ð)(ð : structure ð¹ ð {Î±}{Ï})
    â     Rel (carrier ð) ((arity ð) r) {Ï}
   _Ê³_ = flip rel

   _áµ_ :  â{Î± Ï} â (f : symbol ð¹)(ð : structure ð¹ ð {Î±}{Ï})
    â     Op (carrier ð)((arity ð¹) f)
   _áµ_ = flip op

   compatible :  â{Î± Ï â} â (ð¨ : structure ð¹ ð {Î±}{Ï})
    â            BinRel (carrier ð¨) â â Type _
   compatible ð¨ r = â (f : symbol ð¹) â (f áµ ð¨) |: r

   open Level

   -- lift an operation to act on type of higher universe level
   Lift-op :  â{Î¹ Î±} â {I : Type Î¹}{A : Type Î±}
    â         Op A I â {â : Level} â Op (Lift â A) I

   Lift-op f = Î» z â lift (f (lower â z))

   -- lift a relation to a predicate on type of higher universe level
   -- (note Ï doesn't change; see Lift-StructÊ³ for that)
   Lift-rel :  â{Î¹ Î± Ï} â {I : Type Î¹}{A : Type Î±}
    â          Rel A I {Ï} â {â : Level} â Rel (Lift â A) I{Ï}

   Lift-rel r x = r (lower â x)

   -- lift the domain of a structure to live in a type at a higher universe level
   Lift-StrucË¡ :  â{Î± Ï} â (â : Level)
    â             structure ð¹ ð {Î±}{Ï} â structure ð¹ ð  {Î± â â}{Ï}

   Lift-StrucË¡ â ð¨ = record  { carrier = Lift â (carrier ð¨)
                             ; op = Î» f â Lift-op (f áµ ð¨)
                             ; rel = Î» R â Lift-rel (R Ê³ ð¨)
                             }

   -- lift the relations of a structure from level Ï to level Ï â â
   Lift-StrucÊ³ :  â{Î± Ï} â (â : Level)
    â             structure ð¹ ð {Î±}{Ï} â structure ð¹ ð {Î±}{Ï â â}

   Lift-StrucÊ³ â ð¨ = record { carrier = carrier ð¨ ; op = op ð¨ ; rel = lrel }
    where
    lrel : (r : symbol ð) â Rel (carrier ð¨) ((arity ð) r)
    lrel r = Lift â â r Ê³ ð¨

   -- lift both domain of structure and the level of its relations
   Lift-Struc :  â{Î± Ï} â (âË¡ âÊ³ : Level)
    â            structure ð¹ ð {Î±}{Ï} â structure ð¹ ð {Î± â âË¡}{Ï â âÊ³}

   Lift-Struc âË¡ âÊ³ ð¨ = Lift-StrucÊ³ âÊ³ (Lift-StrucË¡ âË¡ ð¨)
