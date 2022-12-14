.. FILE      : Setoid/Varieties/Properties.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 18 Jul 2021
.. UPDATED   : 22 Jun 2022

.. highlight:: agda
.. role:: code

.. _setoid-varieties-properties-of-the-models-relation:

Properties of the models relation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Subalgebras.Properties`_ module of the `Agda Universal Algebra Library`_.

We prove some closure and invariance properties of the relation ``β§``. In
particular, we prove the following facts (which are needed, for example, in the
proof the Birkhoff HSP Theorem). 

-  `Algebraic invariance <#algebraic-invariance>`__. ``β§`` is an *algebraic
   invariant* (stable under isomorphism).

-  `Subalgebraic invariance <#subalgebraic-invariance>`__. Identities modeled by a
   class of algebras are also modeled by all subalgebras of algebras in the class.

-  `Product invariance <#product-invariance>`__. Identities modeled by a class of
   algebras are also modeled by all products of algebras in the class.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (π ; π₯ ; Signature)

  module Setoid.Varieties.Properties {π : Signature π π₯} where

  -- Imports from Agda and the Agda Standard Library -------------------------------------------
  open import Agda.Primitive   using () renaming ( Set to Type )
  open import Data.Product     using ( _,_ )
  open import Function         using ( _β_ ; Func )
  open import Level            using ( Level )
  open import Relation.Binary  using ( Setoid )
  open import Relation.Unary   using ( Pred ; _β_ )

  import Relation.Binary.Reasoning.Setoid as SetoidReasoning

  -- Imports from the Agda Universal Algebra Library ---------------------------------------------
  open  import Overture                       using  ( β£_β£ ; β₯_β₯ )
  open  import Setoid.Functions               using  ( InvIsInverseΚ³ ; SurjInv )
  open  import Base.Terms            {π = π}  using  ( Term ; β )
  open  import Setoid.Algebras       {π = π}
        using  ( Algebra ; Lift-AlgΛ‘ ; ov ; π[_] ; π»[_] ; β¨ )
  open  import Setoid.Homomorphisms  {π = π}
        using  ( hom ; _β_ ; mkiso ; Lift-βΛ‘ ; β-sym ; _IsHomImageOf_ )
  open  import Setoid.Terms          {π = π}
        using  ( π» ; module Environment ; comm-hom-term ; interp-prod ; term-agreement )
  open  import Setoid.Subalgebras    {π = π}  using  ( _β€_ ; SubalgebrasOfClass )
  open  import Setoid.Varieties.SoundAndComplete {π = π}
        using ( _β§_ ; _β¨_ ; _β«_ ; Eq ; _βΜ_ ; lhs ; rhs ; _β’_βΉ_β_ )

  private variable Ξ± Οα΅ Ξ² Οα΅ Ο β : Level

  open Func     using ( cong ) renaming (f to _β¨$β©_ )
  open Algebra  using ( Domain )


.. _setoid-varieties-algebraic-invariance-of-the-models-relation:

Algebraic invariance of β§
^^^^^^^^^^^^^^^^^^^^^^^^^

The models relation β§ would be practically useless if it were not an *algebraic
invariant* (i.e., invariant under isomorphism), so let us establish this property.

::

  module _ {X : Type Ο}{π¨ : Algebra Ξ± Οα΅}(π© : Algebra Ξ² Οα΅)(p q : Term X) where
   open Environment π¨      using () renaming ( β¦_β§   to β¦_β§β )
   open Environment π©      using () renaming ( β¦_β§   to β¦_β§β )
   open Setoid (Domain π¨)  using () renaming ( _β_   to _ββ_ )
   open Setoid (Domain π©)  using ( _β_ ; sym )
   open SetoidReasoning (Domain π©)

   β§-I-invar : π¨ β§ (p βΜ q)  β  π¨ β π©  β  π© β§ (p βΜ q)
   β§-I-invar Apq (mkiso fh gh fβΌg gβΌf) Ο =
    begin
     β¦ p β§β β¨$β© Ο              βΛβ¨ cong β¦ p β§β (Ξ» x β fβΌg (Ο x)) β©
     β¦ p β§β β¨$β© (f β (g β Ο))  βΛβ¨ comm-hom-term fh p (g β Ο) β©
     f (β¦ p β§β β¨$β© (g β Ο))    ββ¨ cong β£ fh β£ (Apq (g β Ο)) β©
     f (β¦ q β§β β¨$β© (g β Ο))    ββ¨ comm-hom-term fh q (g β Ο) β©
     β¦ q β§β β¨$β© (f β (g β Ο))  ββ¨ cong β¦ q β§β (Ξ» x β fβΌg (Ο x)) β©
     β¦ q β§β β¨$β© Ο              β
    where private f = _β¨$β©_ β£ fh β£ ; g = _β¨$β©_ β£ gh β£

As the proof makes clear, we show ``π© β§ p β q`` by showing that ``π© β¦ p β§ β‘ π© β¦ q β§``
holds *extensionally*, that is, ``β x, π© β¦ p β§ x β‘ π© β¦q β§ x``.

.. _setoid-varieties-lift-invariance-of-models:

Lift-invariance of β§
^^^^^^^^^^^^^^^^^^^^

The models relation, β§, is also invariant under the algebraic lift and lower operations.

::

  module _ {X : Type Ο}{π¨ : Algebra Ξ± Οα΅} where

   β§-Lift-invar : (p q : Term X) β π¨ β§ (p βΜ q) β Lift-AlgΛ‘ π¨ Ξ² β§ (p βΜ q)
   β§-Lift-invar p q Apq = β§-I-invar (Lift-AlgΛ‘ π¨ _) p q Apq Lift-βΛ‘

   β§-lower-invar : (p q : Term X) β Lift-AlgΛ‘ π¨ Ξ² β§ (p βΜ q)  β  π¨ β§ (p βΜ q)
   β§-lower-invar p q lApq = β§-I-invar π¨ p q lApq (β-sym Lift-βΛ‘)

.. _setoid-varieties-homomorphic-invariance-of-models:

Homomorphic invariance of β§
^^^^^^^^^^^^^^^^^^^^^^^^^^^

Identities modeled by an algebra ``π¨`` are also modeled by every homomorphic image
of ``π¨``, which fact can be formalized as follows. 

::

  module _ {X : Type Ο}{π¨ : Algebra Ξ± Οα΅}{π© : Algebra Ξ² Οα΅}{p q : Term X} where

   β§-H-invar : π¨ β§ (p βΜ q) β π© IsHomImageOf π¨ β π© β§ (p βΜ q)
   β§-H-invar Apq (Οh , ΟE) Ο =
    begin
         β¦ p β§   β¨$β©               Ο    βΛβ¨  cong β¦ p β§(Ξ» _ β InvIsInverseΚ³ ΟE)  β©
         β¦ p β§   β¨$β© (Ο β  Οβ»ΒΉ  β  Ο)   βΛβ¨  comm-hom-term Οh p (Οβ»ΒΉ β Ο)        β©
     Ο(  β¦ p β§α΄¬  β¨$β© (     Οβ»ΒΉ  β  Ο))  ββ¨   cong β£ Οh β£ (Apq (Οβ»ΒΉ β Ο))         β©
     Ο(  β¦ q β§α΄¬  β¨$β© (     Οβ»ΒΉ  β  Ο))  ββ¨   comm-hom-term Οh q (Οβ»ΒΉ β Ο)        β©
         β¦ q β§   β¨$β© (Ο β  Οβ»ΒΉ  β  Ο)   ββ¨   cong β¦ q β§(Ξ» _ β InvIsInverseΚ³ ΟE)  β©
         β¦ q β§   β¨$β©               Ο    β
    where
    Οβ»ΒΉ : π[ π© ] β π[ π¨ ]
    Οβ»ΒΉ = SurjInv β£ Οh β£ ΟE
    private Ο = (_β¨$β©_ β£ Οh β£)
    open Environment π¨  using () renaming ( β¦_β§ to β¦_β§α΄¬)
    open Environment π©  using ( β¦_β§ )
    open SetoidReasoning π»[ π© ]

.. _setoid-varieties-subalgebraic-invariance-of-models:

Subalgebraic invariance of β§
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Identities modeled by an algebra ``π¨`` are also modeled by every subalgebra of
``π¨``, which fact can be formalized as follows.

::

  module _ {X : Type Ο}{p q : Term X}{π¨ : Algebra Ξ± Οα΅}{π© : Algebra Ξ² Οα΅} where
   open Environment π¨      using () renaming ( β¦_β§ to β¦_β§β )
   open Environment π©      using () renaming ( β¦_β§ to β¦_β§β )
   open Setoid (Domain π¨)  using ( _β_ )
   open Setoid (Domain π©)  using () renaming ( _β_ to _ββ_ )
   open SetoidReasoning (Domain π¨)

   β§-S-invar : π¨ β§ (p βΜ q) β  π© β€ π¨  β  π© β§ (p βΜ q)
   β§-S-invar Apq Bβ€A b = goal
    where
    hh : hom π© π¨
    hh = β£ Bβ€A β£
    h = _β¨$β©_ β£ hh β£
    ΞΎ : β b β h (β¦ p β§β β¨$β© b) β h (β¦ q β§β β¨$β© b)
    ΞΎ b = begin
           h (β¦ p β§β β¨$β© b)    ββ¨ comm-hom-term hh p b β©
           β¦ p β§β β¨$β© (h β b)  ββ¨ Apq (h β b) β©
           β¦ q β§β β¨$β© (h β b)  βΛβ¨ comm-hom-term hh q b β©
           h (β¦ q β§β β¨$β© b)    β

    goal : β¦ p β§β β¨$β© b ββ β¦ q β§β β¨$β© b
    goal = β₯ Bβ€A β₯ (ΞΎ b)

Next, identities modeled by a class of algebras is also modeled by all subalgebras
of the class. In other terms, every term equation ``(p βΜ q)`` that is satisfied by
all ``π¨ β π¦`` is also satisfied by every subalgebra of a member of ``π¦``.

::

  module _ {X : Type Ο}{p q : Term X} where

   β§-S-class-invar :  {π¦ : Pred (Algebra Ξ± Οα΅) β}
    β                 (π¦ β« (p βΜ q)) β ((π© , _) : SubalgebrasOfClass π¦ {Ξ²}{Οα΅})
    β                 π© β§ (p βΜ q)
   β§-S-class-invar Kpq (π© , π¨ , kA , Bβ€A) = β§-S-invar{p = p}{q} (Kpq π¨ kA) Bβ€A

.. _setoid-varieties-product-invariance-of-models:

Product invariance of β§
^^^^^^^^^^^^^^^^^^^^^^^

An identity satisfied by all algebras in an indexed collection is also
satisfied by the product of algebras in that collection.

::

  module _ {X : Type Ο}{p q : Term X}{I : Type β}(π : I β Algebra Ξ± Οα΅) where

   β§-P-invar : (β i β π i β§ (p βΜ q)) β β¨ π β§ (p βΜ q)
   β§-P-invar πpq a = goal
    where
    open Algebra (β¨ π)      using () renaming ( Domain to β¨A )
    open Environment (β¨ π)  using () renaming ( β¦_β§ to β¦_β§β )
    open Environment        using ( β¦_β§ )
    open Setoid β¨A          using ( _β_ )
    open SetoidReasoning β¨A

    ΞΎ : (Ξ» i β (β¦ π i β§ p) β¨$β© (Ξ» x β (a x) i)) β (Ξ» i β (β¦ π i β§ q) β¨$β© (Ξ» x β (a x) i))
    ΞΎ = Ξ» i β πpq i (Ξ» x β (a x) i)
    goal : β¦ p β§β β¨$β© a β β¦ q β§β β¨$β© a
    goal = begin
            β¦ p β§β β¨$β© a                             ββ¨ interp-prod π p a β©
            (Ξ» i β (β¦ π i β§ p) β¨$β© (Ξ» x β (a x) i))  ββ¨ ΞΎ β©
            (Ξ» i β (β¦ π i β§ q) β¨$β© (Ξ» x β (a x) i))  βΛβ¨ interp-prod π q a β©
            β¦ q β§β β¨$β© a                             β

An identity satisfied by all algebras in a class is also satisfied by the product
of algebras in the class.

::

   β§-P-class-invar :  (π¦ : Pred (Algebra Ξ± Οα΅)(ov Ξ±))
    β                 π¦ β« (p βΜ q) β (β i β π i β π¦) β β¨ π β§ (p βΜ q)

   β§-P-class-invar π¦ Ο Kπ = β§-P-invar (Ξ» i Ο β Ο (π i) (Kπ i) Ο)

Another fact that will turn out to be useful is that a product of a collection of
algebras models (p βΜ q) if the lift of each algebra in the collection models (p βΜ q).

::

   β§-P-lift-invar : (β i β Lift-AlgΛ‘ (π i) Ξ² β§ (p βΜ q))  β  β¨ π β§ (p βΜ q)
   β§-P-lift-invar Ξ± = β§-P-invar Aipq
    where
    Aipq : β i β (π i) β§ (p βΜ q)
    Aipq i = β§-lower-invar{π¨ = (π i)} p q (Ξ± i)

.. _setoid-varieties-homomorphic-invariance-of-1:

Homomorphic invariance of β§
^^^^^^^^^^^^^^^^^^^^^^^^^^^

If an algebra π¨ models an identity (p βΜ q), then the pair (p , q)
belongs to the kernel of every homomorphism Ο : hom (π» X) π¨ from the
term algebra to π¨; that is, every homomorphism from π» X to π¨ maps p and
q to the same element of π¨.

::

  module _ {X : Type Ο}{p q : Term X}{π¨ : Algebra Ξ± Οα΅}(Οh : hom (π» X) π¨) where
   open Setoid (Domain π¨) using ( _β_ )
   private Ο = _β¨$β©_ β£ Οh β£

   β§-H-ker : π¨ β§ (p βΜ q) β Ο p β Ο q
   β§-H-ker Ξ² =
    begin
     Ο p                 ββ¨ cong β£ Οh β£ (term-agreement p)β©
     Ο (β¦ p β§ β¨$β© β)     ββ¨ comm-hom-term Οh p β β©
     β¦ p β§β β¨$β© (Ο β β)  ββ¨ Ξ² (Ο β β) β©
     β¦ q β§β β¨$β© (Ο β β)  βΛβ¨ comm-hom-term Οh q β β©
     Ο (β¦ q β§ β¨$β© β)     βΛβ¨ cong β£ Οh β£ (term-agreement q)β©
     Ο q                 β

    where
    open SetoidReasoning (Domain π¨)
    open Environment π¨      using () renaming ( β¦_β§ to β¦_β§β )
    open Environment (π» X)  using ( β¦_β§ )

