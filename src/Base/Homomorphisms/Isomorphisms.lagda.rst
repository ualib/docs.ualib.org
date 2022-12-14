.. FILE      : Base/Homomorphisms/Isomorphisms.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 11 Jul 2022
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-homomorphisms-isomorphisms:

Isomorphisms
~~~~~~~~~~~~

This is the `Base.Homomorphisms.Isomorphisms`_ module of the
`Agda Universal Algebra Library`_. Here we formalize the informal notion of
isomorphism between algebraic structures.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using ( Signature ; π ; π₯ )

  module Base.Homomorphisms.Isomorphisms {π : Signature π π₯}  where

  -- Imports from Agda and the Agda Standard Library -----------------------------------------------
  open import Agda.Primitive   using () renaming ( Set to Type )
  open import Data.Product     using ( _,_ ; Ξ£-syntax ; _Γ_ )
  open import Function         using ( _β_ )
  open import Level            using ( Level ; _β_ )
  open import Relation.Binary  using ( Reflexive ; Sym ; Symmetric; Trans; Transitive )

  open  import Relation.Binary.PropositionalEquality as β‘
        using ( _β‘_ ; module β‘-Reasoning )

  open  import Axiom.Extensionality.Propositional
        using () renaming (Extensionality to funext )

  -- Imports from the Agda Universal Algebra Library -----------------------------------------------
  open import Overture using ( β£_β£ ; β₯_β₯ ; _β_ ; _β_ ; lowerβΌlift ; liftβΌlower )
  open import Base.Functions using ( IsInjective )

  open import Base.Algebras {π = π} using ( Algebra ; Lift-Alg ; β¨ )

  open import Base.Homomorphisms.Basic {π = π}
   using ( hom ; πΎπΉ ; ππΎπ»π ; πβ΄πβ―π ; is-homomorphism )

  open import Base.Homomorphisms.Properties  {π = π}  using ( β-hom )


.. _base-homomorphisms-definition-of-isomorphism:

Definition of isomorphism
^^^^^^^^^^^^^^^^^^^^^^^^^

Recall, we use ``f β g`` to denote the assertion that ``f`` and ``g`` are *extensionally* (or point-wise) equal; i.e., ``β x, f x β‘ g x``. We use this notion of equality of functions in the following definition of *isomorphism* between two algebras, say, `π¨` and `π©`.

::

  record _β_ {Ξ± Ξ² : Level}(π¨ : Algebra Ξ±)(π© : Algebra Ξ²) : Type (π β π₯ β Ξ± β Ξ²) where
   constructor mkiso
   field
    to : hom π¨ π©
    from : hom π© π¨
    toβΌfrom : β£ to β£ β β£ from β£ β β£ πΎπΉ π© β£
    fromβΌto : β£ from β£ β β£ to β£ β β£ πΎπΉ π¨ β£

  open _β_ public

That is, two structures are *isomorphic* provided there are homomorphisms going
back and forth between them which compose to the identity map.

We could define this using Sigma types, like so.

.. code:: agda

   _β_ : {Ξ± Ξ² : Level}(π¨ : Algebra Ξ±)(π© : Algebra Ξ²) β Type(π β π₯ β Ξ± β Ξ²)
   π¨ β π© =  Ξ£[ f β (hom π¨ π©)] Ξ£[ g β hom π© π¨ ]
            ( (β£ f β£ β β£ g β£ β β£ πΎπΉ π© β£ ) Γ ( β£ g β£ β β£ f β£ β β£ πΎπΉ π¨ β£) )

However, with four components, the equivalent record type defined above is easier
to work with; in particular, equality testing is easily with record types than
with than Sigma types.



.. _base-homomorphisms-isomorphism-is-an-equivalence-relation:

Isomorphism is an equivalence relation
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  private variable Ξ± Ξ² Ξ³ ΞΉ : Level

  β-refl : Reflexive (_β_ {Ξ±})
  β-refl {Ξ±}{π¨} = mkiso (πΎπΉ π¨) (πΎπΉ π¨) (Ξ» _ β β‘.refl) Ξ» _ β β‘.refl

  β-sym : Sym (_β_ {Ξ±}) (_β_ {Ξ²})
  β-sym Ο = mkiso (from Ο) (to Ο) (fromβΌto Ο) (toβΌfrom Ο)

  β-trans : Trans (_β_ {Ξ±})(_β_ {Ξ²})(_β_ {Ξ±}{Ξ³})
  β-trans {Ξ³ = Ξ³}{π¨}{π©}{πͺ} ab bc = mkiso f g Ο Ξ½
   where
    f : hom π¨ πͺ
    f = β-hom π¨ πͺ (to ab) (to bc)
    g : hom πͺ π¨
    g = β-hom πͺ π¨ (from bc) (from ab)

    Ο : β£ f β£ β β£ g β£ β β£ πΎπΉ πͺ β£
    Ο x = (β‘.cong β£ to bc β£(toβΌfrom ab (β£ from bc β£ x)))β(toβΌfrom bc) x

    Ξ½ : β£ g β£ β β£ f β£ β β£ πΎπΉ π¨ β£
    Ξ½ x = (β‘.cong β£ from ab β£(fromβΌto bc (β£ to ab β£ x)))β(fromβΌto ab) x


  -- The "to" map of an isomorphism is injective.
  βtoInjective :  {Ξ± Ξ² : Level}{π¨ : Algebra Ξ±}{π© : Algebra Ξ²}
                  (Ο : π¨ β π©) β IsInjective β£ to Ο β£

  βtoInjective (mkiso (f , _) (g , _) _ gβΌf){a}{b} fafb =
   a        β‘β¨ β‘.sym (gβΌf a) β©
   g (f a)  β‘β¨ β‘.cong g fafb β©
   g (f b)  β‘β¨ gβΌf b β©
   b        β where open β‘-Reasoning


  -- The "from" map of an isomorphism is injective.
  βfromInjective :  {Ξ± Ξ² : Level}{π¨ : Algebra Ξ±}{π© : Algebra Ξ²}
                    (Ο : π¨ β π©) β IsInjective β£ from Ο β£

  βfromInjective Ο = βtoInjective (β-sym Ο)


.. _base-homomorphisms-lift-is-an-algebraic-invariant:

Lift is an algebraic invariant
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Fortunately, the lift operation preserves isomorphism (i.e., it's an *algebraic
invariant*). As our focus is universal algebra, this is important and is what
makes the lift operation a workable solution to the technical problems that arise
from the noncumulativity of Agda's universe hierarchy.

::

  open Level

  Lift-β : {Ξ± Ξ² : Level}{π¨ : Algebra Ξ±} β π¨ β (Lift-Alg π¨ Ξ²)
  Lift-β{Ξ² = Ξ²}{π¨ = π¨} = record  { to = ππΎπ»π π¨
                                 ; from = πβ΄πβ―π π¨
                                 ; toβΌfrom = β‘.cong-app liftβΌlower
                                 ; fromβΌto = β‘.cong-app (lowerβΌlift {Ξ² = Ξ²})
                                 }

  Lift-Alg-iso :  {Ξ± Ξ² : Level}{π¨ : Algebra Ξ±}{π§ : Level}
                  {π© : Algebra Ξ²}{π¨ : Level}
   β              π¨ β π© β (Lift-Alg π¨ π§) β (Lift-Alg π© π¨)

  Lift-Alg-iso AβB = β-trans (β-trans (β-sym Lift-β) AβB) Lift-β


.. _base-homomorphisms-lift-associativity:

Lift associativity
^^^^^^^^^^^^^^^^^^

The lift is also associative, up to isomorphism at least.

::

  Lift-Alg-assoc :  (ββ ββ : Level) {π¨ : Algebra Ξ±}
   β                Lift-Alg π¨ (ββ β ββ) β (Lift-Alg (Lift-Alg π¨ ββ) ββ)

  Lift-Alg-assoc ββ ββ {π¨} = β-trans (β-trans Goal Lift-β) Lift-β
   where
   Goal : Lift-Alg π¨ (ββ β ββ) β π¨
   Goal = β-sym Lift-β


.. _base-homomorphisms-products-preserve-isomorphisms:

Products preserve isomorphisms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Products of isomorphic families of algebras are themselves isomorphic. The proof
looks a bit technical, but it is as straightforward as it ought to be.

::

  module _ {Ξ± Ξ² ΞΉ : Level}{I : Type ΞΉ}{fiu : funext ΞΉ Ξ±}{fiw : funext ΞΉ Ξ²} where

    β¨β :  {π : I β Algebra Ξ±}{β¬ : I β Algebra Ξ²}
     β     (β (i : I) β π i β β¬ i) β β¨ π β β¨ β¬

    β¨β {π}{β¬} AB = record  { to = Ο , Οhom ; from = Ο , Οhom
                           ; toβΌfrom = ΟβΌΟ ; fromβΌto = ΟβΌΟ
                           }
     where
     Ο : β£ β¨ π β£ β β£ β¨ β¬ β£
     Ο a i = β£ to (AB i) β£ (a i)

     Οhom : is-homomorphism (β¨ π) (β¨ β¬) Ο
     Οhom π a = fiw (Ξ» i β β₯ to (AB i) β₯ π (Ξ» x β a x i))

     Ο : β£ β¨ β¬ β£ β β£ β¨ π β£
     Ο b i = β£ from (AB i) β£ (b i)

     Οhom : is-homomorphism (β¨ β¬) (β¨ π) Ο
     Οhom π π = fiu (Ξ» i β β₯ from (AB i) β₯ π (Ξ» x β π x i))

     ΟβΌΟ : Ο β Ο β β£ πΎπΉ (β¨ β¬) β£
     ΟβΌΟ π = fiw Ξ» i β toβΌfrom (AB i) (π i)

     ΟβΌΟ : Ο β Ο β β£ πΎπΉ (β¨ π) β£
     ΟβΌΟ a = fiu Ξ» i β fromβΌto (AB i)(a i)

A nearly identical proof goes through for isomorphisms of lifted products (though,
just for fun, we use the universal quantifier syntax here to express the dependent
function type in the statement of the lemma, instead of the Pi notation we used in
the statement of the previous lemma; that is, ``β i β π i β β¬ (lift i)`` instead of
``Ξ  i κ I , π i β β¬ (lift i)``.)

::

  module _ {Ξ± Ξ² Ξ³ ΞΉ  : Level}{I : Type ΞΉ}{fizw : funext (ΞΉ β Ξ³) Ξ²}{fiu : funext ΞΉ Ξ±} where

    Lift-Alg-β¨β :  {π : I β Algebra Ξ±}{β¬ : (Lift Ξ³ I) β Algebra Ξ²}
     β             (β i β π i β β¬ (lift i)) β Lift-Alg (β¨ π) Ξ³ β β¨ β¬

    Lift-Alg-β¨β {π}{β¬} AB = Goal
     where
     Ο : β£ β¨ π β£ β β£ β¨ β¬ β£
     Ο a i = β£ to (AB  (lower i)) β£ (a (lower i))

     Οhom : is-homomorphism (β¨ π) (β¨ β¬) Ο
     Οhom π a = fizw (Ξ» i β (β₯ to (AB (lower i)) β₯) π (Ξ» x β a x (lower i)))

     Ο : β£ β¨ β¬ β£ β β£ β¨ π β£
     Ο b i = β£ from (AB i) β£ (b (lift i))

     Οhom : is-homomorphism (β¨ β¬) (β¨ π) Ο
     Οhom π π = fiu (Ξ» i β β₯ from (AB i) β₯ π (Ξ» x β π x (lift i)))

     ΟβΌΟ : Ο β Ο β β£ πΎπΉ (β¨ β¬) β£
     ΟβΌΟ π = fizw Ξ» i β toβΌfrom (AB (lower i)) (π i)

     ΟβΌΟ : Ο β Ο β β£ πΎπΉ (β¨ π) β£
     ΟβΌΟ a = fiu Ξ» i β fromβΌto (AB i) (a i)

     AβB : β¨ π β β¨ β¬
     AβB = record  { to       = Ο , Οhom
                   ; from     = Ο , Οhom
                   ; toβΌfrom  = ΟβΌΟ
                   ; fromβΌto  = ΟβΌΟ
                   }

     Goal : Lift-Alg (β¨ π) Ξ³ β β¨ β¬
     Goal = β-trans (β-sym Lift-β) AβB
