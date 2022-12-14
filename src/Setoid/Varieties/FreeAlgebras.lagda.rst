.. FILE      : Setoid/Varieties/FreeAlgebras.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 29 Jun 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _setoid-varieties-free-setoid-algebras:

Free setoid algebras
~~~~~~~~~~~~~~~~~~~~

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (π ; π₯ ; Signature)

  module Setoid.Varieties.FreeAlgebras {π : Signature π π₯} where

  -- Imports from Agda and the Agda Standard Library -------------------------------
  open import Agda.Primitive   using ()                  renaming ( Set to Type )
  open import Data.Product     using ( Ξ£-syntax ; _,_ )
                               renaming ( projβ to fst ; projβ to snd )
  open import Function         using ( _β_ ; id )        renaming ( Func to _βΆ_ )
  open import Level            using ( Level ; _β_)
  open import Relation.Binary  using ( Setoid )
  open import Relation.Unary   using ( Pred ; _β_ ; _β_ )

  open import Relation.Binary.PropositionalEquality as β‘ using (_β‘_)

  -- Imports from the Agda Universal Algebra Library -------------------------------
  open  import Overture          using ( β£_β£ ; β₯_β₯ )
  open  import Setoid.Relations  using ( fkerPred )
  open  import Setoid.Functions  using ( eq ; IsSurjective )

  open  import Base.Terms {π = π}       using ( β )
  open  import Setoid.Algebras {π = π}  using ( Algebra ; ov ; Lift-Alg )

  open  import Setoid.Homomorphisms {π = π}
        using ( epi ; IsEpi ; IsHom ; hom ; epiβhom ; β-epi ; ToLift-epi )

  open  import Setoid.Terms {π = π}
        using ( π» ; _β_ ; module Environment ; free-lift ; free-lift-interp )

  open  import Setoid.Varieties.Closure {π = π} using ( V ; S )

  open  import Setoid.Varieties.Preservation {π = π}
        using ( classIds-β-VIds ; S-id1 )
  open  import Setoid.Varieties.SoundAndComplete  {π = π}
        using  ( Eq ; _β«_ ; _βΜ_ ; _β’_βΉ_β_ ; Th ; Mod
               ; module Soundness ; module FreeAlgebra )

  open _βΆ_      using ( cong ) renaming ( f to _β¨$β©_ )
  open Algebra  using ( Domain )

In the code below, ``X`` will play the role of an arbitrary collection
of variables; it would suffice to take ``X`` to be the cardinality of
the largest algebra in π¦, but since we donβt know that cardinality, we
leave ``X`` aribtrary for now.

Alternatively, we could let ``X`` be the product of all algebras in the
class ``π¦``, like so.

.. code:: agda

   π : Type oΞ±
   π = Carrier ( Domain (β¨ (π{π¦ = S π¦})) )

::

  module FreeHom (Ο : Level){Ξ± Οα΅ β : Level}
                 {π¦ : Pred(Algebra Ξ± Οα΅) (Ξ± β Οα΅ β ov β)} where
   private
    ΞΉ = ov(Ο β Ξ± β Οα΅ β β)

   open Eq

We now define the algebra ``π½``, which plays the role of the relatively
free algebra, along with the natural epimorphism ``epiπ½ : epi (π» π) π½``
from ``π» π`` to ``π½``. The relatively free algebra (relative to
``Th π¦``) is called ``M`` and is derived from ``TermSetoid π`` and
``TermInterp π`` and imported from the EquationalLogic module.

::

   -- β indexes the collection of equations modeled by π¦
   β : Type ΞΉ
   β = Ξ£[ eq β Eq{Ο} ] π¦ β« ((lhs eq) βΜ (rhs eq))

   β° : β β Eq
   β° (eqv , p) = eqv

   β°β’[_]βΉThπ¦ : (X : Type Ο) β β{p q} β β° β’ X βΉ p β q β π¦ β« (p βΜ q)
   β°β’[ X ]βΉThπ¦ x π¨ kA = sound (Ξ» i Ο β β₯ i β₯ π¨ kA Ο) x
    where open Soundness β° π¨

   ----------- THE RELATIVELY FREE ALGEBRA -----------
   open FreeAlgebra {ΞΉ = ΞΉ}{I = β} β° using ( π½[_] )



Finally, we define an epimorphism from ``π» X`` onto the relatively free algebra
``π½[ X ]``. Of course, the kernel of this epimorphism will be the congruence of
``π» X`` defined by identities modeled by (``S π¦``, hence) ``π¦``.

::

   epiπ½[_] : (X : Type Ο) β epi (π» X) π½[ X ]
   epiπ½[ X ] = h , hepi
    where
    open Algebra π½[ X ]  using() renaming ( Domain to F ; Interp to InterpF )
    open Setoid F        using() renaming ( _β_  to _βFβ_ ; refl to reflF )
    open Algebra (π» X)   using() renaming (Domain to TX)
    open Setoid TX       using() renaming ( _β_ to _βTβ_ ; refl to reflT )

    open _β_ ; open IsEpi ; open IsHom

    c : β {x y} β x βTβ y β x βFβ y
    c (rfl {x}{y} β‘.refl) = reflF
    c (gnl {f}{s}{t} x) = cong InterpF (β‘.refl , c β x)

    h : TX βΆ F
    h = record { f = id ; cong = c }

    hepi : IsEpi (π» X) π½[ X ] h
    compatible (isHom hepi) = cong h reflT
    isSurjective hepi {y} = eq y reflF


   homπ½[_] : (X : Type Ο) β hom (π» X) π½[ X ]
   homπ½[ X ] = epiβhom (π» X) π½[ X ] epiπ½[ X ]

   homπ½[_]-is-epic : (X : Type Ο) β IsSurjective β£ homπ½[ X ] β£
   homπ½[ X ]-is-epic = IsEpi.isSurjective (snd (epiπ½[ X ]))


   class-models-kernel : β{X p q} β (p , q) β fkerPred β£ homπ½[ X ] β£ β π¦ β« (p βΜ q)
   class-models-kernel {X = X}{p}{q} pKq = β°β’[ X ]βΉThπ¦ pKq

   kernel-in-theory : {X : Type Ο} β fkerPred β£ homπ½[ X ] β£ β Th (V β ΞΉ π¦)
   kernel-in-theory {X = X} {p , q} pKq vkA x =
    classIds-β-VIds {β = β} {p = p}{q} (class-models-kernel pKq) vkA x


   module _  {X : Type Ο} {π¨ : Algebra Ξ± Οα΅}{sA : π¨ β S {Ξ² = Ξ±}{Οα΅} β π¦} where
    open Environment π¨ using ( Equal )
    kerπ½βEqual : β{p q} β (p , q) β fkerPred β£ homπ½[ X ] β£ β Equal p q
    kerπ½βEqual{p = p}{q} x = S-id1{β = β}{p = p}{q} (β°β’[ X ]βΉThπ¦ x) π¨ sA

   π¦β«ββ°β’ : {X : Type Ο} β β{p q} β π¦ β« (p βΜ q) β β° β’ X βΉ p β q
   π¦β«ββ°β’ {p = p} {q} pKq = hyp ((p βΜ q) , pKq) where open _β’_βΉ_β_ using (hyp)

  ------------------------------------------------------------------------------

::

  module _ {Ξ± Οα΅ β : Level} {π¦ : Pred(Algebra Ξ± Οα΅) (Ξ± β Οα΅ β ov β)} where
   private ΞΉ = ov(Ξ± β Οα΅ β β)
   open IsEpi ; open IsHom

   module lower-universe-version {π¨ : Algebra Ξ± Οα΅} where
    open FreeHom Ξ± {Ξ±}{Οα΅}{β}{π¦}
    open FreeAlgebra {ΞΉ = ΞΉ}{I = β} β°            using ( π½[_] )
    open Algebra π¨  renaming (Domain to A)       using( Interp )
    open Setoid A   renaming ( Carrier to β£Aβ£ )  using ( trans ; sym ; refl )

    π½-ModTh-epi : π¨ β Mod (Th (V β ΞΉ π¦)) β epi π½[ β£Aβ£ ] π¨
    π½-ModTh-epi AβModThK = Ο , isEpi
      where
      Ο : (Domain π½[ β£Aβ£ ]) βΆ A
      _β¨$β©_ Ο = free-lift{π¨ = π¨} id
      cong Ο {p} {q} pq =  trans (sym (free-lift-interp{π¨ = π¨} id p))
                           ( trans (AβModThK{p = p}{q} (kernel-in-theory pq) id )
                           ( free-lift-interp{π¨ = π¨} id q) )

      isEpi : IsEpi π½[ β£Aβ£ ] π¨ Ο
      compatible (isHom isEpi) = cong Interp (β‘.refl , (Ξ» _ β refl))
      isSurjective isEpi {y} = eq (β y) refl


    π½-ModTh-epi-lift :  π¨ β Mod (Th (V β ΞΉ π¦))
     β                  epi π½[ β£Aβ£ ] (Lift-Alg π¨ (ov Ξ±) (ov Ξ±))

    π½-ModTh-epi-lift AβModThK = β-epi (π½-ModTh-epi (Ξ» {p q} β AβModThK{p = p}{q})) ToLift-epi

   module _  -- higher-universe-version
             -- (HSP theorem needs π¨ in higher universe level)
             {π¨ : Algebra (Ξ± β Οα΅ β β) (Ξ± β Οα΅ β β)} where

    open FreeHom (Ξ± β Οα΅ β β) {Ξ±}{Οα΅}{β}{π¦}
    open FreeAlgebra {ΞΉ = ΞΉ}{I = β} β°            using ( π½[_] )
    open Algebra π¨  renaming (Domain to A)       using( Interp )
    open Setoid A   renaming ( Carrier to β£Aβ£ )  using ( trans ; sym ; refl )

    π½-ModTh-epi : π¨ β Mod (Th (V β ΞΉ π¦)) β epi π½[ β£Aβ£ ] π¨
    π½-ModTh-epi AβModThK = Ο , isEpi
     where
     Ο : (Domain π½[ β£Aβ£ ]) βΆ A
     _β¨$β©_ Ο = free-lift{π¨ = π¨} id
     cong Ο {p} {q} pq =  trans (sym (free-lift-interp{π¨ = π¨} id p))
                          ( trans (AβModThK{p = p}{q} (kernel-in-theory pq) id )
                          ( free-lift-interp{π¨ = π¨} id q) )
     isEpi : IsEpi π½[ β£Aβ£ ] π¨ Ο
     compatible (isHom isEpi) = cong Interp (β‘.refl , (Ξ» _ β refl))
     isSurjective isEpi {y} = eq (β y) refl

    π½-ModTh-epi-lift : π¨ β Mod (Th (V β ΞΉ π¦)) β epi π½[ β£Aβ£ ] (Lift-Alg π¨ ΞΉ ΞΉ)
    π½-ModTh-epi-lift AβModThK = β-epi (π½-ModTh-epi (Ξ» {p q} β AβModThK{p = p}{q})) ToLift-epi

