{-# OPTIONS --universe-polymorphism #-}

module Category.NaturalIsomorphism where

open import Support
open import Category
open import Category.Functor.Core hiding (id) renaming (_∘_ to _∘F_)
open import Category.NaturalTransformation.Core hiding (_≡_)
import Category.Morphisms as Morphisms

record NaturalIsomorphism {o ℓ e o′ ℓ′ e′}
                          {C : Category o ℓ e}
                          {D : Category o′ ℓ′ e′}
                          (F G : Functor C D) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  module C = Category.Category C
  module D = Category.Category D
  module F = Functor F
  module G = Functor G
  open F
  open G renaming (F₀ to G₀; F₁ to G₁)

  field
    F⇒G : NaturalTransformation F G
    F⇐G : NaturalTransformation G F

  module ⇒ = NaturalTransformation F⇒G
  module ⇐ = NaturalTransformation F⇐G

  open Morphisms D

  field
    .iso : ∀ X → Iso (⇒.η X) (⇐.η X)

equiv : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → IsEquivalence (NaturalIsomorphism {C = C} {D})
equiv {C = C} {D} = record 
  { refl = record
    { F⇒G = id
    ; F⇐G = id
    ; iso = λ _ → record 
      { isoˡ = D.identityˡ
      ; isoʳ = D.identityˡ
      }
    }
  ; sym = λ X → record
    { F⇒G = NaturalIsomorphism.F⇐G X
    ; F⇐G = NaturalIsomorphism.F⇒G X
    ; iso = λ Y → record 
      { isoˡ = Morphisms.Iso.isoʳ D (NaturalIsomorphism.iso X Y)
      ; isoʳ = Morphisms.Iso.isoˡ D (NaturalIsomorphism.iso X Y)
      }
    }
  ; trans = trans′
  }
  where
  module C = Category.Category C
  module D = Category.Category D
  open D hiding (id)

  trans′ : {x y z : Functor C D} → NaturalIsomorphism x y → NaturalIsomorphism y z → NaturalIsomorphism x z
  trans′ X Y = record 
    { F⇒G = F⇒G′
    ; F⇐G = F⇐G′
    ; iso = iso′
    }
    where
    F⇒G′ = NaturalIsomorphism.F⇒G Y ∘₁ NaturalIsomorphism.F⇒G X
    F⇐G′ = NaturalIsomorphism.F⇐G X ∘₁ NaturalIsomorphism.F⇐G Y

    .iso′ : (X : C.Obj) → _
    iso′ Z = record 
      { isoˡ = isoˡ′
      ; isoʳ = isoʳ′
      }
      where
      open NaturalIsomorphism hiding (module C; module D)
      open NaturalTransformation hiding (module C; module D)

      isoˡ′ : (η (F⇐G X) Z ∘ η (F⇐G Y) Z) ∘ (η (F⇒G Y) Z ∘ η (F⇒G X) Z) ≡ D.id
      isoˡ′ = begin
                (η (F⇐G X) Z ∘ η (F⇐G Y) Z) ∘ (η (F⇒G Y) Z ∘ η (F⇒G X) Z)
              ≈⟨ D.assoc ⟩
                η (F⇐G X) Z ∘ (η (F⇐G Y) Z ∘ (η (F⇒G Y) Z ∘ η (F⇒G X) Z))
              ≈⟨ D.∘-resp-≡ʳ (sym D.assoc) ⟩
                η (F⇐G X) Z ∘ ((η (F⇐G Y) Z ∘ η (F⇒G Y) Z) ∘ η (F⇒G X) Z)
              ≈⟨ D.∘-resp-≡ʳ (D.∘-resp-≡ˡ (Morphisms.Iso.isoˡ D (iso Y Z))) ⟩
                η (F⇐G X) Z ∘ (D.id ∘ η (F⇒G X) Z)
              ≈⟨ D.∘-resp-≡ʳ D.identityˡ ⟩
                η (F⇐G X) Z ∘ η (F⇒G X) Z
              ≈⟨ Morphisms.Iso.isoˡ D (iso X Z) ⟩
                D.id
              ∎
        where
        open IsEquivalence D.equiv
        open SetoidReasoning D.hom-setoid

      isoʳ′ : (η (F⇒G Y) Z ∘ η (F⇒G X) Z) ∘ (η (F⇐G X) Z ∘ η (F⇐G Y) Z) ≡ D.id
      isoʳ′ = begin
                (η (F⇒G Y) Z ∘ η (F⇒G X) Z) ∘ (η (F⇐G X) Z ∘ η (F⇐G Y) Z)
              ≈⟨ D.assoc ⟩
                η (F⇒G Y) Z ∘ (η (F⇒G X) Z ∘ (η (F⇐G X) Z ∘ η (F⇐G Y) Z))
              ≈⟨ D.∘-resp-≡ʳ (sym D.assoc) ⟩
                η (F⇒G Y) Z ∘ ((η (F⇒G X) Z ∘ η (F⇐G X) Z) ∘ η (F⇐G Y) Z)
              ≈⟨ D.∘-resp-≡ʳ (D.∘-resp-≡ˡ (Morphisms.Iso.isoʳ D (iso X Z))) ⟩
                η (F⇒G Y) Z ∘ (D.id ∘ η (F⇐G Y) Z)
              ≈⟨ D.∘-resp-≡ʳ D.identityˡ ⟩
                η (F⇒G Y) Z ∘ η (F⇐G Y) Z
              ≈⟨ Morphisms.Iso.isoʳ D (iso Y Z) ⟩
                D.id
              ∎
        where
        open IsEquivalence D.equiv
        open SetoidReasoning D.hom-setoid

setoid : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → Setoid _ _
setoid {C = C} {D} = record 
  { Carrier = Functor C D
  ; _≈_ = NaturalIsomorphism
  ; isEquivalence = equiv {C = C} {D}
  }