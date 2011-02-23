{-# OPTIONS --universe-polymorphism #-}
module Category.NaturalTransformation where

open import Support
open import Category
open import Category.Functor renaming (id to idF; _≡_ to _≡F_; _∘_ to _∘F_)
open import Category.NaturalTransformation.Core


.equiv : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F G : Functor C D} → IsEquivalence (_≡_ {F = F} {G})
equiv {C = C} {D} {F} {G} = record 
  { refl = IsEquivalence.refl D.equiv
  ; sym = λ x → IsEquivalence.sym D.equiv x -- N.B: η expansion is needed here!
  ; trans = λ x y → IsEquivalence.trans D.equiv x y
  }
  where
  module C = Category.Category C
  module D = Category.Category D

setoid : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F G : Functor C D} → Setoid _ _
setoid {F = F} {G} = record 
  { Carrier = NaturalTransformation F G
  ; _≈_ = _≡_
  ; isEquivalence = equiv {F = F}
  }

-- The vertical versions
.identity₁ˡ : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F G : Functor C D} {X : NaturalTransformation F G} 
           → id ∘₁ X ≡ X
identity₁ˡ {D = D} = Category.identityˡ D

.identity₁ʳ : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F G : Functor C D} {X : NaturalTransformation F G} 
           → X ∘₁ id ≡ X
identity₁ʳ {D = D} = Category.identityʳ D



.assoc₁ : ∀ {o ℓ e o′ ℓ′ e′} 
           {P : Category o ℓ e} {Q : Category o′ ℓ′ e′} {A B C D : Functor P Q} 
           {X : NaturalTransformation A B} {Y : NaturalTransformation B C} {Z : NaturalTransformation C D} 
       → (Z ∘₁ Y) ∘₁ X ≡ Z ∘₁ (Y ∘₁ X)
assoc₁ {Q = Q} = Category.assoc Q


-- The horizontal ones
.identity₀ˡ : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F G : Functor C D} {X : NaturalTransformation F G} 
           → id {F = idF} ∘₀ X ≡ X
identity₀ˡ {D = D} = Category.identityʳ D

.identity₀ʳ : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F G : Functor C D} {X : NaturalTransformation F G} 
           → X ∘₀ id {F = idF} ≡ X
identity₀ʳ {C = C} {D} {F} {G} {X} = 
    begin
      G₁ C.id ∘D (η _)
    ≈⟨ ∘-resp-≡ˡ G.identity ⟩
      D.id ∘D (η _)
    ≈⟨ D.identityˡ ⟩
      η _
    ∎
  where
  module C = Category.Category C renaming (_∘_ to _∘C_; _≡_ to _≡C_)
  module D = Category.Category D renaming (_∘_ to _∘D_; _≡_ to _≡D_)
  module F = Functor F hiding (module C; module D)
  module G = Functor G hiding (module C; module D) renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)
  open NaturalTransformation X hiding (module C; module D; module F; module G)
  open SetoidReasoning D.hom-setoid
  open F
  open G
  open D

.assoc₀ : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃} 
            {C₀ : Category o₀ ℓ₀ e₀} {C₁ : Category o₁ ℓ₁ e₁} {C₂ : Category o₂ ℓ₂ e₂} {C₃ : Category o₃ ℓ₃ e₃} 
            {F G : Functor C₀ C₁} {H I : Functor C₁ C₂} {J K : Functor C₂ C₃}
        → {X : NaturalTransformation F G} → {Y : NaturalTransformation H I} → {Z : NaturalTransformation J K}
        → (Z ∘₀ Y) ∘₀ X ≡ Z ∘₀ (Y ∘₀ X) 
assoc₀ {C₀ = C₀} {C₁} {C₂} {C₃} {F} {G} {H} {I} {J} {K} {X} {Y} {Z} = 
    begin
      K₁ (I₁ (X.η _)) ∘C₃ (K₁ (Y.η (F₀ _)) ∘C₃ Z.η (H₀ (F₀ _)))
    ≈⟨ sym C₃.assoc ⟩
      (K₁ (I₁ (X.η _)) ∘C₃ K₁ (Y.η (F₀ _))) ∘C₃ Z.η (H₀ (F₀ _))
    ≈⟨ sym (C₃.∘-resp-≡ˡ K.homomorphism) ⟩
      (K₁ ((I₁ (X.η _)) ∘C₂ Y.η (F₀ _))) ∘C₃ Z.η (H₀ (F₀ _))
    ∎
  where
  module C₂ = Category.Category C₂ renaming (_∘_ to _∘C₂_; _≡_ to _≡C₂_)
  module C₃ = Category.Category C₃ renaming (_∘_ to _∘C₃_; _≡_ to _≡C₃_)
  module F = Functor F
  module G = Functor G renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)
  module H = Functor H renaming (F₀ to H₀; F₁ to H₁; F-resp-≡ to H-resp-≡)
  module I = Functor I renaming (F₀ to I₀; F₁ to I₁; F-resp-≡ to I-resp-≡)
  module J = Functor J renaming (F₀ to J₀; F₁ to J₁; F-resp-≡ to J-resp-≡)
  module K = Functor K renaming (F₀ to K₀; F₁ to K₁; F-resp-≡ to K-resp-≡)
  module X = NaturalTransformation X hiding (module C; module D; module F; module G)
  module Y = NaturalTransformation Y hiding (module C; module D; module F; module G)
  module Z = NaturalTransformation Z hiding (module C; module D; module F; module G)
  open IsEquivalence C₃.equiv
  open SetoidReasoning C₃.hom-setoid
  open C₂
  open C₃
  open F
  open H
  open I
  open K


.interchange : ∀ {o₀ ℓ₀ e₀} {o₁ ℓ₁ e₁} {o₂ ℓ₂ e₂}
                 {C₀ : Category o₀ ℓ₀ e₀} {C₁ : Category o₁ ℓ₁ e₁} {C₂ : Category o₂ ℓ₂ e₂}
                 {F₀ F₁ F₅ : Functor C₀ C₁} {F₂ F₃ F₄ : Functor C₁ C₂} 
                 {α : NaturalTransformation F₃ F₄} 
                 {β : NaturalTransformation F₁ F₅} 
                 {γ : NaturalTransformation F₂ F₃} 
                 {δ : NaturalTransformation F₀ F₁} 
             → (α ∘₀ β) ∘₁ (γ ∘₀ δ) ≡ (α ∘₁ γ) ∘₀ (β ∘₁ δ)
interchange {C₀ = C₀} {C₁} {C₂} {F₀} {F₁} {F₅} {F₂} {F₃} {F₄} {α} {β} {γ} {δ} = 
    begin
      (F₄.F₁ (β.η _) ∘ α.η (F₁.F₀ _)) ∘ (F₃.F₁ (δ.η _) ∘ γ.η (F₀.F₀ _))
    ≈⟨ C₂.assoc ⟩
      F₄.F₁ (β.η _) ∘ (α.η (F₁.F₀ _) ∘ (F₃.F₁ (δ.η _) ∘ γ.η (F₀.F₀ _)))
    ≈⟨ sym (C₂.∘-resp-≡ʳ C₂.assoc) ⟩
      F₄.F₁ (β.η _) ∘ ((α.η (F₁.F₀ _) ∘ (F₃.F₁ (δ.η _))) ∘ γ.η (F₀.F₀ _))
    ≈⟨ C₂.∘-resp-≡ʳ (C₂.∘-resp-≡ˡ (α.commute (δ.η _))) ⟩
      F₄.F₁ (β.η _) ∘ ((F₄.F₁ (δ.η _) ∘ α.η (F₀.F₀ _)) ∘ γ.η (F₀.F₀ _))
    ≈⟨ C₂.∘-resp-≡ʳ C₂.assoc ⟩
      F₄.F₁ (β.η _) ∘ (F₄.F₁ (δ.η _) ∘ (α.η (F₀.F₀ _) ∘ γ.η (F₀.F₀ _)))
    ≈⟨ sym C₂.assoc ⟩
      (F₄.F₁ (β.η _) ∘ F₄.F₁ (δ.η _)) ∘ (α.η (F₀.F₀ _) ∘ γ.η (F₀.F₀ _))
    ≈⟨ sym (C₂.∘-resp-≡ˡ F₄.homomorphism) ⟩
      F₄.F₁ (β.η _ ∘C₁ δ.η _) ∘ (α.η (F₀.F₀ _) ∘ γ.η (F₀.F₀ _))
    ∎
  where
  module C₁ = Category.Category C₁ renaming (_∘_ to _∘C₁_; _≡_ to _≡C₁_)
  module C₂ = Category.Category C₂ 
  module F₀ = Functor F₀
  module F₁ = Functor F₁
  module F₂ = Functor F₂
  module F₃ = Functor F₃
  module F₄ = Functor F₄
  module F₅ = Functor F₅
  module α = NaturalTransformation α
  module β = NaturalTransformation β
  module γ = NaturalTransformation γ
  module δ = NaturalTransformation δ
  open C₁
  open C₂
  open IsEquivalence C₂.equiv
  open SetoidReasoning C₂.hom-setoid


.∘₁-resp-≡ : ∀ {o ℓ e} {o′ ℓ′ e′}
               {D : Category o ℓ e} {E : Category o′ ℓ′ e′}
               {A B C : Functor D E} 
               {f h : NaturalTransformation B C} {g i : NaturalTransformation A B} 
          → f ≡ h → g ≡ i → f ∘₁ g ≡ h ∘₁ i
∘₁-resp-≡ {E = E} f≡h g≡i = Category.∘-resp-≡ E f≡h g≡i
