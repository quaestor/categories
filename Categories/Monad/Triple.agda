{-# OPTIONS --universe-polymorphism #-}
module Categories.Monad.Triple where

open import Level

open import Categories.Category
open import Categories.Monad
open import Categories.Monad.Kleisli

open import Categories.Support.EqReasoning
open import Categories.Functor hiding (∘-resp-≡; _≡_; assoc; identityˡ; identityʳ) renaming (id to idF; _∘_ to _∘F_)
open import Categories.NaturalTransformation renaming (id to idN; _≡_ to _≡N_)

record Triple {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  open Category C
  field
    T : Obj → Obj
    η : ∀ {X} → (X ⇒ T X)
    _* : ∀ {X Y} → (X ⇒ T Y) → (T X ⇒ T Y)

  field
    .lift-unit  : ∀ {X} → (η {X}) * ≡ id
    .unlift     : ∀ {X Y} {f : X ⇒ T Y} → f * ∘ η ≡ f
    .lift-comp  : ∀ {X Y Z} {f : X ⇒ T Y} {g : Y ⇒ T Z} → (g * ∘ f) * ≡ g * ∘ f *
    .{*-resp-≡} : ∀ {X Y} {f g : X ⇒ T Y} → f ≡ g → f * ≡ g *

Triple→Monad : ∀ {o ℓ e} {C : Category o ℓ e} → Triple C → Monad C
Triple→Monad {C = C} 𝕋 = record
  { F = functor´
  ; η = unit´
  ; μ = multiplication´
  ; assoc  = assoc´
  ; identityˡ = identityˡ´
  ; identityʳ = identityʳ´
  }
  where

  module 𝕋 = Triple 𝕋 
  open 𝕋 using (T; η; _*)
  open Category C

  functor´ : Endofunctor C
  functor´ = record
    { F₀ = T
    ; F₁ = λ f → (η ∘ f) *
    ; identity = identity´
    ; homomorphism = homomorphism´
    ; F-resp-≡ = F-resp-≡´
    }
    where

      .identity´ : ∀ {A} → (η ∘ id {A}) * ≡ id
      identity´ {A} =
          begin
            (η ∘ id {A}) *
          ↓⟨ 𝕋.*-resp-≡ identityʳ ⟩
            η *
          ↓⟨ 𝕋.lift-unit ⟩
            id
          ∎
        where
        open HomReasoning

      .homomorphism´ :  ∀ {X Y Z} {f : X ⇒ Y} {g : Y ⇒ Z} → (η ∘ (g ∘ f)) * ≡ (η ∘ g) * ∘ (η ∘ f) *
      homomorphism´ {X} {Y} {Z} {f} {g} =
          begin
            (η ∘ (g ∘ f)) *
          ↑⟨ 𝕋.*-resp-≡ assoc ⟩
            ((η ∘ g) ∘ f) *
          ↑⟨ 𝕋.*-resp-≡ (∘-resp-≡ˡ 𝕋.unlift) ⟩
            (((η ∘ g) * ∘ η) ∘ f) *
          ↓⟨ 𝕋.*-resp-≡ assoc ⟩
            ((η ∘ g) * ∘ (η ∘ f)) *
          ↓⟨ 𝕋.lift-comp ⟩
            (η ∘ g) * ∘ (η ∘ f) *
          ∎
        where
        open HomReasoning

      .F-resp-≡´ : ∀ {A B} {f g : A ⇒ B} → f ≡ g → (η ∘ f) * ≡ (η ∘ g) *
      F-resp-≡´ f≡g = 𝕋.*-resp-≡ (∘-resp-≡ refl f≡g)
        where open Equiv

  unit´ : NaturalTransformation idF functor´
  unit´ = record
    { η = λ X → η {X}
    ; commute = commute´
    }
    where

    .commute´ : ∀ {X Y} (f : X ⇒ Y) → CommutativeSquare f η η ((η ∘ f) *)
    commute´ f =
        begin
          η ∘ f
        ↑⟨ 𝕋.unlift ⟩
          (η ∘ f) * ∘ η
        ∎
      where
      open HomReasoning

  multiplication´ : NaturalTransformation (functor´ ∘F functor´) functor´
  multiplication´ = record
    { η = λ X → id *
    ; commute = commute´´
    }
    where

    .commute´´ : ∀ {X Y} (f : X ⇒ Y) → CommutativeSquare ((η ∘ (η ∘ f) *) *) (id *) (id *) ((η ∘ f) *)
    commute´´ f =
        begin
          id * ∘ (η ∘ (η ∘ f) *) *
        ↑⟨ 𝕋.lift-comp ⟩
          (id * ∘ (η ∘ (η ∘ f) *)) *
        ↑⟨ 𝕋.*-resp-≡ assoc ⟩
          ((id * ∘ η) ∘ (η ∘ f) *) *
        ↓⟨ 𝕋.*-resp-≡ (∘-resp-≡ˡ 𝕋.unlift) ⟩
          (id ∘ (η ∘ f) *) *
        ↓⟨ 𝕋.*-resp-≡ identityˡ ⟩
          ((η ∘ f) *) *
        ↑⟨ 𝕋.*-resp-≡ identityʳ ⟩
          ((η ∘ f) * ∘ id) *
        ↓⟨ 𝕋.lift-comp ⟩
          (η ∘ f) * ∘ id *
        ∎
      where
      open HomReasoning

  .assoc´ : ∀ {X} → (id {T X}) * ∘ (η ∘ ((id {T X}) *)) * ≡ (id {T X}) * ∘ (id {T (T X)}) *
  assoc´ {X} =
      begin
        (id {T X}) * ∘ (η ∘ ((id {T X}) *)) *
      ↑⟨ 𝕋.lift-comp ⟩
        (((id {T X}) *) ∘ (η ∘ ((id {T X}) *))) *
      ↑⟨ 𝕋.*-resp-≡ assoc ⟩
        (((id {T X}) * ∘ η) ∘ (id {T X}) *) *
      ↓⟨ 𝕋.*-resp-≡ (∘-resp-≡ˡ 𝕋.unlift) ⟩
        ((id {T X}) ∘ (id {T X}) *) *
      ↓⟨ 𝕋.*-resp-≡ identityˡ ⟩
        ((id {T X}) *) *
      ↑⟨ 𝕋.*-resp-≡ identityʳ ⟩
        ((id {T X}) * ∘ (id {T (T X)})) *
      ↓⟨ 𝕋.lift-comp ⟩
        (id {T X}) * ∘ (id {T (T X)}) *
      ∎
    where
    open HomReasoning

  .identityˡ´ : ∀ {X} → (id {T X}) * ∘ (η ∘ η) * ≡ id {T X}
  identityˡ´ {X} =
      begin
        (id {T X}) * ∘ (η ∘ η) *
      ↑⟨ 𝕋.lift-comp ⟩
        ((id {T X}) * ∘ (η ∘ η)) * 
      ↑⟨ 𝕋.*-resp-≡ assoc ⟩
        (((id {T X}) * ∘ η) ∘ η) * 
      ↓⟨ 𝕋.*-resp-≡ (∘-resp-≡ˡ 𝕋.unlift) ⟩
        ((id {T X}) ∘ η) *
      ↓⟨ 𝕋.*-resp-≡ identityˡ ⟩
        η *
      ↓⟨ 𝕋.lift-unit ⟩
        id {T X}
      ∎
    where
    open HomReasoning

  .identityʳ´ : ∀ {X} → (id {T X}) * ∘ η  ≡ id {T X}
  identityʳ´ {X} =
      begin
        (id {T X}) * ∘ η
      ↓⟨ 𝕋.unlift ⟩
        id {T X}
      ∎
    where
    open HomReasoning

Monad→Triple : ∀ {o ℓ e} {C : Category o ℓ e} → Monad C → Triple C
Monad→Triple {C = C} 𝕋 = record
  { T = F₀
  ; η = λ {X} → η.η X
  ; _* = λ f  → μ.η _ ∘ (F₁ f)
  ; lift-unit = 𝕋.identityˡ
  ; unlift = CT.identityʳ
  ; lift-comp = lift-comp´
  ; *-resp-≡ = λ f≡g → ∘-resp-≡ʳ (F-resp-≡ f≡g)
  }
  where
  module 𝕋 = Monad 𝕋
  open 𝕋 using (η; μ; F)
  open Functor F using (F₀; F₁; F-resp-≡)
  CT = Kleisli 𝕋
  module CT = Category CT 
  module η = NaturalTransformation η
  module μ = NaturalTransformation μ
  open Category C

  .lift-comp´ : ∀ {X Y Z} {f : X ⇒ F₀ Y} {g : Y ⇒ F₀ Z} → μ.η _ ∘ F₁ ((μ.η _ ∘ F₁ g) ∘ f) ≡ (μ.η _ ∘ F₁ g) ∘ μ.η _ ∘ F₁ f
  lift-comp´ {X} {Y} {Z} {f} {g} =
      begin
        μ.η _ ∘ F₁ ((μ.η _ ∘ F₁ g) ∘ f)
      ↑⟨ identityʳ ⟩
        (μ.η _ ∘ (F₁ ((μ.η _ ∘ F₁ g) ∘ f))) ∘ id {F₀ X}
      ↓⟨ CT.assoc ⟩
        (μ.η _ ∘ F₁ g) ∘ ((μ.η _ ∘ F₁ f) ∘ id {F₀ X})
      ↓⟨ ∘-resp-≡ʳ identityʳ ⟩
        (μ.η _ ∘ F₁ g) ∘ (μ.η _ ∘ F₁ f)
      ∎
      where
      open HomReasoning
