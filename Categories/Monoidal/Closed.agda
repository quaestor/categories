module Categories.Monoidal.Closed where

open import Level using (_⊔_)

open import Categories.Category
open import Categories.Adjunction hiding (id)
open import Categories.Functor.Core using (id)
open import Categories.Functor.Constant
open import Categories.Bifunctor

open import Categories.Monoidal

record Closed {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) : Set (o ⊔ ℓ ⊔ e) where
  private module C = Category C
  private module M = Monoidal M
  open C hiding (id; identityˡ; identityʳ; assoc)
  open M using (⊗)

  field
    hom : Bifunctor (Category.op C) C C

  field
    .adjoint : ∀ {X} → Adjunction (overlap-× ⊗ id (Constant {D = C} X))
                                  (overlap-× hom (Constant {D = Category.op C} X) id)
