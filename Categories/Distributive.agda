{-# OPTIONS --universe-polymorphism #-}
module Categories.Distributive where

open import Level

open import Categories.Category
open import Categories.Morphisms

open import Categories.Object.BinaryProducts
open import Categories.Object.Products

open import Categories.Object.BinaryCoproducts
open import Categories.Object.Coproducts

open import Categories.Product hiding (_⁂_)

record Distributive {o ℓ e} {C : Category o ℓ e} (P : Products C) (Q : Coproducts C) : Set (o ⊔ ℓ ⊔ e) where

  open Products C P renaming (binary to P₀)
  open Coproducts C Q renaming (binary to Q₀)
  open BinaryProducts C P₀ using (_×_; _⁂_)
  open BinaryCoproducts C Q₀
  open Category C

  field
    dist : ∀ {X Y Z} → (X × (Y ∐ Z)) ⇒ ((X × Y) ∐ (X × Z))
    .iso : ∀ {X Y Z} → Iso C (dist {X} {Y} {Z}) ([ id ⁂ i₁ , id ⁂ i₂ ])
