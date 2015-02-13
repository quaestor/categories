{-# OPTIONS --universe-polymorphism #-}
module Categories.Monad.Elgot where

open import Categories.Category
open import Categories.Monoidal.Cartesian
open import Categories.Distributive

open import Categories.NaturalTransformation.Core hiding (_≡_; id)
open import Categories.Functor
  renaming (id to idF; _∘_ to _∘F_; _≡_ to _≡F_)
  
open import Categories.Object.BinaryCoproducts
open import Categories.Object.Coproducts

open import Categories.Object.BinaryProducts
open import Categories.Object.Products

open import Categories.Monad.Triple
open import Categories.Monad.Strong

open import Level

record Dagger
  {o ℓ e}(C : Category o ℓ e)
  (P : Products C)
  (Q : Coproducts C)
  (D : Distributive P Q)
  (M : Triple C)
  (S : Strength C (Cartesian C P) (Triple→Monad M))
  : Set (o ⊔ ℓ ⊔ e) where

  open Category C
  open Coproducts C Q renaming (binary to Q₀)
  open BinaryCoproducts C Q₀ hiding (η)

  open module M = Triple M

  field
    {_†} : ∀ {X Y} → X ⇒ T (Y ∐ X) → X ⇒ T Y

  field
    .unfold       : ∀ {X Y}   (f : X ⇒ T (Y ∐ X))                     → [ η , f † ] * ∘ f ≡ f †
    .naturality   : ∀ {X Y Z} (f : X ⇒ T (Y ∐ X)) (g : Y ⇒ T Z)       → g * ∘ f † ≡ ([ T₁ i₁ ∘ g , η ∘ i₂ ] * ∘ f) †
    .dinaturality : ∀ {X Y Z} (g : X ⇒ T (Y ∐ Z)) (h : Z ⇒ T (Y ∐ X)) → ([ η ∘ i₁ , h ] * ∘ g) † ≡ [ η , ([ η ∘ i₁ , g ] * ∘ h) † ] * ∘ g
    .codiagonal   : ∀ {X Y}   (g : X ⇒ T ((Y ∐ X) ∐ X))               → (T₁([ id , i₂ ]) ∘ g) † ≡ (g †) †
    .uniformity   : ∀ {X Y Z} (f : X ⇒ T (Y ∐ X)) (g : Z ⇒ T (Y ∐ Z)) (h : Z ⇒ X)
                                                                      → f ∘ h ≡ T₁ (id ⧻ h) ∘ g → f † ∘ h ≡ g †
                                                                      
  open Strength S
  open Products C P renaming (binary to P₀)
  open BinaryProducts C P₀
  open Distributive D
  open NaturalTransformation σ renaming (η to τ)

  field
    .comp-str : ∀ {X Y Z} (f : X ⇒ T (Y ∐ X)) → τ _ ∘ (id {Z} ⁂ (f †)) ≡ (T₁ dist ∘ τ _ ∘ (id {Z} ⁂ f)) †
