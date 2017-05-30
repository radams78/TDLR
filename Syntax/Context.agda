module Syntax.Context where
open import Semantics.Groupoid

data Context : Groupoid → Set

data _⊢_gpd : ∀ {G} → Context G → Groupoid-Fibration G → Set where
  -Set- : ∀ {G} {Γ : Context G} → Γ ⊢ K G Sets gpd

data _⊢₂_∶_ : ∀ {G} {H} (Γ : Context G) → Section H → Γ ⊢ H gpd → Set where
  -Prop- : ∀ {G} {Γ : Context G} → Γ ⊢₂ K₀ G Props ∶ -Set-
  -var- : ∀ {G} {H} {Γ} {s} {T} → Γ ∋ s ∶ T → Γ ⊢₂ s ∶ T

data _⊢₁_∶_ : ∀ {G} {S} (Γ : Context G) → Section₁ S → Γ ⊢₂ S ∶ -Set- → Set where

data Context where
  ε : Context ONE
  _,₂_ : ∀ {G} {A} Γ → Γ ⊢ A gpd → Context (Sigma₂ G A)
  _,₁_ : ∀ {G} {A} Γ → Γ ⊢₂ A ∶ -Set- → Context (Sigma₁ G A)
  _,₀_ : ∀ {G} {P} Γ → Γ ⊢₁ P ∶ -Prop- → Context (Sigma₀ G P)

