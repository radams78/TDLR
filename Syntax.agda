module Syntax where
open import Semantics

data Cx : Set
⟦_⟧C : Cx → Groupoid

infix 25 _,₂_
data Cx where
  ε : Cx
  _,₂_ : ∀ Γ → Fibration₂ ⟦ Γ ⟧C → Cx
  _,₁_ : ∀ Γ → Fibration₁ ⟦ Γ ⟧C → Cx
  _,₀_ : ∀ Γ → Fibration₀ ⟦ Γ ⟧C → Cx
  
⟦ ε ⟧C = ONE
⟦ Γ ,₂ G ⟧C = Sigma₂ ⟦ Γ ⟧C G
⟦ Γ ,₁ S ⟧C = Sigma₁ ⟦ Γ ⟧C S
⟦ Γ ,₀ P ⟧C = Sigma₀ ⟦ Γ ⟧C P

--Variables

infix 10 _∋₂_
data _∋₂_ : ∀ Γ → Fibration₂ ⟦ Γ ⟧C → Set where
  top : ∀ {Γ} {H} → Γ ,₂ H ∋₂ pullback₂ p₂ H
  pop₂ : ∀ {Γ} {G} {H} → Γ ∋₂ H → Γ ,₂ G ∋₂ pullback₂ p₂ H
  pop₁ : ∀ {Γ} {S} {H} → Γ ∋₂ H → Γ ,₁ S ∋₂ pullback₂ p₁ H
  pop₀ : ∀ {Γ} {P} {H} → Γ ∋₂ H → Γ ,₀ P ∋₂ pullback₂ p₀ H

⟦_⟧V₂ : ∀ {Γ} {H} → Γ ∋₂ H → Section₂ H
⟦ top ⟧V₂ = q₂
⟦ pop₂ x ⟧V₂ = section-pullback₂ p₂ ⟦ x ⟧V₂
⟦ pop₁ x ⟧V₂ = section-pullback₂ p₁ ⟦ x ⟧V₂
⟦ pop₀ x ⟧V₂ = section-pullback₂ p₀ ⟦ x ⟧V₂

infix 10 _∋₁_
data _∋₁_ : ∀ Γ → Fibration₁ ⟦ Γ ⟧C → Set where
  top : ∀ {Γ} {T} → Γ ,₁ T ∋₁ pullback₁ p₁ T
  pop₂ : ∀ {Γ} {G} {T} → Γ ∋₁ T → Γ ,₂ G ∋₁ pullback₁ p₂ T
  pop₁ : ∀ {Γ} {S} {T} → Γ ∋₁ T → Γ ,₁ S ∋₁ pullback₁ p₁ T
  pop₀ : ∀ {Γ} {P} {T} → Γ ∋₁ T → Γ ,₀ P ∋₁ pullback₁ p₀ T

infix 10 _∋₀_
data _∋₀_ : ∀ Γ → Fibration₀ ⟦ Γ ⟧C → Set where
  top : ∀ {Γ} {T} → Γ ,₀ T ∋₀ pullback₀ p₀ T
  pop₂ : ∀ {Γ} {G} {T} → Γ ∋₀ T → Γ ,₂ G ∋₀ pullback₀ p₂ T
  pop₁ : ∀ {Γ} {S} {T} → Γ ∋₀ T → Γ ,₁ S ∋₀ pullback₀ p₁ T
  pop₀ : ∀ {Γ} {P} {T} → Γ ∋₀ T → Γ ,₀ P ∋₀ pullback₀ p₀ T

--The typing judgements

data _⊢gpd : Cx → Set where

data _⊢₂_ : ∀ Γ → Fibration₂ ⟦ Γ ⟧C → Set where
  var : ∀ {Γ} {T} → Γ ∋₂ T → Γ ⊢₂ T

data _⊢₁_ : ∀ Γ → Fibration₁ ⟦ Γ ⟧C → Set where
  var : ∀ {Γ} {T} → Γ ∋₁ T → Γ ⊢₁ T

data _⊢₀_ : ∀ Γ → Fibration₀ ⟦ Γ ⟧C → Set where
  var : ∀ {Γ} {T} → Γ ∋₀ T → Γ ⊢₀ T
