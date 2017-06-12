module Syntax.Substitution where
open import Semantics
open import Syntax.Context
open import Syntax.Variable
open import Syntax.Typing

data Sub Γ : Cx → Set
⟦_⟧S : ∀ {Γ} {Δ} → Sub Γ Δ → Groupoid-Functor ⟦ Γ ⟧C ⟦ Δ ⟧C

data Sub Γ where
  • : Sub Γ ε
  _,₂_∋_≡_ : ∀ {Δ} (σ : Sub Γ Δ) G ⟦t⟧ → Γ ⊢₂ pullback₂ ⟦ σ ⟧S G ∋ ⟦t⟧ → Sub Γ (Δ ,₂ G)
  _,₁_∋_≡_ : ∀ {Δ} (σ : Sub Γ Δ) S ⟦t⟧ → Γ ⊢₁ pullback₁ ⟦ σ ⟧S S ∋ ⟦t⟧  → Sub Γ (Δ ,₁ S)
  _,₀_∋_≡_ : ∀ {Δ} (σ : Sub Γ Δ) P ⟦t⟧ → Γ ⊢₀ pullback₀ ⟦ σ ⟧S P ∋ ⟦t⟧ → Sub Γ (Δ ,₀ P)

⟦ • ⟧S = bang
⟦ σ ,₂ G ∋ ⟦t⟧ ≡ t ⟧S = pair₂ G ⟦ σ ⟧S ⟦t⟧
⟦ σ ,₁ S ∋ ⟦a⟧ ≡ a ⟧S = pair₁ S ⟦ σ ⟧S ⟦a⟧
⟦ σ ,₀ P ∋ ⟦p⟧ ≡ p ⟧S = pair₀ P ⟦ σ ⟧S ⟦p⟧

apV₂ : ∀ {Γ Δ G} (σ : Sub Γ Δ) {⟦t⟧} → Δ var₂ G ∋ ⟦t⟧ → Γ ⊢₂ pullback₂ ⟦ σ ⟧S G ∋ section-pullback₂ ⟦ σ ⟧S ⟦t⟧
apV₂ (σ ,₂ _ ∋ _ ≡ t) top = t
apV₂ (σ ,₂ _ ∋ _ ≡ t) (pop₂ x) = apV₂ σ x
apV₂ (σ ,₁ _ ∋ _ ≡ t) (pop₁ x) = apV₂ σ x
apV₂ (σ ,₀ _ ∋ _ ≡ t) (pop₀ x) = apV₂ σ x

apV₁ : ∀ {Γ Δ G} (σ : Sub Γ Δ) {⟦t⟧} → Δ var₁ G ∋ ⟦t⟧ → Γ ⊢₁ pullback₁ ⟦ σ ⟧S G ∋ section-pullback₁ ⟦ σ ⟧S ⟦t⟧
apV₁ (σ ,₁ _ ∋ _ ≡ t) top = t
apV₁ (σ ,₂ _ ∋ _ ≡ t) (pop₂ x) = apV₁ σ x
apV₁ (σ ,₁ _ ∋ _ ≡ t) (pop₁ x) = apV₁ σ x
apV₁ (σ ,₀ _ ∋ _ ≡ t) (pop₀ x) = apV₁ σ x

apV₀ : ∀ {Γ Δ G} (σ : Sub Γ Δ) {⟦t⟧} → Δ var₀ G ∋ ⟦t⟧ → Γ ⊢₀ pullback₀ ⟦ σ ⟧S G ∋ section-pullback₀ ⟦ σ ⟧S ⟦t⟧
apV₀ (σ ,₀ _ ∋ _ ≡ t) top = t
apV₀ (σ ,₂ _ ∋ _ ≡ t) (pop₂ x) = apV₀ σ x
apV₀ (σ ,₁ _ ∋ _ ≡ t) (pop₁ x) = apV₀ σ x
apV₀ (σ ,₀ _ ∋ _ ≡ t) (pop₀ x) = apV₀ σ x

ap₃ : ∀ {Γ Δ G} (σ : Sub Γ Δ) → Δ ⊢ G gpd → Γ ⊢ pullback₂ ⟦ σ ⟧S G gpd
ap₃ σ (-eq- G H) = -eq- (ap₃ σ G) (ap₃ σ H)

ap₂ : ∀ {Γ Δ G} (σ : Sub Γ Δ) {⟦t⟧} → Δ ⊢₂ G ∋ ⟦t⟧ → Γ ⊢₂ pullback₂ ⟦ σ ⟧S G ∋ section-pullback₂ ⟦ σ ⟧S ⟦t⟧
ap₂ σ (-var- x) = apV₂ σ x
ap₂ σ (-eq*- G* H*) = -eq*- (ap₂ σ G*) (ap₂ σ H*)

ap₁ : ∀ {Γ Δ G} (σ : Sub Γ Δ) {⟦t⟧} → Δ ⊢₁ G ∋ ⟦t⟧ → Γ ⊢₁ pullback₁ ⟦ σ ⟧S G ∋ section-pullback₁ ⟦ σ ⟧S ⟦t⟧
ap₁ σ (-var- x) = apV₁ σ x

