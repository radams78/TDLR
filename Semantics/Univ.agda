module Semantics.Univ where

postulate U₂ : Set
postulate T₂ : U₂ → Set
postulate Eq₂ : U₂ → U₂ → U₂
postulate Eq₂-cong : ∀ {A A' B B'} → T₂ (Eq₂ A A') → T₂ (Eq₂ B B') → T₂ (Eq₂ (Eq₂ A B) (Eq₂ A' B'))

postulate U₁ : Set
postulate T₁ : U₁ → Set
postulate Eq₁ : U₁ → U₁ → U₁
postulate eq₂ : ∀ {A B} → T₂ A → T₂ (Eq₂ A B) → T₂ B → U₁

postulate U₀ : Set
postulate T₀ : U₀ → Set
postulate Eq₀ : U₀ → U₀ → U₀
postulate eq₁ : ∀ {S T} → T₁ S → T₁ (Eq₁ S T) → T₁ T → U₀
postulate eq₂-cong : ∀ {A A' B B'}
                   {a : T₂ A} {a' : T₂ A'} {b : T₂ B} {b' : T₂ B'}
                   {A* : T₂ (Eq₂ A A')} {B* : T₂ (Eq₂ B B')} {e : T₂ (Eq₂ A B)} {e' : T₂ (Eq₂ A' B')}
                   (a* : T₁ (eq₂ a A* a')) (e* : T₁ (eq₂ e (Eq₂-cong A* B*) e')) (b* : T₁ (eq₂ b B* b')) →
                   T₁ (Eq₁ (eq₂ a e b) (eq₂ a' e' b'))

