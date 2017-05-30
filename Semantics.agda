module Semantics where

postulate Groupoid : Set
postulate ONE : Groupoid

postulate Groupoid-Functor : Groupoid → Groupoid → Set

postulate Fibration₂ : Groupoid → Set
postulate pullback₂ : ∀ {G} {H} → Groupoid-Functor G H → Fibration₂ H → Fibration₂ G
postulate Section₂ : ∀ {G} → Fibration₂ G → Set
postulate section-pullback₂ : ∀ {G H K} (F : Groupoid-Functor G H) → Section₂ K → Section₂ (pullback₂ F K)

postulate Sigma₂ : ∀ G → Fibration₂ G → Groupoid
postulate p₂ : ∀ {G} {H} → Groupoid-Functor (Sigma₂ G H) G
postulate q₂ : ∀ {G} {H} → Section₂ {Sigma₂ G H} (pullback₂ p₂ H)

postulate Fibration₁ : Groupoid → Set
postulate pullback₁ : ∀ {G} {H} → Groupoid-Functor G H → Fibration₁ H → Fibration₁ G

postulate Sigma₁ : ∀ G → Fibration₁ G → Groupoid
postulate p₁ : ∀ {G} {S} → Groupoid-Functor (Sigma₁ G S) G

postulate Fibration₀ : Groupoid → Set
postulate pullback₀ : ∀ {G} {H} → Groupoid-Functor G H → Fibration₀ H → Fibration₀ G

postulate Sigma₀ : ∀ G → Fibration₀ G → Groupoid
postulate p₀ : ∀ {G} {P} → Groupoid-Functor (Sigma₀ G P) G


