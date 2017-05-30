module Semantics where

postulate Groupoid : Set
postulate ONE : Groupoid

postulate Fibration₂ : Groupoid → Set
postulate Sigma₂ : ∀ G → Fibration₂ G → Groupoid

postulate Fibration₁ : Groupoid → Set
postulate Sigma₁ : ∀ G → Fibration₁ G → Groupoid

postulate Fibration₀ : Groupoid → Set
postulate Sigma₀ : ∀ G → Fibration₀ G → Groupoid

