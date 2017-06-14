module Semantics.Univ.UnivTwo where

postulate U₂ : Set
postulate T₂ : U₂ → Set
postulate Eq₂ : U₂ → U₂ → U₂
postulate Eq₂-cong : ∀ {A A' B B'} → T₂ (Eq₂ A A') → T₂ (Eq₂ B B') → T₂ (Eq₂ (Eq₂ A B) (Eq₂ A' B'))
postulate Ref₂ : ∀ A → T₂ (Eq₂ A A)

