module Semantics where

postulate Groupoid : Set
postulate Groupoid-Functor : Groupoid → Groupoid → Set
postulate Groupoid-NatIso : ∀ {G H} → Groupoid-Functor G H → Groupoid-Functor G H → Set

postulate ONE : Groupoid
postulate bang : ∀ {G} → Groupoid-Functor G ONE
postulate bang-ref : ∀ {G} → Groupoid-NatIso (bang {G}) bang

postulate Fibration₂ : Groupoid → Set
postulate Fibration-Eq₂ : ∀ {G} → Fibration₂ G → Fibration₂ G → Set
postulate pullback₂ : ∀ {G} {H} → Groupoid-Functor G H → Fibration₂ H → Fibration₂ G
postulate pullback₂-congl : ∀ {G} {H} {F F' : Groupoid-Functor G H} →
                          Groupoid-NatIso F F' → (K : Fibration₂ H) → Fibration-Eq₂ (pullback₂ F K) (pullback₂ F' K)
postulate Section₂ : ∀ {G} → Fibration₂ G → Set
postulate section-pullback₂ : ∀ {G H K} (F : Groupoid-Functor G H) → Section₂ K → Section₂ (pullback₂ F K)

postulate Sigma₂ : ∀ G → Fibration₂ G → Groupoid
postulate pair₂ : ∀ {G H K} (F : Groupoid-Functor G H) → Section₂ (pullback₂ F K) → Groupoid-Functor G (Sigma₂ H K)
postulate p₂ : ∀ {G} {H} → Groupoid-Functor (Sigma₂ G H) G
postulate q₂ : ∀ {G} {H} → Section₂ {Sigma₂ G H} (pullback₂ p₂ H)

postulate Fibration₁ : Groupoid → Set
postulate Fibration-Eq₁ : ∀ {G} → Fibration₁ G → Fibration₁ G → Set
postulate pullback₁ : ∀ {G} {H} → Groupoid-Functor G H → Fibration₁ H → Fibration₁ G
postulate pullback₁-congl : ∀ {G} {H} {F F' : Groupoid-Functor G H} →
                          Groupoid-NatIso F F' → (S : Fibration₁ H) → Fibration-Eq₁ (pullback₁ F S) (pullback₁ F' S)
postulate Section₁ : ∀ {G} → Fibration₁ G → Set
postulate section-pullback₁ : ∀ {G H S} (F : Groupoid-Functor G H) → Section₁ S → Section₁ (pullback₁ F S)

postulate EQ₂ : ∀ {G H K} → Section₂ {G} H → Fibration-Eq₂ H K → Section₂ K → Fibration₁ G
postulate pair₂-cong : ∀ {G H K} {F F' : Groupoid-Functor G H} {s : Section₂ (pullback₂ F K)} {t : Section₂ (pullback₂ F' K)} →
                     (α : Groupoid-NatIso F F') → Section₁ (EQ₂ s (pullback₂-congl α K) t) → Groupoid-NatIso (pair₂ F s) (pair₂ F' t)

postulate Sigma₁ : ∀ G → Fibration₁ G → Groupoid
postulate pair₁ : ∀ {G H S} (F : Groupoid-Functor G H) → Section₁ (pullback₁ F S) → Groupoid-Functor G (Sigma₁ H S)
postulate p₁ : ∀ {G} {S} → Groupoid-Functor (Sigma₁ G S) G
postulate q₁ : ∀ {G} {S} → Section₁ {Sigma₁ G S} (pullback₁ p₁ S)

postulate Fibration₀ : Groupoid → Set
postulate pullback₀ : ∀ {G} {H} → Groupoid-Functor G H → Fibration₀ H → Fibration₀ G
postulate Section₀ : ∀ {G} → Fibration₀ G → Set
postulate section-pullback₀ : ∀ {G H S} (F : Groupoid-Functor G H) → Section₀ S → Section₀ (pullback₀ F S)

postulate EQ₁ : ∀ {G S T} → Section₁ {G} S → Fibration-Eq₁ S T → Section₁ T → Fibration₀ G
postulate pair₁-cong : ∀ {G H S} {F F' : Groupoid-Functor G H} {s : Section₁ (pullback₁ F S)} {t : Section₁ (pullback₁ F' S)} →
                     (α : Groupoid-NatIso F F') → Section₀ (EQ₁ s (pullback₁-congl α S) t) → Groupoid-NatIso (pair₁ F s) (pair₁ F' t)

postulate Sigma₀ : ∀ G → Fibration₀ G → Groupoid
postulate pair₀ : ∀ {G H S} (F : Groupoid-Functor G H) → Section₀ (pullback₀ F S) → Groupoid-Functor G (Sigma₀ H S)
postulate p₀ : ∀ {G} {P} → Groupoid-Functor (Sigma₀ G P) G
postulate q₀ : ∀ {G} {S} → Section₀ {Sigma₀ G S} (pullback₀ p₀ S)
