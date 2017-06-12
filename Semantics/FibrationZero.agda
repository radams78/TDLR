module Semantics.FibrationZero where
open import Semantics.Groupoid
open import Semantics.Univ

record Fibration₀ (G : Groupoid) : Set where
  field
    Fibre : Groupoid.Vertex G → U₀
    Fibre-cong : ∀ {x y} → Groupoid.Path G x y → T₀ (Eq₀ (Fibre x) (Fibre y))

pullback₀ : ∀ {G} {H} → Groupoid-Functor G H → Fibration₀ H → Fibration₀ G
pullback₀ F P = record {
  Fibre = λ x → Fibration₀.Fibre P (ap-vertex F x) ;
  Fibre-cong = λ p → Fibration₀.Fibre-cong P (ap-path F p) }

record Section₀ {G} (P : Fibration₀ G) : Set where
  field
    vertex : ∀ x → T₀ (Fibration₀.Fibre P x)
    
section-pullback₀ : ∀ {G H S} (F : Groupoid-Functor G H) → Section₀ S → Section₀ (pullback₀ F S)
section-pullback₀ F s = record { vertex = λ x → Section₀.vertex s (ap-vertex F x) }

