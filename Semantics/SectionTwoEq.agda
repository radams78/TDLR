module Semantics.SectionTwoEq where

open import Semantics.Univ
open import Semantics.Groupoid
open import Semantics.FibrationZero
open import Semantics.FibrationOne
open import Semantics.FibrationTwo
open import Semantics.SectionTwo

EQ₂ : ∀ {G H K} → Section₂ {G} H → Section₂ (Fibration-Eq₂ H K) → Section₂ K → Fibration₁ G
EQ₂ s e t = record {
  Fibre = λ x → eq₂ (Section₂.vertex s x) (Section₂.vertex e x) (Section₂.vertex t x) ;
  Fibre-cong = λ p → eq₂-cong (Section₂.path s p) (Section₂.path e p) (Section₂.path t p);
  Fibre-cong₂ = λ fill → eq₂-cong₂ (Section₂.face s fill) (Section₂.face e fill) (Section₂.face t fill) }

EQ₂-cong : ∀ {G H H' K K'}
  (s : Section₂ {G} H) (s' : Section₂ H')
  (t : Section₂ K) (t' : Section₂ K')
  {e : Section₂ (Fibration-Eq₂ H K)} {e' : Section₂ (Fibration-Eq₂ H' K')}
  {H* : Section₂ (Fibration-Eq₂ H H')} {K* : Section₂ (Fibration-Eq₂ K K')} →
  Section₁ (EQ₂ s H* s') → Section₁ (EQ₂ e (Fibration-Eq₂-cong H* K*) e') → Section₁ (EQ₂ t K* t') →
  Section₁ (Fibration-Eq₁ (EQ₂ s e t) (EQ₂ s' e' t'))
EQ₂-cong _ _ _ _ s* e* t* = record {
  vertex = λ x → eq₂-cong (Section₁.vertex s* x) (Section₁.vertex e* x) (Section₁.vertex t* x) ;
  edge = λ p → eq₂-cong₂ (Section₁.edge s* p) (Section₁.edge e* p) (Section₁.edge t* p) }

section-pullback₂-congl : ∀ {G H K} {F F' : Groupoid-Functor G H} →
  (α : Groupoid-NatIso F F') (s : Section₂ K) →
  Section₁ (EQ₂ (section-pullback₂ F s) (pullback₂-congl α K) (section-pullback₂ F' s))
section-pullback₂-congl α s = record {
  vertex = λ x → Section₂.path s (Groupoid-NatIso.comp α x) ;
  edge = λ p → Section₂.face s (Groupoid-NatIso.natural α p) }

Fibration-Eq₂-cong₂ : ∀ {G} {A A' B B' C C' D D' : Fibration₂ G}
    (A* : Section₂ (Fibration-Eq₂ A A')) (B* : Section₂ (Fibration-Eq₂ B B'))
    (C* : Section₂ (Fibration-Eq₂ C C')) (D* : Section₂ (Fibration-Eq₂ D D'))
    {AB : Section₂ (Fibration-Eq₂ A B)} {A'B' : Section₂ (Fibration-Eq₂ A' B')}
    {CD : Section₂ (Fibration-Eq₂ C D)} {C'D' : Section₂ (Fibration-Eq₂ C' D')} →
    Section₁ (EQ₂ A* (Fibration-Eq₂-cong AB A'B') B*) →
    Section₁ (EQ₂ C* (Fibration-Eq₂-cong CD C'D') D*) →
    Section₁ (EQ₂ (Fibration-Eq₂-cong A* C*)
      (Fibration-Eq₂-cong (Fibration-Eq₂-cong AB CD) (Fibration-Eq₂-cong A'B' C'D'))
      (Fibration-Eq₂-cong B* D*))
Fibration-Eq₂-cong₂ _ _ _ _ A*B* C*D* = record {
  vertex = λ x → Eq₂-cong₂ (Section₁.vertex A*B* x) (Section₁.vertex C*D* x) ;
  edge = λ p → Eq₂-cong₃ (Section₁.edge A*B* p) (Section₁.edge C*D* p) }

