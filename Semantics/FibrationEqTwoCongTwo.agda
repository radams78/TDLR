module Semantics.FibrationEqTwoCongTwo where

open import Semantics.Univ
open import Semantics.Groupoid
open import Semantics.FibrationZero
open import Semantics.FibrationOne
open import Semantics.FibrationTwo
open import Semantics.SectionTwo
open import Semantics.SectionTwoEq

Fibration-Eq₂-cong₂ : ∀ {G} {NWU NWD NEU NED SWU SWD SEU SED : Fibration₂ G}
  (NW : Section₂ (Fibration-Eq₂ NWU NWD)) (SW : Section₂ (Fibration-Eq₂ SWU SWD))
  (NE : Section₂ (Fibration-Eq₂ NEU NED)) (SE : Section₂ (Fibration-Eq₂ SEU SED))
  {WU : Section₂ (Fibration-Eq₂ NWU SWU)} {WD : Section₂ (Fibration-Eq₂ NWD SWD)}
  {EU : Section₂ (Fibration-Eq₂ NEU SEU)} {ED : Section₂ (Fibration-Eq₂ NED SED)} →
  Section₁ (EQ₂ NW (Fibration-Eq₂-cong WU WD) SW) → Section₁ (EQ₂ NE (Fibration-Eq₂-cong EU ED) SE) →
  Section₁ (EQ₂ (Fibration-Eq₂-cong NW NE) (Fibration-Eq₂-cong (Fibration-Eq₂-cong WU EU) (Fibration-Eq₂-cong WD ED)) (Fibration-Eq₂-cong SW SE))
Fibration-Eq₂-cong₂ _ _ _ _ W E = record {
  vertex = λ x → Eq₂-cong₂ (Section₁.vertex W x) (Section₁.vertex E x) ;
  edge = λ p → Eq₂-cong₃ (Section₁.edge W p) (Section₁.edge E p) }

