module Semantics.Square where
open import Semantics.Univ
open import Semantics.Groupoid
open import Semantics.FibrationZero
open import Semantics.FibrationOne
open import Semantics.FibrationTwo
open import Semantics.SectionTwo
open import Semantics.SectionTwoEq

record Square (G : Groupoid) : Set where
  constructor mkSquare
  field
    NW : Fibration₂ G
    NE : Fibration₂ G
    SW : Fibration₂ G
    SE : Fibration₂ G
    N : Section₂ (Fibration-Eq₂ NW NE)
    S : Section₂ (Fibration-Eq₂ SW SE)
    W : Section₂ (Fibration-Eq₂ NW SW)
    E : Section₂ (Fibration-Eq₂ NE SE)

  Fill : Fibration₁ G
  Fill = EQ₂ N (Fibration-Eq₂-cong W E) S

  record Section : Set where
    field
      nw : Section₂ NW
      ne : Section₂ NE
      sw : Section₂ SW
      se : Section₂ SE
      n : Section₁ (EQ₂ nw N ne)
      s : Section₁ (EQ₂ sw S se)
      w : Section₁ (EQ₂ nw W sw)
      e : Section₁ (EQ₂ ne E se)

    Matches-Fill : Section₁ Fill → Fibration₀ G
    Matches-Fill f = EQ₁ n (EQ₂-cong nw sw ne se w f e) s

Fibration-Eq₂-cong₂ : ∀ {G} (top bottom : Square G) →
  Section₁ (Square.Fill top) → Section₁ (Square.Fill bottom) →
  Section₁ (Square.Fill (Square-Eq top bottom))
Fibration-Eq₂-cong₂ top bottom top-fill bottom-fill = record {
  vertex = λ x → Eq₂-cong₂ (Section₁.vertex top-fill x) (Section₁.vertex bottom-fill x) ;
  edge = λ p → Eq₂-cong₃ (Section₁.edge top-fill p) (Section₁.edge bottom-fill p) }

Fill-cong : ∀ {G} {S T : Square G} (E : Square.Section (Square-Eq S T)) →
  Section₁ (Fibration-Eq₁ (Square.Fill S) (Square.Fill T))
Fill-cong {G} {S} {T} E N* S* W* E* = EQ₂-cong (Square.N S) (Square.N T) (Square.S S) (Square.S T) N* (Fibration-Eq₂-cong₂
  (mkSquare (Square.NW S) (Square.SW S) (Square.NW T) (Square.SW T) (Square.W S) (Square.W T) (Square.Section.nw E) (Square.Section.sw E))
  (mkSquare (Square.NE S) (Square.SE S) (Square.NE T) (Square.SE T) (Square.E S) (Square.E T) (Square.Section.ne E) (Square.Section.se E)) W* E*) S*
