module Syntax.Context where
open import Semantics

data Cx : Set
⟦_⟧C : Cx → Groupoid

infix 25 _,₂_
data Cx where
  ε : Cx
  _,₂_ : ∀ Γ → Fibration₂ ⟦ Γ ⟧C → Cx
  _,₁_ : ∀ Γ → Fibration₁ ⟦ Γ ⟧C → Cx
  _,₀_ : ∀ Γ → Fibration₀ ⟦ Γ ⟧C → Cx
  
⟦ ε ⟧C = ONE
⟦ Γ ,₂ G ⟧C = Sigma₂ ⟦ Γ ⟧C G
⟦ Γ ,₁ S ⟧C = Sigma₁ ⟦ Γ ⟧C S
⟦ Γ ,₀ P ⟧C = Sigma₀ ⟦ Γ ⟧C P
