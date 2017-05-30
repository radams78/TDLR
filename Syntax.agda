module Syntax where

postulate Groupoid : Set
postulate Groupoid-Fibration : Groupoid → Set
postulate ONE : Groupoid
postulate Sigma : ∀ G → Groupoid-Fibration G → Groupoid

data Cx : Set
⟦_⟧C : Cx → Groupoid

data Cx where
  ε : Cx
  _,₂_ : ∀ Γ → Groupoid-Fibration ⟦ Γ ⟧C → Cx

⟦ ε ⟧C = ONE
⟦ Γ ,₂ G ⟧C = Sigma ⟦ Γ ⟧C G
