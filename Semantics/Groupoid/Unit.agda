module Semantics.Groupoid.Unit where
open import Semantics.Groupoid

postulate ONE : Groupoid
postulate bang : ∀ {G} → Groupoid-Functor G ONE
postulate bang-ref : ∀ {G} → Groupoid-NatIso (bang {G}) bang

