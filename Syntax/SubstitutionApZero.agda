module Syntax.SubstitutionApZero where
open import Semantics
open import Syntax.Typing
open import Syntax.Substitution

ap₀ : ∀ {Γ Δ ⟦T⟧} (σ : Sub Γ Δ) {⟦t⟧} → Δ ⊢₀ ⟦T⟧ ∋ ⟦t⟧ → Γ ⊢₀ pullback₀ ⟦ σ ⟧S ⟦T⟧ ∋ section-pullback₀ ⟦ σ ⟧S ⟦t⟧
ap₀ σ (-var- x) = apV₀ σ x
ap₀ {Γ} .{Δ} σ (-eq***- {Δ} {NWU} {NWU'} {NWD} {NWD'} {NEU} {NEU'} {NED} {NED'} {SWU} {SWU'} {SWD} {SWD'} {SEU} {SEU'} {SED} {SED'}
  {NWU*}
  {NWD*}
  {NEU*}
  {NED*}
  {SWU*}
  {SWD*}
  {SEU*}
  {SED*}
  {NW}
  {NW'}
  {SW}
  {SW'}
  {NE}
  {NE'}
  {SE}
  {SE'}
  {WU}
  {WU'}
  {WD}
  {WD'}
  {EU}
  {EU'}
  {ED}
  {ED'}
  {W}
  {W'}
  {E}
  {E'}
  {NW*}
  {NE*}
  {SW*}
  {SE*}
  {WU*}
  {EU*}
  {WD*}
  {ED*}
  {W*} {E*} s t) =
  -eq***- {Γ} {pullback₂ ⟦ σ ⟧S NWU} {pullback₂ ⟦ σ ⟧S NWU'} {pullback₂ ⟦ σ ⟧S NWD} {pullback₂ ⟦ σ ⟧S NWD'} {pullback₂ ⟦ σ ⟧S NEU}
  {pullback₂ ⟦ σ ⟧S NEU'} {pullback₂ ⟦ σ ⟧S NED} {pullback₂ ⟦ σ ⟧S NED'} {pullback₂ ⟦ σ ⟧S SWU} {pullback₂ ⟦ σ ⟧S SWU'}
  {pullback₂ ⟦ σ ⟧S SWD} {pullback₂ ⟦ σ ⟧S SWD'} {pullback₂ ⟦ σ ⟧S SEU} {pullback₂ ⟦ σ ⟧S SEU'} {pullback₂ ⟦ σ ⟧S SED}
  {pullback₂ ⟦ σ ⟧S SED'} {section-pullback₂ ⟦ σ ⟧S NWU*} {section-pullback₂ ⟦ σ ⟧S NWD*} {section-pullback₂ ⟦ σ ⟧S NEU*}
  {section-pullback₂ ⟦ σ ⟧S NED*} {section-pullback₂ ⟦ σ ⟧S SWU*} {section-pullback₂ ⟦ σ ⟧S SWD*} {section-pullback₂ ⟦ σ ⟧S SEU*}
  {section-pullback₂ ⟦ σ ⟧S SED*} {section-pullback₂ ⟦ σ ⟧S NW} {section-pullback₂ ⟦ σ ⟧S NW'} {section-pullback₂ ⟦ σ ⟧S SW}
  {section-pullback₂ ⟦ σ ⟧S SW'} {section-pullback₂ ⟦ σ ⟧S NE} {section-pullback₂ ⟦ σ ⟧S NE'} {section-pullback₂ ⟦ σ ⟧S SE}
  {section-pullback₂ ⟦ σ ⟧S SE'}
  {section-pullback₂ ⟦ σ ⟧S WU}
  {section-pullback₂ ⟦ σ ⟧S WU'}
  {section-pullback₂ ⟦ σ ⟧S WD}
  {section-pullback₂ ⟦ σ ⟧S WD'} {section-pullback₂ ⟦ σ ⟧S EU}
  {section-pullback₂ ⟦ σ ⟧S EU'}
  {section-pullback₂ ⟦ σ ⟧S ED}
  {section-pullback₂ ⟦ σ ⟧S ED'} {section-pullback₁ ⟦ σ ⟧S W}
  {section-pullback₁ ⟦ σ ⟧S W'}
  {section-pullback₁ ⟦ σ ⟧S E}
  {section-pullback₁ ⟦ σ ⟧S E'} {section-pullback₁ ⟦ σ ⟧S NW*}
  {section-pullback₁ ⟦ σ ⟧S NE*} {section-pullback₁ ⟦ σ ⟧S SW*} {section-pullback₁ ⟦ σ ⟧S SE*} {section-pullback₁ ⟦ σ ⟧S WU*}
  {section-pullback₁ ⟦ σ ⟧S EU*} {section-pullback₁ ⟦ σ ⟧S WD*} {section-pullback₁ ⟦ σ ⟧S ED*}
  {section-pullback₀ ⟦ σ ⟧S W*} {section-pullback₀ ⟦ σ ⟧S E*} (ap₀ σ s) (ap₀ σ t)
