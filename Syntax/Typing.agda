module Syntax.Typing where
open import Semantics
open import Syntax.Context
open import Syntax.Variable

data _⊢_gpd : ∀ Γ → Fibration₂ ⟦ Γ ⟧C → Set where
  -eq- : ∀ {Γ G H} → Γ ⊢ G gpd → Γ ⊢ H gpd → Γ ⊢ Fibration-Eq₂ G H gpd
  
data _⊢₂_∋_ : ∀ Γ (G : Fibration₂ ⟦ Γ ⟧C) → Section₂ G → Set where
  -var- : ∀ {Γ T ⟦x⟧} → Γ var₂ T ∋ ⟦x⟧ → Γ ⊢₂ T ∋ ⟦x⟧
  -eq*- : ∀ {Γ ⟦G⟧ ⟦G'⟧ ⟦H⟧ ⟦H'⟧ ⟦G*⟧ ⟦H*⟧} →
    Γ ⊢₂ Fibration-Eq₂ ⟦G⟧ ⟦G'⟧ ∋ ⟦G*⟧ → Γ ⊢₂ Fibration-Eq₂ ⟦H⟧ ⟦H'⟧ ∋ ⟦H*⟧ →
    Γ ⊢₂ Fibration-Eq₂ (Fibration-Eq₂ ⟦G⟧ ⟦H⟧) (Fibration-Eq₂ ⟦G'⟧ ⟦H'⟧) ∋ Fibration-Eq₂-cong ⟦G*⟧ ⟦H*⟧

--TODO Relabel with cubical notation
data _⊢₁_∋_ : ∀ Γ (S : Fibration₁ ⟦ Γ ⟧C) → Section₁ S → Set where
  -var- : ∀ {Γ T ⟦x⟧} → Γ var₁ T ∋ ⟦x⟧ → Γ ⊢₁ T ∋ ⟦x⟧
  -eq**- : ∀ {Γ ⟦G⟧ ⟦G'⟧ ⟦H⟧ ⟦H'⟧ ⟦K⟧ ⟦K'⟧ ⟦L⟧ ⟦L'⟧}
    {⟦G*⟧ : Section₂ (Fibration-Eq₂ ⟦G⟧ ⟦G'⟧)}
    {⟦H*⟧ : Section₂ (Fibration-Eq₂ ⟦H⟧ ⟦H'⟧)}
    {⟦K*⟧ : Section₂ (Fibration-Eq₂ ⟦K⟧ ⟦K'⟧)}
    {⟦L*⟧ : Section₂ (Fibration-Eq₂ ⟦L⟧ ⟦L'⟧)}
    {⟦GK⟧ : Section₂ (Fibration-Eq₂ ⟦G⟧ ⟦K⟧)}
    {⟦G'K'⟧ : Section₂ (Fibration-Eq₂ ⟦G'⟧ ⟦K'⟧)}
    {⟦HL⟧ : Section₂ (Fibration-Eq₂ ⟦H⟧ ⟦L⟧)}
    {⟦H'L'⟧  : Section₂ (Fibration-Eq₂ ⟦H'⟧ ⟦L'⟧)}
    {⟦e⟧ ⟦f⟧} →
    Γ ⊢₁ EQ₂ ⟦G*⟧ (Fibration-Eq₂-cong ⟦GK⟧ ⟦G'K'⟧) ⟦K*⟧ ∋ ⟦e⟧ →
    Γ ⊢₁ EQ₂ ⟦H*⟧ (Fibration-Eq₂-cong ⟦HL⟧ ⟦H'L'⟧) ⟦L*⟧ ∋ ⟦f⟧ →
    Γ ⊢₁ EQ₂ (Fibration-Eq₂-cong ⟦G*⟧ ⟦H*⟧) (Fibration-Eq₂-cong (Fibration-Eq₂-cong ⟦GK⟧ ⟦HL⟧) (Fibration-Eq₂-cong ⟦G'K'⟧ ⟦H'L'⟧)) (Fibration-Eq₂-cong ⟦K*⟧ ⟦L*⟧) ∋ Fibration-Eq₂-cong₂ ⟦G*⟧ ⟦K*⟧ ⟦H*⟧ ⟦L*⟧ ⟦e⟧ ⟦f⟧
--  -eq*- : ∀ {Γ ⟦S⟧ ⟦S'⟧ ⟦T⟧ ⟦T'⟧ ⟦S*⟧ ⟦T*⟧} →
--    Γ ⊢₁ Fibration-Eq₁ ⟦S⟧ ⟦S'⟧ ∋ ⟦S*⟧ → Γ ⊢₁ Fibration-Eq₁ ⟦T⟧ ⟦T'⟧ ∋ ⟦T*⟧ →
--    Γ ⊢₁ Fibration-Eq₁ (Fibration-Eq₁ ⟦S⟧ ⟦T⟧) (Fibration-Eq₁ ⟦S'⟧ ⟦T'⟧) ∋ Fibration-Eq₁-cong ⟦S*⟧ ⟦T*⟧

data _⊢₀_∋_ : ∀ Γ (P : Fibration₀ ⟦ Γ ⟧C) → Section₀ P → Set where
  -var- : ∀ {Γ P ⟦x⟧} → Γ var₀ P ∋ ⟦x⟧ → Γ ⊢₀ P ∋ ⟦x⟧
  -eq***- : ∀ {Γ NWU NWU' NWD NWD' NEU NEU' NED NED' SWU SWU' SWD SWD' SEU SEU' SED SED'}
    {NWU* : Section₂ (Fibration-Eq₂ NWU NWU')} {NWD* : Section₂ (Fibration-Eq₂ NWD NWD')}
    {NEU* : Section₂ (Fibration-Eq₂ NEU NEU')} {NED* : Section₂ (Fibration-Eq₂ NED NED')}
    {SWU* : Section₂ (Fibration-Eq₂ SWU SWU')} {SWD* : Section₂ (Fibration-Eq₂ SWD SWD')}
    {SEU* : Section₂ (Fibration-Eq₂ SEU SEU')} {SED* : Section₂ (Fibration-Eq₂ SED SED')}
    {NW : Section₂ (Fibration-Eq₂ NWU NWD)}
    {NW' : Section₂ (Fibration-Eq₂ NWU' NWD')}
    {SW : Section₂ (Fibration-Eq₂ SWU SWD)}
    {SW' : Section₂ (Fibration-Eq₂ SWU' SWD')}
    {NE : Section₂ (Fibration-Eq₂ NEU NED)}
    {NE' : Section₂ (Fibration-Eq₂ NEU' NED')}
    {SE : Section₂ (Fibration-Eq₂ SEU SED)}
    {SE' : Section₂ (Fibration-Eq₂ SEU' SED')}
    {WU : Section₂ (Fibration-Eq₂ NWU SWU)}
    {WU' : Section₂ (Fibration-Eq₂ NWU' SWU')}
    {WD : Section₂ (Fibration-Eq₂ NWD SWD)}
    {WD' : Section₂ (Fibration-Eq₂ NWD' SWD')}
    {EU : Section₂ (Fibration-Eq₂ NEU SEU)}
    {EU' : Section₂ (Fibration-Eq₂ NEU' SEU')}
    {ED : Section₂ (Fibration-Eq₂ NED SED)}
    {ED' : Section₂ (Fibration-Eq₂ NED' SED')}
    {W : Section₁ (EQ₂ NW (Fibration-Eq₂-cong WU WD) SW)}
    {W' : Section₁ (EQ₂ NW' (Fibration-Eq₂-cong WU' WD') SW')}
    {E : Section₁ (EQ₂ NE (Fibration-Eq₂-cong EU ED) SE)}
    {E' : Section₁ (EQ₂ NE' (Fibration-Eq₂-cong EU' ED') SE')}
    {NW* : Section₁ (EQ₂ NW (Fibration-Eq₂-cong NWU* NWD*) NW')} {NE* : Section₁ (EQ₂ NE (Fibration-Eq₂-cong NEU* NED*) NE')}
    {SW* : Section₁ (EQ₂ SW (Fibration-Eq₂-cong SWU* SWD*) SW')} {SE* : Section₁ (EQ₂ SE (Fibration-Eq₂-cong SEU* SED*) SE')}
    {WU* : Section₁ (EQ₂ WU (Fibration-Eq₂-cong NWU* SWU*) WU')}
    {WD* : Section₁ (EQ₂ WD (Fibration-Eq₂-cong NWD* SWD*) WD')}
    {EU* : Section₁ (EQ₂ EU (Fibration-Eq₂-cong NEU* SEU*) EU')}
    {ED* : Section₁ (EQ₂ ED (Fibration-Eq₂-cong NED* SED*) ED')}
    {W* : Section₀ (EQ₁ W (EQ₂-cong NW NW' SW SW' NW* (Fibration-Eq₂-cong₂ WU WU' WD WD' WU* WD*) SW*) W')}
    {E* : Section₀ (EQ₁ E (EQ₂-cong NE NE' SE SE' NE* (Fibration-Eq₂-cong₂ EU EU' ED ED' EU* ED*) SE*) E')} →
    Γ ⊢₀ EQ₁ W (EQ₂-cong NW NW' SW SW' NW* (Fibration-Eq₂-cong₂ WU WU' WD WD' WU* WD*) SW*) W' ∋ W* →
    Γ ⊢₀ EQ₁ E (EQ₂-cong NE NE' SE SE' NE* (Fibration-Eq₂-cong₂ EU EU' ED ED' EU* ED*) SE*) E' ∋ E* →
    Γ ⊢₀ Fibration-Eq₂-cong₂-eq-Eq₂-cong₂
      NWU NWU' NWD NWD' NEU NEU' NED NED' SWU SWU' SWD SWD' SEU SEU' SED SED'
      W W' E E' NW* NE* SW* SE* WU* WD* EU* ED* ∋
        Fibration-Eq₂-cong₃ NW NE NW' NE' SW SE SW' SE' WU EU WU' EU' WD ED WD' ED' NWU* NWD* NEU* NED* SWU* SWD* SEU* SED* W* E*
