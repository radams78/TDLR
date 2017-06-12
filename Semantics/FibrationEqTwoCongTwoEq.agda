module Semantics.FibrationEqTwoCongTwoEq where
open import Semantics.FibrationZero
open import Semantics.FibrationOne
open import Semantics.FibrationTwo
open import Semantics.SectionTwo
open import Semantics.SectionTwoEq
open import Semantics.FibrationEqTwoCongTwo

Fibration-Eq₂-cong₂-eq-Eq₂-cong₂ : ∀ {G}
 (NWU NWU' NWD NWD' NEU NEU' NED NED' SWU SWU' SWD SWD' SEU SEU' SED SED' : Fibration₂ G)
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
    (W : Section₁ (EQ₂ NW (Fibration-Eq₂-cong WU WD) SW))
    (W' : Section₁ (EQ₂ NW' (Fibration-Eq₂-cong WU' WD') SW'))
    (E : Section₁ (EQ₂ NE (Fibration-Eq₂-cong EU ED) SE))
    (E' : Section₁ (EQ₂ NE' (Fibration-Eq₂-cong EU' ED') SE'))
    (NW* : Section₁ (EQ₂ NW (Fibration-Eq₂-cong NWU* NWD*) NW')) (NE* : Section₁ (EQ₂ NE (Fibration-Eq₂-cong NEU* NED*) NE'))
    (SW* : Section₁ (EQ₂ SW (Fibration-Eq₂-cong SWU* SWD*) SW')) (SE* : Section₁ (EQ₂ SE (Fibration-Eq₂-cong SEU* SED*) SE'))
    (WU* : Section₁ (EQ₂ WU (Fibration-Eq₂-cong NWU* SWU*) WU'))
    (WD* : Section₁ (EQ₂ WD (Fibration-Eq₂-cong NWD* SWD*) WD'))
    (EU* : Section₁ (EQ₂ EU (Fibration-Eq₂-cong NEU* SEU*) EU'))
    (ED* : Section₁ (EQ₂ ED (Fibration-Eq₂-cong NED* SED*) ED')) →
    Fibration₀ G
Fibration-Eq₂-cong₂-eq-Eq₂-cong₂ {G} NWU NWU' NWD NWD' NEU NEU' NED NED' SWU SWU' SWD SWD' SEU SEU' SED SED'
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
  W
  W'
  E
  E' NW* NE* SW* SE* WU* WD* EU* ED*
  = EQ₁ (Fibration-Eq₂-cong₂ NW SW NE SE W E)
    (EQ₂-cong (Fibration-Eq₂-cong NW NE) (Fibration-Eq₂-cong NW' NE') (Fibration-Eq₂-cong SW SE) (Fibration-Eq₂-cong SW' SE')
        (Fibration-Eq₂-cong₂ NW NW' NE NE' NW* NE*)
        (Fibration-Eq₂-cong₂ (Fibration-Eq₂-cong WU EU) (Fibration-Eq₂-cong WU' EU') (Fibration-Eq₂-cong WD ED) (Fibration-Eq₂-cong WD' ED')
          (Fibration-Eq₂-cong₂ WU WU' EU EU' WU* EU*) (Fibration-Eq₂-cong₂ WD WD' ED ED' WD* ED*)) (Fibration-Eq₂-cong₂ SW SW' SE SE' SW* SE*))
        (Fibration-Eq₂-cong₂ NW' SW' NE' SE' W' E')
