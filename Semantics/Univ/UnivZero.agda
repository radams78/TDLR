{-# OPTIONS --rewriting #-}

module Semantics.Univ.UnivZero where

open import Semantics.Univ.UnivTwo
open import Semantics.Univ.UnivOne

postulate U₀ : Set
postulate T₀ : U₀ → Set
postulate Eq₀ : U₀ → U₀ → U₀
postulate Eq₀-cong : ∀ {P P' Q Q'} → T₀ (Eq₀ P P') → T₀ (Eq₀ Q Q') → T₀ (Eq₀ (Eq₀ P Q) (Eq₀ P' Q'))
postulate eq₁ : ∀ {S T} → T₁ S → T₁ (Eq₁ S T) → T₁ T → U₀
postulate eq₁-cong : ∀ {S S' T T'}
                   {x : T₁ S} {x' : T₁ S'} {y : T₁ T} {y' : T₁ T'}
                   {S* : T₁ (Eq₁ S S')} {T* : T₁ (Eq₁ T T')} {e : T₁ (Eq₁ S T)} {e' : T₁ (Eq₁ S' T')} →
                   T₀ (eq₁ x S* x') → T₀ (eq₁ e (Eq₁-cong S* T*) e') → T₀ (eq₁ y T* y') →
                   T₀ (Eq₀ (eq₁ x e y) (eq₁ x' e' y'))

postulate Pi₂₀ : ∀ A → (T₂ A → U₀) → U₀
postulate Λ₂₀ : ∀ {A} {B} → (∀ a → T₀ (B a)) → T₀ (Pi₂₀ A B)
postulate App₂₀ : ∀ {A} {B} → T₀ (Pi₂₀ A B) → ∀ (a : T₂ A) → T₀ (B a)
postulate Beta₂₀ : ∀ {A} {B} {b} {a} → App₂₀ {A} {B} (Λ₂₀ b) a ▷ b a
{-# REWRITE Beta₂₀ #-}
postulate Pi₂₀* : ∀ {A A' B B'} (A* : T₂ (Eq₂ A A')) → (∀ a a' → T₁ (eq₂ a A* a') → T₀ (Eq₀ (B a) (B' a'))) → T₀ (Eq₀ (Pi₂₀ A B) (Pi₂₀ A' B'))

postulate Pi₀ : ∀ A → (T₁ A → U₀) → U₀
postulate Λ₀ : ∀ {A} {B} → (∀ a → T₀ (B a)) → T₀ (Pi₀ A B)
postulate App₀ : ∀ {A} {B} → T₀ (Pi₀ A B) → ∀ (a : T₁ A) → T₀ (B a)
postulate Beta₀ : ∀ {A} {B} {b} {a} → App₀ {A} {B} (Λ₀ b) a ▷ b a
{-# REWRITE Beta₀ #-}
postulate Pi₀* : ∀ {A A' B B'} (A* : T₁ (Eq₁ A A')) → (∀ a a' → T₀ (eq₁ a A* a') → T₀ (Eq₀ (B a) (B' a'))) → T₀ (Eq₀ (Pi₀ A B) (Pi₀ A' B'))


postulate _⇒₀_ : U₀ → U₀ → U₀
postulate lam₀ : ∀ {A} {B} → (T₀ A → T₀ B) → T₀ (A ⇒₀ B)
postulate app₀ : ∀ {A} {B} → T₀ (A ⇒₀ B) → T₀ A → T₀ B
postulate beta₀ : ∀ {A} {B} {b} {a} → app₀ {A} {B} (lam₀ b) a ▷ b a
{-# REWRITE beta₀ #-}
postulate ⇒₀* : ∀ {A A' B B'} → T₀ (Eq₀ A A') → T₀ (Eq₀ B B') → T₀ (Eq₀ (A ⇒₀ B) (A' ⇒₀ B'))

postulate eq₁-Eq₁-cong : ∀ {A A' B B'}
                       (A* : T₁ (Eq₁ A A')) (B* : T₁ (Eq₁ B B')) (e : T₁ (Eq₁ A B)) (e' : T₁ (Eq₁ A' B')) →
                       eq₁ e (Eq₁-cong A* B*) e' ▷ Pi₀ A (λ a → Pi₀ A' (λ a' → Pi₀ B (λ b → Pi₀ B' (λ b' → eq₁ a A* a' ⇒₀ (eq₁ b B* b' ⇒₀ Eq₀ (eq₁ a e b) (eq₁ a' e' b'))))))
{-# REWRITE eq₁-Eq₁-cong #-}

postulate eq₁-Pi₁* : ∀ {A A' B B'} {A* : T₂ (Eq₂ A A')} {B* : ∀ a a' → T₁ (eq₂ a A* a') → T₁ (Eq₁ (B a) (B' a'))} {f : T₁ (Pi₁ A B)} {g : T₁ (Pi₁ A' B')} →
                   eq₁ f (Pi₁* A* B*) g ▷ Pi₂₀ A (λ a → Pi₂₀ A' (λ a' → Pi₀ (eq₂ a A* a') (λ a* → eq₁ (App₁ f a) (B* a a' a*) (App₁ g a'))))
{-# REWRITE eq₁-Pi₁* #-}

postulate eq₁-⇒₁* : ∀ {A A' B B'} {A* : T₁ (Eq₁ A A')} {B* : T₁ (Eq₁ B B')} {f : T₁ (A ⇒₁ B)} {g : T₁ (A' ⇒₁ B')} →
                  eq₁ f (⇒₁* A* B*) g ▷ Pi₀ A (λ a → Pi₀ A' (λ a' → eq₁ a A* a' ⇒₀ eq₁ (app₁ f a) B* (app₁ g a')))
{-# REWRITE eq₁-⇒₁* #-}

eq₂-cong₂ : ∀ {A A' B B' C C' D D'}
  {a : T₂ A} {a' : T₂ A'} {b : T₂ B} {b' : T₂ B'} {c : T₂ C} {c' : T₂ C'} {d : T₂ D} {d' : T₂ D'}
  {A* : T₂ (Eq₂ A A')} {B* : T₂ (Eq₂ B B')} {C* : T₂ (Eq₂ C C')} {D* : T₂ (Eq₂ D D')}
  {e : T₂ (Eq₂ A B)} {e' : T₂ (Eq₂ A' B')} {f : T₂ (Eq₂ C D)} {f' : T₂ (Eq₂ C' D')}
  {AC : T₂ (Eq₂ A C)} {A'C' : T₂ (Eq₂ A' C')} {BD : T₂ (Eq₂ B D)} {B'D' : T₂ (Eq₂ B' D')}
  {a* : T₁ (eq₂ a A* a')} {b* : T₁ (eq₂ b B* b')} {c* : T₁ (eq₂ c C* c')} {d* : T₁ (eq₂ d D* d')}
  {ac : T₁ (eq₂ a AC c)} {a'c' : T₁ (eq₂ a' A'C' c')} {bd : T₁ (eq₂ b BD d)} {b'd' : T₁ (eq₂ b' B'D' d')}
  {A*C* : T₁ (eq₂ A* (Eq₂-cong AC A'C') C*)} {B*D* : T₁ (eq₂ B* (Eq₂-cong BD B'D') D*)}
  {e* : T₁ (eq₂ e (Eq₂-cong A* B*) e')} {f* : T₁ (eq₂ f (Eq₂-cong C* D*) f')}
  {ef : T₁ (eq₂ e (Eq₂-cong AC BD) f)} {e'f' : T₁ (eq₂ e' (Eq₂-cong A'C' B'D') f')} →
  T₀ (eq₁ a* (eq₂-cong AC A'C' A* C* ac A*C* a'c') c*) →
  T₀ (eq₁ e* (eq₂-cong (Eq₂-cong AC BD) (Eq₂-cong A'C' B'D') (Eq₂-cong A* B*) (Eq₂-cong C* D*) ef (Eq₂-cong₂ A*C* B*D*) e'f') f*) →
  T₀ (eq₁ b* (eq₂-cong BD B'D' B* D* bd B*D* b'd') d*) →
  T₀ (eq₁ (eq₂-cong A* B* e e' a* e* b*) (Eq₁-cong (eq₂-cong AC BD e f ac ef bd) (eq₂-cong A'C' B'D' e' f' a'c' e'f' b'd')) (eq₂-cong C* D* f f' c* f* d*))
eq₂-cong₂ {a = a} {a'} {b} {b'} {c} {c'} {d} {d'} {a* = a*} {b*} {c*} {d*} {ac} {a'c'} {bd} {b'd'} a*∼c* e*∼f* b*∼d* =
  app₀ (App₀ (App₀ (app₀ (App₀ (App₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ e*∼f* a) c) ac) a') c') a'c') b) d) bd) b') d') b'd') a*) c*) a*∼c*) b*) d*) b*∼d*

Eq₁-cong₂ : ∀ {NWU NWD NEU NED SWU SWD SEU SED}
  {NW : T₁ (Eq₁ NWU NWD)} {NE : T₁ (Eq₁ NEU NED)} {SW : T₁ (Eq₁ SWU SWD)} {SE : T₁ (Eq₁ SEU SED)}
  {WU : T₁ (Eq₁ NWU SWU)} {WD : T₁ (Eq₁ NWD SWD)} {EU : T₁ (Eq₁ NEU SEU)} {ED : T₁ (Eq₁ NED SED)} → 
  T₀ (eq₁ NW (Eq₁-cong WU WD) SW) → T₀ (eq₁ NE (Eq₁-cong EU ED) SE) →
  T₀ (eq₁ (Eq₁-cong NW NE) (Eq₁-cong (Eq₁-cong WU EU) (Eq₁-cong WD ED)) (Eq₁-cong SW SE))
Eq₁-cong₂ {WU = WU} {WD} {EU} {ED} W E = Λ₀ (λ NU → Λ₀ (λ SU → Λ₀ (λ ND → Λ₀ (λ SD → lam₀ (λ U → lam₀ (λ D →
  Pi₀* WU (λ nwu swu wu → Pi₀* WD (λ nwd swd wd → Pi₀* EU (λ neu seu eu → Pi₀* ED (λ ned sed ed →
  ⇒₀* (app₀ (app₀ (App₀ (App₀ (App₀ (App₀ W nwu) swu) nwd) swd) wu) wd)
  (⇒₀* (app₀ (app₀ (App₀ (App₀ (App₀ (App₀ E neu) seu) ned) sed) eu) ed)
  (Eq₀-cong (app₀ (app₀ (App₀ (App₀ (App₀ (App₀ U nwu) swu) neu) seu) wu) eu)
  (app₀ (app₀ (App₀ (App₀ (App₀ (App₀ D nwd) swd) ned) sed) wd) ed)))))))))))))

Eq₂-cong₃ : ∀ {NWU NWU' NWD NWD' NEU NEU' NED NED' SWU SWU' SWD SWD' SEU SEU' SED SED'}
  {NWU* : T₂ (Eq₂ NWU NWU')} {NWD* : T₂ (Eq₂ NWD NWD')} {NEU* : T₂ (Eq₂ NEU NEU')} {NED* : T₂ (Eq₂ NED NED')}
  {SWU* : T₂ (Eq₂ SWU SWU')} {SWD* : T₂ (Eq₂ SWD SWD')} {SEU* : T₂ (Eq₂ SEU SEU')} {SED* : T₂ (Eq₂ SED SED')}
  {NW : T₂ (Eq₂ NWU NWD)} {NW' : T₂ (Eq₂ NWU' NWD')} {NE : T₂ (Eq₂ NEU NED)} {NE' : T₂ (Eq₂ NEU' NED')}
  {SW : T₂ (Eq₂ SWU SWD)} {SW' : T₂ (Eq₂ SWU' SWD')} {SE : T₂ (Eq₂ SEU SED)} {SE' : T₂ (Eq₂ SEU' SED')}
  {WU : T₂ (Eq₂ NWU SWU)} {WU' : T₂ (Eq₂ NWU' SWU')} {EU : T₂ (Eq₂ NEU SEU)} {EU' : T₂ (Eq₂ NEU' SEU')}
  {WD : T₂ (Eq₂ NWD SWD)} {WD' : T₂ (Eq₂ NWD' SWD')} {ED : T₂ (Eq₂ NED SED)} {ED' : T₂ (Eq₂ NED' SED')}
  {NW* : T₁ (eq₂ NW (Eq₂-cong NWU* NWD*) NW')} {NE* : T₁ (eq₂ NE (Eq₂-cong NEU* NED*) NE')}
  {SW* : T₁ (eq₂ SW (Eq₂-cong SWU* SWD*) SW')} {SE* : T₁ (eq₂ SE (Eq₂-cong SEU* SED*) SE')}
  {WU* : T₁ (eq₂ NWU* (Eq₂-cong WU WU') SWU*)} {WD* : T₁ (eq₂ NWD* (Eq₂-cong WD WD') SWD*)}
  {EU* : T₁ (eq₂ NEU* (Eq₂-cong EU EU') SEU*)} {ED* : T₁ (eq₂ NED* (Eq₂-cong ED ED') SED*)}
  {W : T₁ (eq₂ NW (Eq₂-cong WU WD) SW)} {E : T₁ (eq₂ NE (Eq₂-cong EU ED) SE)}
  {W' : T₁ (eq₂ NW' (Eq₂-cong WU' WD') SW')} {E' : T₁ (eq₂ NE' (Eq₂-cong EU' ED') SE')} →
  T₀ (eq₁ NW* (eq₂-cong (Eq₂-cong WU WD) (Eq₂-cong WU' WD') (Eq₂-cong NWU* NWD*) (Eq₂-cong SWU* SWD*) W (Eq₂-cong₂ WU* WD*) W') SW*) →
  T₀ (eq₁ NE* (eq₂-cong (Eq₂-cong EU ED) (Eq₂-cong EU' ED') (Eq₂-cong NEU* NED*) (Eq₂-cong SEU* SED*) E (Eq₂-cong₂ EU* ED*) E') SE*) →
  T₀ (eq₁ (Eq₂-cong₂ NW* NE*) (eq₂-cong {a = Eq₂-cong NW NE} {Eq₂-cong SW SE} {Eq₂-cong NW' NE'} {Eq₂-cong SW' SE'}
    (Eq₂-cong (Eq₂-cong WU EU) (Eq₂-cong WD ED)) (Eq₂-cong (Eq₂-cong WU' EU') (Eq₂-cong WD' ED'))
    (Eq₂-cong (Eq₂-cong NWU* NEU*) (Eq₂-cong NWD* NED*)) (Eq₂-cong (Eq₂-cong SWU* SEU*) (Eq₂-cong SWD* SED*))
    (Eq₂-cong₂ W E)
    (Eq₂-cong₂ {A* = Eq₂-cong NWU* NEU*} {Eq₂-cong NWD* NED*} {Eq₂-cong SWU* SEU*} {Eq₂-cong SWD* SED*} {Eq₂-cong WU EU} {Eq₂-cong WU' EU'}
      {Eq₂-cong WD ED} {Eq₂-cong WD' ED'} (Eq₂-cong₂ WU* EU*) (Eq₂-cong₂ WD* ED*)) (Eq₂-cong₂ W' E')) (Eq₂-cong₂ SW* SE*))
Eq₂-cong₃ {NWU* = NWU*} {NWD*} {NEU*} {NED*} {SWU*} {SWD*} {SEU*} {SED*} {NW} {NW'} {NE} {NE'} {SW = SW} {SW'} {SE} {SE'} {WU = WU} {WU'} {EU} {EU'} {WD} {WD'} {ED} {ED'} {NW*} {WU* = WU*} {WD*} {EU*} {ED*} {W} {E} {W'} {E'} W* E* =
  Λ₂₀ (λ NU → Λ₂₀ (λ SU → Λ₀ (λ U → Λ₂₀ (λ NU' → Λ₂₀ (λ SU' → Λ₀ (λ U' → Λ₂₀ (λ ND → Λ₂₀ (λ SD → Λ₀ (λ D →
  Λ₂₀ (λ ND' → Λ₂₀ (λ SD' → Λ₀ (λ D' → Λ₀ (λ NU* → Λ₀ (λ SU* → lam₀ (λ U* → Λ₀ (λ ND* → Λ₀ (λ SD* → lam₀ (λ D* →
  Λ₀ (λ N → Λ₀ (λ S → Λ₀ (λ N' → Λ₀ (λ S' → lam₀ (λ x → lam₀ (λ x₁ → Pi₂₀* WU (λ nwu swu wu → Pi₂₀* WU' (λ nwu' swu' wu' →
  Pi₀* (eq₂-cong WU WU' NWU* SWU* wu WU* wu') (λ nwu* swu* wu* → Pi₂₀* WD (λ nwd swd wd → Pi₂₀* WD' (λ nwd' swd' wd' →
  Pi₀* (eq₂-cong WD WD' NWD* SWD* wd WD* wd') (λ nwd* swd* wd* → Pi₂₀* EU (λ neu seu eu → Pi₂₀* EU' (λ neu' seu' eu' →
  Pi₀* (eq₂-cong EU EU' NEU* SEU* eu EU* eu') (λ neu* seu* eu* → Pi₂₀* ED (λ ned sed ed → Pi₂₀* ED' (λ ned' sed' ed' →
  Pi₀* (eq₂-cong ED ED' NED* SED* ed ED* ed') (λ ned* sed* ed* → Pi₀* (eq₂-cong WU WD NW SW wu W wd) (λ nw sw w →
  Pi₀* (eq₂-cong WU' WD' NW' SW' wu' W' wd') (λ nw' sw' w' → ⇒₀* (eq₁-cong {eq₂ nwu NW nwd} {eq₂ swu SW swd} {eq₂ nwu' NW' nwd'} {eq₂ swu' SW' swd'} {nw} {sw} {nw'} {sw'} {eq₂-cong WU WD NW SW wu W wd} {eq₂-cong WU' WD' NW' SW' wu' W' wd'} {eq₂-cong NWU* NWD* NW NW' nwu* NW* nwd*} w
    (app₀ (App₀ (App₀ (app₀ (App₀ (App₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ W* nwu) swu) wu) nwu') swu') wu') nwd) swd) wd) nwd') swd') wd') nwu*) swu*) wu*) nwd*) swd*) wd*)
    w')
  (Pi₀* (eq₂-cong EU ED NE SE eu E ed) (λ ne se e → Pi₀* (eq₂-cong EU' ED' NE' SE' eu' E' ed') (λ ne' se' e' → ⇒₀* (eq₁-cong e
    (app₀ (App₀ (App₀ (app₀ (App₀ (App₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ E* neu) seu) eu) neu') seu') eu') ned) sed) ed) ned') sed') ed') neu*) seu*) eu*) ned*) sed*) ed*)
    e')
  (Pi₀* (eq₂-cong WU EU NU SU wu U eu) (λ nu su u → Pi₀* (eq₂-cong WU' EU' NU' SU' wu' U' eu') (λ nu' su' u' → Pi₀* (eq₂-cong WD ED ND SD wd D ed) (λ nd sd d →
  Pi₀* (eq₂-cong WD' ED' ND' SD' wd' D' ed') (λ nd' sd' d' → ⇒₀*
    (eq₁-cong u (app₀ (App₀ (App₀ (app₀ (App₀ (App₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ U* nwu) swu) wu) nwu') swu') wu') neu) seu) eu) neu') seu') eu') nwu*) swu*) wu*) neu*) seu*) eu*) u')
    (⇒₀* (eq₁-cong d (app₀ (App₀ (App₀ (app₀ (App₀ (App₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ D* nwd) swd) wd) nwd') swd') wd') ned) sed) ed) ned') sed') ed') nwd*) swd*) wd*) ned*) sed*) ed*) d')
    (Eq₀-cong (eq₁-cong u (app₀ (App₀ (App₀ (app₀ (App₀ (App₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ x nwu) swu) wu) nwd) swd) wd) neu) seu) eu) ned) sed) ed) nw) sw) w) ne) se) e) d)
    (eq₁-cong u' (app₀ (App₀ (App₀ (app₀ (App₀ (App₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ (App₀ (App₂₀ (App₂₀ x₁ nwu') swu') wu') nwd') swd') wd') neu') seu') eu') ned') sed') ed') nw') sw') w') ne') se') e') d')))))))))))))))))))))))))))))))))))))))))))))))))
