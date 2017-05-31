\begin{code}
module Syntax where
open import Semantics
\end{code}

%<*Contexts>
\begin{code}
data Cx : Set
⟦_⟧C : Cx → Groupoid
\end{code}
%</Contexts>

\begin{code}
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

--Variables

infix 10 _∋₂_
data _∋₂_ : ∀ Γ → Fibration₂ ⟦ Γ ⟧C → Set where
  top : ∀ {Γ} {H} → Γ ,₂ H ∋₂ pullback₂ p₂ H
  pop₂ : ∀ {Γ} {G} {H} → Γ ∋₂ H → Γ ,₂ G ∋₂ pullback₂ p₂ H
  pop₁ : ∀ {Γ} {S} {H} → Γ ∋₂ H → Γ ,₁ S ∋₂ pullback₂ p₁ H
  pop₀ : ∀ {Γ} {P} {H} → Γ ∋₂ H → Γ ,₀ P ∋₂ pullback₂ p₀ H

⟦_⟧V₂ : ∀ {Γ} {H} → Γ ∋₂ H → Section₂ H
⟦ top ⟧V₂ = q₂
⟦ pop₂ x ⟧V₂ = section-pullback₂ p₂ ⟦ x ⟧V₂
⟦ pop₁ x ⟧V₂ = section-pullback₂ p₁ ⟦ x ⟧V₂
⟦ pop₀ x ⟧V₂ = section-pullback₂ p₀ ⟦ x ⟧V₂

infix 10 _∋₁_
data _∋₁_ : ∀ Γ → Fibration₁ ⟦ Γ ⟧C → Set where
  top : ∀ {Γ} {T} → Γ ,₁ T ∋₁ pullback₁ p₁ T
  pop₂ : ∀ {Γ} {G} {T} → Γ ∋₁ T → Γ ,₂ G ∋₁ pullback₁ p₂ T
  pop₁ : ∀ {Γ} {S} {T} → Γ ∋₁ T → Γ ,₁ S ∋₁ pullback₁ p₁ T
  pop₀ : ∀ {Γ} {P} {T} → Γ ∋₁ T → Γ ,₀ P ∋₁ pullback₁ p₀ T

⟦_⟧V₁ : ∀ {Γ} {H} → Γ ∋₁ H → Section₁ H
⟦ top ⟧V₁ = q₁
⟦ pop₂ x ⟧V₁ = section-pullback₁ p₂ ⟦ x ⟧V₁
⟦ pop₁ x ⟧V₁ = section-pullback₁ p₁ ⟦ x ⟧V₁
⟦ pop₀ x ⟧V₁ = section-pullback₁ p₀ ⟦ x ⟧V₁

infix 10 _∋₀_
data _∋₀_ : ∀ Γ → Fibration₀ ⟦ Γ ⟧C → Set where
  top : ∀ {Γ} {T} → Γ ,₀ T ∋₀ pullback₀ p₀ T
  pop₂ : ∀ {Γ} {G} {T} → Γ ∋₀ T → Γ ,₂ G ∋₀ pullback₀ p₂ T
  pop₁ : ∀ {Γ} {S} {T} → Γ ∋₀ T → Γ ,₁ S ∋₀ pullback₀ p₁ T
  pop₀ : ∀ {Γ} {P} {T} → Γ ∋₀ T → Γ ,₀ P ∋₀ pullback₀ p₀ T

⟦_⟧V₀ : ∀ {Γ} {H} → Γ ∋₀ H → Section₀ H
⟦ top ⟧V₀ = q₀
⟦ pop₂ x ⟧V₀ = section-pullback₀ p₂ ⟦ x ⟧V₀
⟦ pop₁ x ⟧V₀ = section-pullback₀ p₁ ⟦ x ⟧V₀
⟦ pop₀ x ⟧V₀ = section-pullback₀ p₀ ⟦ x ⟧V₀

--The typing judgements

\end{code}

%<*Typing>
\begin{code}
data _⊢gpd : Cx → Set where

data _⊢₂_ : ∀ Γ → Fibration₂ ⟦ Γ ⟧C → Set where
\end{code}
%</Typing>

\begin{code}
  -var- : ∀ {Γ} {T} → Γ ∋₂ T → Γ ⊢₂ T
\end{code}

%<*Typing2>
\begin{code}
⟦_⟧₂ : ∀ {Γ} {T} → Γ ⊢₂ T → Section₂ T
\end{code}
%</Typing2>

\begin{code}
⟦ -var- x ⟧₂ = ⟦ x ⟧V₂

data _⊢₁_ : ∀ Γ → Fibration₁ ⟦ Γ ⟧C → Set where
  -var- : ∀ {Γ} {T} → Γ ∋₁ T → Γ ⊢₁ T

⟦_⟧₁ : ∀ {Γ} {S} → Γ ⊢₁ S → Section₁ S
⟦ -var- x ⟧₁ = ⟦ x ⟧V₁

data _⊢₀_ : ∀ Γ → Fibration₀ ⟦ Γ ⟧C → Set where
  -var- : ∀ {Γ} {T} → Γ ∋₀ T → Γ ⊢₀ T

⟦_⟧₀ : ∀ {Γ} {S} → Γ ⊢₀ S → Section₀ S
⟦ -var- x ⟧₀ = ⟦ x ⟧V₀

--Substitution

\end{code}

%<*Sub>
\begin{code}
data Sub Γ : Cx → Set
⟦_⟧S : ∀ {Γ} {Δ} → Sub Γ Δ → Groupoid-Functor ⟦ Γ ⟧C ⟦ Δ ⟧C
\end{code}
%</Sub>

\begin{code}
data Sub Γ where
  • : Sub Γ ε
  _,₂_ : ∀ {Δ G} (σ : Sub Γ Δ) → Γ ⊢₂ pullback₂ ⟦ σ ⟧S G → Sub Γ (Δ ,₂ G)
  _,₁_ : ∀ {Δ S} (σ : Sub Γ Δ) → Γ ⊢₁ pullback₁ ⟦ σ ⟧S S → Sub Γ (Δ ,₁ S)
  _,₀_ : ∀ {Δ P} (σ : Sub Γ Δ) → Γ ⊢₀ pullback₀ ⟦ σ ⟧S P → Sub Γ (Δ ,₀ P)

⟦ • ⟧S = bang
⟦ σ ,₂ t ⟧S = pair₂ _ ⟦ σ ⟧S ⟦ t ⟧₂
⟦ σ ,₁ a ⟧S = pair₁ ⟦ σ ⟧S ⟦ a ⟧₁
⟦ σ ,₀ p ⟧S = pair₀ ⟦ σ ⟧S ⟦ p ⟧₀

apV₂ : ∀ {Γ Δ T} (σ : Sub Γ Δ) → Δ ∋₂ T → Γ ⊢₂ pullback₂ ⟦ σ ⟧S T
apV₂ (σ ,₂ t) top = t
apV₂ (σ ,₂ t) (pop₂ x) = apV₂ σ x
apV₂ (σ ,₁ t) (pop₁ x) = {!apV₂ σ x!}
apV₂ σ (pop₀ x) = {!!}

--Path Substitution
\end{code}

%<*PathSub>
\begin{code}
data PathSub {Γ} : ∀ {Δ} → Sub Γ Δ → Sub Γ Δ → Set
⟦_⟧PS : ∀ {Γ Δ} {ρ σ : Sub Γ Δ} → PathSub ρ σ → Groupoid-NatIso ⟦ ρ ⟧S ⟦ σ ⟧S
\end{code}
%</PathSub>

\begin{code}
data PathSub {Γ} where
  • : PathSub • •
  _,₂_ : ∀ {Δ G} {ρ σ : Sub Γ Δ} {s : Γ ⊢₂ pullback₂ ⟦ ρ ⟧S G} {t : Γ ⊢₂ pullback₂ ⟦ σ ⟧S G}
    (τ : PathSub ρ σ) → Γ ⊢₁ EQ₂ ⟦ s ⟧₂ (pullback₂-congl ⟦ τ ⟧PS G) ⟦ t ⟧₂ → PathSub (ρ ,₂ s) (σ ,₂ t)
  _,₁_ : ∀ {Δ S} {ρ σ : Sub Γ Δ} {s : Γ ⊢₁ pullback₁ ⟦ ρ ⟧S S} {t : Γ ⊢₁ pullback₁ ⟦ σ ⟧S S}
    (τ : PathSub ρ σ) → Γ ⊢₀ EQ₁ ⟦ s ⟧₁ (pullback₁-congl ⟦ τ ⟧PS S) ⟦ t ⟧₁ → PathSub (ρ ,₁ s) (σ ,₁ t)
  _,₀* : ∀ {Δ P} {ρ σ : Sub Γ Δ} {s : Γ ⊢₀ pullback₀ ⟦ ρ ⟧S P} {t : Γ ⊢₀ pullback₀ ⟦ σ ⟧S P}
    (τ : PathSub ρ σ) → PathSub (ρ ,₀ s) (σ ,₀ t)

⟦ • ⟧PS = bang-ref
⟦ τ ,₂ e ⟧PS = pair₂-cong ⟦ τ ⟧PS ⟦ e ⟧₁
⟦ τ ,₁ e ⟧PS = pair₁-cong ⟦ τ ⟧PS ⟦ e ⟧₀
⟦ τ ,₀* ⟧PS = pair₀-cong ⟦ τ ⟧PS
\end{code}
