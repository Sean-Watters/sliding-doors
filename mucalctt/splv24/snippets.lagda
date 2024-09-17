%%%%%%%%%%
% latex preamble
% (missing unicode chars)

\usepackage{newunicodechar}
\newunicodechar{∈}{\ensuremath{\mathnormal{\in}}}
\newunicodechar{≡}{\ensuremath{\mathnormal{\equiv}}}
\newunicodechar{∷}{\ensuremath{\mathnormal{\dblcolon}}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{₀}{\ensuremath{\mathnormal{_0}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{π}{\ensuremath{\mathnormal{π}}}
\newunicodechar{∀}{\ensuremath{\mathnormal{\forall}}}
\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
\newunicodechar{μ}{\ensuremath{\mathnormal{\mu}}}
\newunicodechar{ϕ}{\ensuremath{\mathnormal{\varphi}}}
\newunicodechar{ψ}{\ensuremath{\mathnormal{\psi}}}
\newunicodechar{η}{\ensuremath{\mathnormal{\eta}}}
\newunicodechar{≈}{\ensuremath{\mathnormal{\approx}}}

%%%%%%%%%%
% agda preamble

\begin{code}[hide]

open import Data.Nat hiding (_≟_)
open import Data.Fin using (Fin; zero; suc; _≟_) renaming (inject₁ to fin-inject₁)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

data Opη : Set where
  mu nu : Opη

data Op₀ (At : Set) : Set where
  tt ff : Op₀ At
  at ¬at : At → Op₀ At

data Op₁ : Set where
  box dia : Op₁

data Op₂ : Set where
  and or : Op₂

\end{code}

%%%%%%%%%%
% agda snippets

\newcommand{\snippetwellscoped}{%
\begin{code}
data WST (At : Set) (n : ℕ) : Set where
  tt ff      : WST At n
  at ¬at     : At → WST At n
  and or     : (ϕ ψ : WST At n) → WST At n
  box dia : (ϕ : WST At n) → WST At n
  mu nu      : (ϕ : WST At (suc n)) → WST At n
  var        : Fin n → WST At n
\end{code}}

\begin{code}[hide]
data IsFP {At : Set} {n : ℕ} : WST At n → Set where
  mu : (ϕ : WST At (suc n)) → IsFP (mu ϕ)
  nu : (ϕ : WST At (suc n)) → IsFP (nu ϕ)
\end{code}

\newcommand{\snippetscope}{%
\begin{code}
data Scope (At : Set) : ℕ → Set where
  [] : Scope At zero
  _-,_ : ∀ {n} (Γ₀ : Scope At n) {ϕ : WST At n}
       → (Γ₀ : IsFP ϕ) → Scope At (suc n)
\end{code}}

\newcommand{\snippetsublimelyscoped}{%
\begin{code}
mutual
  data SST (At : Set) {n : ℕ} (Γ : Scope At n) : Set where
    -- other constructors here...
    var : (x : Fin n) → SST At Γ
    mu  : {ψ : WST At (suc n)}
        → (ϕ : SST At (Γ -, mu ψ))
        → ψ ≈ ϕ
        → SST At Γ

  data _≈_ {At : Set} {n : ℕ} {Γ : Scope At n}
    : WST At n → SST At Γ → Set where
    -- other constructors here...
    var : (x : Fin n) → (var x) ≈ (var x)
    mu  : {ϕ : WST At (suc n)}
        → {ϕ' : SST At (Γ -, mu ϕ)}
        → (p : ϕ ≈ ϕ')
        → mu ϕ ≈ mu ϕ' p
\end{code}}
