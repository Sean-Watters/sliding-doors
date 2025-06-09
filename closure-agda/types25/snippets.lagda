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
\newunicodechar{∞}{\ensuremath{\mathnormal{\infty}}}
\newunicodechar{Γ}{\ensuremath{\mathnormal{\Gamma}}}
\newunicodechar{Δ}{\ensuremath{\mathnormal{\Delta}}}

%%%%%%%%%%
% agda preamble

\begin{code}[hide]
{-# OPTIONS --guardedness #-}
open import Data.Nat hiding (_≟_)
open import Data.Fin using (Fin; zero; suc; _≟_) renaming (inject₁ to fin-inject₁)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable


\end{code}

%%%%%%%%%%
% agda snippets

\newcommand{\snippetcotree}{%
\begin{code}
mutual
  record ∞NWFTree (X : Set) : Set where
    coinductive
    field
      head : X
      subtree : NWFTree X

  data NWFTree (X : Set) : Set where
    leaf : NWFTree X
    node1 : ∞NWFTree X → NWFTree X
    node2 : ∞NWFTree X → ∞NWFTree X → NWFTree X
    nodeη : ∞NWFTree X → NWFTree X

\end{code}}

\newcommand{\snippetrational}{%
\begin{code}
mutual
  data RTree (X : Set) (n : ℕ) : Set where
    step : (x : X) → (t : RTree-step X n) → RTree X n
    var  : (x : Fin n) → RTree X n

  data RTree-step (X : Set) (n : ℕ) : Set where
    leaf  : RTree-step X n
    node1 : RTree X n → RTree-step X n
    node2 : RTree X n → RTree X n → RTree-step X n
    nodeη : RTree X (suc n) → RTree-step X n
\end{code}
\begin{code}[hide]
data NonVar {X : Set} {n : ℕ} : RTree X n → Set where
  instance step : ∀ {x t} → NonVar (step x t)
\end{code}
\begin{code}
data Scope (X : Set) : ℕ → Set where
  []  : Scope X zero
  _∷_ : ∀ {n} → (t : RTree X n) → {{_ : NonVar t}}
      → (Γ₀ : Scope X n) → Scope X (suc n)
\end{code}}


%-- \newcommand{\snippetscope}{%
%-- \begin{code}
%-- data Scope (X : Set) : ℕ → Set where
%--   []  : Scope X zero
%--   _∷_ : ∀ {n} → (t : RTree X n) → {{_ : NonVar t}}
%--       → (Γ₀ : Scope X n) → Scope X (suc n)
%-- \end{code}}

\newcommand{\snippetunfolding}{%
\begin{code}
head : ∀ {X n} → (Γ : Scope X n) → RTree X n → X
head Γ       (step x t)    = x
head (t ∷ Γ) (var zero)    = head Γ t
head (t ∷ Γ) (var (suc x)) = head Γ (var x)

mutual
  unfold : ∀ {X n} → (Γ : Scope X n) → RTree X n → ∞NWFTree X
  unfold Γ t .∞NWFTree.head    = head Γ t
  unfold Γ t .∞NWFTree.subtree = unfold-subtree Γ t

  unfold-subtree : ∀ {X n} → (Γ : Scope X n) → RTree X n → NWFTree X
  unfold-subtree Γ (step x leaf)          = leaf
  unfold-subtree Γ (step x (node1 t))     = node1 (unfold Γ t)
  unfold-subtree Γ (step x (node2 tl tr)) = node2 (unfold Γ tl) (unfold Γ tr)
  unfold-subtree Γ (step x (nodeη t))     = nodeη (unfold ((step x (nodeη t)) ∷ Γ) t)
  unfold-subtree (t ∷ Γ) (var zero)       = unfold-subtree Γ t
  unfold-subtree (t ∷ Γ) (var (suc x))    = unfold-subtree Γ (var x)
\end{code}}
