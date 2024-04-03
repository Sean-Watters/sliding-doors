%%%%%%%%%%
% latex preamble
% (missing unicode chars)

\usepackage{newunicodechar}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{∷}{\ensuremath{\mathnormal{\dblcolon}}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{π}{\ensuremath{\mathnormal{π}}}

%%%%%%%%%%
% agda preamble

\begin{code}[hide]
data ⊤ : Set where
  tt : ⊤

record _×_ (X Y : Set) : Set where
  field
    π₁ : X
    π₂ : Y

data List (X : Set) : Set where
  [] : List X
  _∷_ : X → List X → List X

postulate
  Var : Set
  _∈_ : {X : Set} → X → List X → Set

\end{code}

%%%%%%%%%%
% agda snippets

\newcommand{\snippetdatatm}{%
\begin{code}
data Tm (Γ : List Var) : Set where
  var : (x : Var) → x ∈ Γ → Tm Γ
  abs : (x : Var) → Tm (x ∷ Γ) → Tm Γ
\end{code}}

\newcommand{\snippetdatafreshlist}{%
\begin{code}
mutual
  data FList {X : Set} (R : X → X → Set) : Set where
    nil  : FList R
    cons : (x : X) → (xs : FList R) → x # xs → FList R


  _#_ : {X : Set} {R : X → X → Set}
      → X → FList R → Set
  x # nil = ⊤
  _#_ {R = R} x (cons y ys p) = (R x y) × (x # ys)
\end{code}
}
