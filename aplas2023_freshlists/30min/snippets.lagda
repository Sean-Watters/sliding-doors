%%%%%%%%%%
% latex preamble
% (missing unicode chars)

\usepackage{newunicodechar}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{∷}{\ensuremath{\mathnormal{\dblcolon}}}

%%%%%%%%%%
% agda preamble

\begin{code}[hide]
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
