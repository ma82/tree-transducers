# Tree transducers?

\begin{code}
module TT where

open import AD hiding (Cont ; Functor ; module Functor ; _*_)
\end{code}

## Functors

\begin{code}
record Functor : Set₁ where
  constructor mk
  field
    ∣_∣    : Set → Set
    ∣_∣map : ∀ {X Y} → (X → Y) → ∣_∣ X → ∣_∣ Y
open Functor

idF : Functor
idF = mk id id

_∙_ : Functor → Functor → Functor
(mk A a) ∙ (mk B b) = mk (A ∘ B) (a ∘ b)
\end{code}

## Containers

\begin{code}
record Cont : Set₁ where
  constructor mk
  field
    A : Set
    B : A → Set
open Cont

⟦_⟧ : Cont → Set → Set
⟦ mk A B ⟧ X = Σ A λ a → B a → X

⟦_⟧map : Cont → Functor
⟦ F ⟧map = mk ⟦ F ⟧ λ { f (a , t) → a , f ∘ t }
\end{code}

## Free monad

TODO. Alternatively, define

_*C : Cont → Cont
μ   : Cont → Set

\begin{code}
data _*_ (F : Cont)(X : Set) : Set where
  η  : X             → F * X
  In : ⟦ F ⟧ (F * X) → F * X
\end{code}

\begin{code}
_>>=_ : ∀ {F X Y} → F * X → (X → F * Y) → F * Y
(η x       ) >>= f = f x
(In (a , t)) >>= f = In (a , λ b → t b >>= f)

*map : ∀ {F X Y} → (X → Y) → F * X → F * Y
*map f xs = xs >>= (η ∘ f)

join : ∀ {F X} → F * (F * X) → F * X
join xs = xs >>= *map id
\end{code}

## Iteration

\begin{code}
_ALG>_ : Cont → Set → Set
F ALG> X = ⟦ F ⟧ X → X
\end{code}

\begin{code}
module Cata F {X Y} where

  cata* : F ALG> X → (Y → X) → F * Y → X
  cata* α f (η        x) = f x
  cata* α f (In (a , t)) = α (a , λ b → cata* α f (t b))
\end{code}

## Tree transducers and behaviours

\begin{code}
_TT[_]>_ _LBEH[_]>_ _GBEH[_]>_ : Cont → Functor → Cont → Set₁
F TT[   H ]> G = ∀ {X} → ⟦ F ⟧ (∣ H ∣ X) → ∣ H ∣ (G * X)
F LBEH[ H ]> G = ∀ {X} → F ALG> ∣ H ∣ (G * X)
F GBEH[ H ]> G = ∀ {X} → F * ∣ H ∣ X → ∣ H ∣ (G * X)
\end{code}

TODO. In order to prove anything interesting, one should refine these
definitions. For example, TTs should be paired with their naturality.

\begin{code}
module Behs (F : Cont)(H : Functor)(G : Cont) where

  open Cata F

  TT→LBEH : F TT[ H ]> G → F LBEH[ H ]> G
  TT→LBEH α = ∣ H ∣map join ∘ α

  LBEH→GBEH : F LBEH[ H ]> G → F GBEH[ H ]> G
  LBEH→GBEH α = cata* α (∣ H ∣map η)

  TT→GBEH : F TT[ H ]> G → F GBEH[ H ]> G
  TT→GBEH = LBEH→GBEH ∘ TT→LBEH
\end{code}

### Category of tree transducers?

\begin{code}
idTT : ∀ {F} → F TT[ idF ]> F
idTT (a , f) = In (a , η ∘ f)
\end{code}

\begin{code}
module ∙TT {F G H : Cont}{M N : Functor} where

  _∙TT_ : G TT[ M ]> H → F TT[ N ]> G → F TT[ N ∙ M ]> H
  α ∙TT β = ∣ N ∣map (TT→GBEH α) ∘ β where open Behs G M H
\end{code}

