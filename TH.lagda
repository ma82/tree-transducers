# (Generalised? Effectful?) Tree homomorphisms between containers

A generalisation of the definition of term/tree homomorphisms by Bahr
& Hvitved, restricted to `Set`-based containers. They also seem to
generalise `TT` at page 24 of Tarmo Uustalu's slides from ICALP 2007.

This is more useful with (heterogeneous) indexed
containers/interaction structures. In general it should be attempted
on top of a suitable formalisation of category theory, but I'd like to
keep things simple for now.

\begin{code}
module TH where

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

## Tree homomorphisms and their behaviours

The "behaviours" terminology is inspired by the ICALP 2007 slides by
Tarmo Uustalu. However, these `LBEH` and `GBEH` seem different, and
not necessarily correct.

\begin{code}
_TH[_]>_ _LBEH[_]>_ _GBEH[_]>_ : Cont → Functor → Cont → Set₁
F TH[   H ]> G = ∀ {X} → ⟦ F ⟧ (∣ H ∣ X) → ∣ H ∣ (G * X)
-- [1] This is what I used to do:
F LBEH[ H ]> G = ∀ {X} → F ALG> ∣ H ∣ (G * X)
-- [2] This one, more similar to icalp-slides.pdf, maybe works when H is a monad...
-- F LBEH[ H ]> G = ∀ {X} → ⟦ F ⟧ (∣ H ∣ (F * X)) → ∣ H ∣ (G * X)
F GBEH[ H ]> G = ∀ {X} → F * ∣ H ∣ X → ∣ H ∣ (G * X)
\end{code}

TODO. In order to prove anything interesting, one must refine these
definitions. For example, THs should at least be paired with their
naturality. For what concerns LBEHs and GBEHs, I don't know yet.

\begin{code}
module Behs (F : Cont)(H : Functor)(G : Cont) where

  open Cata F

  TH→LBEH : F TH[ H ]> G → F LBEH[ H ]> G
-- [1]
  TH→LBEH α = ∣ H ∣map join ∘ α
-- [2]
--  TH→LBEH α = ∣ H ∣map join ∘ α ∘ ∣ ⟦ F ⟧map ∣map {!!}

  LBEH→GBEH : F LBEH[ H ]> G → F GBEH[ H ]> G
  LBEH→GBEH α = cata* α (∣ H ∣map η)

  TH→GBEH : F TH[ H ]> G → F GBEH[ H ]> G
  TH→GBEH = LBEH→GBEH ∘ TH→LBEH
\end{code}

### Category of tree homomorphisms?

Helpers.

\begin{code}
idTH : ∀ {F} → F TH[ idF ]> F
idTH (a , f) = In (a , η ∘ f)
\end{code}

\begin{code}
module ∙TH {F G H : Cont}{M N : Functor} where

  _∙TH_ : G TH[ M ]> H → F TH[ N ]> G → F TH[ N ∙ M ]> H
  α ∙TH β = ∣ N ∣map (TH→GBEH α) ∘ β where open Behs G M H
\end{code}

Objects are containers (`Cont`).

I guess `TH/ H` might be a valid homset only if `H` is a monad, but
this is not the category we need.

\begin{code}
TH/ : Functor → Cont → Cont → Set₁
TH/ H F G = F TH[ H ]> G
\end{code}

`TH` should capture the homset of the category of containers and tree
homomorphisms.

\begin{code}
TH : Cont → Cont → Set₁
TH F G = Σ _ λ H → TH/ H F G
\end{code}

### page 24 of icalp-slides.pdf (sort of)

\begin{code}
TT/ : Set → Cont → Cont → Set₁
TT/ X F G = ∀ {Y} → ⟦ F ⟧ (Y × X) → G * Y × X
\end{code}

In Tarmo Uustalu's talk slides there are three possible definitions of
tree transducers: with `TT` we refer to the homset for the last one.

\begin{code}
TT : Cont → Cont → Set₁
TT F G = Σ _ λ X → TT/ X F G
\end{code}

`TH` and `TT` share the same objects, and we have this inclusion of
morphisms.

\begin{code}
TT→TH : ∀ {F G} → TT F G → TH F G 
TT→TH (X , α) = mk (_×_ § X) (Σ.map § id) , α
\end{code}

TODO. Is `TT` a "lluf" subcategory of `TH`?
