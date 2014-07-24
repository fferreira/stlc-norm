module weakMod where

import Var

-- Types

data tp : Set where
  i : tp
  _⇝_ : tp -> tp -> tp -- (T S : tp) -> tp -- with dependent functions

open module V = Var tp -- this module defines bound variables and renamings

-- Typed expresions in a context

data exp (Γ : ctx) : tp -> Set where
  c : exp Γ i
  ▹ : ∀ {T} -> var Γ T -> exp Γ T
  ƛ : ∀ {T S} (M : exp (Γ , T) S) -> exp Γ (T ⇝ S)
  _·_ : ∀ {T S} (M : exp Γ (T ⇝ S)) (N : exp Γ T) -> exp Γ S

[_]r : ∀{Γ Δ T} -> ren Γ Δ -> exp Γ T -> exp Δ T
[_]r σ c = c
[_]r σ (▹ x) = ▹ (app-ren σ x)
[_]r σ (ƛ M) = ƛ ([ (ext-r σ) ]r M)
[_]r σ (M · N) = [ σ ]r M · [ σ ]r N

open module S = Subst exp ▹ [_]r -- this module defines simultaneous substitutions

[_] : ∀{Γ Δ T} -> sub Γ Δ -> exp Γ T -> exp Δ T
[_] σ c = c
[_] σ (▹ x) = app σ x
[_] σ (ƛ M) = ƛ ([ wkn-sub _ σ ] M)
[_] σ (M · M₁) = [ σ ] M · [ σ ] M₁

_∘_ : ∀{Γ Δ Θ} -> sub Δ Θ -> sub Γ Δ -> sub Γ Θ
_∘_ δ ∅ = ∅
_∘_ δ (x ∷ σ) = ([ δ ] x) ∷ (δ ∘ σ)

-- we don't evaluate under ƛ so our values are:

data value {Γ : ctx} : {T : tp} -> exp Γ T -> Set where
  c : value c
  vƛ : ∀ {T S} (M : exp (Γ , T) S) -> value (ƛ M)

-- The language supports the following evaluation rules

data eval' {T : tp} {Γ : ctx} : exp Γ T -> exp Γ T ->  Set where
  ev-refl : ∀{M} -> eval' M M
  ev-trans : ∀{M M' N} -> eval' M M' -> eval' M' N -> eval' M N
  ev-beta : ∀{Tp N} {M : exp (Γ , Tp) T} -> eval' ((ƛ M) · N) ([ N ∷ id-sub ] M)
  ev-app : ∀{Tp M' N} {M : exp Γ (Tp ⇝ T)} -> eval' M M' -> eval' (M · N) (M' · N)

-- perhaps we want an empty context since we don't evaluate under
-- binders so the context is always empty.

data eval {T : tp} : exp ⊡ T -> exp ⊡ T ->  Set where
  ev-refl : ∀{M} -> eval M M
  ev-trans : ∀{M M' N} -> (d1 : eval M M') (d2 : eval M' N) -> eval M N
  ev-beta : ∀{Tp N} {M : exp (⊡ , Tp) T} -> eval ((ƛ M) · N) ([ N ∷ ∅ ] M)
  ev-app : ∀{Tp M' N} {M : exp ⊡ (Tp ⇝ T)} -> eval M M' -> eval (M · N) (M' · N)

-- Halting (or evaluating to a value)

data halts' {Γ : ctx} {T : tp} : (M : exp Γ T) ->  Set where
  evals-to-value : ∀{M'} {M : exp Γ T} -> eval' M M' -> value M' -> halts' M

-- but for the time being let's use only closed contexts

data halts {T : tp} : (M : exp ⊡ T) ->  Set where
  evals-to-value : ∀{M'} {M : exp ⊡ T} -> eval M M' -> value M' -> halts M

-- Reducibility candidates

-- Wrong definition as it is not strictly positive

-- data red' : (T : tp) -> exp ⊡ T -> Set where
--   red-i : {M : exp ⊡ i} -> halts M -> red' i M
--   red-arr : ∀{T S}{M : exp ⊡ (T ⇝ S)} {N : exp ⊡ T} -> 
--     halts M -> (red' T N -> red' S (M · N)) -> red' (T ⇝ S) M

data _*_ (T S : Set) : Set where
 _,_ : T -> S -> T * S

fst : ∀{T S} -> T * S -> T
fst (x , _) = x

red : (T : tp) -> exp ⊡ T -> Set
red i M = halts M
red (T ⇝ T') M = (halts M) * ((N : _) → red T N → red T' (M · N))

-- Immediate, reducible terms halt

n : ∀{T M} -> red T M -> halts M
n {i} r = r
n {T ⇝ T₁} r = fst r

-- Lemma. 
-- Closure under expansion: If M' ∈ RA and M −→ M' then M ∈ RA

lemma-1 : (T : tp) {M M' : exp ⊡ T} -> red T M' -> eval M M' -> red T M
lemma-1 i (evals-to-value d' v) d = evals-to-value (ev-trans d d') v
lemma-1 (T ⇝ i) (evals-to-value d' v , r') d = 
  (evals-to-value (ev-trans d d') v) ,  (λ N z → lemma-1 i (r' N z) (ev-app d))
lemma-1 (T ⇝ (T' ⇝ T'')) (evals-to-value d' v , r') d =
  (evals-to-value (ev-trans d d') v) ,  (λ N → λ r → 
  lemma-1 (T' ⇝ T'') (r' N r) (ev-app d))

-- we define the concept of reducible substitutions, where all the
-- terms in the substitution are reducible

data rsub : {Γ : ctx} -> sub Γ ⊡ -> Set where
  ∅ : rsub ∅
  _∷_ : ∀{Γ T M} {σ : sub Γ ⊡} -> red T M -> rsub σ -> rsub (M ∷ σ)

data _≡_ {A : Set} (a : A) : A -> Set where
 refl : a ≡ a

congruence : {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
congruence f refl = refl

transitivity : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
transitivity refl refl = refl

-- sometimes called J roughly (it is the elimination of ≡) 
subst : ∀ {A} (P : A -> Set) {x y} -> x ≡ y -> P x -> P y
subst P refl t = t

lemma-long : ∀ {Γ Δ Θ N S} {M : exp {!!} S} {σ : sub Γ Δ} {δ : sub Δ Θ} -> ([
       ▹ top ∷
       ([ wkn-ren ]r ([ δ ] N) ∷
        weaken-sub (δ ∘ σ))
       ]
       M) ≡ ([
       ▹ top ∷
       ([ ▹ top ∷ weaken-sub δ ]
        ([ wkn-ren ]r N)
        ∷ ((▹ top ∷ weaken-sub δ) ∘ weaken-sub σ))
       ]
       M)
lemma-long = {!!}

comp-seq : ∀{Γ Δ Θ T} (σ : sub Γ Δ) (δ : sub Δ Θ) (M : exp Γ T) -> [ δ ∘ σ ] M  ≡ [ δ ] ([ σ ]  M)
comp-seq ∅ δ M = {!!} 
comp-seq (N ∷ σ) δ c = refl
comp-seq (N ∷ σ) δ (▹ top) = refl
comp-seq (N ∷ σ) δ (▹ (pop x)) = comp-seq σ δ (▹ x)
comp-seq {Γ , S} {Δ} {Θ} {T₁ ⇝ T₂ } (N ∷ σ) δ (ƛ M) with δ ∘ (N ∷ σ)| comp-seq (▹ top ∷ weaken-sub (N ∷ σ)) (▹ top ∷ weaken-sub δ) M
...| δ∘σ  | ih with congruence ƛ ih
... | foo =  {!!}
comp-seq (N ∷ σ) δ (M · M₁) with δ ∘ (N ∷ σ) | comp-seq (N ∷ σ) δ M | comp-seq (N ∷ σ) δ M₁
...| δ∘σ  | ih₁ | ih₂ 
  with congruence (λ M' → M' · [ δ ] ([ N ∷ σ ] M₁)) ih₁ | congruence (λ M' → [ δ∘σ ] M · M') ih₂ 
...| foo | bar = transitivity bar foo

--not so fun lemma

fun-lemma : ∀{Γ T S} (N : exp ⊡ T) (σ : sub Γ ⊡)  (M : exp (Γ , T) S) -> 
  [ N ∷ σ ] M ≡ [ N ∷ ∅ ] ([ ▹ top ∷ weaken-sub σ ] M)
fun-lemma N σ M = {!!}

-- Main lemma. 
-- If Γ ⊢ M : A and σ ∈ RΓ then [σ]M ∈ RA.

ml : ∀{Γ T σ} -> (M : exp Γ T) -> rsub σ -> red T ([ σ ] M)
ml c rσ = evals-to-value ev-refl c
ml (▹ top) (x ∷ σ) = x
ml (▹ (pop x)) (x' ∷ σ) = ml (▹ x) σ
ml (M · N) rσ with ml M rσ 
... | h , r = r ([ _ ] N) (ml N rσ)
ml (ƛ {T} {S} M) rσ = evals-to-value ev-refl (vƛ ([ ▹ top ∷ weaken-sub _ ] M)) , 
  (λ N → λ rN → lemma-1 _ (subst (red S) (fun-lemma N _ M) (ml M (rN ∷ rσ))) ev-beta)

lemma-id-var : ∀{Γ T}  (x : var Γ T) -> [ id-sub ] (▹ x) ≡ ▹ x
lemma-id-var top = refl
lemma-id-var (pop x) with lemma-id-var x
...| foo = {!!} -- congruence weaken foo does not work for some subtle thing with renamings vs substs.

lemma-id : ∀{Γ T}  (M : exp Γ T) -> [ id-sub ] M ≡ M
lemma-id c = refl
lemma-id (▹ x) = lemma-id-var x
lemma-id (ƛ M) with lemma-id M
...| [id]M≡M = congruence ƛ [id]M≡M
lemma-id (M · N) with lemma-id M | lemma-id N 
...| foo | bar = {!!}

lemma-empty : ∀{T}(M : exp ⊡ T) -> [ ∅ ] M ≡ M
lemma-empty = lemma-id

-- all closed terms are reducible
all-red : ∀{T} -> (M : exp ⊡ T) -> red T M
all-red M with ml M ∅
...| redT[∅]M = subst (red _) (lemma-empty M) redT[∅]M

