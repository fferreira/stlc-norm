module Var (tp : Set) where

data ctx : Set where
  ⊡ : ctx
  _,_ : (Γ : ctx) (T : tp) -> ctx

data var : ctx -> tp -> Set where
  top : ∀ {Γ T} -> var (Γ , T) T
  pop : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

-- we define simultaneous variable renamings

data ren : ctx -> ctx -> Set where
  ∅ : ∀{Γ} -> ren ⊡ Γ
  _∷_ : ∀{Γ Δ}{T : tp} -> var Δ T -> ren Γ Δ -> ren (Γ , T) Δ

-- now we define renamings

app-ren : ∀{Γ Δ T} -> ren Γ Δ -> var Γ T -> var Δ T
app-ren (x ∷ σ) top = x
app-ren (x ∷ σ) (pop x₁) = app-ren σ x₁

[_]rv : ∀{Γ Δ T} -> ren Γ Δ -> var Γ T -> var Δ T
[_]rv ∅ ()
[_]rv (x ∷ σ) top = x
[_]rv (x ∷ σ) (pop x') = [ σ ]rv x'

map-ren : ∀{Γ Δ Δ'} -> (f : ∀{T} -> var Δ T -> var Δ' T) -> ren Γ Δ -> ren Γ Δ'
map-ren f ∅ = ∅
map-ren f (x ∷ σ) = f x ∷ map-ren f σ

ext-r : ∀{Γ Δ T} -> ren Γ Δ -> ren (Γ , T) (Δ , T)
ext-r σ = top ∷ (map-ren (λ {T} → pop) σ)

id-ren : ∀{Γ} -> ren Γ Γ
id-ren {⊡} = ∅
id-ren {Γ , T} = top ∷ (map-ren (λ {T₁} → pop) id-ren)

wkn-ren : ∀{Γ T} -> ren Γ (Γ , T)
wkn-ren = map-ren (λ {T} → pop) id-ren

-- one has to write [_]r :  ∀{Γ Δ T} -> ren Γ Δ -> exp Γ T -> exp Δ T

module Subst (exp : ctx -> tp -> Set) (▹ : ∀{T Γ} -> var Γ T -> exp Γ T) ([_]r :  ∀{Γ Δ T} -> ren Γ Δ -> exp Γ T -> exp Δ T) where

  -- we define simultaneous substitutions to transport terms from a context to another

  data sub : ctx -> ctx -> Set where
    ∅ : ∀{Γ} -> sub ⊡ Γ
    _∷_ : ∀{Γ Δ}{T : tp} -> exp Δ T -> sub Γ Δ -> sub (Γ , T) Δ

  -- before we can define the SOS we need to define how to apply
  -- substitutions

  app : ∀{Γ Δ T} -> sub Γ Δ -> var Γ T -> exp Δ T
  app ∅ ()
  app (y ∷ σ) top = y
  app (y ∷ σ) (pop x) = app σ x

  weaken : ∀{Γ T S} -> exp Γ T -> exp (Γ , S) T
  weaken M = [ wkn-ren ]r M

  weaken-⊡ : ∀{Γ T} -> exp ⊡ T -> exp Γ T
  weaken-⊡ {⊡} M = M
  weaken-⊡ {Γ , T} M = weaken (weaken-⊡ M)

  weaken-sub : ∀{Γ T Δ} -> sub Γ Δ -> sub Γ (Δ , T)
  weaken-sub ∅ = ∅
  weaken-sub (x ∷ σ) = (weaken x) ∷ (weaken-sub σ)

  wkn-sub : ∀{Γ Δ} -> (T : tp) -> sub Γ Δ -> sub (Γ , T) (Δ , T)
  wkn-sub T σ = ▹ top ∷ weaken-sub σ

  id-sub : ∀ {Γ} -> sub Γ Γ
  id-sub {⊡} = ∅
  id-sub {Γ , T} = (▹ top) ∷ weaken-sub id-sub

  -- one has to write [_] : ∀{Γ Δ T} -> sub Γ Δ -> exp Γ T -> exp Δ T
