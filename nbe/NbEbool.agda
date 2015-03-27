module NbEbool where
  open import Var
  import Data.Bool as B
  open import Data.List

data tp : Set where
  bool : tp
  _↛_ : tp -> tp -> tp

data exp (Γ : ctx tp) : tp -> Set where
  _·_ : ∀{T S} -> exp Γ (T ↛ S) -> exp Γ T -> exp Γ S
  ƛ : ∀{T S} -> exp (Γ , T) S -> exp Γ (T ↛ S)
  ▹ : ∀{T} -> var tp Γ T -> exp Γ T
  tt : exp Γ bool
  ff : exp Γ bool
  if_then_else_ : ∀{T} -> exp Γ bool -> exp Γ T -> exp Γ T -> exp Γ T

mutual 
  data nf (Γ : ctx tp) : tp -> Set where
    ƛ : ∀{T S} -> nf (Γ , T) S -> nf Γ (T ↛ S)    
    tt : nf Γ bool
    ff : nf Γ bool
    ne : ∀{T} -> neu Γ T -> nf Γ T

  data neu (Γ : ctx tp) : tp -> Set where
    _·_ : ∀{T S} -> neu Γ (T ↛ S) -> nf Γ T -> neu Γ S
    ▹ : ∀{T} -> var tp Γ T -> neu Γ T
    -- let's start with this here
    if_then_else_ : ∀{T} -> neu Γ bool -> nf Γ T -> nf Γ T -> neu Γ T

data sem-bool : Set where
  tt : sem-bool
  ff : sem-bool
  stuck : (∀{Γ} -> neu Γ bool)  -> sem-bool

⟦_⟧t :  ∀ T -> Set
⟦_⟧t bool = sem-bool
⟦_⟧t (t ↛ t₁) = ⟦ t ⟧t → ⟦ t₁ ⟧t

data ⟦_⟧c : (Γ : ctx tp) -> Set where
  ⊡ : ⟦ ⊡ ⟧c
  _,_ : ∀{Γ T} -> (ρ : ⟦ Γ ⟧c) -> ⟦ T ⟧t -> ⟦ Γ , T ⟧c


lookup : ∀{Γ T} -> ⟦ Γ ⟧c -> var tp Γ T -> ⟦ T ⟧t
lookup ⊡ ()
lookup (ρ , s) top = s
lookup (ρ , s) (pop x) = lookup ρ x

data splits (Γ : ctx tp) (s : tp) : (Δ : ctx tp) -> Set where
 yes : ∀ {Γ'} -> splits Γ s (Var._⋈_ tp (Γ Var., s) Γ')
 no : ∀ {Δ} -> splits Γ s Δ

dec-splits : ∀ Γ s Δ -> splits Γ s Δ
dec-splits Γ s Δ = {!!}

fresh : ∀ {T} -> (Γ : ctx tp) -> (∀ Γ' -> neu Γ' T)
fresh {s} Γ Δ with dec-splits Γ s Δ
fresh Γ ._ | yes = {!!}
fresh Γ Δ | no = {!!}

mutual
  reflect : ∀ T -> (∀ Γ -> neu Γ T) -> ⟦ T ⟧t
  reflect bool e = stuck (e _) -- ??
  reflect (s ↛ t) u = λ a → reflect t (λ Γ → u Γ · reify s a Γ)

  reify : ∀ T -> ⟦ T ⟧t -> ∀ Γ -> nf Γ T
  reify bool tt Γ = tt
  reify bool ff Γ = ff
  reify bool (stuck n) Γ = ne n -- and poof! it fails
  reify (s ↛ t) f Γ = ƛ (reify t (f (reflect s (fresh Γ))) (Γ , s))

⟦_⟧ : ∀{Γ T} -> exp Γ T -> ⟦ Γ ⟧c -> ⟦ T ⟧t
⟦ e · e₁ ⟧ ρ = (⟦ e ⟧ ρ) (⟦ e₁ ⟧ ρ)
⟦_⟧ (ƛ e) ρ = λ x → ⟦ e ⟧ (ρ , x)
⟦ ▹ x ⟧ ρ = lookup ρ x
⟦ tt ⟧ ρ_ = tt
⟦ ff ⟧ ρ_ = ff
⟦ if c then e1 else e2 ⟧ ρ with ⟦ c ⟧ ρ 
⟦ if c then e else _ ⟧ ρ | tt = ⟦ e ⟧ ρ
⟦ if c then _ else e ⟧ ρ | ff = ⟦ e ⟧ ρ
⟦ if c then e1 else e2 ⟧ ρ | stuck st = reflect _ (λ Γ → if st then (reify _ (⟦ e1 ⟧ ρ) Γ) else reify _ (⟦ e2 ⟧ ρ) Γ)





