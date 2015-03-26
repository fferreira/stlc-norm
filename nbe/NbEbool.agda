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

data sem : tp -> Set where
  
  

⟦_⟧t :  ∀ T -> Set
⟦_⟧t bool = B.Bool
⟦_⟧t (t ↛ t₁) = ⟦ t ⟧t → ⟦ t₁ ⟧t

data ⟦_⟧c : (Γ : ctx tp) -> Set where
  ⊡ : ⟦ ⊡ ⟧c
  _,_ : ∀{Γ T} -> (ρ : ⟦ Γ ⟧c) -> ⟦ T ⟧t -> ⟦ Γ , T ⟧c


lookup : ∀{Γ T} -> ⟦ Γ ⟧c -> var tp Γ T -> ⟦ T ⟧t
lookup ⊡ ()
lookup (ρ , s) top = s
lookup (ρ , s) (pop x) = lookup ρ x

⟦_⟧ : ∀{Γ T} -> exp Γ T -> ⟦ Γ ⟧c -> ⟦ T ⟧t
⟦ e · e₁ ⟧ ρ = (⟦ e ⟧ ρ) (⟦ e₁ ⟧ ρ)
⟦_⟧ (ƛ e) ρ = λ x → ⟦ e ⟧ (ρ , x)
⟦ ▹ x ⟧ ρ = lookup ρ x
⟦ tt ⟧ ρ_ = B.true
⟦ ff ⟧ ρ_ = B.false
⟦ if c then e1 else e2 ⟧ ρ with ⟦ c ⟧ ρ 
⟦ if c then e else _ ⟧ ρ | B.true = ⟦ e ⟧ ρ
⟦ if c then _ else e ⟧ ρ | B.false = ⟦ e ⟧ ρ

mutual 
  data nf (Γ : ctx tp) : tp -> Set where
    ƛ : ∀{T S} -> nf (Γ , T) S -> nf Γ (T ↛ S)    
    tt : nf Γ bool
    ff : nf Γ bool


  data neu (Γ : ctx tp) : tp -> Set where
    _·_ : ∀{T S} -> neu Γ (T ↛ S) -> nf Γ T -> neu Γ S
    ▹ : ∀{T} -> var tp Γ T -> neu Γ T
    -- let's start with this here
    if_then_else_ : ∀{T} -> neu Γ bool -> nf Γ T -> nf Γ T -> neu Γ T

mutual
  reify : ∀ Γ T -> ⟦ T ⟧t -> nf Γ T
  reify Γ bool B.true = tt
  reify Γ bool B.false = ff
  reify Γ (t ↛ t₁) s = ƛ (reify (Γ , t) t₁ (s (reflect (Γ , t) t (▹ top))))

  reflect : ∀ Γ T -> neu Γ T -> ⟦ T ⟧t
  reflect Γ bool e = {!!} -- ??
  reflect Γ (t ↛ t₁) e = λ x → reflect Γ t₁ (e · (reify Γ t x))


