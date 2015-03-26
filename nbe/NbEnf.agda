module NbEnf where
  open import Var
  open import Data.Unit

data tp : Set where
  i : tp
  _↛_ : tp -> tp -> tp

data exp (Γ : ctx tp) : tp -> Set where
  _·_ : ∀{T S} -> exp Γ (T ↛ S) -> exp Γ T -> exp Γ S
  ƛ : ∀{T S} -> exp (Γ , T) S -> exp Γ (T ↛ S)
  ▹ : ∀{T} -> var tp Γ T -> exp Γ T
  c : exp Γ i

⟦_⟧t :  ∀ T -> Set
⟦_⟧t i = Unit
⟦_⟧t (t ↛ t₁) = ⟦ t ⟧t → ⟦ t₁ ⟧t

data s-env : (Γ : ctx tp) -> Set where
  ⊡ : s-env ⊡
  _,_ : ∀{Γ T} -> (ρ : s-env Γ) -> ⟦ T ⟧t -> s-env (Γ , T)

lookup : ∀{Γ T} -> s-env Γ -> var tp Γ T -> ⟦ T ⟧t
lookup ⊡ ()
lookup (ρ , s) top = s
lookup (ρ , s) (pop x) = lookup ρ x

⟦_⟧ : ∀{Γ T} -> exp Γ T -> s-env Γ -> ⟦ T ⟧t
⟦ e · e₁ ⟧ ρ = (⟦ e ⟧ ρ) (⟦ e₁ ⟧ ρ)
⟦_⟧ (ƛ e) ρ = λ x → ⟦ e ⟧ (ρ , x)
⟦ ▹ x ⟧ ρ = lookup ρ x
⟦ c ⟧ ρ_ = unit

mutual
  data nf (Γ : ctx tp) : tp -> Set where
    ƛ : ∀{T S} -> nf (Γ , T) S -> nf Γ (T ↛ S)
    ne : ∀{T} -> neu Γ T -> nf Γ T
    c : nf Γ i

  data neu (Γ : ctx tp) : tp -> Set where
      _·_ : ∀{T S} -> neu Γ (T ↛ S) -> nf Γ T -> neu Γ S
      ▹ : ∀{T} -> var tp Γ T -> neu Γ T

mutual 
  bn : ∀{Γ T} -> nf Γ T -> exp Γ T
  bn (ƛ n) = ƛ (bn n)
  bn (ne n) = be n
  bn c = c

  be : ∀{Γ T} -> neu Γ T -> exp Γ T
  be (n · n') = be n · bn n'
  be (▹ x) = ▹ x
  
mutual
  reflect : ∀ Γ T -> exp Γ T -> ⟦ T ⟧t
  reflect Γ i e = unit -- ??
  reflect Γ (t ↛ t₁) e = λ x → reflect Γ t₁ (e · bn (reify Γ t x))

  reify : ∀ Γ T -> ⟦ T ⟧t -> nf Γ T
  reify Γ i unit = c
  reify Γ (t ↛ t₁) s = ƛ (reify (Γ , t) t₁ (s (reflect (Γ , t) t (▹ top))))

nbe : ∀{T} -> exp ⊡ T -> nf ⊡ T
nbe e = reify _ _ (⟦ e ⟧ ⊡)

ex0 : exp ⊡ (i ↛ i)
ex0 = ƛ (▹ top) -- OH OH

ex1 : exp ⊡ i
ex1 = (ƛ (▹ top)) · c

