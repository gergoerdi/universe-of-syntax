open import Data.List
import SimplyTyped.Code
import SimplyTyped.Typed

module SimplyTyped.Sub {Ty : Set} (code : SimplyTyped.Code.Code Ty) where

open import Data.Vec
open SimplyTyped.Code Ty

open SimplyTyped.Typed code public
open import SimplyTyped.Ren Ty
open import Data.List.All
open import Data.Product

open import Relation.Binary.PropositionalEquality

mutual
  ren : ∀ {Γ Δ t} → Γ ⊇ Δ → Tm Δ t → Tm Γ t
  ren Γ⊇Δ (var v) = var (renᵛ Γ⊇Δ v)
  ren Γ⊇Δ (con c) = con (renᶜ Γ⊇Δ c)

  renᶜ : ∀ {Γ Δ t c} → Γ ⊇ Δ → Con Δ t c → Con Γ t c
  renᶜ Γ⊇Δ (some x c)   = some x (renᶜ Γ⊇Δ c)
  renᶜ Γ⊇Δ (node es wt) rewrite ren-sound Γ⊇Δ es = node (renˡ Γ⊇Δ es) wt

  renˡ : ∀ {Γ Δ shape} → Γ ⊇ Δ → Children Δ shape → Children Γ shape
  renˡ Γ⊇Δ [] = []
  renˡ Γ⊇Δ ((ts , t , e) ∷ es) = (ts , t , ren (ren-<>< Γ⊇Δ ts) e) ∷ renˡ Γ⊇Δ es

  ren-sound : ∀ {Γ Δ shape} → (Γ⊇Δ : Γ ⊇ Δ) → (es : Children Δ shape) → typesOf es ≡ typesOf (renˡ Γ⊇Δ es)
  ren-sound Γ⊇Δ [] = refl
  ren-sound Γ⊇Δ (x ∷ es) = cong₂ _∷_ refl (ren-sound Γ⊇Δ es)

infixr 4 _,_
infix 3 _⊢⋆_
data _⊢⋆_ (Γ : Ctx) : Ctx → Set where
  ∅ : Γ ⊢⋆ ∅
  _,_ : ∀ {t Δ} → (σ : Γ ⊢⋆ Δ) → (e : Tm Γ t) → Γ ⊢⋆ Δ , t

infixr 20 _⊇⊢⋆_
_⊇⊢⋆_ : ∀ {Γ Δ Θ} → Θ ⊇ Γ → Γ ⊢⋆ Δ → Θ ⊢⋆ Δ
Θ⊇Γ ⊇⊢⋆ ∅       = ∅
Θ⊇Γ ⊇⊢⋆ (σ , e) = Θ⊇Γ ⊇⊢⋆ σ , ren Θ⊇Γ e

infixl 20 _⊢⋆⊇_
_⊢⋆⊇_ : ∀ {Γ Δ Θ} → Γ ⊢⋆ Δ → Δ ⊇ Θ → Γ ⊢⋆ Θ
σ       ⊢⋆⊇ done       = σ
(σ , e) ⊢⋆⊇ (drop Δ⊇Θ) = σ ⊢⋆⊇ Δ⊇Θ
(σ , e) ⊢⋆⊇ (keep Δ⊇Θ) = σ ⊢⋆⊇ Δ⊇Θ , e

wkₛ : ∀ {t Γ Δ} → Γ ⊢⋆ Δ → Γ , t ⊢⋆ Δ
wkₛ σ = wk ⊇⊢⋆ σ

subᵛ : ∀ {Γ Δ t} → Γ ⊢⋆ Δ → Var t Δ → Tm Γ t
subᵛ (σ , e) vz     = e
subᵛ (σ , e) (vs v) = subᵛ σ v

shift : ∀ {t Γ Δ} → Γ ⊢⋆ Δ → Γ , t ⊢⋆ Δ , t
shift {t} σ = wk ⊇⊢⋆ σ , var vz

ren⇒sub : ∀ {Γ Δ} → Γ ⊇ Δ → Γ ⊢⋆ Δ
ren⇒sub done       = ∅
ren⇒sub (drop Γ⊇Δ) = wk ⊇⊢⋆ (ren⇒sub Γ⊇Δ)
ren⇒sub (keep Γ⊇Δ) = shift (ren⇒sub Γ⊇Δ)

reflₛ : ∀ {Γ} → Γ ⊢⋆ Γ
reflₛ {∅}     = ∅
reflₛ {Γ , t} = shift reflₛ

-- mutual
--   sub : ∀ {Γ Δ t} → Γ ⊢⋆ Δ → Tm Δ t → Tm Γ t
--   sub σ (var v)   = subᵛ σ v
--   sub σ (con i e) = con i (subᶜ σ  e)

--   subᶜ : ∀ {c Γ Δ t} → Γ ⊢⋆ Δ → ⟦ c ⟧ᶜ Δ t → ⟦ c ⟧ᶜ Γ t
--   subᶜ σ (bind t e) = bind t (sub (shift σ) e)
--   subᶜ σ (node es)  = node (subˡ σ es)
--   subᶜ σ (some t e) = some t (subᶜ σ e)

--   subˡ : ∀ {Γ Δ ts} → Γ ⊢⋆ Δ → All (Tm Δ) ts → All (Tm Γ) ts
--   subˡ σ [] = []
--   subˡ σ (e ∷ es) = sub σ e ∷ subˡ σ es

-- _⊢⊢⋆_ : ∀ {Γ Δ Θ} → Γ ⊢⋆ Θ → Θ ⊢⋆ Δ → Γ ⊢⋆ Δ
-- σ ⊢⊢⋆ ∅ = ∅
-- σ ⊢⊢⋆ (ρ , e) = (σ ⊢⊢⋆ ρ) , sub σ e
