import SimplyTyped.Code
import SimplyTyped.Typed

module SimplyTyped.Sub.Properties {Ty : Set} (code : SimplyTyped.Code.Code Ty) where

open SimplyTyped.Code Ty
open import SimplyTyped.Sub code
open import SimplyTyped.Ren Ty
open import SimplyTyped.Ren.Properties Ty
open import Data.Vec using (toList)
open import Data.List hiding (drop)
open import Data.List.All
open import Data.Product
open import Relation.Binary.PropositionalEquality

mutual
  ren-refl : ∀ {Γ t} → (e : Tm Γ t) → ren reflᵣ e ≡ e
  ren-refl (var v) rewrite renᵛ-refl v = refl
  ren-refl (con e) rewrite renᶜ-refl e = refl

  renᶜ-refl : ∀ {c Γ t} (e : Con Γ t c) → renᶜ reflᵣ e ≡ e
  renᶜ-refl (sg x e)     rewrite renᶜ-refl e  = refl
  renᶜ-refl (node ts es) rewrite renˡ-refl es = refl

  renˡ-refl : ∀ {Γ n sh ts₀ ts} (es : Children Γ {n} ts₀ {sh} ts) → renˡ reflᵣ es ≡ es
  renˡ-refl                         []       = refl
  renˡ-refl {Γ} {sh = bs ∷ _} {ts₀} (e ∷ es) rewrite keep*-refl {Γ} (visible bs ts₀) = cong₂ _∷_ (ren-refl e) (renˡ-refl es)

mutual
  ren-⊇⊇ : ∀ {Γ Θ Δ t} (Γ⊇Θ : Γ ⊇ Θ) (Θ⊇Δ : Θ ⊇ Δ) (e : Tm Δ t) →
    ren Γ⊇Θ (ren Θ⊇Δ e) ≡ ren (Γ⊇Θ ⊇⊇ Θ⊇Δ) e
  ren-⊇⊇ Γ⊇Θ Θ⊇Δ (var v) rewrite renᵛ-⊇⊇ Γ⊇Θ Θ⊇Δ v = refl
  ren-⊇⊇ Γ⊇Θ Θ⊇Δ (con e) rewrite renᶜ-⊇⊇ Γ⊇Θ Θ⊇Δ e = refl

  renᶜ-⊇⊇ : ∀ {Γ Θ Δ t c} (Γ⊇Θ : Γ ⊇ Θ) (Θ⊇Δ : Θ ⊇ Δ) (e : Con Δ t c) →
    renᶜ Γ⊇Θ (renᶜ Θ⊇Δ e) ≡ renᶜ (Γ⊇Θ ⊇⊇ Θ⊇Δ) e
  renᶜ-⊇⊇ Γ⊇Θ Θ⊇Δ (sg x e)     rewrite renᶜ-⊇⊇ Γ⊇Θ Θ⊇Δ e  = refl
  renᶜ-⊇⊇ Γ⊇Θ Θ⊇Δ (node ts es) rewrite renˡ-⊇⊇ Γ⊇Θ Θ⊇Δ es = refl

  renˡ-⊇⊇ : ∀ {Γ Θ Δ n sh ts₀ ts} (Γ⊇Θ : Γ ⊇ Θ) (Θ⊇Δ : Θ ⊇ Δ) (es : Children Δ {n} ts₀ {sh} ts) →
    renˡ Γ⊇Θ (renˡ Θ⊇Δ es) ≡ renˡ (Γ⊇Θ ⊇⊇ Θ⊇Δ) es
  renˡ-⊇⊇ Γ⊇Θ Θ⊇Δ [] = refl
  renˡ-⊇⊇ {sh = bs ∷ _} {ts₀} Γ⊇Θ Θ⊇Δ (e ∷ es) rewrite
    ren-⊇⊇ (keep* (visible bs ts₀) Γ⊇Θ) (keep* (visible bs ts₀) Θ⊇Δ) e |
    keep*-⊇⊇ (visible bs ts₀) Γ⊇Θ Θ⊇Δ |
    renˡ-⊇⊇ Γ⊇Θ Θ⊇Δ es
    = refl

assocᵣᵣₛ : ∀ {Γ Δ Θ Ξ} (Γ⊇Δ : Γ ⊇ Δ) (Δ⊇Θ : Δ ⊇ Θ) (σ : Θ ⊢⋆ Ξ) →
  Γ⊇Δ ⊇⊢⋆ (Δ⊇Θ ⊇⊢⋆ σ) ≡ (Γ⊇Δ ⊇⊇ Δ⊇Θ) ⊇⊢⋆ σ
assocᵣᵣₛ Γ⊇Δ Δ⊇Θ ∅ = refl
assocᵣᵣₛ Γ⊇Δ Δ⊇Θ (σ , e) rewrite assocᵣᵣₛ Γ⊇Δ Δ⊇Θ σ | ren-⊇⊇ Γ⊇Δ Δ⊇Θ e = refl

assocᵣₛᵣ : ∀ {Γ Δ Θ Ξ} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (Θ⊇Ξ : Θ ⊇ Ξ) →
  Γ⊇Δ ⊇⊢⋆ (σ ⊢⋆⊇ Θ⊇Ξ) ≡  (Γ⊇Δ ⊇⊢⋆ σ) ⊢⋆⊇ Θ⊇Ξ
assocᵣₛᵣ Γ⊇Δ σ       done       = refl
assocᵣₛᵣ Γ⊇Δ (σ , e) (drop Θ⊇Ξ) rewrite assocᵣₛᵣ Γ⊇Δ σ Θ⊇Ξ = refl
assocᵣₛᵣ Γ⊇Δ (σ , e) (keep Θ⊇Ξ) rewrite assocᵣₛᵣ Γ⊇Δ σ Θ⊇Ξ = refl

shift*-keep* : ∀ {Γ Δ Θ} ts (σ : Γ ⊢⋆ Δ) (Δ⊇Θ : Δ ⊇ Θ) →
  shift* ts (σ ⊢⋆⊇ Δ⊇Θ) ≡ shift* ts σ ⊢⋆⊇ keep* ts Δ⊇Θ
shift*-keep* [] σ Δ⊇Θ = refl
shift*-keep* (t ∷ ts) σ Δ⊇Θ rewrite assocᵣₛᵣ (drop {t} reflᵣ) σ Δ⊇Θ = shift*-keep* ts (shift σ) (keep Δ⊇Θ)

keep*-shift* : ∀ {Γ Δ Θ} ts (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) →
  shift* ts (Γ⊇Δ ⊇⊢⋆ σ) ≡ keep* ts Γ⊇Δ ⊇⊢⋆ shift* ts σ
keep*-shift* []       Γ⊇Δ σ = refl
keep*-shift* (t ∷ ts) Γ⊇Δ σ rewrite
  assocᵣᵣₛ (wk {t}) Γ⊇Δ σ |
  refl-⊇⊇ Γ⊇Δ | sym (Γ⊇Δ ⊇⊇-refl) |
  sym (assocᵣᵣₛ (keep {t} Γ⊇Δ) wk σ) | Γ⊇Δ ⊇⊇-refl
  = keep*-shift* ts (keep Γ⊇Δ) (shift σ)

refl-⊇⊢⋆_ : ∀ {Γ Δ} (σ : Γ ⊢⋆ Δ) →
  reflᵣ ⊇⊢⋆ σ ≡ σ
refl-⊇⊢⋆ ∅       = refl
refl-⊇⊢⋆ (σ , e) rewrite refl-⊇⊢⋆ σ | ren-refl e = refl

_⊢⋆⊇-refl : ∀ {Γ Δ} (σ : Γ ⊢⋆ Δ) → σ ⊢⋆⊇ reflᵣ ≡ σ
∅       ⊢⋆⊇-refl = refl
(σ , e) ⊢⋆⊇-refl rewrite σ ⊢⋆⊇-refl = refl

refl-⊢⋆⊇_ : ∀ {Γ Δ} (Γ⊇Δ : Γ ⊇ Δ) →
  reflₛ ⊢⋆⊇ Γ⊇Δ ≡ ren⇒sub Γ⊇Δ
refl-⊢⋆⊇ done           = refl
refl-⊢⋆⊇ (drop {t} Γ⊇Δ) rewrite sym (assocᵣₛᵣ (wk {t}) reflₛ Γ⊇Δ) | refl-⊢⋆⊇ Γ⊇Δ = refl
refl-⊢⋆⊇ (keep {t} Γ⊇Δ) rewrite sym (assocᵣₛᵣ (wk {t}) reflₛ Γ⊇Δ) | refl-⊢⋆⊇ Γ⊇Δ = refl

subᵛ-⊢⋆⊇ : ∀ {Γ Δ Θ t} (σ : Γ ⊢⋆ Δ) (Δ⊇Θ : Δ ⊇ Θ) (v : Var t Θ) →
  subᵛ (σ ⊢⋆⊇ Δ⊇Θ) v ≡ subᵛ σ (renᵛ Δ⊇Θ v)
subᵛ-⊢⋆⊇ σ       done v            = refl
subᵛ-⊢⋆⊇ (σ , e) (drop Δ⊇Θ) v      rewrite subᵛ-⊢⋆⊇ σ Δ⊇Θ v = refl
subᵛ-⊢⋆⊇ (σ , e) (keep Δ⊇Θ) vz     = refl
subᵛ-⊢⋆⊇ (σ , e) (keep Δ⊇Θ) (vs v) rewrite subᵛ-⊢⋆⊇ σ Δ⊇Θ v = refl

mutual
  sub-⊢⋆⊇ : ∀ {Γ Δ Θ t} (σ : Γ ⊢⋆ Δ) (Δ⊇Θ : Δ ⊇ Θ) (e : Tm Θ t) →
    sub (σ ⊢⋆⊇ Δ⊇Θ) e ≡ sub σ (ren Δ⊇Θ e)
  sub-⊢⋆⊇ σ Δ⊇Θ (var v) rewrite subᵛ-⊢⋆⊇ σ Δ⊇Θ v = refl
  sub-⊢⋆⊇ σ Δ⊇Θ (con e) rewrite subᶜ-⊢⋆⊇ σ Δ⊇Θ e = refl

  subᶜ-⊢⋆⊇ : ∀ {Γ Δ Θ t c} (σ : Γ ⊢⋆ Δ) (Δ⊇Θ : Δ ⊇ Θ) (e : Con Θ t c) →
    subᶜ (σ ⊢⋆⊇ Δ⊇Θ) e ≡ subᶜ σ (renᶜ Δ⊇Θ e)
  subᶜ-⊢⋆⊇ σ Δ⊇Θ (sg x e)     rewrite subᶜ-⊢⋆⊇ σ Δ⊇Θ e = refl
  subᶜ-⊢⋆⊇ σ Δ⊇Θ (node ts es) rewrite subˡ-⊢⋆⊇ σ Δ⊇Θ es = refl

  subˡ-⊢⋆⊇ : ∀ {Γ Δ Θ n sh ts₀ ts} (σ : Γ ⊢⋆ Δ) (Δ⊇Θ : Δ ⊇ Θ) (es : Children Θ {n} ts₀ {sh} ts) →
    subˡ (σ ⊢⋆⊇ Δ⊇Θ) es ≡ subˡ σ (renˡ Δ⊇Θ es)
  subˡ-⊢⋆⊇                     σ Δ⊇Θ []       = refl
  subˡ-⊢⋆⊇ {sh = bs ∷ _} {ts₀} σ Δ⊇Θ (e ∷ es) rewrite
    shift*-keep* (visible bs ts₀) σ Δ⊇Θ |
    sub-⊢⋆⊇ (shift* (visible bs ts₀) σ) (keep* (visible bs ts₀) Δ⊇Θ) e |
    subˡ-⊢⋆⊇ σ Δ⊇Θ es
    = refl

subᵛ-⊇⊢⋆ : ∀ {Γ Δ Θ t} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (v : Var t Θ) →
  subᵛ (Γ⊇Δ ⊇⊢⋆ σ) v ≡ ren Γ⊇Δ (subᵛ σ v)
subᵛ-⊇⊢⋆ Γ⊇Δ (σ , _) vz     = refl
subᵛ-⊇⊢⋆ Γ⊇Δ (σ , _) (vs v) = subᵛ-⊇⊢⋆ Γ⊇Δ σ v

mutual
  sub-⊇⊢⋆ : ∀ {Γ Δ Θ t} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (e : Tm Θ t) →
    sub (Γ⊇Δ ⊇⊢⋆ σ) e ≡ ren Γ⊇Δ (sub σ e)
  sub-⊇⊢⋆ σ Δ⊇Θ (var v) rewrite subᵛ-⊇⊢⋆ σ Δ⊇Θ v = refl
  sub-⊇⊢⋆ σ Δ⊇Θ (con e) rewrite subᶜ-⊇⊢⋆ σ Δ⊇Θ e = refl

  subᶜ-⊇⊢⋆ : ∀ {Γ Δ Θ t c} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (e : Con Θ t c) →
    subᶜ (Γ⊇Δ ⊇⊢⋆ σ) e ≡ renᶜ Γ⊇Δ (subᶜ σ e)
  subᶜ-⊇⊢⋆ Γ⊇Δ σ (sg x e)     rewrite subᶜ-⊇⊢⋆ Γ⊇Δ σ e = refl
  subᶜ-⊇⊢⋆ Γ⊇Δ σ (node ts es) rewrite subˡ-⊇⊢⋆ Γ⊇Δ σ es = refl

  subˡ-⊇⊢⋆ : ∀ {Γ Δ Θ n sh ts₀ ts} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (es : Children Θ {n} ts₀ {sh} ts) →
    subˡ (Γ⊇Δ ⊇⊢⋆ σ) es ≡ renˡ Γ⊇Δ (subˡ σ es)
  subˡ-⊇⊢⋆                     Γ⊇Δ σ []       = refl
  subˡ-⊇⊢⋆ {sh = bs ∷ _} {ts₀} Γ⊇Δ σ (e ∷ es) rewrite
    keep*-shift* (visible bs ts₀) Γ⊇Δ σ |
    sub-⊇⊢⋆ (keep* (visible bs ts₀) Γ⊇Δ) (shift* (visible bs ts₀) σ) e |
    subˡ-⊇⊢⋆ Γ⊇Δ σ es
    = refl

assocₛᵣₛ : ∀ {Γ Δ Θ Ξ} (ρ : Θ ⊢⋆ Ξ) (Δ⊇Θ : Δ ⊇ Θ) (σ : Γ ⊢⋆ Δ) →
  σ ⊢⊢⋆ (Δ⊇Θ ⊇⊢⋆ ρ) ≡ (σ ⊢⋆⊇ Δ⊇Θ) ⊢⊢⋆ ρ
assocₛᵣₛ ∅       Δ⊇Θ σ = refl
assocₛᵣₛ (ρ , e) Δ⊇Θ σ rewrite assocₛᵣₛ ρ Δ⊇Θ σ | sym (sub-⊢⋆⊇ σ Δ⊇Θ e) = refl

assocᵣₛₛ :  ∀ {Γ Δ Θ Ξ} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Ξ) →
  Γ⊇Δ ⊇⊢⋆ (σ ⊢⊢⋆ ρ) ≡ (Γ⊇Δ ⊇⊢⋆ σ) ⊢⊢⋆ ρ
assocᵣₛₛ Γ⊇Δ σ ∅       = refl
assocᵣₛₛ Γ⊇Δ σ (ρ , e) rewrite assocᵣₛₛ Γ⊇Δ σ ρ | sym (sub-⊇⊢⋆ Γ⊇Δ σ e) = refl

subᵛ-refl : ∀ {Γ t} (v : Var t Γ) → subᵛ reflₛ v ≡ var v
subᵛ-refl vz         = refl
subᵛ-refl (vs {u} v) rewrite subᵛ-⊇⊢⋆ (wk {u}) reflₛ v | subᵛ-refl v | renᵛ-refl v = refl

shift*-refl : ∀ {Γ} ts → shift* ts (reflₛ {Γ}) ≡ reflₛ
shift*-refl {Γ} [] = refl
shift*-refl {Γ} (t ∷ ts) = shift*-refl {Γ , t} ts

mutual
  sub-refl : ∀ {Γ t} (e : Tm Γ t) → sub reflₛ e ≡ e
  sub-refl (var v) rewrite subᵛ-refl v = refl
  sub-refl (con e) rewrite subᶜ-refl e = refl

  subᶜ-refl : ∀ {Γ t c} (e : Con Γ t c) → subᶜ reflₛ e ≡ e
  subᶜ-refl (sg x e)    rewrite subᶜ-refl e = refl
  subᶜ-refl (node s es) rewrite subˡ-refl es = refl

  subˡ-refl : ∀ {Γ n sh ts₀ ts} (es : Children Γ {n} ts₀ {sh} ts) → subˡ reflₛ es ≡ es
  subˡ-refl                         []       = refl
  subˡ-refl {Γ} {sh = bs ∷ _} {ts₀} (e ∷ es) rewrite shift*-refl {Γ} (visible bs ts₀) = cong₂ _∷_ (sub-refl _) (subˡ-refl _)

subᵛ-⊢⊢⋆  : ∀ {Γ Δ Θ t} (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) (v : Var t Δ) →
  subᵛ (σ ⊢⊢⋆ ρ) v ≡ sub σ (subᵛ ρ v)
subᵛ-⊢⊢⋆ σ (ρ , _) vz     = refl
subᵛ-⊢⊢⋆ σ (ρ , _) (vs v) = subᵛ-⊢⊢⋆ σ ρ v

shift*-⊢⊢⋆ : ∀ {Γ Δ Θ} ts (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) → shift* ts (σ ⊢⊢⋆ ρ) ≡ shift* ts σ ⊢⊢⋆ shift* ts ρ
shift*-⊢⊢⋆ []       σ ρ = refl
shift*-⊢⊢⋆ (t ∷ ts) σ ρ rewrite
  assocᵣₛₛ (wk {t}) σ ρ |
  cong (_⊢⊢⋆ ρ) (sym ((wk {t} ⊇⊢⋆ σ) ⊢⋆⊇-refl)) |
  sym (assocₛᵣₛ ρ (wk {t}) (shift σ))
  = shift*-⊢⊢⋆ ts (wk ⊇⊢⋆ σ , var vz) (wk ⊇⊢⋆ ρ , var vz)

mutual
  sub-⊢⊢⋆ : ∀ {Γ Δ Θ t} (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) (e : Tm Δ t) →
    sub (σ ⊢⊢⋆ ρ) e ≡ sub σ (sub ρ e)
  sub-⊢⊢⋆ σ ρ (var v) rewrite subᵛ-⊢⊢⋆ σ ρ v = refl
  sub-⊢⊢⋆ σ ρ (con e) rewrite subᶜ-⊢⊢⋆ σ ρ e = refl

  subᶜ-⊢⊢⋆ : ∀ {Γ Δ Θ t c} (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) (e : Con Δ t c) →
    subᶜ (σ ⊢⊢⋆ ρ) e ≡ subᶜ σ (subᶜ ρ e)
  subᶜ-⊢⊢⋆ σ ρ (sg x e)    rewrite subᶜ-⊢⊢⋆ σ ρ e = refl
  subᶜ-⊢⊢⋆ σ ρ (node s es) rewrite subˡ-⊢⊢⋆ σ ρ es = refl

  subˡ-⊢⊢⋆ : ∀ {Γ Δ Θ n sh ts₀ ts} (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) (es : Children Δ {n} ts₀ {sh} ts) →
    subˡ (σ ⊢⊢⋆ ρ) es ≡ subˡ σ (subˡ ρ es)
  subˡ-⊢⊢⋆                     σ ρ []       = refl
  subˡ-⊢⊢⋆ {sh = bs ∷ _} {ts₀} σ ρ (e ∷ es) rewrite
    shift*-⊢⊢⋆ (visible bs ts₀) σ ρ
    = cong₂ _∷_ (sub-⊢⊢⋆ _ _ e) (subˡ-⊢⊢⋆ _ _ es)

refl-⊢⊢⋆_ : ∀ {Γ Δ} (σ : Γ ⊢⋆ Δ) → reflₛ ⊢⊢⋆ σ ≡ σ
refl-⊢⊢⋆ ∅       = refl
refl-⊢⊢⋆ (σ , e) rewrite refl-⊢⊢⋆ σ | sub-refl e = refl

_⊢⊢⋆-refl : ∀ {Γ Δ} (σ : Γ ⊢⋆ Δ) → σ ⊢⊢⋆ reflₛ ≡ σ
∅       ⊢⊢⋆-refl = refl
(σ , e) ⊢⊢⋆-refl rewrite assocₛᵣₛ reflₛ wk (σ , e) | σ ⊢⋆⊇-refl | σ ⊢⊢⋆-refl = refl
