module SimplyTyped.Ren {a : _} (A : Set a) where

open import SimplyTyped.Ctx A

infix 3 _⊇_
data _⊇_ : Ctx → Ctx → Set where
  done : ∅ ⊇ ∅
  drop : ∀ {t Γ Δ} → Γ ⊇ Δ → Γ , t ⊇ Δ
  keep : ∀ {t Γ Δ} → Γ ⊇ Δ → Γ , t ⊇ Δ , t

reflᵣ : ∀ {Γ} → Γ ⊇ Γ
reflᵣ {∅} = done
reflᵣ {Γ , _} = keep reflᵣ

wk : ∀ {t Γ} → (Γ , t) ⊇ Γ
wk = drop reflᵣ

_⊇⊇_ : ∀ {Γ Θ Δ} → Γ ⊇ Θ → Θ ⊇ Δ → Γ ⊇ Δ
done       ⊇⊇       Θ⊇Δ  = Θ⊇Δ
(drop Γ⊇Θ) ⊇⊇       Θ⊇Δ  = drop (Γ⊇Θ ⊇⊇ Θ⊇Δ)
(keep Γ⊇Θ) ⊇⊇ (drop Θ⊇Δ) = drop (Γ⊇Θ ⊇⊇ Θ⊇Δ)
(keep Γ⊇Θ) ⊇⊇ (keep Θ⊇Δ) = keep (Γ⊇Θ ⊇⊇ Θ⊇Δ)

renᵛ : ∀ {Γ Δ t} → Δ ⊇ Γ → Var t Γ → Var t Δ
renᵛ done       v      = v
renᵛ (drop Δ⊇Γ) v      = vs (renᵛ Δ⊇Γ v)
renᵛ (keep Δ⊇Γ) vz     = vz
renᵛ (keep Δ⊇Γ) (vs v) = vs (renᵛ Δ⊇Γ v)
