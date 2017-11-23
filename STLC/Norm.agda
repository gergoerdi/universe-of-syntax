module STLC.Norm where

open import STLC

open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Relation.Binary
open import Data.Star
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product
open import Function.Equivalence hiding (sym)
open import Function.Equality using (_⟨$⟩_)

-- -- This would not be strictly positive!
-- data Saturated : ∀ {Γ t} → Tm Γ t → Set where
--   fun : ∀ {t u} {f : Tm ∅ (t ▷ u)} → Halts f → (∀ {e} → Saturated e → Saturated (f · e)) → Saturated f

mutual
  Saturated : ∀ {t} → Tm ∅ t → Set
  Saturated e = Halts e × Saturated′ _ e

  Saturated′ : ∀ t → Tm ∅ t → Set
  Saturated′ ∙ _ = ⊥
  Saturated′ (t ▷ u) f = ∀ {e} → Saturated e → Saturated (f [·] e)

saturated⇒halts : ∀ {t e} → Saturated {t} e → Halts e
saturated⇒halts = proj₁

step‿preserves‿halting : ∀ {Γ t} {e e′ : Tm Γ t} → e ==> e′ → Halts e ⇔ Halts e′
step‿preserves‿halting {e = e} {e′ = e′} step = equivalence fwd bwd
  where
    fwd : Halts e → Halts e′
    fwd (e″ , ε , v) = ⊥-elim (value⇒normal v (, step ))
    fwd (e″ , s ◅ steps , v) rewrite deterministic step s = e″ , steps , v

    bwd : Halts e′ → Halts e
    bwd (e″ , steps , v) = e″ , step ◅ steps , v

step‿preserves‿saturated : ∀ {t} {e e′ : Tm _ t} → e ==> e′ → Saturated e ⇔ Saturated e′
step‿preserves‿saturated step = equivalence (fwd step) (bwd step)
  where
    fwd : ∀ {t} {e e′ : Tm _ t} → e ==> e′ → Saturated e → Saturated e′
    fwd {∙}       step (halts , ())
    fwd {u ▷ t}   step (halts , sat) = Equivalence.to (step‿preserves‿halting step) ⟨$⟩ halts , λ e → fwd (appˡ step _) (sat e)

    bwd : ∀ {t} {e e′ : Tm _ t} → e ==> e′ → Saturated e′ → Saturated e
    bwd {∙}       step (halts , ())
    bwd {u ▷ t}   step (halts , sat) = Equivalence.from (step‿preserves‿halting step) ⟨$⟩ halts , λ e → bwd (appˡ step _) (sat e)

step*‿preserves‿saturated : ∀ {t} {e e′ : Tm _ t} → e ==>* e′ → Saturated e ⇔ Saturated e′
step*‿preserves‿saturated ε = id
step*‿preserves‿saturated (step ◅ steps) = step*‿preserves‿saturated steps ∘ step‿preserves‿saturated step

data Instantiation : ∀ {Γ} → ∅ ⊢⋆ Γ → Set where
  ∅ : Instantiation ∅
  _,_ : ∀ {Γ t σ} → Instantiation {Γ} σ → ∀ {e} → Value {_} {t} e × Saturated e → Instantiation (σ , e)

saturateᵛ : ∀ {Γ σ} → Instantiation σ → ∀ {t} (x : Var t Γ) → Saturated (subᵛ σ x)
saturateᵛ (_ , (_ , sat)) vz = sat
saturateᵛ (env , _) (vs x) = saturateᵛ env x

app-lam* : ∀ {Γ t} {e e′ : Tm Γ t} → e ==>* e′ → Value e′ → ∀ {u} (f : Tm _ u) → ([lam] t f [·] e) ==>* sub (reflₛ , e′) f
app-lam* steps v f = gmap _ (appʳ (lam _ _)) steps  ◅◅ app-lam f v ◅ ε

open import SimplyTyped.Ren Ty
open import SimplyTyped.Sub.Properties STLC

-- What is a good name for this?
-- It basically states that you can push in outer arguments before the innermost one.
-- Should this be called some kind of constant propagation?
innermost‿last : ∀ {Γ u} (σ : ∅ ⊢⋆ Γ) (e′ : Tm ∅ u) →
  (∅ , e′) ⊢⊢⋆ (wk ⊇⊢⋆ σ) ≡ σ
innermost‿last ∅       e′ = refl
innermost‿last (σ , e) e′ rewrite innermost‿last σ e′ | sym (sub-⊢⋆⊇ (∅ , e′) wk e) | sub-refl e = refl

saturate : ∀ {Γ σ} → Instantiation σ → ∀ {t} → (e : Tm Γ t) → Saturated (sub σ e)
saturate         env          (var v)                       = saturateᵛ env v
saturate         env          (f [·] e)                     with saturate env f | saturate env e
saturate         env          (f [·] e) | _ , sat-f | sat-e = sat-f sat-e
saturate {Γ} {σ} env {.u ▷ t} ([lam] u f) = value⇒halts (lam u (sub (shift σ) f)) , sat-f
  where
    f′ = sub (shift σ) f

    sat-f : ∀ {e : Tm _ u} → Saturated e → Saturated ([lam] u f′ [·] e)
    sat-f {e} sat-e@((e′ , steps , v) , _) = Equivalence.from (step*‿preserves‿saturated f‿e==>f←σe) ⟨$⟩ sat
      where
        f←σe = sub (σ , e′) f
        f′‿e = [lam] u f′ [·] e

        sat-e′ : Saturated e′
        sat-e′ = Equivalence.to (step*‿preserves‿saturated steps) ⟨$⟩ sat-e

        sat : Saturated f←σe
        sat = saturate (env , (v , sat-e′)) f

        f‿e==>f←σe : f′‿e ==>* f←σe
        f‿e==>f←σe = subst (λ f₀ → _ ==>* f₀) lemma (app-lam* steps v (sub (shift σ) f))
          where
            lemma : sub (∅ , e′) (sub (shift σ) f) ≡ sub (σ , e′) f
            lemma rewrite sym (sub-⊢⊢⋆ (∅ , e′) (shift σ) f) | innermost‿last σ e′ = refl

normalization : ∀ {t} → (e : Tm ∅ t) → Halts e
normalization e rewrite sym (sub-refl e) = saturated⇒halts (saturate ∅ e)
