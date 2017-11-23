module STLC where

infixr 20 _▷_
data Ty : Set where
  ∙   : Ty
  _▷_ : Ty → Ty → Ty

open import SimplyTyped.Code Ty
open import Data.Nat
open import Data.Vec
open import Data.List
open import Data.List.All
open import Data.Product
open import Relation.Binary.PropositionalEquality

data `STLC : Set where
  `lam `app : `STLC

STLC : Code
STLC = sg `STLC λ
  { `lam   → sg Ty λ t → node (1 ∷ []) λ { ((t′ ∷ [] , u) ∷ []) t₀ → t′ ≡ t × t₀ ≡ t ▷ u }
  ; `app   → node (0 ∷ 0 ∷ []) λ { (([] , t₁) ∷ ([] , t₂) ∷ []) t → t₁ ≡ t₂ ▷ t }
  }

open import SimplyTyped.Sub STLC public

[var] : ∀ {t Γ} → Var t Γ → Tm Γ t
[var] = var

-- [lam] : ∀ {Γ u} t → Tm (Γ , t) u → Tm Γ (t ▷ u)
pattern [lam] t e = con (sg `lam (sg t (node ((_ ∷ [] , _) ∷ []) (e ∷ []) {{refl , refl}})))

-- _[·]_ : ∀ {Γ u t} → Tm Γ (u ▷ t) → Tm Γ u → Tm Γ t
pattern _[·]_ f e = con (sg `app (node (([] , _) ∷ ([] , _) ∷ []) (f ∷ e ∷ []) {{refl}}))

open import Relation.Binary
open import Data.Star
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Empty

data Value : {Γ : Ctx} → {t : Ty} → Tm Γ t → Set where
  lam   : ∀ {Γ t} → ∀ u (e : Tm (Γ , u) t) → Value {Γ} {u ▷ t} ([lam] u e)

data _==>_ {Γ} : ∀ {t} → Rel (Tm Γ t) lzero where
  app-lam : ∀ {t u} (f : Tm _ t) {v : Tm _ u} → Value v → ([lam] u f [·] v) ==> sub (reflₛ , v) f
  appˡ : ∀ {t u} {f f′ : Tm Γ (u ▷ t)} → f ==> f′ → (e : Tm Γ u) → (f [·] e) ==> (f′ [·] e)
  appʳ : ∀ {t u} {f} → Value {Γ} {u ▷ t} f → ∀ {e e′ : Tm Γ u} → e ==> e′ → (f [·] e) ==> (f [·] e′)

_==>*_ : ∀ {Γ t} → Rel (Tm Γ t) _
_==>*_ = Star _==>_

NF : ∀ {a b} {A : Set a} → Rel A b → A → Set _
NF next x = ∄ (next x)

value⇒normal : ∀ {Γ t e} → Value {Γ} {t} e → NF _==>_ e
value⇒normal (lam t e) (_ , ())

Deterministic : ∀ {a b} {A : Set a} → Rel A b → Set _
Deterministic _∼_ = ∀ {x y y′} → x ∼ y → x ∼ y′ → y ≡ y′

deterministic : ∀ {Γ t} → Deterministic (_==>_ {Γ} {t})
deterministic (app-lam f _) (app-lam ._ _) = refl
deterministic (app-lam f v) (appˡ () _)
deterministic (app-lam f v) (appʳ f′ e) = ⊥-elim (value⇒normal v (, e))
deterministic (appˡ () e) (app-lam f v)
deterministic (appˡ f e) (appˡ f′ ._) rewrite deterministic f f′ = refl
deterministic (appˡ f e) (appʳ f′ _) = ⊥-elim (value⇒normal f′ (, f))
deterministic (appʳ f e) (app-lam f′ v) = ⊥-elim (value⇒normal v (, e))
deterministic (appʳ f e) (appˡ f′ _) = ⊥-elim (value⇒normal f (, f′))
deterministic (appʳ f e) (appʳ f′ e′) rewrite deterministic e e′ = refl

Halts : ∀ {Γ t} → Tm Γ t → Set
Halts e = ∃ λ e′ → e ==>* e′ × Value e′

value⇒halts : ∀ {Γ t e} → Value {Γ} {t} e → Halts e
value⇒halts {e = e} v = e , ε , v
