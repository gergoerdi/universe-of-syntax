module STLC where

infixr 20 _▷_
data Ty : Set where
  ∙   : Ty
  _▷_ : Ty → Ty → Ty
  Bool : Ty

open import SimplyTyped.Code Ty
open import Data.Nat
open import Data.Vec
open import Data.List
open import Data.List.All
open import Data.Product
open import Relation.Binary.PropositionalEquality

data `STLC : Set where
  `lam `app : `STLC
  `true `false `if : `STLC

STLC : Code
STLC = sg `STLC λ
  { `lam   → sg Ty λ t → node 1 ((bound ∷ []) ∷ []) λ { (t′ ∷ []) (u ∷ []) t₀ → t′ ≡ t × t₀ ≡ t ▷ u }
  ; `app   → node 0 ([] ∷ [] ∷ []) λ { [] (t₁ ∷ t₂ ∷ []) t → t₁ ≡ t₂ ▷ t }
  ; `true  → node 0 [] λ { [] [] → Bool ≡_ }
  ; `false → node 0 [] λ { [] [] → Bool ≡_ }
  ; `if    → node 0 ([] ∷ [] ∷ [] ∷ []) (λ { [] (b ∷ t₁ ∷ t₂ ∷ []) t → b ≡ Bool × t₁ ≡ t₂ × t₁ ≡ t })
  }

open import SimplyTyped.Ctx Ty public
open import SimplyTyped.Typed STLC public
open import SimplyTyped.Sub STLC public

[var] : ∀ {t Γ} → Var t Γ → Tm Γ t
[var] = var

-- [lam] : ∀ {Γ u} t → Tm (Γ , t) u → Tm Γ (t ▷ u)
pattern [lam] t e = con (sg `lam (sg t (node (_ ∷ []) (e ∷ []) {{refl , refl}})))

-- _[·]_ : ∀ {Γ u t} → Tm Γ (u ▷ t) → Tm Γ u → Tm Γ t
pattern _[·]_ f e = con (sg `app (node [] (f ∷ e ∷ []) {{refl}}))

-- [true] : ∀ {Γ} → Tm Γ Bool
pattern [true] = con (sg `true (node [] [] {{refl}}))
pattern [false] = con (sg `false (node [] [] {{refl}}))

-- [if]_[then]_[else]_ : ∀ {Γ t} → Tm Γ Bool → Tm Γ t → Tm Γ t → Tm Γ t
pattern [if]_[then]_[else]_ b thn els = con (sg `if (node [] (b ∷ thn ∷ els ∷ []) {{refl , (refl , refl)}}))

open import Relation.Binary
open import Data.Star
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Empty

data Value : {Γ : Ctx} → {t : Ty} → Tm Γ t → Set where
  lam   : ∀ {Γ t} → ∀ u (e : Tm (Γ , u) t) → Value {Γ} {u ▷ t} ([lam] u e)
  true  : ∀ {Γ} → Value {Γ} [true]
  false : ∀ {Γ} → Value {Γ} [false]

data _==>_ {Γ} : ∀ {t} → Rel (Tm Γ t) lzero where
  app-lam : ∀ {t u} (f : Tm _ t) {v : Tm _ u} → Value v → ([lam] u f [·] v) ==> sub (reflₛ , v) f
  appˡ : ∀ {t u} {f f′ : Tm Γ (u ▷ t)} → f ==> f′ → (e : Tm Γ u) → (f [·] e) ==> (f′ [·] e)
  appʳ : ∀ {t u} {f} → Value {Γ} {u ▷ t} f → ∀ {e e′ : Tm Γ u} → e ==> e′ → (f [·] e) ==> (f [·] e′)
  if-cond : ∀ {t} {b b′ : Tm Γ _} → b ==> b′ → (thn els : Tm Γ t) → ([if] b [then] thn [else] els) ==> ([if] b′ [then] thn [else] els)
  if-true : ∀ {t} (thn els : Tm _ t) → ([if] [true] [then] thn [else] els) ==> thn
  if-false : ∀ {t} (thn els : Tm _ t) → ([if] [false] [then] thn [else] els) ==> els

_==>*_ : ∀ {Γ t} → Rel (Tm Γ t) _
_==>*_ = Star _==>_

NF : ∀ {a b} {A : Set a} → Rel A b → A → Set _
NF next x = ∄ (next x)

value⇒normal : ∀ {Γ t e} → Value {Γ} {t} e → NF _==>_ e
value⇒normal (lam t e) (_ , ())
value⇒normal true (_ , ())
value⇒normal false (_ , ())

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
deterministic (if-true thn els) (if-true _ _) = refl
deterministic (if-false thn els) (if-false _ _) = refl
deterministic (if-cond b thn els) (if-cond b′ _ _) rewrite deterministic b b′ = refl
deterministic (if-cond () thn els) (if-true _ _)
deterministic (if-cond () thn els) (if-false _ _)
deterministic (if-true thn els) (if-cond () _ _)
deterministic (if-false thn els) (if-cond () _ _)

Halts : ∀ {Γ t} → Tm Γ t → Set
Halts e = ∃ λ e′ → e ==>* e′ × Value e′

value⇒halts : ∀ {Γ t e} → Value {Γ} {t} e → Halts e
value⇒halts {e = e} v = e , ε , v
