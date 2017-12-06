import SimplyTyped.Code

module SimplyTyped.EraseType {Ty : Set} (code : SimplyTyped.Code.Code Ty) where

open SimplyTyped.Code Ty
open import SimplyTyped.Ctx Ty
open import SimplyTyped.Typed code
open import SimplyTyped.Untyped code renaming (Con to Conₑ)
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Relation.Binary.PropositionalEquality
open import Data.Vec
open import Data.List
open import Data.List.All
open import Data.Product

size : Ctx → ℕ
size ∅       = 0
size (Γ , _) = suc (size Γ)

x+sy≡sx+y : ∀ x y → x + suc y ≡ suc x + y
x+sy≡sx+y zero    y = refl
x+sy≡sx+y (suc x) y rewrite x+sy≡sx+y x y = refl

size-<>< : ∀ {n} (Γ : Ctx) (bs : Vec Binder n) (ts : Vec Ty n) → size (Γ <>< visible bs ts) ≡ visibleCount bs + size Γ
size-<><         Γ []             []       = refl
size-<>< {suc n} Γ (unbound ∷ bs) (t ∷ ts) rewrite size-<>< Γ bs ts = refl
size-<>< {suc n} Γ (bound ∷ bs)   (t ∷ ts) rewrite size-<>< (Γ , t) bs ts = x+sy≡sx+y (visibleCount bs) (size Γ)

untypeᵛ : ∀ {Γ t} → Var t Γ → Fin (size Γ)
untypeᵛ vz     = zero
untypeᵛ (vs v) = suc (untypeᵛ v)

mutual
  untype : ∀ {Γ t} → Tm Γ t → Expr (size Γ)
  untype (var v) = var (untypeᵛ v)
  untype (con e) = con (untypeᶜ e)

  untypeᶜ : ∀ {Γ t c} → Con Γ t c → Conₑ (size Γ) c
  untypeᶜ (sg x e)     = sg x (untypeᶜ e)
  untypeᶜ (node ts es) = node (untypeˡ es)

  untypeˡ : ∀ {Γ n sh ts₀ ts} → Children Γ {n} ts₀ {sh} ts → All (λ k → Expr (visibleCount k + size Γ)) sh
  untypeˡ                         []       = []
  untypeˡ {Γ} {sh = bs ∷ _} {ts₀} (e ∷ es) = subst Expr (size-<>< Γ bs ts₀) (untype e) ∷ untypeˡ es
