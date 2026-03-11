{-# OPTIONS --rewriting #-}

{-
This module defines environment classifiers (EC) and their contexts
-}

module EnvClassifiers where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Utils
open import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)
open import Relation.Nullary using (¬_; ¬?; Dec; yes; no)

infixl 5 _,α

-- | Environment classifier (EC) contexts
data ECCtx : Set where
  ∅    : ECCtx
  _,α : ECCtx → ECCtx

data _⊆_ : ECCtx → ECCtx → Set where

  Z : ∀ {Δ} → Δ ⊆ Δ

  S_ : ∀ {Δ Δ′} → Δ ⊆ Δ′ → Δ ⊆ (Δ′ ,α)

⊆-trans : ∀ {Δ₁ Δ₂ Δ₃} → Δ₁ ⊆ Δ₂ → Δ₂ ⊆ Δ₃ → Δ₁ ⊆ Δ₃
⊆-trans Δ₁⊆Δ₂ Z = Δ₁⊆Δ₂
⊆-trans Δ₁⊆Δ₂ (S Δ₂⊆Δ₃) = S ⊆-trans Δ₁⊆Δ₂ Δ₂⊆Δ₃

⊆-trans-Z-eq : ∀ {Δ₁ Δ₂} {Δ₁⊆Δ₂ : Δ₁ ⊆ Δ₂} → ⊆-trans Z Δ₁⊆Δ₂ ≡ Δ₁⊆Δ₂
⊆-trans-Z-eq {Δ₁⊆Δ₂ = Z} = refl
⊆-trans-Z-eq {Δ₁⊆Δ₂ = S Δ₁⊆Δ₂} = cong S_ ⊆-trans-Z-eq
{-# REWRITE ⊆-trans-Z-eq #-}

-- | EC variables (α, β)
data ECVar : (Δ : ECCtx) → Set where

  Z : ∀ {Δ} → ECVar (Δ ,α)

  S_ : ∀ {Δ} → ECVar Δ → ECVar (Δ ,α)

-- | EC renaming
infixr 7 _⇒ᵉ_

_⇒ᵉ_ : ECCtx → ECCtx → Set
Δ₁ ⇒ᵉ Δ₂ = ECVar Δ₁ → ECVar Δ₂

idᵉ : ∀ {Δ} → Δ ⇒ᵉ Δ
idᵉ x = x

infixr 6 _•ᵉ_

_•ᵉ_ : ∀ {Δ₁ Δ₂} → ECVar Δ₂ → Δ₁ ⇒ᵉ Δ₂ → (Δ₁ ,α) ⇒ᵉ Δ₂
(β •ᵉ _) Z = β
(_ •ᵉ ρ) (S α) = ρ α

extᵉ : ∀ {Δ₁ Δ₂} → Δ₁ ⇒ᵉ Δ₂ → (Δ₁ ,α) ⇒ᵉ (Δ₂ ,α)
extᵉ ρ Z = Z
extᵉ ρ (S α) = S (ρ α)

extᵉ-id-id : ∀ {Δ} → extᵉ (idᵉ {Δ}) ≡ (idᵉ {Δ ,α})
extᵉ-id-id {Δ} = extensionality λ { Z → refl ; (S α) → refl }
{-# REWRITE extᵉ-id-id #-}

⟰1ᵉ : ∀ {Δ₁ Δ₂} → Δ₁ ⇒ᵉ Δ₂ → Δ₁ ⇒ᵉ (Δ₂ ,α)
⟰1ᵉ ρ α = S (ρ α)

⟰ᵉ : ∀ {Δ₁ Δ₂} → Δ₁ ⊆ Δ₂ → Δ₁ ⇒ᵉ Δ₂
⟰ᵉ Z = idᵉ
⟰ᵉ (S Δ₁⊆Δ₂) = ⟰1ᵉ (⟰ᵉ Δ₁⊆Δ₂)

-- | Well-typed EC (e)
data EC : ECCtx → Set where

  ε : ∀ {Δ} → EC Δ

  `_ : ∀ {Δ} → ECVar Δ → EC Δ


-- | Well-typed gradual EC (ê)
data EC⋆ : ECCtx → Set where

  ⋆ : ∀ {Δ} → EC⋆ Δ

  ec : ∀ {Δ} → EC Δ → EC⋆ Δ

renᵉ-ec : ∀ {Δ₁ Δ₂} → Δ₁ ⇒ᵉ Δ₂ → EC Δ₁ → EC Δ₂
renᵉ-ec ρ ε = ε
renᵉ-ec ρ (` α) = ` ρ α

renᵉ-ec-id : ∀ {Δ} {e : EC Δ} → renᵉ-ec idᵉ e ≡ e
renᵉ-ec-id {Δ} {ε} = refl
renᵉ-ec-id {Δ} {` x} = refl
{-# REWRITE renᵉ-ec-id #-}

⇑ᵉ-ec : ∀ {Δ} → EC Δ → EC (Δ ,α)
⇑ᵉ-ec e = renᵉ-ec S_ e

renᵉ-ec⋆ : ∀ {Δ₁ Δ₂} → Δ₁ ⇒ᵉ Δ₂ → EC⋆ Δ₁ → EC⋆ Δ₂
renᵉ-ec⋆ ρ ⋆ = ⋆
renᵉ-ec⋆ ρ (ec e) = ec (renᵉ-ec ρ e)

renᵉ-ec⋆-id : ∀ {Δ} {ê : EC⋆ Δ} → renᵉ-ec⋆ idᵉ ê ≡ ê
renᵉ-ec⋆-id {Δ} {⋆} = refl
renᵉ-ec⋆-id {Δ} {ec x} = refl
{-# REWRITE renᵉ-ec⋆-id #-}

-- | EC substitution
infixr 7 _→ᵉ_

_→ᵉ_ : ECCtx → ECCtx → Set
Δ₁ →ᵉ Δ₂ = ECVar Δ₁ → EC Δ₂

idsᵉ : ∀ {Δ} → Δ →ᵉ Δ
idsᵉ = `_

extsᵉ : ∀ {Δ₁ Δ₂} → (Δ₁ →ᵉ Δ₂) → (Δ₁ ,α) →ᵉ (Δ₂ ,α)
extsᵉ σ Z = ` Z
extsᵉ σ (S_ α) = ⇑ᵉ-ec (σ α)

infixr 6 _•ᵉₛ_

_•ᵉₛ_ : ∀ {Δ₁ Δ₂} → EC Δ₂ → (Δ₁ →ᵉ Δ₂) → (Δ₁ ,α) →ᵉ Δ₂
(e •ᵉₛ σ) Z = e
(e •ᵉₛ σ) (S_ α) = σ α

subᵉ-ec : ∀ {Δ₁ Δ₂} → Δ₁ →ᵉ Δ₂ → EC Δ₁ → EC Δ₂
subᵉ-ec σ ε = ε
subᵉ-ec σ (` α) = σ α

subᵉ-ec⋆ : ∀ {Δ₁ Δ₂} → Δ₁ →ᵉ Δ₂ → EC⋆ Δ₁ → EC⋆ Δ₂
subᵉ-ec⋆ σ ⋆ = ⋆
subᵉ-ec⋆ σ (ec e) = ec (subᵉ-ec σ e)


infixl 5 _,_<:_

-- | EC subtyping contexts (Θ, Π)
data SubCtx : ECCtx → Set where

  ∅ : ∀ {Δ} → SubCtx Δ

  _,_<:_ : ∀ {Δ} → SubCtx Δ → EC Δ → EC Δ → SubCtx Δ

infix 0 _<:_∈_

data _<:_∈_ : ∀ {Δ} → EC Δ → EC Δ → SubCtx Δ → Set where

  Z : ∀ {Δ Θ} {e₁ e₂ : EC Δ} → e₁ <: e₂ ∈ (Θ , e₁ <: e₂)

  S_ : ∀ {Δ Θ} {e₁ e₂ e₃ e₄ : EC Δ} → e₁ <: e₂ ∈ Θ → e₁ <: e₂ ∈ (Θ , e₃ <: e₄)

renᵉ-subctx : ∀ {Δ₁ Δ₂} → Δ₁ ⇒ᵉ Δ₂ → SubCtx Δ₁ → SubCtx Δ₂
renᵉ-subctx ρ ∅ = ∅
renᵉ-subctx ρ (Θ , e₁ <: e₂) =
  renᵉ-subctx ρ Θ , renᵉ-ec ρ e₁ <: renᵉ-ec ρ e₂

renᵉ-<:∈ : ∀ {Δ₁ Δ₂} {Θ : SubCtx Δ₁} {e₁ e₂}
  → (ρ : Δ₁ ⇒ᵉ Δ₂)
  → e₁ <: e₂ ∈ Θ
  → renᵉ-ec ρ e₁ <: renᵉ-ec ρ e₂ ∈ renᵉ-subctx ρ Θ
renᵉ-<:∈ ρ Z = Z
renᵉ-<:∈ ρ (S x) = S renᵉ-<:∈ ρ x

⇑ᵉ-subctx : ∀ {Δ} → SubCtx Δ → SubCtx (Δ ,α)
⇑ᵉ-subctx Θ = renᵉ-subctx S_ Θ

subᵉ-subctx : ∀ {Δ₁ Δ₂} → (Δ₁ →ᵉ Δ₂) → SubCtx Δ₁ → SubCtx Δ₂
subᵉ-subctx σ ∅ = ∅
subᵉ-subctx σ (Θ , e₁ <: e₂) =
  subᵉ-subctx σ Θ , subᵉ-ec σ e₁ <: subᵉ-ec σ e₂


-- | EC subtyping: Γ ⊢ e <: e′
infix 6 _;_⊢ᵉ_<:_

data _;_⊢ᵉ_<:_ : (Δ : ECCtx) → SubCtx Δ → EC Δ → EC Δ → Set where

  <:-ε : ∀ {Δ Θ e}
      ---------------------
    → Δ ; Θ ⊢ᵉ ε <: e

  <:-refl : ∀ {Δ Θ e}
      ---------------------
    → Δ ; Θ ⊢ᵉ e <: e

  -- TODO (low priority) change the grammar of subintro to α <: β => M
  --      so that Θ ::= ∅ | Θ, α <: β
  <:-ax : ∀ {Δ Θ e α}
    →   e <: ` α ∈ Θ
      ------------------------
    → Δ ; Θ ⊢ᵉ e <: ` α

  <:-trans : ∀ {Δ Θ e₁ e₂ e₃}
    → Δ ; Θ ⊢ᵉ e₁ <: e₂
    → Δ ; Θ ⊢ᵉ e₂ <: e₃
      ------------------------
    → Δ ; Θ ⊢ᵉ e₁ <: e₃

-- | EC subtyping weakening
ec-<:-weaken : ∀ {Δ Θ e₁ e₂ e₃ e₄}
  → Δ ; Θ            ⊢ᵉ e₁ <: e₂
    ---------------------------------
  → Δ ; Θ , e₃ <: e₄ ⊢ᵉ e₁ <: e₂
ec-<:-weaken <:-ε = <:-ε
ec-<:-weaken <:-refl = <:-refl
ec-<:-weaken (<:-ax e₁<:e₂∈Θ) = <:-ax (S e₁<:e₂∈Θ)
ec-<:-weaken (<:-trans e₁<:e e<:e₂) =
  <:-trans (ec-<:-weaken e₁<:e) (ec-<:-weaken e<:e₂)

-- | Gradual EC subtyping: Γ ⊢ ê <: ê′
data _;_⊢ᵉ_<:⋆_ : (Δ : ECCtx) → SubCtx Δ → EC⋆ Δ → EC⋆ Δ → Set where

  <:-⋆ : ∀ {Δ Θ}
      ---------------------
    → Δ ; Θ ⊢ᵉ ⋆ <:⋆ ⋆

  <:-ec : ∀ {Δ Θ e e′}
    → Δ ; Θ ⊢ᵉ    e <: e′
      ------------------------
    → Δ ; Θ ⊢ᵉ ec e <:⋆ ec e′

<:⋆-trans : ∀ {Δ Θ} {ê₁ ê₂ ê₃}
  → Δ ; Θ ⊢ᵉ ê₁ <:⋆ ê₂
  → Δ ; Θ ⊢ᵉ ê₂ <:⋆ ê₃
    ---------------------------
  → Δ ; Θ ⊢ᵉ ê₁ <:⋆ ê₃
<:⋆-trans <:-⋆ <:-⋆ = <:-⋆
<:⋆-trans (<:-ec e₁<:e₂) (<:-ec e₂<:e₃) = <:-ec (<:-trans e₁<:e₂ e₂<:e₃)

_≡?ⱽ_ : ∀{Δ} → (e1 : ECVar Δ) → (e2 : ECVar Δ) → Dec (e1 ≡ e2)
Z ≡?ⱽ Z = yes refl
Z ≡?ⱽ (S e2) = no λ ()
(S e1) ≡?ⱽ Z = no λ ()
(S e1) ≡?ⱽ (S e2)
    with e1 ≡?ⱽ e2
... | yes refl = yes refl
... | no neq = no λ {refl → neq refl}

_≡?ᵉ_ : ∀{Δ} → (e1 : EC Δ) → (e2 : EC Δ) → Dec (e1 ≡ e2)
ε ≡?ᵉ ε = yes refl
ε ≡?ᵉ (` x) = no λ ()
(` x) ≡?ᵉ ε = no λ ()
(` x) ≡?ᵉ (` y)
    with x ≡?ⱽ y
... | yes refl = yes refl
... | no neq = no λ { refl → neq refl }

_≡?ᵉ⋆_ : ∀{Δ} → (e1 : EC⋆ Δ) → (e2 : EC⋆ Δ) → Dec (e1 ≡ e2)
⋆ ≡?ᵉ⋆ ⋆ = yes refl
⋆ ≡?ᵉ⋆ ec x = no λ ()
ec x ≡?ᵉ⋆ ⋆ = no λ ()
ec ε ≡?ᵉ⋆ ec ε = yes refl
ec ε ≡?ᵉ⋆ ec (` x) = no λ ()
ec (` x) ≡?ᵉ⋆ ec ε = no λ ()
ec (` x) ≡?ᵉ⋆ ec (` y)
    with x ≡?ⱽ y
... | yes refl = yes refl
... | no neq = no λ { refl → neq refl }
