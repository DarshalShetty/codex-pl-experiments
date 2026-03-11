{-# OPTIONS --rewriting #-}

module ObjectTypes where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Relation.Nullary using (¬_; ¬?; Dec; yes; no)

open import EnvClassifiers  -- markers in OCtx
open import BaseTypes using (Base; base-eq?)

infixr 6 _⇒_

-- | Object language types (S, T)
data OType : Set where

  `_   : Base → OType

  _⇒_ : OType → OType → OType

-- | Gradual object language types (O)
data OType⋆ : Set where

  ⋆ : OType⋆

  `_   : Base → OType⋆

  _⇒_ : OType⋆ → OType⋆ → OType⋆

{- (predicates on gradual obj types) -}

data OGround : OType⋆ → Set where

  gbase : ∀ {ι} → OGround (` ι)

  gfun : OGround (⋆ ⇒ ⋆)

-- | Equivalent OType (T) and OType⋆ (O) types
infix 4 _≡ᵒ_

data _≡ᵒ_ : OType⋆ → OType → Set where

  `_ : ∀ ι → ` ι ≡ᵒ ` ι

  _⇒_ : ∀ {O₁ O₂ T₁ T₂}
    →       O₁ ≡ᵒ T₁
    →       O₂ ≡ᵒ T₂
    → O₁ ⇒ O₂ ≡ᵒ T₁ ⇒ T₂


-- | Object language typing contexts (Γᵒ)
infixl 5 _,_＠_

data OCtx : ECCtx → Set where

  ∅ : ∀ {Δ} → OCtx Δ

  _,_＠_ : ∀ {Δ} → OCtx Δ → OType → ECVar Δ → OCtx Δ

infix  4 _∋ᵒ_＠_

data _∋ᵒ_＠_ : ∀ {Δ} → OCtx Δ → OType → ECVar Δ → Set where

  Z : ∀ {Δ} {Γᵒ : OCtx Δ} {T α}
     → (Γᵒ , T ＠ α) ∋ᵒ T ＠ α

  S_ : ∀ {Δ} {Γᵒ : OCtx Δ} {S T α β}
     → Γᵒ ∋ᵒ T ＠ α
     → (Γᵒ , S ＠ β) ∋ᵒ T ＠ α

infix 0 _⊢_⦅_⦆≡_

data _⊢_⦅_⦆≡_ : ∀ {T} Δ → (Γᵒ : OCtx Δ) → (α : ECVar Δ) → Γᵒ ∋ᵒ T ＠ α → Set where

  here : ∀ {Δ Γᵒ T α}
      ---------------------------------
    → Δ ⊢ (Γᵒ , T ＠ α) ⦅ α ⦆≡ Z

  there : ∀ {Δ Γᵒ T₁ T₂ α β} {x : Γᵒ ∋ᵒ T₁ ＠ α}
    → Δ ⊢ Γᵒ ⦅ α ⦆≡ x
    → α ≢ β
      ---------------------------------
    → Δ ⊢ (Γᵒ , T₂ ＠ β) ⦅ α ⦆≡ S x

renᵉ-octx : ∀ {Δ₁ Δ₂} → Δ₁ ⇒ᵉ Δ₂ → OCtx Δ₁ → OCtx Δ₂
renᵉ-octx ρ ∅ = ∅
renᵉ-octx ρ (Γᵒ , T ＠ α) = renᵉ-octx ρ Γᵒ , T ＠ ρ α

renᵉ-octx-id : ∀ {Δ} {Γᵒ : OCtx Δ} → renᵉ-octx idᵉ Γᵒ ≡ Γᵒ
renᵉ-octx-id {Δ} {∅} = refl
renᵉ-octx-id {Δ} {Γᵒ , T ＠ α} rewrite renᵉ-octx-id {Δ} {Γᵒ} = refl
{-# REWRITE renᵉ-octx-id #-}

⇑ᵉ-octx : ∀ {Δ} → OCtx Δ → OCtx (Δ ,α)
⇑ᵉ-octx Γᵒ = renᵉ-octx S_ Γᵒ

renᵉ-∋ᵒ : ∀ {Δ₁ Δ₂} {Γᵒ T α}
  → Γᵒ ∋ᵒ T ＠ α
  → (ρ : Δ₁ ⇒ᵉ Δ₂)
    ---------------------------------------
  → renᵉ-octx ρ Γᵒ ∋ᵒ T ＠ ρ α
renᵉ-∋ᵒ Z _ = Z
renᵉ-∋ᵒ (S x) ρ = S renᵉ-∋ᵒ x ρ

_≡?ᵒ_ : ∀(A B : OType⋆) → Dec (A ≡ B)
⋆ ≡?ᵒ ⋆ = yes refl
⋆ ≡?ᵒ (` x) = no λ ()
⋆ ≡?ᵒ (B ⇒ B₁) = no λ ()
(` x) ≡?ᵒ ⋆ = no λ ()
(` x) ≡?ᵒ (` y)
    with base-eq? x y
... | yes refl = yes refl
... | no neq = no λ {refl → neq refl}
(` x) ≡?ᵒ (B ⇒ B₁) = no λ ()
(A ⇒ A₁) ≡?ᵒ ⋆ = no λ ()
(A ⇒ A₁) ≡?ᵒ (` x) = no λ ()
(A ⇒ B) ≡?ᵒ (C ⇒ D)
    with A ≡?ᵒ C | B ≡?ᵒ D
... | yes refl | yes refl = yes refl
... | no neq | _ = no λ {refl → neq refl}
... | yes refl | no neq = no λ {refl → neq refl}
