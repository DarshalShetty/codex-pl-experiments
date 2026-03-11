{-# OPTIONS --rewriting #-}
module Hypercoercions where

  open import EnvClassifiers
  open import BlameLabels public
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Product using (Σ-syntax; ∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
  open import ECSubtypeDecidable using (ec-<:⋆?)

  -- | Coercions between ECs (cᵉ, dᵉ)
  module ECHypercoercions where

    infix 6 _;_⊢ᵉ_⇒_
    infix 6 _⊢ᵉʰ_⇒_
    infix 6 _;_⊢ᵉᵐ_⇒_
    infix 6 _⊢ᵉᵗ_⇒_
    infix 6 _⊢_⨟ʰᵗ_
    infix 6 _⨟ᵐ_
    infix 6 _⊢_⨟_＝_
    infixr 8 _⨾_⨾_

    data _⊢ᵉʰ_⇒_ : ∀ Δ → EC⋆ Δ → EC⋆ Δ → Set where
    
      _？_ : ∀ {Δ}
        → (e : EC Δ)
        → BlameLabel
          --------------------------- ec-hc-head-proj
        → Δ ⊢ᵉʰ ⋆ ⇒ ec e

      id : ∀ {Δ}
        → (e : EC⋆ Δ)
          --------------------------- ec-hc-head-id
        → Δ ⊢ᵉʰ e ⇒ e

    data _⊢ᵉᵗ_⇒_ : ∀ Δ → EC⋆ Δ → EC⋆ Δ → Set where

      _！ : ∀ {Δ}
        → (e : EC Δ)
          --------------------------- ec-hc-tail-inj
        → Δ ⊢ᵉᵗ ec e ⇒ ⋆

      id : ∀ {Δ}
        → (e : EC⋆ Δ)
          --------------------------- ec-hc-tail-id
        → Δ ⊢ᵉᵗ e ⇒ e

    data _;_⊢ᵉᵐ_⇒_ : ∀ Δ (Θ : SubCtx Δ) → EC⋆ Δ → EC⋆ Δ → Set  where

      ↑_ : ∀ {Δ Θ} {ê₁ ê₂ : EC⋆ Δ}
        → Δ ; Θ ⊢ᵉ ê₁ <:⋆ ê₂
          --------------------------- ec-hc-mid-sub
        → Δ ; Θ ⊢ᵉᵐ ê₁ ⇒ ê₂

      err : ∀ {Δ Θ}
        → (ê₁ : EC⋆ Δ)
        → (ê₂ : EC⋆ Δ)
        → BlameLabel
          --------------------------- ec-hc-mid-bot
        → Δ ; Θ ⊢ᵉᵐ ê₁ ⇒ ê₂

    data _;_⊢ᵉ_⇒_ : ∀ Δ (Θ : SubCtx Δ) → EC⋆ Δ → EC⋆ Δ → Set  where

      _⨾_⨾_ : ∀ {Δ Θ} {ê₁ ê₂ ê₃ ê₄ : EC⋆ Δ}
        → (head : Δ ⊢ᵉʰ ê₁ ⇒ ê₂)
        → (middle : Δ ; Θ ⊢ᵉᵐ ê₂ ⇒ ê₃)
        → (tail : Δ ⊢ᵉᵗ ê₃ ⇒ ê₄)
          --------------------------- ec-hc
        → Δ ; Θ ⊢ᵉ ê₁ ⇒ ê₄

    data IsErrEC {ℓ} {Δ Θ} {ê₁ ê₂ : EC⋆ Δ} : Δ ; Θ ⊢ᵉᵐ ê₁ ⇒ ê₂ → Set where
      error : IsErrEC (err ê₁ ê₂ ℓ)

    data ECHeadMiddleTail {Δ} (ê₁ ê₂ : EC⋆ Δ) : Set where
      head : Δ ⊢ᵉʰ ê₁ ⇒ ê₂ → ECHeadMiddleTail ê₁ ê₂
      middle : ∀ Θ → Δ ; Θ ⊢ᵉᵐ ê₁ ⇒ ê₂ → ECHeadMiddleTail ê₁ ê₂
      tail : Δ ⊢ᵉᵗ ê₁ ⇒ ê₂ → ECHeadMiddleTail ê₁ ê₂

    _⊢_⨟ʰᵗ_ : ∀ {Δ ê₁ ê₂ ê₃}
      → (Θ : SubCtx Δ)
      → Δ ⊢ᵉᵗ ê₁ ⇒ ê₂
      → Δ ⊢ᵉʰ ê₂ ⇒ ê₃
      → ECHeadMiddleTail ê₁ ê₃
    Θ ⊢ e₁ ！ ⨟ʰᵗ (e₂ ？ ℓ) with ec-<:⋆? Θ (ec e₁) (ec e₂)
    ... | yes e₁<:⋆e₂ = middle Θ (↑ e₁<:⋆e₂)
    ... | no  _       = middle Θ (err (ec e₁) (ec e₂) ℓ)
    Θ ⊢ e ！ ⨟ʰᵗ id ⋆ = tail (e ！)
    Θ ⊢ id ê₁ ⨟ʰᵗ h = head h

    _⨟ᵐ_ : ∀ {Δ Θ ê₁ ê₂ ê₃}
      → Δ ; Θ ⊢ᵉᵐ ê₁ ⇒ ê₂ → Δ ; Θ ⊢ᵉᵐ ê₂ ⇒ ê₃ → Δ ; Θ ⊢ᵉᵐ ê₁ ⇒ ê₃
    ↑ ê₁<:⋆ê₂ ⨟ᵐ ↑ ê₂<:⋆ê₃ = ↑ (<:⋆-trans ê₁<:⋆ê₂ ê₂<:⋆ê₃)
    ↑ {ê₁ = ê₁} ê₁<:⋆ê₂ ⨟ᵐ err ê₂ ê₃ ℓ = err ê₁ ê₃ ℓ
    err {ê₃ = ê₃} ê₁ ê₂ ℓ ⨟ᵐ m = err ê₁ ê₃ ℓ

    data _⊢_⨟_＝_ {Δ} Θ : ∀ {ê₁ ê₂ ê₃} 
      → Δ ; Θ ⊢ᵉ ê₁ ⇒ ê₂ → Δ ; Θ ⊢ᵉ ê₂ ⇒ ê₃ → Δ ; Θ ⊢ᵉ ê₁ ⇒ ê₃ → Set where

      err-left : ∀ {ℓ ê₁ ê₂ ê₃ ê₄ ê₅ ê₆ ê₇}
        → {h₁ : Δ ⊢ᵉʰ ê₁ ⇒ ê₂} {t₁ : Δ ⊢ᵉᵗ ê₃ ⇒ ê₄}
        → {h₂ : Δ ⊢ᵉʰ ê₄ ⇒ ê₅} {m₂ : Δ ; Θ ⊢ᵉᵐ ê₅ ⇒ ê₆} {t₂ : Δ ⊢ᵉᵗ ê₆ ⇒ ê₇}
        → Θ ⊢ h₁ ⨾ err ê₂ ê₃ ℓ ⨾ t₁ ⨟ h₂ ⨾ m₂ ⨾ t₂ ＝ h₁ ⨾ err ê₂ ê₆ ℓ ⨾ t₂
    
      err-right-head-tail : ∀ {ℓ ℓ′ ê₁ ê₂ ê₃ ê₄ ê₅ ê₆ ê₇}
        → {h₁ : Δ ⊢ᵉʰ ê₁ ⇒ ê₂} {m₁ : Δ ; Θ ⊢ᵉᵐ ê₂ ⇒ ê₃} {t₁ : Δ ⊢ᵉᵗ ê₃ ⇒ ê₄}
        → {h₂ : Δ ⊢ᵉʰ ê₄ ⇒ ê₅} {t₂ : Δ ⊢ᵉᵗ ê₆ ⇒ ê₇}
        → ¬ IsErrEC m₁
        → Θ ⊢ t₁ ⨟ʰᵗ h₂ ≡ middle Θ (err ê₃ ê₅ ℓ′)
        → Θ ⊢ h₁ ⨾ m₁ ⨾ t₁ ⨟ h₂ ⨾ err ê₅ ê₆ ℓ ⨾ t₂ ＝ h₁ ⨾ err ê₂ ê₆ ℓ′ ⨾ t₂
    
      err-right : ∀ {ℓ ℓ′ ê₁ ê₂ ê₃ ê₄ ê₅ ê₆ ê₇}
        → {h₁ : Δ ⊢ᵉʰ ê₁ ⇒ ê₂} {m₁ : Δ ; Θ ⊢ᵉᵐ ê₂ ⇒ ê₃} {t₁ : Δ ⊢ᵉᵗ ê₃ ⇒ ê₄}
        → {h₂ : Δ ⊢ᵉʰ ê₄ ⇒ ê₅} {t₂ : Δ ⊢ᵉᵗ ê₆ ⇒ ê₇}
        → ¬ IsErrEC m₁
        → ¬ (Θ ⊢ t₁ ⨟ʰᵗ h₂ ≡ middle Θ (err ê₃ ê₅ ℓ′))
        → Θ ⊢ h₁ ⨾ m₁ ⨾ t₁ ⨟ h₂ ⨾ err ê₅ ê₆ ℓ ⨾ t₂ ＝ h₁ ⨾ err ê₂ ê₆ ℓ ⨾ t₂
    
      head-tail-sub : ∀ {ê₁ ê₂ ê₃ ê₄ ê₅ ê₆ ê₇ m₃ m₄}
        → {h₁ : Δ ⊢ᵉʰ ê₁ ⇒ ê₂} {m₁ : Δ ; Θ ⊢ᵉᵐ ê₂ ⇒ ê₃} {t₁ : Δ ⊢ᵉᵗ ê₃ ⇒ ê₄}
        → {h₂ : Δ ⊢ᵉʰ ê₄ ⇒ ê₅} {m₂ : Δ ; Θ ⊢ᵉᵐ ê₅ ⇒ ê₆} {t₂ : Δ ⊢ᵉᵗ ê₆ ⇒ ê₇}
        → {ê₃<:⋆ê₅ : Δ ; Θ ⊢ᵉ ê₃ <:⋆ ê₅}
        → ¬ IsErrEC m₁ → ¬ IsErrEC m₂
        → Θ ⊢ t₁ ⨟ʰᵗ h₂ ≡ middle Θ (↑ ê₃<:⋆ê₅)
        → (↑ ê₃<:⋆ê₅ ⨟ᵐ m₂) ≡ m₃
        → (m₁ ⨟ᵐ m₃) ≡ m₄
        → Θ ⊢ h₁ ⨾ m₁ ⨾ t₁ ⨟ h₂ ⨾ m₂ ⨾ t₂ ＝ h₁ ⨾ m₄ ⨾ t₂

      head-tail-err : ∀ {ê₁ ê₂ ê₃ ê₄ ê₅ ê₆ ê₇ ℓ}
        → {h₁ : Δ ⊢ᵉʰ ê₁ ⇒ ê₂} {m₁ : Δ ; Θ ⊢ᵉᵐ ê₂ ⇒ ê₃} {t₁ : Δ ⊢ᵉᵗ ê₃ ⇒ ê₄}
        → {h₂ : Δ ⊢ᵉʰ ê₄ ⇒ ê₅} {m₂ : Δ ; Θ ⊢ᵉᵐ ê₅ ⇒ ê₆} {t₂ : Δ ⊢ᵉᵗ ê₆ ⇒ ê₇}
        → ¬ IsErrEC m₁ → ¬ IsErrEC m₂
        → Θ ⊢ t₁ ⨟ʰᵗ h₂ ≡ middle Θ (err ê₃ ê₅ ℓ)
        → Θ ⊢ h₁ ⨾ m₁ ⨾ t₁ ⨟ h₂ ⨾ m₂ ⨾ t₂ ＝ h₁ ⨾ (err ê₂ ê₆ ℓ) ⨾ t₂

      head-tail-id : ∀ {ê₁ ê₂ ê₃ ê₆ ê₇ m₃}
        → {h₁ : Δ ⊢ᵉʰ ê₁ ⇒ ê₂} {m₁ : Δ ; Θ ⊢ᵉᵐ ê₂ ⇒ ê₃} {t₁ : Δ ⊢ᵉᵗ ê₃ ⇒ ê₃}
        → {h₂ : Δ ⊢ᵉʰ ê₃ ⇒ ê₃} {m₂ : Δ ; Θ ⊢ᵉᵐ ê₃ ⇒ ê₆} {t₂ : Δ ⊢ᵉᵗ ê₆ ⇒ ê₇}
        → ¬ IsErrEC m₁ → ¬ IsErrEC m₂
        → Θ ⊢ t₁ ⨟ʰᵗ h₂ ≡ head (id ê₃)
        → (m₁ ⨟ᵐ m₂) ≡ m₃
        → Θ ⊢ h₁ ⨾ m₁ ⨾ t₁ ⨟ h₂ ⨾ m₂ ⨾ t₂ ＝ h₁ ⨾ m₃ ⨾ t₂

      -- head-tail-proj : ∀ {ê₁ ê₂ e₅ ê₆ ê₇ ℓ}
      --   → {h₁ : Δ ⊢ᵉʰ ê₁ ⇒ ê₂} {m₁ : Δ ; Θ ⊢ᵉᵐ ê₂ ⇒ ⋆} {t₁ : Δ ⊢ᵉᵗ ⋆ ⇒ ⋆}
      --   → {h₂ : Δ ⊢ᵉʰ ⋆ ⇒ ec e₅} {m₂ : Δ ; Θ ⊢ᵉᵐ ec e₅ ⇒ ê₆} {t₂ : Δ ⊢ᵉᵗ ê₆ ⇒ ê₇}
      --   → ¬ IsErrEC m₁ → ¬ IsErrEC m₂
      --   → Θ ⊢ t₁ ⨟ʰᵗ h₂ ≡ head (e₅ ？ ℓ)
      --   → Θ ⊢ h₁ ⨾ m₁ ⨾ t₁ ⨟ h₂ ⨾ m₂ ⨾ t₂ ＝ e₅ ？ ℓ ⨾ m₂ ⨾ t₂

  open ECHypercoercions public

  -- | Coercions between gradual code types (cᵒ, dᵒ)
  module ObjectHypercoercions where
    open import ObjectTypes

    infix 6 ⊢ᵒ_⇒_
    infix 6 ⊢ᵒʰ_⇒_
    infix 6 ⊢ᵒᵐ_⇒_
    infix 6 ⊢ᵒᵗ_⇒_
    infixr 8 _⨾_⨾_

    data ⊢ᵒʰ_⇒_ : OType⋆ → OType⋆ → Set where

      _？_ : ∀ Gᵒ
        → BlameLabel
        → OGround Gᵒ
          --------------------- code-hc-head-proj
        → ⊢ᵒʰ ⋆ ⇒ Gᵒ

      id : ∀ O → ⊢ᵒʰ O ⇒ O  -- code-hc-head-id

    data ⊢ᵒᵗ_⇒_ : OType⋆ → OType⋆ → Set where

      _！ : ∀ Gᵒ
        → OGround Gᵒ
          --------------------- code-hc-tail-inj
        → ⊢ᵒᵗ Gᵒ ⇒ ⋆

      id : ∀ O → ⊢ᵒᵗ O ⇒ O  -- code-hc-tail-id

    data ⊢ᵒᵐ_⇒_ : OType⋆ → OType⋆ → Set
    data ⊢ᵒ_⇒_ : OType⋆ → OType⋆ → Set

    data ⊢ᵒᵐ_⇒_ where

      _⇒_ : ∀ {O₁ O₂ O₃ O₄}
        → ⊢ᵒ O₃ ⇒ O₁
        → ⊢ᵒ O₂ ⇒ O₄
          --------------------------------- code-hc-mid-fun
        → ⊢ᵒᵐ (O₁ ⇒ O₂) ⇒ (O₃ ⇒ O₄)

      err : ∀ O₁ O₂
        → BlameLabel
          --------------- code-hc-mid-bot
        → ⊢ᵒᵐ O₁ ⇒ O₂

      id⋆ : ⊢ᵒᵐ ⋆ ⇒ ⋆  -- code-hc-mid-id⋆

      idι : ∀ ι → ⊢ᵒᵐ ` ι ⇒ ` ι  -- code-hc-mid-idι

    data ⊢ᵒ_⇒_ where

      _⨾_⨾_ : ∀ {O₁ O₂ O₃ O₄}
        → ⊢ᵒʰ O₁ ⇒ O₂
        → ⊢ᵒᵐ O₂ ⇒ O₃
        → ⊢ᵒᵗ O₃ ⇒ O₄
          --------------------- code-hc
        → ⊢ᵒ O₁ ⇒ O₄

  open ObjectHypercoercions public

  -- | Coercions between metalanguage types (c, d)
  module MetaCoercions where
    open import MetaTypes

    infix 6 _;_⊢ᵐ_⇒_
    infix 6 _⊢ᵐʰ_⇒_
    infix 6 _;_⊢ᵐᵐ_⇒_
    infix 6 _⊢ᵐᵗ_⇒_
    infixr 8 _⨾_⨾_

    data _⊢ᵐʰ_⇒_ : ∀ Δ → MType Δ → MType Δ → Set where

      _？_ : ∀ {Δ}
        → (G : MType Δ)
        → BlameLabel
        → Ground G
          ------------------------ meta-hc-head-proj
        → Δ ⊢ᵐʰ ⋆ ⇒ G

      id : ∀ {Δ}
        → (A : MType Δ)
          ------------------------ meta-hc-head-id
        → Δ ⊢ᵐʰ A ⇒ A

    data _⊢ᵐᵗ_⇒_ : ∀ Δ → MType Δ → MType Δ → Set where

      _！ : ∀ {Δ}
        → (G : MType Δ)
        → Ground G
          ------------------------ meta-hc-tail-inj
        → Δ ⊢ᵐᵗ G ⇒ ⋆

      id : ∀ {Δ}
        → (A : MType Δ)
          ------------------------ meta-hc-tail-id
        → Δ ⊢ᵐᵗ A ⇒ A

    data _;_⊢ᵐᵐ_⇒_ : ∀ Δ (Θ : SubCtx Δ) → MType Δ → MType Δ → Set
    data _;_⊢ᵐ_⇒_ : ∀ Δ (Θ : SubCtx Δ) → MType Δ → MType Δ → Set

    data _;_⊢ᵐᵐ_⇒_ where

      _⇒_ : ∀ {Δ Θ} {A B C D}
        → Δ ; Θ ⊢ᵐ C ⇒ A
        → Δ ; Θ ⊢ᵐ B ⇒ D
          --------------------------------- meta-hc-mid-fun
        → Δ ; Θ ⊢ᵐᵐ (A ⇒ B) ⇒ (C ⇒ D)

      ‶_″_ : ∀ {Δ Θ} {O₁ O₂ ê₁ ê₂}
        →       ⊢ᵒ O₁ ⇒ O₂
        → Δ ; Θ ⊢ᵉ ê₁ ⇒ ê₂
          --------------------------------------------- meta-hc-mid-code
        → Δ ; Θ ⊢ᵐᵐ (‶ O₁ ″ ê₁) ⇒ (‶ O₂ ″ ê₂)

      ref : ∀ {Δ Θ} {A B}
        → Δ ; Θ ⊢ᵐ B ⇒ A
        → Δ ; Θ ⊢ᵐ A ⇒ B
          ------------------------------ meta-hc-mid-ref
        → Δ ; Θ ⊢ᵐᵐ Ref A ⇒ Ref B

      ∀̇_ : ∀ {Δ Θ} {A B}
        → (Δ ,α) ; ⇑ᵉ-subctx Θ ⊢ᵐ A ⇒ B
          ------------------------------------------ meta-hc-mid-univ
        → Δ ; Θ ⊢ᵐᵐ ∀̇ A ⇒ ∀̇ B

      _<:_=>_ : ∀ {Δ Θ} {A B}
        → (e₁ e₂ : EC Δ)
        → Δ ; Θ , e₁ <: e₂ ⊢ᵐ A ⇒ B
          ------------------------------------------------ meta-hc-mid-sub
        → Δ ; Θ ⊢ᵐᵐ (e₁ <: e₂ => A) ⇒ (e₁ <: e₂ => B)

      id⋆ : ∀ {Δ Θ}
          ------------------------ meta-hc-mid-id⋆
        → Δ ; Θ ⊢ᵐᵐ ⋆ ⇒ ⋆

      idι : ∀ {Δ Θ} ι
          ------------------------ meta-hc-mid-idι
        → Δ ; Θ ⊢ᵐᵐ ` ι ⇒ ` ι

      err : ∀ {Δ Θ}
        → (A : MType Δ)
        → (B : MType Δ)
        → BlameLabel
          ------------------------ meta-hc-mid-bot
        → Δ ; Θ ⊢ᵐᵐ A ⇒ B

    data _;_⊢ᵐ_⇒_ where

      _⨾_⨾_ : ∀ {Δ Θ} {A B B′ C}
        → Δ ⊢ᵐʰ A ⇒ B
        → Δ ; Θ ⊢ᵐ B ⇒ B′
        → Δ ⊢ᵐᵗ B′ ⇒ C
          ------------------------ meta-hc
        → Δ ; Θ ⊢ᵐ A ⇒ C

    -- data IsProj : ∀ {Δ Θ} {A B} → (c : Δ ; Θ ⊢ᵐ A ⇒ B) → Set where
    --   proj : ∀{Δ}{Θ}{H : MType Δ}{h : Ground H}{ℓ} → IsProj{Δ}{Θ} ((H ？ ℓ) h)

    -- data IsErr : ∀ {Δ Θ} {A B} → (c : Δ ; Θ ⊢ᵐ A ⇒ B) → Set where
    --   error : ∀{Δ}{Θ}{A B : MType Δ}{ℓ} → IsErr{Δ}{Θ} (err A B ℓ)

    -- not-star-proj : ∀ {Δ Θ} {A B}
    --   → (c : Δ ; Θ ⊢ᵐ A ⇒ B)
    --   → A ≢ ⋆
    --   → ¬ IsProj c
    -- not-star-proj {Δ} {Θ} {A} {B} (id .A) A⋆ = λ ()
    -- not-star-proj {Δ} {Θ} {A} {B} ((.A ！) x) A⋆ = λ ()
    -- not-star-proj {Δ} {Θ} {A} {B} ((.B ？ x) x₁) A⋆ = ⊥-elim (A⋆ refl)
    -- not-star-proj {Δ} {Θ} {A} {B} (c ⨾ d) A⋆ = λ ()
    -- not-star-proj {Δ} {Θ} {A} {B} (c ⇒ d) A⋆ = λ ()
    -- not-star-proj {Δ} {Θ} {A} {B} (‶ co ″ ce) A⋆ = λ ()
    -- not-star-proj {Δ} {Θ} {A} {B} (ref c d) A⋆ = λ ()
    -- not-star-proj {Δ} {Θ} {A} {B} (∀̇ c) A⋆ = λ ()
    -- not-star-proj {Δ} {Θ} {A} {B} (e₁ <: e₂ => c) A⋆ = λ ()
    -- not-star-proj {Δ} {Θ} {A} {B} (err .A .B ℓ) A⋆ = λ ()

    -- is-err : ∀ {Δ Θ} {A B} → (c : Δ ; Θ ⊢ᵐ A ⇒ B) → Dec (IsErr c)
    -- is-err (id _) = no (λ ())
    -- is-err ((_ ！) x) = no (λ ())
    -- is-err ((_ ？ x) x₁) = no (λ ())
    -- is-err (c ⨾ c₁) = no (λ ())
    -- is-err (c ⇒ c₁) = no (λ ())
    -- is-err (‶ x ″ x₁) = no (λ ())
    -- is-err (ref c c₁) = no (λ ())
    -- is-err (∀̇ c) = no (λ ())
    -- is-err (e₁ <: e₂ => c) = no (λ ())
    -- is-err (err _ _ x) = yes error

    -- Θ-swap-c : ∀ {Δ Θ A B e₁ e₂ e₃ e₄}
    --   → Δ ; Θ , e₃ <: e₄ , e₁ <: e₂ ⊢ᵐ A ⇒ B
    --   → Δ ; Θ , e₁ <: e₂ , e₃ <: e₄ ⊢ᵐ A ⇒ B
    -- Θ-swap-c (id A) = id A
    -- Θ-swap-c ((G ！) g) = (G ！) g
    -- Θ-swap-c ((G ？ ℓ) g) = (G ？ ℓ) g
    -- Θ-swap-c (c ⨾ d) = (Θ-swap-c c) ⨾ (Θ-swap-c d)
    -- Θ-swap-c (c ⇒ d) = (Θ-swap-c c) ⇒ (Θ-swap-c d)
    -- Θ-swap-c (‶ x ″ x₁) = {!!}
    -- Θ-swap-c (ref c c₁) = {!!}
    -- Θ-swap-c (∀̇ c) = {!!}
    -- Θ-swap-c {e₁ = e₁} {e₂} {e₃ } (e₁ <: e₂ => c) = {!!}
    -- Θ-swap-c (err _ _ x) = {!!}

    -- Θ-weaken-c : ∀ {Δ Θ A B e₁ e₂}
    --   → Δ ; Θ ⊢ᵐ A ⇒ B
    --   → Δ ; Θ , e₁ <: e₂ ⊢ᵐ A ⇒ B
    -- Θ-weaken-c (id _) = {!!}
    -- Θ-weaken-c ((_ ！) x) = {!!}
    -- Θ-weaken-c ((_ ？ x) x₁) = {!!}
    -- Θ-weaken-c (c ⨾ c₁) = {!!}
    -- Θ-weaken-c (c ⇒ c₁) = {!!}
    -- Θ-weaken-c (‶ x ″ x₁) = {!!}
    -- Θ-weaken-c (ref c c₁) = {!!}
    -- Θ-weaken-c (∀̇ c) = {!!}
    -- Θ-weaken-c (e₁ <: e₂ => c) = e₁ <: e₂ => {!!}
    -- Θ-weaken-c (err A B ℓ) = err A B ℓ

  open MetaCoercions public
