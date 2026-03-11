{-# OPTIONS --rewriting #-}

module ECSubtypeDecidable where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)
open import Relation.Nullary using (¬_; ¬?; Dec; yes; no)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; _◅_; _◅◅_) renaming (ε to star-ε)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.Tree.AVL.Map <-strictTotalOrder using (singleton; insert; empty; Map; lookup)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.List using (List; _++_; length; reverse; map; foldr; downFrom; []; _∷_)
open import EnvClassifiers 

ec-<:∈? : ∀ {Δ} (Θ : SubCtx Δ) e₁ e₂ →  Dec (e₁ <: e₂ ∈ Θ)
ec-<:∈? ∅ e₁ e₂ = no (λ { ()})
ec-<:∈? (Θ , e <: e′) e₁ e₂ with ec-<:∈? Θ e₁ e₂
... | yes e₁<:e₂∈Θ = yes (S e₁<:e₂∈Θ)
... | no e₁<:e₂∉Θ with e₁ ≡?ᵉ e
...   | no e₁≠e₁ = no (λ { Z → e₁≠e₁ refl
                         ; (S e₁<:e₂∈Θ) → e₁<:e₂∉Θ e₁<:e₂∈Θ})
...   | yes e₁≡e with e₂ ≡?ᵉ e′
...     | no e₂≠e₂ = no (λ { Z → e₂≠e₂ refl
                           ; (S e₁<:e₂∈Θ) → e₁<:e₂∉Θ e₁<:e₂∈Θ})
...     | yes e₂=e′ rewrite e₁≡e | e₂=e′ = yes Z

α≮:ε : ∀ {Δ Θ α} → ¬ (Δ ; Θ ⊢ᵉ ` α <: ε)
α≮:ε (<:-trans {e₂ = ε} α<:ε ε<:ε) = α≮:ε α<:ε
α≮:ε (<:-trans {e₂ = ` β} α<:β β<:ε) = α≮:ε β<:ε

find-<:-neighbours : ∀ {Δ} (Θ : SubCtx Δ) α → List (∃[ β ] (` α <: ` β ∈ Θ))
find-<:-neighbours ∅ α = []
find-<:-neighbours (Θ , e₁ <: e₂) α with find-<:-neighbours Θ α
... | IH with e₁ ≡?ᵉ (` α)
...   | no e₁≢α = map (λ { ⟨ β , α<:β ⟩ → ⟨ β , (S α<:β) ⟩}) IH
find-<:-neighbours (Θ , e₁ <: ε) α | IH | yes e₁≡α rewrite e₁≡α
  = map (λ { ⟨ β , α<:β ⟩ → ⟨ β , (S α<:β) ⟩}) IH
find-<:-neighbours (Θ , e₁ <: (` α′)) α | IH | yes e₁≡α rewrite e₁≡α
  = ⟨ α′ , Z ⟩ ∷ map (λ { ⟨ β , α<:β ⟩ → ⟨ β , (S α<:β) ⟩ }) IH

Δ-to-list : ∀ (Δ : ECCtx) → List (ECVar Δ)
Δ-to-list ∅ = []
Δ-to-list (Δ ,α) = Z ∷ map S_ (Δ-to-list Δ)

ECVar-to-ℕ : ∀ {Δ} → ECVar Δ → ℕ
ECVar-to-ℕ Z = zero
ECVar-to-ℕ (S α) = suc (ECVar-to-ℕ α)

Edge : ∀ {Δ} (Θ : SubCtx Δ) → ECVar Δ → ECVar Δ → Set
Edge Θ α β = ` α <: ` β ∈ Θ

path->sub : ∀ {Δ Θ α β} → Star (Edge {Δ} Θ) α β → Δ ; Θ ⊢ᵉ ` α <: ` β
path->sub star-ε = <:-refl
path->sub (α<:β∈Θ ◅ β↠γ) = <:-trans (<:-ax α<:β∈Θ) (path->sub β↠γ)

Reachable : ∀ {Δ : ECCtx} (Θ : SubCtx Δ) (α β : ECVar Δ) → Set
Reachable {Δ} Θ α β = Star (Edge {Δ} Θ) α β

-- TODO: Formalize the notion of Reachable in k steps

sub->path : ∀ {Δ Θ α β} → Δ ; Θ ⊢ᵉ ` α <: ` β → Reachable Θ α β
sub->path <:-refl = star-ε
sub->path (<:-ax α<:β∈Θ) = α<:β∈Θ ◅ star-ε
sub->path (<:-trans {e₂ = ε} α<:ε ε<:β) = ⊥-elim (α≮:ε α<:ε)
sub->path (<:-trans {e₂ = ` γ} α<:γ γ<:β) = sub->path α<:γ ◅◅ sub->path γ<:β

-- edge-path? : ∀ {Δ} (Θ : SubCtx Δ) α β → Dec (Reachable Θ α β) 
-- edge-path? Θ α β = {!!}

-- TODO: Write a BFS algo in Agda with simple non-dependent types

-- The invariant for completeness should state that every node that is Reachable
-- in k hops is in the reachable map
-- find-trans-<:-path : ∀ {Δ} Θ α β
--   → (unvisited : List (ECVar Δ)) → (frontier : List (∀ {α′ β′} → ` α′ <: ` β′ ∈ Θ))
--   → (reachable : Map (∃[ β′ ] (Δ ; Θ ⊢ᵉ ` α <: ` β′)))
--   → Dec (Δ ; Θ ⊢ᵉ ` α <: ` β) 
-- find-trans-<:-path Θ α β unvis frontier R with edge-path? Θ α β
-- ... | yes α↠β = yes (path->sub α↠β)
-- ... | no α↛β = no (λ α<:β → α↛β (sub->path α<:β))

-- ec-var-<:? : ∀ {Δ} Θ α β → Dec (Δ ; Θ ⊢ᵉ ` α <: ` β)
-- ec-var-<:? {Δ} Θ α β = find-trans-<:-path Θ α β (Δ-to-list Δ) [] (singleton (ECVar-to-ℕ α) ⟨ α , <:-refl ⟩)

-- ec-<:? : ∀ {Δ} Θ e₁ e₂ → Dec (Δ ; Θ ⊢ᵉ e₁ <: e₂)
-- ec-<:? Θ ε e₂ = yes <:-ε
-- ec-<:? Θ (` α) ε = no (λ α<:ε → α≮:ε α<:ε)
-- ec-<:? Θ (` α) (` β) = ec-var-<:? Θ α β

postulate
  ec-<:⋆? : ∀ {Δ} Θ ê₁ ê₂ → Dec (Δ ; Θ ⊢ᵉ ê₁ <:⋆ ê₂)
-- ec-<:⋆? Θ ⋆ ⋆ = yes <:-⋆
-- ec-<:⋆? Θ ⋆ (ec e₂) = no (λ { ()})
-- ec-<:⋆? Θ (ec e₁) ⋆ = no (λ { ()})
-- ec-<:⋆? Θ (ec e₁) (ec e₂) with ec-<:? Θ e₁ e₂
-- ... | no e₁≮:e₂ = no λ { (<:-ec e₁<:e₂) → e₁≮:e₂ e₁<:e₂}
-- ... | yes e₁<:e₂ = yes (<:-ec e₁<:e₂)
