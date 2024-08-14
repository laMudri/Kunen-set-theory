{-# OPTIONS --prop --rewriting #-}

module naive-comprehension where
open import Agda.Builtin.Equality
open import Agda.Primitive
open import Trebor-Huang.Trebor-Huang-logic
open import Trebor-Huang.Trebor-Huang-ZF
open import Trebor-Huang.Trebor-Huang-funrel
open import logic
open _∧_

-- This is its own file in order to isolate the inconsistency.

-- Garbage I.6.4
-- Navie Comprehension Axiom.
postulate
    Naive-Comprehension : (P : 𝕍 → Prop) → 𝕍
    Naive-Membership : ∀ z P → z ∈ Naive-Comprehension P ≡ P z

{-# REWRITE Naive-Membership #-}
syntax Naive-Comprehension (λ x → P) = ⟦ x ∥ P ⟧
    
-- Paradox I.6.5
russell-set : 𝕍
russell-set = ⟦ x ∥ ¬ x ∈ x ⟧

russell-paradox : ⊥
russell-paradox = [P→¬P]∧[¬P→P]→⊥ [ zig , zag ]
    where
        zig : russell-set ∈ russell-set → ¬ russell-set ∈ russell-set
        zig yes = yes
        zag : ¬ russell-set ∈ russell-set → russell-set ∈ russell-set
        zag no = no