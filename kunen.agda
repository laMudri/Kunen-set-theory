{-# OPTIONS --prop --rewriting #-}

module kunen where
open import Agda.Builtin.Equality
open import Agda.Primitive
open import not-mine.logic
open import not-mine.ZF
open import not-mine.funrel

-- I am not sure whether existential import is derivable
-- from logic.agda, so I postulate it.
postulate
    existential-import :
        (A : Set) → (P : A → Prop) → ((x : A) → P x) → ∃[ x ∈ A ] P x

-- Axiom 0. Set Existence.
set-existence : ∃[ x ∈ 𝕍 ] (x ≗ x)
set-existence = existential-import 𝕍 (λ x → x ≗ x) (λ x → refl𝕍)

-- Definition I.6.1
emp : ∀ x → Prop
emp x = ∀ y → ¬ y ∈ x

-- Theorem I.6.2
empty-unique : ∀ x y → emp x ∧ emp y → x ≗ y
empty-unique x y [ emp-x , emp-y ] =
    ≡-≗ (Extensional λ z → equiv-equal
        [ (λ z∈x → ex-falso (emp-x z z∈x)) ,
          (λ z∈y → ex-falso (emp-y z z∈y)) ])

private
    -- A private block, because the following axiom is inconsistent.
    
    -- Garbage I.6.4
    -- Navie Comprehension Axiom.
    postulate
        Naive-Comprehension : (P : 𝕍 → Prop) → 𝕍
        Naive-Membership : ∀ z P → z ∈ Naive-Comprehension P ≡ P z

    {-# REWRITE Naive-Membership #-}
    syntax Naive-Comprehension (λ x -> P) = ⟦ x ∥ P ⟧
    
    -- Paradox I.6.5
    russell-set : 𝕍
    russell-set = ⟦ x ∥ ¬ x ∈ x ⟧
    
    zig : russell-set ∈ russell-set → ¬ russell-set ∈ russell-set
    zig yes = yes
    
    zag : ¬ russell-set ∈ russell-set → russell-set ∈ russell-set
    zag no = no

    -- Bonus: this derivation does not use LEM, as (P ↔ ¬P) → ⊥ is valid intuitionistically.
    intuitive : {P : Prop} → (P → ¬ P) ∧ (¬ P → P) → ⊥
    intuitive {P} [ zig , zag ] = (λ x → zig x x) (zag (λ x → zig x x))
    
    russell-paradox : ⊥
    russell-paradox = intuitive [ zig , zag ]
    