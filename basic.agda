{-# OPTIONS --prop --rewriting #-}

module basic where
open import Agda.Builtin.Equality
open import Agda.Primitive
open import Trebor-Huang.Trebor-Huang-logic
open import Trebor-Huang.Trebor-Huang-ZF
open import Trebor-Huang.Trebor-Huang-funrel
open import logic
open _∧_

¬≗-¬≡ : ∀ {x y} → ¬ x ≗ y → (x ≡ y → ⊥)
¬≗-¬≡ ¬x≗y x≡y = ¬x≗y (≡-≗ x≡y)

≗-trans : ∀ {a b c} → a ≗ b → b ≗ c → a ≗ c
≗-trans refl𝕍 refl𝕍 = refl𝕍

≗-transport : ∀ {a b} (f : 𝕍 → Prop) → a ≗ b → f a → f b
≗-transport f refl𝕍 fa = fa

∃-to-¬∅ : ∀ {A} → ∃[ y ∈ 𝕍 ] y ∈ A → ¬ A ≗ ∅
∃-to-¬∅ (exists absurd absurd∈∅) refl𝕍 = absurd∈∅

-- "Axiom" 0. Set Existence.
-- As you can see above, this actually follows from FOL directly.
set-existence : ∃[ x ∈ 𝕍 ] (x ≗ x)
set-existence = existential-import 𝕍 (λ x → x ≗ x) (λ x → refl𝕍)

-- Definition I.6.1
emp : 𝕍 → Prop
emp x = ∀ y → ¬ y ∈ x

-- Theorem I.6.2
empty-unique : ∀ x y → emp x ∧ emp y → x ≗ y
empty-unique x y [ emp-x , emp-y ] =
    ≡-≗ (Extensional λ z → equiv-equal
        [ (λ z∈x → ex-falso (emp-x z z∈x)) ,
          (λ z∈y → ex-falso (emp-y z z∈y)) ])

-- Theorem I.6.6
-- There is no set which contains all sets.
russell : 𝕍 → 𝕍
russell z = ⟦ x ∈ z ∥ ¬ x ∈ x ⟧

no-𝕍-set : ∀ x → ∃[ y ∈ 𝕍 ] ¬ y ∈ x
no-𝕍-set x = exists (russell x) λ y∈x → [P→¬P]∧[¬P→P]→⊥ [ zig y∈x , zag y∈x ]
    where
        zig : russell x ∈ x → russell x ∈ russell x → ¬ russell x ∈ russell x
        zig _ [ y∈x , rx∉rx ] = rx∉rx 
        zag : russell x ∈ x → ¬ russell x ∈ russell x → russell x ∈ russell x
        zag y∈x rx∉rx = [ y∈x , rx∉rx ]

A∩B⊆A : ∀ {A B} → (A ∩ B) ⊆ A
A∩B⊆A = π₁  -- [ z∈A , z∈B ] = z∈A

A∩B⊆B : ∀ {A B} → (A ∩ B) ⊆ B
A∩B⊆B = π₂  -- [ z∈A , z∈B ] = z∈B

⊆-transitive : ∀ {A B C} → A ⊆ B → B ⊆ C → A ⊆ C
⊆-transitive A⊆B B⊆C z∈A = B⊆C (A⊆B z∈A)

_∖_ : 𝕍 → 𝕍 → 𝕍
_∖_ A B = ⟦ x ∈ A ∥ ¬ x ∈ B ⟧

∅-implies-empty : ∀ {A} → A ≗ ∅ → ∀ z → ¬ z ∈ A
∅-implies-empty refl𝕍 z = equal-equiv (∅-empty {z})

⊆-antisymmetry : ∀ {A B} → A ⊆ B → B ⊆ A → A ≗ B
⊆-antisymmetry A⊆B B⊆A = ≡-≗ (Extensional (λ z → equiv-equal [ A⊆B , B⊆A ]))

-- Some lemmas about setminus.
∖-not-∅ : ∀ {A B} → ¬ A ≗ B → A ⊆ B → ¬ (B ∖ A) ≗ ∅
∖-not-∅ {A} {B} ¬A≗B A⊆B eq = ¬A≗B (⊆-antisymmetry A⊆B B⊆A)
    where
        B⊆A : B ⊆ A
        B⊆A {z} z∈B = (¬[P∧¬Q]→[P→Q] (∅-implies-empty eq z)) z∈B
        
∖-⊆ : ∀ {A B} → (A ∖ B) ⊆ A
∖-⊆ [ x∈A , x∉B ] = x∈A