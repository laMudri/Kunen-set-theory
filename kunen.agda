{-# OPTIONS --prop --rewriting #-}

module kunen where
open import Agda.Builtin.Equality
open import Agda.Primitive
open import not-mine.logic
open import not-mine.ZF
open import not-mine.funrel
open _∧_

-- Because we are trying to work in FOL, I add the classical property of existential import.
postulate
    existential-import :
        (A : Set) → (P : A → Prop) → ((x : A) → P x) → ∃[ x ∈ A ] P x

-- "Axiom" 0. Set Existence.
-- As you can see above, this actually follows from FOL directly.
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
    -- Well, until I figure out how to actually limit postulates, let's pretend that the private block does.
    
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

    -- Bonus: this derivation does not use LEM, as (P ↔ ¬P) → ⊥ is derivable intuitionistically.
    intuitive : {P : Prop} → (P → ¬ P) ∧ (¬ P → P) → ⊥
    intuitive {P} [ zig , zag ] = (λ x → zig x x) (zag (λ x → zig x x))
    
    russell-paradox : ⊥
    russell-paradox = intuitive [ zig , zag ]
        where
            zig : russell-set ∈ russell-set → ¬ russell-set ∈ russell-set
            zig yes = yes
            zag : ¬ russell-set ∈ russell-set → russell-set ∈ russell-set
            zag no = no

-- Theorem I.6.6
-- There is no set which contains all sets.
russell : ∀ z → 𝕍
russell z = ⟦ x ∈ z ∥ ¬ x ∈ x ⟧ 

no-𝕍-set : ∀ x → ∃[ y ∈ 𝕍 ] ¬ y ∈ x
no-𝕍-set x = exists (russell x) λ y∈x → intuitive [ zig y∈x , zag y∈x ]
    where
        zig : russell x ∈ x → russell x ∈ russell x → ¬ russell x ∈ russell x
        zig _ [ y∈x , rx∉rx ] = rx∉rx 
        zag : russell x ∈ x → ¬ russell x ∈ russell x → russell x ∈ russell x
        zag y∈x rx∉rx = [ y∈x , rx∉rx ]

-- We skip some stuff about unions and ordered/unordered pairs, because that has been done already.

-- Relations

-- Special ∈-properties to define ordinals.
∈-transitive : 𝕍 → Prop
∈-transitive A = (x y z : 𝕍) → x ∈ A → y ∈ A → z ∈ A →
    x ∈ y → y ∈ z → x ∈ z

-- I leave ∈-irreflexivity out, since Foundation guarantees it for all sets.
-- ∈-irreflexive : 𝕍 → Prop
-- ∈-irreflexive A = (x : 𝕍) → x ∈ A → ¬ x ∈ x

∈-trichotomy : 𝕍 → Prop
∈-trichotomy A = (x y : 𝕍) → x ∈ A → y ∈ A →
    x ∈ y ∨ y ∈ x ∨ x ≗ y
    
∈-total : 𝕍 → Prop
∈-total A = ∈-transitive A ∧ ∈-trichotomy A -- ∧ ∈-irreflexive A

-- I leave ∈-well-foundedness out of the definition as well, as Foundation guarantees it.
∈-well-ordered : 𝕍 → Prop
∈-well-ordered A = ∈-total A

transitive-set : 𝕍 → Prop
transitive-set z = ∀ y → y ∈ z → y ⊆ z

ordinal : 𝕍 → Prop
ordinal z = transitive-set z ∧ ∈-well-ordered z

-- Exercise I.7.21 (for ∈)
well-order-⊆-transport : ∀ {A X} → ∈-well-ordered A → X ⊆ A → ∈-well-ordered X
well-order-⊆-transport {A} {X} wo-A X⊆A = [ trans-X , trichotomy-X ]
    where
        trans-X : ∈-transitive X
        trans-X x y z x∈X y∈X z∈X x∈y y∈z =
            (π₁ wo-A) x y z (X⊆A x∈X) (X⊆A y∈X) (X⊆A z∈X) x∈y y∈z
        trichotomy-X : ∈-trichotomy X
        trichotomy-X x y x∈X y∈X =
            (π₂ wo-A) x y (X⊆A x∈X) (X⊆A y∈X)
        
-- Theorem I.8.5
-- The well-ordering of ON.

-- Lemma I.8.6
ON-transitive-class : ∀ α z → ordinal α → z ∈ α → ordinal z
ON-transitive-class α z ord-α z∈α =
    [ trans-set-z ,
    well-order-⊆-transport {α} {z} (π₂ ord-α) ((π₁ ord-α) z z∈α) ]
    where
        z⊆α : z ⊆ α
        z⊆α = (π₁ ord-α) z z∈α
        trans-set-z : transitive-set z
        trans-set-z y y∈z x∈y =
            (π₁ (π₂ ord-α)) _ y z (y⊆α x∈y) (z⊆α y∈z) z∈α x∈y y∈z
                where
                    y⊆α : y ⊆ α
                    y⊆α = (π₁ ord-α) y (z⊆α y∈z)
