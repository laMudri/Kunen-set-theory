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
emp : 𝕍 → Prop
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
    intuitive [ zig , zag ] = (λ x → zig x x) (zag (λ x → zig x x))
    
    russell-paradox : ⊥
    russell-paradox = intuitive [ zig , zag ]
        where
            zig : russell-set ∈ russell-set → ¬ russell-set ∈ russell-set
            zig yes = yes
            zag : ¬ russell-set ∈ russell-set → russell-set ∈ russell-set
            zag no = no

-- Theorem I.6.6
-- There is no set which contains all sets.
russell : 𝕍 → 𝕍
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
-- It gets special treatment, because this is not a set relation,
-- it is a relation on the proper class 𝕍
∈-transitive : 𝕍 → Prop
∈-transitive A = ∀ {x y z} → x ∈ A → y ∈ A → z ∈ A →
    x ∈ y → y ∈ z → x ∈ z

∈-irreflexive : 𝕍 → Prop
∈-irreflexive A = ∀ {x} → x ∈ A → ¬ x ∈ x

∈-trichotomy : 𝕍 → Prop
∈-trichotomy A = ∀ {x y} → x ∈ A → y ∈ A →
    x ∈ y ∨ y ∈ x ∨ x ≗ y
    
∈-total : 𝕍 → Prop
∈-total A = ∈-transitive A ∧ ∈-irreflexive A ∧ ∈-trichotomy A

∈-well-founded : 𝕍 → Prop
∈-well-founded A = ∀ X → ¬ X ≗ ∅ → X ⊆ A → ∃[ y ∈ 𝕍 ] (y ∈ X ∧ ∀ z → z ∈ X → ¬ z ∈ y)

∈-well-ordered : 𝕍 → Prop
∈-well-ordered A = ∈-total A ∧ ∈-well-founded A

transitive-set : 𝕍 → Prop
transitive-set z = ∀ y → y ∈ z → y ⊆ z

ordinal : 𝕍 → Prop
ordinal z = transitive-set z ∧ ∈-well-ordered z


-- Constructors for properties of ordinals
ordinal-is-transitive : ∀ {α} → ordinal α → ∈-transitive α
ordinal-is-transitive ord-α = π₁ (π₁ (π₁ (π₂ ord-α)))

ordinal-is-irreflexive : ∀ {α} → ordinal α → ∈-irreflexive α
ordinal-is-irreflexive ord-α = π₂ (π₁ (π₁ (π₂ ord-α)))

ordinal-has-trichotomy : ∀ {α} → ordinal α → ∈-trichotomy α
ordinal-has-trichotomy ord-α = π₂ (π₁ (π₂ ord-α))

ordinal-is-total : ∀ {α} → ordinal α → ∈-total α
ordinal-is-total ord-α = π₁ (π₂ ord-α)

ordinal-is-well-founded : ∀ {α} → ordinal α → ∈-well-founded α
ordinal-is-well-founded ord-α = π₂ (π₂ ord-α)

ordinal-is-well-ordered : ∀ {α} → ordinal α → ∈-well-ordered α
ordinal-is-well-ordered ord-α = π₂ ord-α

ordinal-is-transitive-set : ∀ {α} → ordinal α → transitive-set α
ordinal-is-transitive-set ord-α = π₁ ord-α


-- Really simple, but thus far unproved.
A∩B⊆A : ∀ {A B} → (A ∩ B) ⊆ A
A∩B⊆A = π₁  -- [ z∈A , z∈B ] = z∈A

A∩B⊆B : ∀ {A B} → (A ∩ B) ⊆ B
A∩B⊆B = π₂  -- [ z∈A , z∈B ] = z∈B

⊆-transitive : ∀ {A B C} → A ⊆ B → B ⊆ C → A ⊆ C
⊆-transitive A⊆B B⊆C z∈A = B⊆C (A⊆B z∈A)

-- Exercise I.7.21 (for ∈)
well-order-⊆-transport : ∀ {A X} → ∈-well-ordered A → X ⊆ A → ∈-well-ordered X
well-order-⊆-transport {A} {X} wo-A X⊆A = [ total-X , well-founded-X ]
    where
        total-X : ∈-total X
        total-X = [ [ trans-X , irreflexive-X ] , trichotomy-X ]
            where
                trans-X : ∈-transitive X
                trans-X x∈X y∈X z∈X x∈y y∈z =
                   (π₁ (π₁ (π₁ wo-A))) (X⊆A x∈X) (X⊆A y∈X) (X⊆A z∈X) x∈y y∈z
                irreflexive-X :  ∈-irreflexive X
                irreflexive-X x∈X = (π₂ (π₁ (π₁ wo-A))) (X⊆A x∈X)
                trichotomy-X : ∈-trichotomy X
                trichotomy-X x∈X y∈X =
                   (π₂ (π₁ wo-A)) (X⊆A x∈X) (X⊆A y∈X)
                
        well-founded-X : ∈-well-founded X
        well-founded-X Y not-∅ Y⊆X =
            (π₂ wo-A) Y not-∅ (⊆-transitive {Y} {X} {A} Y⊆X X⊆A)
        
-- Theorem I.8.5
-- The well-ordering of ON.

-- -- Lemma I.8.6
-- ON-transitive-class : ∀ α z → ordinal α → z ∈ α → ordinal z
-- ON-transitive-class α z ord-α z∈α =
--     [ trans-set-z ,
--     well-order-⊆-transport {α} {z} (π₂ ord-α) ((π₁ ord-α) z z∈α) ]
--     where
--         z⊆α : z ⊆ α
--         z⊆α = (π₁ ord-α) z z∈α
--         trans-set-z : transitive-set z
--         trans-set-z y y∈z x∈y =
--             (π₁ (π₂ ord-α)) _ y z (y⊆α x∈y) (z⊆α y∈z) z∈α x∈y y∈z
--                 where
--                     y⊆α : y ⊆ α
--                     y⊆α = (π₁ ord-α) y (z⊆α y∈z)
-- 
-- ∩-preserves-transitive-set : ∀ {x y} → transitive-set x → transitive-set y → transitive-set (x ∩ y)
-- ∩-preserves-transitive-set {x} {y} trans-x trans-y =
--     λ z → λ { [ z∈x , z∈y ] → λ w∈z → [ (trans-x z z∈x) w∈z , (trans-y z z∈y) w∈z ] } 
-- 
-- 
-- -- Lemma I.8.7
-- ∩-preserves-ordinal : ∀ {α β} → ordinal α → ordinal β → ordinal (α ∩ β)
-- ∩-preserves-ordinal {α} {β} ord-α ord-β =
--     [ ∩-preserves-transitive-set {α} {β} (π₁ ord-α) (π₁ ord-β) ,
--       well-order-⊆-transport {α} {α ∩ β} (π₂ ord-α) (A∩B⊆A {α} {β}) ]
-- 
-- -- Lemma I.8.8
-- ⊆-is-≤ : ∀ {α β} → ordinal α → ordinal β → α ⊆ β ≡ α ∈ β ∨ α ≗ β
-- ⊆-is-≤ {α} {β} ord-α ord-β =
--     equiv-equal [ zig , zag ]
--     where
--         zig : α ⊆ β → α ∈ β ∨ (α ≗ β)
--         zig α⊆β = {!   !}
--         
--         zag : α ∈ β ∨ (α ≗ β) → α ⊆ β
--         zag (ι₁ α∈β) = (π₁ ord-β) α α∈β 
--         zag (ι₂ refl𝕍) = idP