{-# OPTIONS --prop --rewriting #-}

module logic where
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Primitive
open import Trebor-Huang.Trebor-Huang-logic
open import Trebor-Huang.Trebor-Huang-ZF

-- Because we are trying to work in FOL, I add the classical property of existential import.
postulate
    existential-import :
        (A : Set) → (P : A → Prop) → ((x : A) → P x) → ∃[ x ∈ A ] P x

[P→¬P]∧[¬P→P]→⊥ : {P : Prop} → (P → ¬ P) ∧ (¬ P → P) → ⊥
[P→¬P]∧[¬P→P]→⊥ [ zig , zag ] = (λ x → zig x x) (zag (λ x → zig x x))

¬[P∧¬Q]→[P→Q] : {P Q : Prop} → ¬ (P ∧ ¬ Q) → (P → Q)
¬[P∧¬Q]→[P→Q] {P} {Q} hyp p with truth Q
... | inj₁ yes = ≡-true yes
... | inj₂ no = ex-falso (hyp [ p , ≡-false no ])

¬P→P∨Q∨R→Q∨R : {P Q R : Prop} → ¬ P → P ∨ Q ∨ R → Q ∨ R
¬P→P∨Q∨R→Q∨R {P} {Q} {R} ¬p (ι₁ (ι₁ p)) = ex-falso (¬p p)
¬P→P∨Q∨R→Q∨R {P} {Q} {R} ¬p (ι₁ (ι₂ q)) = ι₁ q
¬P→P∨Q∨R→Q∨R {P} {Q} {R} ¬p (ι₂ r) = ι₂ r
-- solve 1 (λ P Q R → (¡ P ==> P ||| Q ||| R ==> Q ||| R)) P Q R
-- Solver can't handle multiple proposition variables?

DeMorgan-¬∧-¬¬∨ : {P Q : Prop} → ¬ (P ∧ Q) → ¬ P ∨ ¬ Q
DeMorgan-¬∧-¬¬∨ {P} {Q} ¬[P∧Q] with truth P | truth Q
... | inj₁ p | inj₁ q = ex-falso (¬[P∧Q] [ ≡-true p , ≡-true q ] )
... | _ | inj₂ ¬q = ι₂ (≡-false ¬q)
... | inj₂ ¬p | _ = ι₁ (≡-false ¬p)

¬[P→¬Q]→P∧Q : {P Q : Prop} → ¬(P → ¬ Q) → P ∧ Q
¬[P→¬Q]→P∧Q {P} {Q} ¬[p→¬q] with truth P | truth Q
... | inj₁ p | inj₁ q = [ ≡-true p , ≡-true q ]
... | _ | inj₂ ¬q = ex-falso (¬[p→¬q] (λ p → (≡-false ¬q)))
... | inj₂ ¬p | _ = ex-falso (¬[p→¬q] (λ p → ex-falso ((≡-false ¬p) p)))

P→¬P∨Q→Q : {P Q : Prop} → P → ¬ P ∨ Q → Q
P→¬P∨Q→Q p (ι₁ ¬p) = ex-falso (¬p p)
P→¬P∨Q→Q p (ι₂ q) = q

¬∃-∀¬ : {P : 𝕍 → Prop} → ¬ (∃[ x ∈ 𝕍 ] P x) → (∀ x → ¬ P x)
¬∃-∀¬ ¬∃ x Px = ¬∃ (exists x Px)

¬¬P→P : {P : Prop} → ¬ ¬ P → P
¬¬P→P {P} = solve 1 (\ P -> (¡ ¡ P ==> P)) P

¬∀-∃¬ : {P : 𝕍 → Prop} → ¬ (∀ x → P x) → ∃[ x ∈ 𝕍 ] ¬ P x
¬∀-∃¬ {P} ¬∀ with truth (∃[ x ∈ 𝕍 ] ¬ P x)
... | inj₁ yes = ≡-true yes
... | inj₂ no = ex-falso (¬∀ (λ x → ¬¬P→P (¬∃-∀¬ (≡-false no) x)))

∃-prop-transfer : {P Q : Prop} → (P → Q) → ∃[ y ∈ 𝕍 ] P → ∃[ y ∈ 𝕍 ] Q
∃-prop-transfer p→q (exists y p) = exists y (p→q p)

∃-prop-transfer-param : {P Q : 𝕍 → Prop} → {x : 𝕍} → (∀ {x} → P x → Q x) → ∃[ y ∈ 𝕍 ] P x → ∃[ y ∈ 𝕍 ] Q x
∃-prop-transfer-param px→qx (exists y px) = exists y (px→qx px)

∧-comm : {P Q : Prop} → P ∧ Q → Q ∧ P
∧-comm [ p , q ] = [ q , p ]

infix 8 _↔_
_↔_ : Prop → Prop → Prop
_↔_ P Q = (P → Q) ∧ (Q → P)