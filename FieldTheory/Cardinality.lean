/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.Algebra.MonoidAlgebra.Cardinal
public import Mathlib.Data.Rat.Encodable
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.Localization.Cardinality
public import Mathlib.SetTheory.Cardinal.Divisibility

/-!
# Cardinality of Fields

In this file we show all the possible cardinalities of fields. All infinite cardinals can harbour
a field structure, and so can all types with prime power cardinalities, and this is sharp.

## Main statements

* `Fintype.nonempty_field_iff`: A `Fintype` can be given a field structure iff its cardinality is a
  prime power.
* `Infinite.nonempty_field` : Any infinite type can be endowed a field structure.
* `Field.nonempty_iff` : There is a field structure on type iff its cardinality is a prime power.

-/

public section


local notation "‖" x "‖" => Fintype.card x

open scoped Cardinal nonZeroDivisors

universe u

/-- A finite field has prime power cardinality. -/
/-
**Fintype.isPrimePow_card_of_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.isPrimePow_card_of_field {α} [Fintype α] [Field α] : IsPrimePow ‖α
‖
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FiniteField.isPrimePow_card`：isPrimePow_card : IsPrimePow (Fintype.card 
K)

--- 原说明 ---
A finite field has prime power cardinality.
-/
theorem Fintype.isPrimePow_card_of_field {α} [Fintype α] [Field α] : IsPrimePow ‖α‖ :=
  -- TODO: `Algebra` version of `CharP.exists`, of type `∀ p, Algebra (ZMod p) α`
  FiniteField.isPrimePow_card α

/-- A `Fintype` can be given a field structure iff its cardinality is a prime power. -/
/-
**Fintype.nonempty_field_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.nonempty_field_iff {α} [Fintype α] : Nonempty (Field α) ↔ IsPrimeP
ow ‖α‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.isPrimePow_card_of_field`：Fintype.isPrimePow_card_of_field {α} [
Fintype α] [Field α] : IsPrimePow ‖α‖
· 使用定理 `Prime.nat_prime`：∀ {p : ℕ}, Prime p → Nat.Prime p
· 使用定理 `instFiniteGaloisField`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (n : ℕ), Fi
nite (GaloisField p n)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `GaloisField.card`：card (h : n != 0) : Nat.card (GaloisField p n) = p ^ n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
A `Fintype` can be given a field structure iff its cardinality is a prime power.
-/
theorem Fintype.nonempty_field_iff {α} [Fintype α] : Nonempty (Field α) ↔ IsPrimePow ‖α‖ := by
  refine ⟨fun ⟨h⟩ => Fintype.isPrimePow_card_of_field, ?_⟩
  rintro ⟨p, n, hp, hn, hα⟩
  have := Fact.mk hp.nat_prime
  have : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  exact ⟨(Fintype.equivOfCardEq
    (((Fintype.card_eq_nat_card).trans (GaloisField.card p n hn.ne')).trans hα)).symm.field⟩
/-
**Fintype.not_isField_of_card_not_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.not_isField_of_card_not_prime_pow {α} [Fintype α] [Ring α] : ¬IsPr
imePow ‖α‖ -> ¬IsField α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.nonempty_field_iff`：Fintype.nonempty_field_iff {α} [Fintype α] :
 Nonempty (Field α) ↔ IsPrimePow ‖α‖
-/
theorem Fintype.not_isField_of_card_not_prime_pow {α} [Fintype α] [Ring α] :
    ¬IsPrimePow ‖α‖ → ¬IsField α :=
  mt fun h => Fintype.nonempty_field_iff.mp ⟨h.toField⟩

/-- Any infinite type can be endowed a field structure. -/
/-
**Infinite.nonempty_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Infinite.nonempty_field {α : Type u} [Infinite α] : Nonempty (Field α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fractionRing`：Cardinal.mk_fractionRing (R : Type u) [CommRin
g R] : #(FractionRing R) = #R
· 使用定理 `AddMonoidAlgebra.cardinalMk_eq_max_lift_of_infinite`：∀ (R : Type u) (M' 
: Type v) [inst : Semiring R] [Infinite M'] [Nontrivial R],   Cardinal.mk (AddMo
noidAlgebra R M') =     max (Cardinal.lif…
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Infinite.instNontrivial`：∀ (α : Type u_4) [Infinite α], Nontrivial α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.mk_eq_aleph0`：mk_eq_aleph0 (α : Type*) [Countable α] [Infinite 
α] : #α = ℵ₀
· 使用定理 `instCountableULift`：∀ {β : Type v} [Countable β], Countable (ULift.{u, v
} β)
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `instInfiniteULift`：∀ {α : Type v} [Infinite α], Infinite (ULift.{u, v} α
)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Cardinal.mk_finsupp_lift_of_infinite`：mk_finsupp_lift_of_infinite (α : T
ype u) (β : Type v) [Infinite α] [Zero β] [Nontrivial β] : #(α ->₀ β) = max (lif
t.{v} #α) (lift.{u} #β)
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `MvPolynomial.instNoZeroDivisors`：∀ {R : Type u} {σ : Type u_1} [inst : C
ommSemiring R] [NoZeroDivisors R], NoZeroDivisors (MvPolynomial σ R)
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.eq`：∀ {α β : Type u}, Cardinal.mk α = Cardinal.mk β ↔ Nonempty 
(α ≃ β)

--- 原说明 ---
Any infinite type can be endowed a field structure.
-/
theorem Infinite.nonempty_field {α : Type u} [Infinite α] : Nonempty (Field α) := by
  suffices #α = #(FractionRing (MvPolynomial α <| ULift.{u} ℚ)) from
    (Cardinal.eq.1 this).map (·.field)
  simp

/-- There is a field structure on type if and only if its cardinality is a prime power. -/
/-
**Field.nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Field.nonempty_iff {α : Type u} : Nonempty (Field α) ↔ IsPrimePow #α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.isPrimePow_iff`：isPrimePow_iff {a : Cardinal} : IsPrimePow a ↔ 
ℵ₀ <= a ∨ exists n : Nat, a = n ∧ IsPrimePow n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Fintype.nonempty_field_iff`：Fintype.nonempty_field_iff {α} [Fintype α] :
 Nonempty (Field α) ↔ IsPrimePow ‖α‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Infinite.nonempty_field`：Infinite.nonempty_field {α : Type u} [Infinite 
α] : Nonempty (Field α)

--- 原说明 ---
There is a field structure on type if and only if its cardinality is a prime pow
er.
-/
theorem Field.nonempty_iff {α : Type u} : Nonempty (Field α) ↔ IsPrimePow #α := by
  rw [Cardinal.isPrimePow_iff]
  obtain h | h := fintypeOrInfinite α
  · simpa only [Cardinal.mk_fintype, Nat.cast_inj, exists_eq_left',
      Cardinal.natCast_lt_aleph0.not_ge, false_or] using Fintype.nonempty_field_iff
  · simpa only [← Cardinal.infinite_iff, h, true_or, iff_true] using Infinite.nonempty_field
