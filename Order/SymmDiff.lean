/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Bryan Gin-ge Chen, Yaël Dillies
-/
module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Logic.Equiv.Basic

/-!
# Symmetric difference and bi-implication

This file defines the symmetric difference and bi-implication operators in (co-)Heyting algebras.

## Examples

Some examples are
* The symmetric difference of two sets is the set of elements that are in either but not both.
* The symmetric difference on propositions is `Xor`.
* The symmetric difference on `Bool` is `Bool.xor`.
* The equivalence of propositions. Two propositions are equivalent if they imply each other.
* The symmetric difference translates to addition when considering a Boolean algebra as a Boolean
  ring.

## Main declarations

* `symmDiff`: The symmetric difference operator, defined as `(a \ b) ⊔ (b \ a)`
* `bihimp`: The bi-implication operator, defined as `(b ⇨ a) ⊓ (a ⇨ b)`

In generalized Boolean algebras, the symmetric difference operator is:

* `symmDiff_comm`: commutative, and
* `symmDiff_assoc`: associative.

## Notation

* `a ∆ b`: `symmDiff a b`
* `a ⇔ b`: `bihimp a b`

## References

The proof of associativity follows the note "Associativity of the Symmetric Difference of Sets: A
Proof from the Book" by John McCuan:

* <https://people.math.gatech.edu/~mccuan/courses/4317/symmetricdifference.pdf>

## Tags

boolean ring, generalized boolean algebra, boolean algebra, symmetric difference, bi-implication,
Heyting
-/

@[expose] public section

assert_not_exists RelIso

open Function OrderDual

variable {ι α β : Type*} {π : ι -> Type*}

to_dual_name_hint Compl HNot, SDiff HImp

/-- The symmetric difference operator on a type with `⊔` and `\` is `(A \ B) ⊔ (B \ A)`. -/
@[to_dual
/-- The Heyting bi-implication is `(b ⇨ a) ⊓ (a ⇨ b)`. This generalizes equivalence of
propositions. -/]
/--
Definition of `symmDiff` / `symmDiff` 的定义

English:
definition symmDiff
  signature: [Max α] [SDiff α] (a b : α)
  body: a \ b ⊔ b \ a

中文:
定义 symmDiff
  签名: [最大值 α] [对称差 α] (a b : α)
  定义体: a \ b ⊔ b \ a

Depends on / 依赖: DirectSum, DirectSum.mk_apply_of_mem, DirectSum.mk_apply_of_notMem, Finset, Finset.image, Submodule, Submodule.coe_zero, Subtype, Subtype.coe_mk, coe_mk, coe_zero, decompose, mk_apply_of_mem, mk_apply_of_notMem, support, weight, weightedHomogeneousComponent_eq_zero_of_notMem
-/
def symmDiff [Max α] [SDiff α] (a b : α) : α :=
  a \ b ⊔ b \ a

/-- Notation for symmDiff -/
scoped[symmDiff] infixl:100 " ∆ " => symmDiff

/-- Notation for bihimp -/
scoped[symmDiff] infixl:100 " ⇔ " => bihimp

open scoped symmDiff

@[to_dual]
/--
theorem `symmDiff_def` / 定理 `symmDiff_def`

English:
theorem symmDiff_def
  given: [Max α] [SDiff α] (a b : α)
  statement: a ∆ b = a \ b ⊔ b \ a
  proof: rfl

中文:
定理 symmDiff_def
  条件: [最大值 α] [对称差 α] (a b : α)
  结论: a ∆ b = a \ b ⊔ b \ a
  证明: rfl
-/
theorem symmDiff_def [Max α] [SDiff α] (a b : α) : a ∆ b = a \ b ⊔ b \ a :=
  rfl

/--
theorem `symmDiff_eq_xor` / 定理 `symmDiff_eq_xor`

English:
theorem symmDiff_eq_xor
  given: (p q : Prop)
  statement: p ∆ q = Xor p q
  proof: rfl

@[deprecated (since := "2026-04-27")] alias symmDiff_eq_Xor' := symmDiff_eq_xor

@[simp]

中文:
定理 symmDiff_eq_xor
  条件: (p q : 命题)
  结论: p ∆ q = Xor p q
  证明: rfl

@[deprecated (since := "2026-04-27")] alias symmDiff_eq_Xor' := symmDiff_eq_xor

@[simp]
-/
theorem symmDiff_eq_xor (p q : Prop) : p ∆ q = Xor p q :=
  rfl

@[deprecated (since := "2026-04-27")] alias symmDiff_eq_Xor' := symmDiff_eq_xor

@[simp]
/--
theorem `bihimp_iff_iff` / 定理 `bihimp_iff_iff`

English:
theorem bihimp_iff_iff
  given: {p q : Prop}
  statement: p ⇔ q ↔ (p ↔ q)
  proof: iff_iff_implies_and_implies.symm.trans Iff.comm

@[simp]

中文:
定理 bihimp_iff_iff
  条件: {p q : 命题}
  结论: p ⇔ q ↔ (p ↔ q)
  证明: iff_iff_implies_and_implies.symm.trans Iff.comm

@[simp]

Depends on / 依赖: Iff.comm, iff_iff_implies_and_implies, iff_iff_implies_and_implies.symm.trans
-/
theorem bihimp_iff_iff {p q : Prop} : p ⇔ q ↔ (p ↔ q) :=
  iff_iff_implies_and_implies.symm.trans Iff.comm

@[simp]
/--
theorem `Bool.symmDiff_eq_xor` / 定理 `Bool.symmDiff_eq_xor`

English:
theorem Bool.symmDiff_eq_xor
  statement: forall p q : Bool, p ∆ q = xor p q
  proof: by decide

中文:
定理 布尔值.symmDiff_eq_xor
  结论: 对任意 p q : 布尔值, p ∆ q = xor p q
  证明: by decide

Depends on / 依赖: MvPolynomial, MvPolynomial.decompose, _apply, decompose
-/
theorem Bool.symmDiff_eq_xor : forall p q : Bool, p ∆ q = xor p q := by decide

section GeneralizedCoheytingAlgebra

variable [GeneralizedCoheytingAlgebra α] (a b c : α)

@[to_dual (attr := simp)]
/--
theorem `toDual_symmDiff` / 定理 `toDual_symmDiff`

English:
theorem toDual_symmDiff
  statement: toDual (a ∆ b) = toDual a ⇔ toDual b
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 toDual_symmDiff
  结论: toDual (a ∆ b) = toDual a ⇔ toDual b
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem toDual_symmDiff : toDual (a ∆ b) = toDual a ⇔ toDual b :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `ofDual_bihimp` / 定理 `ofDual_bihimp`

English:
theorem ofDual_bihimp
  given: (a b : αᵒᵈ)
  statement: ofDual (a ⇔ b) = ofDual a ∆ ofDual b
  proof: rfl

@[to_dual]

中文:
定理 ofDual_bihimp
  条件: (a b : αᵒᵈ)
  结论: ofDual (a ⇔ b) = ofDual a ∆ ofDual b
  证明: rfl

@[to_dual]
-/
theorem ofDual_bihimp (a b : αᵒᵈ) : ofDual (a ⇔ b) = ofDual a ∆ ofDual b :=
  rfl

@[to_dual]
/--
theorem `symmDiff_comm` / 定理 `symmDiff_comm`

English:
theorem symmDiff_comm
  statement: a ∆ b = b ∆ a
  proof: by simp only [symmDiff, sup_comm]

@[to_dual]

中文:
定理 symmDiff_comm
  结论: a ∆ b = b ∆ a
  证明: by simp only [symmDiff, sup_comm]

@[to_dual]

Depends on / 依赖: sup_comm, symmDiff
-/
theorem symmDiff_comm : a ∆ b = b ∆ a := by simp only [symmDiff, sup_comm]

@[to_dual]
/--
Instance `symmDiff_isCommutative` / 实例 `symmDiff_isCommutative`

English:
instance symmDiff_isCommutative
  signature: : Std.Commutative (α := α) (· ∆ ·)
  body: ⟨symmDiff_comm⟩

@[to_dual (attr := simp)]

中文:
实例 symmDiff_isCommutative
  签名: : Std.交换 (α := α) (· ∆ ·)
  定义体: ⟨symmDiff_comm⟩

@[to_dual (attr := simp)]
-/
instance symmDiff_isCommutative : Std.Commutative (α := α) (· ∆ ·) :=
  ⟨symmDiff_comm⟩

@[to_dual (attr := simp)]
/--
theorem `symmDiff_self` / 定理 `symmDiff_self`

English:
theorem symmDiff_self
  statement: a ∆ a = ⊥
  proof: by rw [symmDiff, sup_idem, sdiff_self]

@[to_dual (attr := simp)]

中文:
定理 symmDiff_self
  结论: a ∆ a = ⊥
  证明: by rw [symmDiff, sup_idem, sdiff_self]

@[to_dual (attr := simp)]

Depends on / 依赖: sdiff_self, sup_idem, symmDiff
-/
theorem symmDiff_self : a ∆ a = ⊥ := by rw [symmDiff, sup_idem, sdiff_self]

@[to_dual (attr := simp)]
/--
theorem `symmDiff_bot` / 定理 `symmDiff_bot`

English:
theorem symmDiff_bot
  statement: a ∆ ⊥ = a
  proof: by rw [symmDiff, sdiff_bot, bot_sdiff, sup_bot_eq]

@[to_dual (attr := simp)]

中文:
定理 symmDiff_bot
  结论: a ∆ ⊥ = a
  证明: by rw [symmDiff, sdiff_bot, bot_sdiff, sup_bot_eq]

@[to_dual (attr := simp)]

Depends on / 依赖: bot_sdiff, sdiff_bot, sup_bot_eq, symmDiff
-/
theorem symmDiff_bot : a ∆ ⊥ = a := by rw [symmDiff, sdiff_bot, bot_sdiff, sup_bot_eq]

@[to_dual (attr := simp)]
/--
theorem `bot_symmDiff` / 定理 `bot_symmDiff`

English:
theorem bot_symmDiff
  statement: ⊥ ∆ a = a
  proof: by rw [symmDiff_comm, symmDiff_bot]

@[to_dual (attr := simp)]

中文:
定理 bot_symmDiff
  结论: ⊥ ∆ a = a
  证明: by rw [symmDiff_comm, symmDiff_bot]

@[to_dual (attr := simp)]

Depends on / 依赖: symmDiff_bot, symmDiff_comm
-/
theorem bot_symmDiff : ⊥ ∆ a = a := by rw [symmDiff_comm, symmDiff_bot]

@[to_dual (attr := simp)]
/--
theorem `symmDiff_eq_bot` / 定理 `symmDiff_eq_bot`

English:
theorem symmDiff_eq_bot
  given: {a b : α}
  statement: a ∆ b = ⊥ ↔ a = b
  proof: by
  simp_rw [symmDiff, sup_eq_bot_iff, sdiff_eq_bot_iff, le_antisymm_iff]

@[to_dual]

中文:
定理 symmDiff_eq_bot
  条件: {a b : α}
  结论: a ∆ b = ⊥ ↔ a = b
  证明: by
  simp_rw [symmDiff, sup_eq_bot_iff, sdiff_eq_bot_iff, le_antisymm_iff]

@[to_dual]

Depends on / 依赖: le_antisymm_iff, sdiff_eq_bot_iff, simp_rw, sup_eq_bot_iff, symmDiff
-/
theorem symmDiff_eq_bot {a b : α} : a ∆ b = ⊥ ↔ a = b := by
  simp_rw [symmDiff, sup_eq_bot_iff, sdiff_eq_bot_iff, le_antisymm_iff]

@[to_dual]
/--
theorem `symmDiff_of_le` / 定理 `symmDiff_of_le`

English:
theorem symmDiff_of_le
  given: {a b : α} (h : a <= b)
  statement: a ∆ b = b \ a
  proof: by
  rw [symmDiff]; rw [sdiff_eq_bot_iff.2 h]; rw [bot_sup_eq]

@[to_dual]

中文:
定理 symmDiff_of_le
  条件: {a b : α} (h : a <= b)
  结论: a ∆ b = b \ a
  证明: by
  rw [symmDiff]; rw [sdiff_eq_bot_iff.2 h]; rw [bot_sup_eq]

@[to_dual]

Depends on / 依赖: bot_sup_eq, sdiff_eq_bot_iff, symmDiff
-/
theorem symmDiff_of_le {a b : α} (h : a <= b) : a ∆ b = b \ a := by
  rw [symmDiff]; rw [sdiff_eq_bot_iff.2 h]; rw [bot_sup_eq]

@[to_dual]
/--
theorem `symmDiff_of_ge` / 定理 `symmDiff_of_ge`

English:
theorem symmDiff_of_ge
  given: {a b : α} (h : b <= a)
  statement: a ∆ b = a \ b
  proof: by
  rw [symmDiff]; rw [sdiff_eq_bot_iff.2 h]; rw [sup_bot_eq]

@[to_dual le_bihimp]

中文:
定理 symmDiff_of_ge
  条件: {a b : α} (h : b <= a)
  结论: a ∆ b = a \ b
  证明: by
  rw [symmDiff]; rw [sdiff_eq_bot_iff.2 h]; rw [sup_bot_eq]

@[to_dual le_bihimp]

Depends on / 依赖: sdiff_eq_bot_iff, sup_bot_eq, symmDiff
-/
theorem symmDiff_of_ge {a b : α} (h : b <= a) : a ∆ b = a \ b := by
  rw [symmDiff]; rw [sdiff_eq_bot_iff.2 h]; rw [sup_bot_eq]

@[to_dual le_bihimp]
/--
theorem `symmDiff_le` / 定理 `symmDiff_le`

English:
theorem symmDiff_le
  given: {a b c : α} (ha : a <= b ⊔ c) (hb : b <= a ⊔ c)
  statement: a ∆ b <= c
  proof: sup_le (sdiff_le_iff.2 ha) sdiff_le_iff.2 hb

@[to_dual le_bihimp_iff]

中文:
定理 symmDiff_le
  条件: {a b c : α} (ha : a <= b ⊔ c) (hb : b <= a ⊔ c)
  结论: a ∆ b <= c
  证明: sup_le (sdiff_le_iff.2 ha) sdiff_le_iff.2 hb

@[to_dual le_bihimp_iff]

Depends on / 依赖: sdiff_le_iff, sup_le
-/
theorem symmDiff_le {a b c : α} (ha : a <= b ⊔ c) (hb : b <= a ⊔ c) : a ∆ b <= c :=
sup_le (sdiff_le_iff.2 ha) sdiff_le_iff.2 hb

@[to_dual le_bihimp_iff]
/--
theorem `symmDiff_le_iff` / 定理 `symmDiff_le_iff`

English:
theorem symmDiff_le_iff
  given: {a b c : α}
  statement: a ∆ b <= c ↔ a <= b ⊔ c ∧ b <= a ⊔ c
  proof: by
  simp_rw [symmDiff, sup_le_iff, sdiff_le_iff]

@[to_dual (attr := simp) inf_le_bihimp]

中文:
定理 symmDiff_le_iff
  条件: {a b c : α}
  结论: a ∆ b <= c ↔ a <= b ⊔ c ∧ b <= a ⊔ c
  证明: by
  simp_rw [symmDiff, sup_le_iff, sdiff_le_iff]

@[to_dual (attr := simp) inf_le_bihimp]

Depends on / 依赖: sdiff_le_iff, simp_rw, sup_le_iff, symmDiff
-/
theorem symmDiff_le_iff {a b c : α} : a ∆ b <= c ↔ a <= b ⊔ c ∧ b <= a ⊔ c := by
  simp_rw [symmDiff, sup_le_iff, sdiff_le_iff]

@[to_dual (attr := simp) inf_le_bihimp]
/--
theorem `symmDiff_le_sup` / 定理 `symmDiff_le_sup`

English:
theorem symmDiff_le_sup
  given: {a b : α}
  statement: a ∆ b <= a ⊔ b
  proof: sup_le_sup sdiff_le sdiff_le

@[to_dual bihimp_eq_sup_himp_inf]

中文:
定理 symmDiff_le_sup
  条件: {a b : α}
  结论: a ∆ b <= a ⊔ b
  证明: sup_le_sup sdiff_le sdiff_le

@[to_dual bihimp_eq_sup_himp_inf]

Depends on / 依赖: sdiff_le, sup_le_sup
-/
theorem symmDiff_le_sup {a b : α} : a ∆ b <= a ⊔ b :=
  sup_le_sup sdiff_le sdiff_le

@[to_dual bihimp_eq_sup_himp_inf]
/--
theorem `symmDiff_eq_sup_sdiff_inf` / 定理 `symmDiff_eq_sup_sdiff_inf`

English:
theorem symmDiff_eq_sup_sdiff_inf
  statement: a ∆ b = (a ⊔ b) \ (a ⊓ b)
  proof: by simp [sup_sdiff, symmDiff]

@[to_dual]

中文:
定理 symmDiff_eq_sup_sdiff_inf
  结论: a ∆ b = (a ⊔ b) \ (a ⊓ b)
  证明: by simp [sup_sdiff, symmDiff]

@[to_dual]

Depends on / 依赖: sup_sdiff, symmDiff
-/
theorem symmDiff_eq_sup_sdiff_inf : a ∆ b = (a ⊔ b) \ (a ⊓ b) := by simp [sup_sdiff, symmDiff]

@[to_dual]
/--
theorem `Disjoint.symmDiff_eq_sup` / 定理 `Disjoint.symmDiff_eq_sup`

English:
theorem Disjoint.symmDiff_eq_sup
  given: {a b : α} (h : Disjoint a b)
  statement: a ∆ b = a ⊔ b
  proof: by
  rw [symmDiff]; rw [h.sdiff_eq_left]; rw [h.sdiff_eq_right]

@[to_dual himp_bihimp]

中文:
定理 Disjoint.symmDiff_eq_sup
  条件: {a b : α} (h : Disjoint a b)
  结论: a ∆ b = a ⊔ b
  证明: by
  rw [symmDiff]; rw [h.sdiff_eq_left]; rw [h.sdiff_eq_right]

@[to_dual himp_bihimp]

Depends on / 依赖: h.sdiff_eq_left, h.sdiff_eq_right, sdiff_eq_left, sdiff_eq_right, symmDiff
-/
theorem Disjoint.symmDiff_eq_sup {a b : α} (h : Disjoint a b) : a ∆ b = a ⊔ b := by
  rw [symmDiff]; rw [h.sdiff_eq_left]; rw [h.sdiff_eq_right]

@[to_dual himp_bihimp]
/--
theorem `symmDiff_sdiff` / 定理 `symmDiff_sdiff`

English:
theorem symmDiff_sdiff
  statement: a ∆ b \ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c)
  proof: by
  rw [symmDiff]; rw [sup_sdiff_distrib]; rw [sdiff_sdiff_left]; rw [sdiff_sdiff_left]

@[to_dual (attr := simp) sup_himp_bihimp]

中文:
定理 symmDiff_sdiff
  结论: a ∆ b \ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c)
  证明: by
  rw [symmDiff]; rw [sup_sdiff_distrib]; rw [sdiff_sdiff_left]; rw [sdiff_sdiff_left]

@[to_dual (attr := simp) sup_himp_bihimp]

Depends on / 依赖: sdiff_sdiff_left, sup_sdiff_distrib, symmDiff
-/
theorem symmDiff_sdiff : a ∆ b \ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) := by
  rw [symmDiff]; rw [sup_sdiff_distrib]; rw [sdiff_sdiff_left]; rw [sdiff_sdiff_left]

@[to_dual (attr := simp) sup_himp_bihimp]
/--
theorem `symmDiff_sdiff_inf` / 定理 `symmDiff_sdiff_inf`

English:
theorem symmDiff_sdiff_inf
  statement: a ∆ b \ (a ⊓ b) = a ∆ b
  proof: by
  rw [symmDiff_sdiff]
  simp [symmDiff]

@[to_dual (attr := simp)]

中文:
定理 symmDiff_sdiff_inf
  结论: a ∆ b \ (a ⊓ b) = a ∆ b
  证明: by
  rw [symmDiff_sdiff]
  simp [symmDiff]

@[to_dual (attr := simp)]

Depends on / 依赖: symmDiff, symmDiff_sdiff
-/
theorem symmDiff_sdiff_inf : a ∆ b \ (a ⊓ b) = a ∆ b := by
  rw [symmDiff_sdiff]
  simp [symmDiff]

@[to_dual (attr := simp)]
/--
theorem `symmDiff_sdiff_eq_sup` / 定理 `symmDiff_sdiff_eq_sup`

English:
theorem symmDiff_sdiff_eq_sup
  statement: a ∆ (b \ a) = a ⊔ b
  proof: by
  rw [symmDiff]; rw [sdiff_idem]
  exact
    le_antisymm (sup_le_sup sdiff_le sdiff_le)
      (sup_le le_sdiff_sup <| le_sdiff_sup.trans <| sup_le le_sup_right le_sdiff_sup)

@[to_dual (attr := simp)]

中文:
定理 symmDiff_sdiff_eq_sup
  结论: a ∆ (b \ a) = a ⊔ b
  证明: by
  rw [symmDiff]; rw [sdiff_idem]
  exact
    le_antisymm (sup_le_sup sdiff_le sdiff_le)
      (sup_le le_sdiff_sup <| le_sdiff_sup.trans <| sup_le le_sup_right le_sdiff_sup)

@[to_dual (attr := simp)]

Depends on / 依赖: le_antisymm, le_sdiff_sup, le_sdiff_sup.trans, le_sup_right, sdiff_idem, sdiff_le, sup_le, sup_le_sup, symmDiff
-/
theorem symmDiff_sdiff_eq_sup : a ∆ (b \ a) = a ⊔ b := by
  rw [symmDiff]; rw [sdiff_idem]
  exact
    le_antisymm (sup_le_sup sdiff_le sdiff_le)
      (sup_le le_sdiff_sup <| le_sdiff_sup.trans <| sup_le le_sup_right le_sdiff_sup)

@[to_dual (attr := simp)]
/--
theorem `sdiff_symmDiff_eq_sup` / 定理 `sdiff_symmDiff_eq_sup`

English:
theorem sdiff_symmDiff_eq_sup
  statement: (a \ b) ∆ b = a ⊔ b
  proof: by
  rw [symmDiff_comm]; rw [symmDiff_sdiff_eq_sup]; rw [sup_comm]

@[to_dual (attr := simp)]

中文:
定理 sdiff_symmDiff_eq_sup
  结论: (a \ b) ∆ b = a ⊔ b
  证明: by
  rw [symmDiff_comm]; rw [symmDiff_sdiff_eq_sup]; rw [sup_comm]

@[to_dual (attr := simp)]

Depends on / 依赖: sup_comm, symmDiff_comm, symmDiff_sdiff_eq_sup
-/
theorem sdiff_symmDiff_eq_sup : (a \ b) ∆ b = a ⊔ b := by
  rw [symmDiff_comm]; rw [symmDiff_sdiff_eq_sup]; rw [sup_comm]

@[to_dual (attr := simp)]
/--
theorem `symmDiff_sup_inf` / 定理 `symmDiff_sup_inf`

English:
theorem symmDiff_sup_inf
  statement: a ∆ b ⊔ a ⊓ b = a ⊔ b
  proof: by
  refine le_antisymm (sup_le symmDiff_le_sup inf_le_sup) ?_
  rw [sup_inf_left]; rw [symmDiff]
  refine sup_le (le_inf le_sup_right ?_) (le_inf ?_ le_sup_right)
  · rw [sup_right_comm]
    exact le_sup_of_le_left le_sdiff_sup
  · rw [sup_assoc]
    exact le_sup_of_le_right le_sdiff_sup

@[to_dual (attr := simp)]

中文:
定理 symmDiff_sup_inf
  结论: a ∆ b ⊔ a ⊓ b = a ⊔ b
  证明: by
  refine le_antisymm (sup_le symmDiff_le_sup inf_le_sup) ?_
  rw [sup_inf_left]; rw [symmDiff]
  refine sup_le (le_inf le_sup_right ?_) (le_inf ?_ le_sup_right)
  · rw [sup_right_comm]
    exact le_sup_of_le_left le_sdiff_sup
  · rw [sup_assoc]
    exact le_sup_of_le_right le_sdiff_sup

@[to_dual (attr := simp)]

Depends on / 依赖: inf_le_sup, le_antisymm, le_inf, le_sdiff_sup, le_sup_of_le_left, le_sup_of_le_right, le_sup_right, sup_assoc, sup_inf_left, sup_le, sup_right_comm, symmDiff, symmDiff_le_sup
-/
theorem symmDiff_sup_inf : a ∆ b ⊔ a ⊓ b = a ⊔ b := by
  refine le_antisymm (sup_le symmDiff_le_sup inf_le_sup) ?_
  rw [sup_inf_left]; rw [symmDiff]
  refine sup_le (le_inf le_sup_right ?_) (le_inf ?_ le_sup_right)
  · rw [sup_right_comm]
    exact le_sup_of_le_left le_sdiff_sup
  · rw [sup_assoc]
    exact le_sup_of_le_right le_sdiff_sup

@[to_dual (attr := simp)]
/--
theorem `inf_sup_symmDiff` / 定理 `inf_sup_symmDiff`

English:
theorem inf_sup_symmDiff
  statement: a ⊓ b ⊔ a ∆ b = a ⊔ b
  proof: by rw [sup_comm, symmDiff_sup_inf]

@[to_dual (attr := simp)]

中文:
定理 inf_sup_symmDiff
  结论: a ⊓ b ⊔ a ∆ b = a ⊔ b
  证明: by rw [sup_comm, symmDiff_sup_inf]

@[to_dual (attr := simp)]

Depends on / 依赖: sup_comm, symmDiff_sup_inf
-/
theorem inf_sup_symmDiff : a ⊓ b ⊔ a ∆ b = a ⊔ b := by rw [sup_comm, symmDiff_sup_inf]

@[to_dual (attr := simp)]
/--
theorem `symmDiff_symmDiff_inf` / 定理 `symmDiff_symmDiff_inf`

English:
theorem symmDiff_symmDiff_inf
  statement: a ∆ b ∆ (a ⊓ b) = a ⊔ b
  proof: by
  rw [← symmDiff_sdiff_inf a]; rw [sdiff_symmDiff_eq_sup]; rw [symmDiff_sup_inf]

@[to_dual (attr := simp)]

中文:
定理 symmDiff_symmDiff_inf
  结论: a ∆ b ∆ (a ⊓ b) = a ⊔ b
  证明: by
  rw [← symmDiff_sdiff_inf a]; rw [sdiff_symmDiff_eq_sup]; rw [symmDiff_sup_inf]

@[to_dual (attr := simp)]

Depends on / 依赖: sdiff_symmDiff_eq_sup, symmDiff_sdiff_inf, symmDiff_sup_inf
-/
theorem symmDiff_symmDiff_inf : a ∆ b ∆ (a ⊓ b) = a ⊔ b := by
  rw [← symmDiff_sdiff_inf a]; rw [sdiff_symmDiff_eq_sup]; rw [symmDiff_sup_inf]

@[to_dual (attr := simp)]
/--
theorem `inf_symmDiff_symmDiff` / 定理 `inf_symmDiff_symmDiff`

English:
theorem inf_symmDiff_symmDiff
  statement: (a ⊓ b) ∆ (a ∆ b) = a ⊔ b
  proof: by
  rw [symmDiff_comm]; rw [symmDiff_symmDiff_inf]

@[to_dual]

中文:
定理 inf_symmDiff_symmDiff
  结论: (a ⊓ b) ∆ (a ∆ b) = a ⊔ b
  证明: by
  rw [symmDiff_comm]; rw [symmDiff_symmDiff_inf]

@[to_dual]

Depends on / 依赖: symmDiff_comm, symmDiff_symmDiff_inf
-/
theorem inf_symmDiff_symmDiff : (a ⊓ b) ∆ (a ∆ b) = a ⊔ b := by
  rw [symmDiff_comm]; rw [symmDiff_symmDiff_inf]

@[to_dual]
/--
theorem `symmDiff_triangle` / 定理 `symmDiff_triangle`

English:
theorem symmDiff_triangle
  statement: a ∆ c <= a ∆ b ⊔ b ∆ c
  proof: by
  refine (sup_le_sup (sdiff_triangle a b c) <| sdiff_triangle _ b _).trans_eq ?_
  rw [sup_comm (c \ b)]; rw [sup_sup_sup_comm]; rw [symmDiff]; rw [symmDiff]

@[to_dual]

中文:
定理 symmDiff_triangle
  结论: a ∆ c <= a ∆ b ⊔ b ∆ c
  证明: by
  refine (sup_le_sup (sdiff_triangle a b c) <| sdiff_triangle _ b _).trans_eq ?_
  rw [sup_comm (c \ b)]; rw [sup_sup_sup_comm]; rw [symmDiff]; rw [symmDiff]

@[to_dual]

Depends on / 依赖: sdiff_triangle, sup_comm, sup_le_sup, sup_sup_sup_comm, symmDiff, trans_eq
-/
theorem symmDiff_triangle : a ∆ c <= a ∆ b ⊔ b ∆ c := by
  refine (sup_le_sup (sdiff_triangle a b c) <| sdiff_triangle _ b _).trans_eq ?_
  rw [sup_comm (c \ b)]; rw [sup_sup_sup_comm]; rw [symmDiff]; rw [symmDiff]

@[to_dual]
/--
theorem `le_symmDiff_sup_right` / 定理 `le_symmDiff_sup_right`

English:
theorem le_symmDiff_sup_right
  given: (a b : α)
  statement: a <= (a ∆ b) ⊔ b
  proof: by
  convert! symmDiff_triangle a b ⊥ <;> rw [symmDiff_bot]

@[to_dual]

中文:
定理 le_symmDiff_sup_right
  条件: (a b : α)
  结论: a <= (a ∆ b) ⊔ b
  证明: by
  convert! symmDiff_triangle a b ⊥ <;> rw [symmDiff_bot]

@[to_dual]

Depends on / 依赖: convert, symmDiff_bot, symmDiff_triangle
-/
theorem le_symmDiff_sup_right (a b : α) : a <= (a ∆ b) ⊔ b := by
  convert! symmDiff_triangle a b ⊥ <;> rw [symmDiff_bot]

@[to_dual]
/--
theorem `le_symmDiff_sup_left` / 定理 `le_symmDiff_sup_left`

English:
theorem le_symmDiff_sup_left
  given: (a b : α)
  statement: b <= (a ∆ b) ⊔ a
  proof: symmDiff_comm a b ▸ le_symmDiff_sup_right ..

中文:
定理 le_symmDiff_sup_left
  条件: (a b : α)
  结论: b <= (a ∆ b) ⊔ a
  证明: symmDiff_comm a b ▸ le_symmDiff_sup_right ..

Depends on / 依赖: le_symmDiff_sup_right, symmDiff_comm
-/
theorem le_symmDiff_sup_left (a b : α) : b <= (a ∆ b) ⊔ a :=
  symmDiff_comm a b ▸ le_symmDiff_sup_right ..

end GeneralizedCoheytingAlgebra

section CoheytingAlgebra

variable [CoheytingAlgebra α] (a : α)

@[to_dual (attr := simp)]
/--
theorem `symmDiff_top` / 定理 `symmDiff_top`

English:
theorem symmDiff_top
  statement: a ∆ ⊤ = ￢a
  proof: by simp [symmDiff]

@[to_dual (attr := simp)]

中文:
定理 symmDiff_top
  结论: a ∆ ⊤ = ￢a
  证明: by simp [symmDiff]

@[to_dual (attr := simp)]

Depends on / 依赖: symmDiff
-/
theorem symmDiff_top : a ∆ ⊤ = ￢a := by simp [symmDiff]

@[to_dual (attr := simp)]
/--
theorem `top_symmDiff` / 定理 `top_symmDiff`

English:
theorem top_symmDiff
  statement: ⊤ ∆ a = ￢a
  proof: by simp [symmDiff]

@[deprecated (since := "2026-08-04")] alias symmDiff_top' := symmDiff_top
@[deprecated (since := "2026-08-04")] alias top_symmDiff' := top_symmDiff

@[to_dual (attr := simp)]

中文:
定理 top_symmDiff
  结论: ⊤ ∆ a = ￢a
  证明: by simp [symmDiff]

@[deprecated (since := "2026-08-04")] alias symmDiff_top' := symmDiff_top
@[deprecated (since := "2026-08-04")] alias top_symmDiff' := top_symmDiff

@[to_dual (attr := simp)]

Depends on / 依赖: symmDiff
-/
theorem top_symmDiff : ⊤ ∆ a = ￢a := by simp [symmDiff]

@[deprecated (since := "2026-08-04")] alias symmDiff_top' := symmDiff_top
@[deprecated (since := "2026-08-04")] alias top_symmDiff' := top_symmDiff

@[to_dual (attr := simp)]
/--
theorem `hnot_symmDiff_self` / 定理 `hnot_symmDiff_self`

English:
theorem hnot_symmDiff_self
  statement: (￢a) ∆ a = ⊤
  proof: by
  rw [eq_top_iff]; rw [symmDiff]; rw [hnot_sdiff]; rw [sup_sdiff_self]
  exact Codisjoint.top_le codisjoint_hnot_left

@[to_dual (attr := simp)]

中文:
定理 hnot_symmDiff_self
  结论: (￢a) ∆ a = ⊤
  证明: by
  rw [eq_top_iff]; rw [symmDiff]; rw [hnot_sdiff]; rw [sup_sdiff_self]
  exact Codisjoint.top_le codisjoint_hnot_left

@[to_dual (attr := simp)]

Depends on / 依赖: Codisjoint, Codisjoint.top_le, codisjoint_hnot_left, eq_top_iff, hnot_sdiff, sup_sdiff_self, symmDiff, top_le
-/
theorem hnot_symmDiff_self : (￢a) ∆ a = ⊤ := by
  rw [eq_top_iff]; rw [symmDiff]; rw [hnot_sdiff]; rw [sup_sdiff_self]
  exact Codisjoint.top_le codisjoint_hnot_left

@[to_dual (attr := simp)]
/--
theorem `symmDiff_hnot_self` / 定理 `symmDiff_hnot_self`

English:
theorem symmDiff_hnot_self
  statement: a ∆ (￢a) = ⊤
  proof: by rw [symmDiff_comm, hnot_symmDiff_self]

@[deprecated (since := "2026-07-15")] alias bihimp_hnot_self := bihimp_compl_self

@[to_dual]

中文:
定理 symmDiff_hnot_self
  结论: a ∆ (￢a) = ⊤
  证明: by rw [symmDiff_comm, hnot_symmDiff_self]

@[deprecated (since := "2026-07-15")] alias bihimp_hnot_self := bihimp_compl_self

@[to_dual]

Depends on / 依赖: hnot_symmDiff_self, symmDiff_comm
-/
theorem symmDiff_hnot_self : a ∆ (￢a) = ⊤ := by rw [symmDiff_comm, hnot_symmDiff_self]

@[deprecated (since := "2026-07-15")] alias bihimp_hnot_self := bihimp_compl_self

@[to_dual]
/--
theorem `IsCompl.symmDiff_eq_top` / 定理 `IsCompl.symmDiff_eq_top`

English:
theorem IsCompl.symmDiff_eq_top
  given: {a b : α} (h : IsCompl a b)
  statement: a ∆ b = ⊤
  proof: by
  rw [h.eq_hnot]; rw [hnot_symmDiff_self]

中文:
定理 是补集.symmDiff_eq_top
  条件: {a b : α} (h : 是补集 a b)
  结论: a ∆ b = ⊤
  证明: by
  rw [h.eq_hnot]; rw [hnot_symmDiff_self]

Depends on / 依赖: eq_hnot, h.eq_hnot, hnot_symmDiff_self
-/
theorem IsCompl.symmDiff_eq_top {a b : α} (h : IsCompl a b) : a ∆ b = ⊤ := by
  rw [h.eq_hnot]; rw [hnot_symmDiff_self]

end CoheytingAlgebra

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α] (a b c d : α)

@[simp]
/--
theorem `sup_sdiff_symmDiff` / 定理 `sup_sdiff_symmDiff`

English:
theorem sup_sdiff_symmDiff
  statement: (a ⊔ b) \ a ∆ b = a ⊓ b
  proof: sdiff_eq_symm inf_le_sup (by rw [symmDiff_eq_sup_sdiff_inf])

中文:
定理 sup_sdiff_symmDiff
  结论: (a ⊔ b) \ a ∆ b = a ⊓ b
  证明: sdiff_eq_symm inf_le_sup (by rw [symmDiff_eq_sup_sdiff_inf])

Depends on / 依赖: inf_le_sup, sdiff_eq_symm, symmDiff_eq_sup_sdiff_inf
-/
theorem sup_sdiff_symmDiff : (a ⊔ b) \ a ∆ b = a ⊓ b :=
  sdiff_eq_symm inf_le_sup (by rw [symmDiff_eq_sup_sdiff_inf])

/--
theorem `disjoint_symmDiff_inf` / 定理 `disjoint_symmDiff_inf`

English:
theorem disjoint_symmDiff_inf
  statement: Disjoint (a ∆ b) (a ⊓ b)
  proof: by
  rw [symmDiff_eq_sup_sdiff_inf]
  exact disjoint_sdiff_self_left

中文:
定理 disjoint_symmDiff_inf
  结论: Disjoint (a ∆ b) (a ⊓ b)
  证明: by
  rw [symmDiff_eq_sup_sdiff_inf]
  exact disjoint_sdiff_self_left

Depends on / 依赖: disjoint_sdiff_self_left, symmDiff_eq_sup_sdiff_inf
-/
theorem disjoint_symmDiff_inf : Disjoint (a ∆ b) (a ⊓ b) := by
  rw [symmDiff_eq_sup_sdiff_inf]
  exact disjoint_sdiff_self_left

/--
theorem `inf_symmDiff_distrib_left` / 定理 `inf_symmDiff_distrib_left`

English:
theorem inf_symmDiff_distrib_left
  statement: a ⊓ b ∆ c = (a ⊓ b) ∆ (a ⊓ c)
  proof: by
  rw [symmDiff_eq_sup_sdiff_inf]; rw [inf_sdiff_distrib_left]; rw [inf_sup_left]; rw [inf_inf_distrib_left]; rw [symmDiff_eq_sup_sdiff_inf]

中文:
定理 inf_symmDiff_distrib_left
  结论: a ⊓ b ∆ c = (a ⊓ b) ∆ (a ⊓ c)
  证明: by
  rw [symmDiff_eq_sup_sdiff_inf]; rw [inf_sdiff_distrib_left]; rw [inf_sup_left]; rw [inf_inf_distrib_left]; rw [symmDiff_eq_sup_sdiff_inf]

Depends on / 依赖: inf_inf_distrib_left, inf_sdiff_distrib_left, inf_sup_left, symmDiff_eq_sup_sdiff_inf
-/
theorem inf_symmDiff_distrib_left : a ⊓ b ∆ c = (a ⊓ b) ∆ (a ⊓ c) := by
  rw [symmDiff_eq_sup_sdiff_inf]; rw [inf_sdiff_distrib_left]; rw [inf_sup_left]; rw [inf_inf_distrib_left]; rw [symmDiff_eq_sup_sdiff_inf]

/--
theorem `inf_symmDiff_distrib_right` / 定理 `inf_symmDiff_distrib_right`

English:
theorem inf_symmDiff_distrib_right
  statement: a ∆ b ⊓ c = (a ⊓ c) ∆ (b ⊓ c)
  proof: by
  simp_rw [inf_comm _ c, inf_symmDiff_distrib_left]

中文:
定理 inf_symmDiff_distrib_right
  结论: a ∆ b ⊓ c = (a ⊓ c) ∆ (b ⊓ c)
  证明: by
  simp_rw [inf_comm _ c, inf_symmDiff_distrib_left]

Depends on / 依赖: inf_comm, inf_symmDiff_distrib_left, simp_rw
-/
theorem inf_symmDiff_distrib_right : a ∆ b ⊓ c = (a ⊓ c) ∆ (b ⊓ c) := by
  simp_rw [inf_comm _ c, inf_symmDiff_distrib_left]

/--
theorem `sdiff_symmDiff` / 定理 `sdiff_symmDiff`

English:
theorem sdiff_symmDiff
  statement: c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ a ⊓ c \ b
  proof: by
  simp only [(· ∆ ·), sdiff_sdiff_sup_sdiff']

中文:
定理 sdiff_symmDiff
  结论: c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ a ⊓ c \ b
  证明: by
  simp only [(· ∆ ·), sdiff_sdiff_sup_sdiff']

Depends on / 依赖: sdiff_sdiff_sup_sdiff
-/
theorem sdiff_symmDiff : c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ a ⊓ c \ b := by
  simp only [(· ∆ ·), sdiff_sdiff_sup_sdiff']

/--
theorem `sdiff_symmDiff'` / 定理 `sdiff_symmDiff'`

English:
theorem sdiff_symmDiff'
  statement: c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ (a ⊔ b)
  proof: by
  rw [sdiff_symmDiff]; rw [sdiff_sup]

@[simp]

中文:
定理 sdiff_symmDiff'
  结论: c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ (a ⊔ b)
  证明: by
  rw [sdiff_symmDiff]; rw [sdiff_sup]

@[simp]

Depends on / 依赖: sdiff_sup, sdiff_symmDiff
-/
theorem sdiff_symmDiff' : c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ (a ⊔ b) := by
  rw [sdiff_symmDiff]; rw [sdiff_sup]

@[simp]
/--
theorem `symmDiff_sdiff_left` / 定理 `symmDiff_sdiff_left`

English:
theorem symmDiff_sdiff_left
  statement: a ∆ b \ a = b \ a
  proof: by
  rw [symmDiff_def]; rw [sup_sdiff]; rw [sdiff_idem]; rw [sdiff_sdiff_self]; rw [bot_sup_eq]

@[simp]

中文:
定理 symmDiff_sdiff_left
  结论: a ∆ b \ a = b \ a
  证明: by
  rw [symmDiff_def]; rw [sup_sdiff]; rw [sdiff_idem]; rw [sdiff_sdiff_self]; rw [bot_sup_eq]

@[simp]

Depends on / 依赖: bot_sup_eq, sdiff_idem, sdiff_sdiff_self, sup_sdiff, symmDiff_def
-/
theorem symmDiff_sdiff_left : a ∆ b \ a = b \ a := by
  rw [symmDiff_def]; rw [sup_sdiff]; rw [sdiff_idem]; rw [sdiff_sdiff_self]; rw [bot_sup_eq]

@[simp]
/--
theorem `symmDiff_sdiff_right` / 定理 `symmDiff_sdiff_right`

English:
theorem symmDiff_sdiff_right
  statement: a ∆ b \ b = a \ b
  proof: by rw [symmDiff_comm, symmDiff_sdiff_left]

@[simp]

中文:
定理 symmDiff_sdiff_right
  结论: a ∆ b \ b = a \ b
  证明: by rw [symmDiff_comm, symmDiff_sdiff_left]

@[simp]

Depends on / 依赖: symmDiff_comm, symmDiff_sdiff_left
-/
theorem symmDiff_sdiff_right : a ∆ b \ b = a \ b := by rw [symmDiff_comm, symmDiff_sdiff_left]

@[simp]
/--
theorem `sdiff_symmDiff_left` / 定理 `sdiff_symmDiff_left`

English:
theorem sdiff_symmDiff_left
  statement: a \ a ∆ b = a ⊓ b
  proof: by simp [sdiff_symmDiff]

@[simp]

中文:
定理 sdiff_symmDiff_left
  结论: a \ a ∆ b = a ⊓ b
  证明: by simp [sdiff_symmDiff]

@[simp]

Depends on / 依赖: sdiff_symmDiff
-/
theorem sdiff_symmDiff_left : a \ a ∆ b = a ⊓ b := by simp [sdiff_symmDiff]

@[simp]
/--
theorem `sdiff_symmDiff_right` / 定理 `sdiff_symmDiff_right`

English:
theorem sdiff_symmDiff_right
  statement: b \ a ∆ b = a ⊓ b
  proof: by
  rw [symmDiff_comm]; rw [inf_comm]; rw [sdiff_symmDiff_left]

中文:
定理 sdiff_symmDiff_right
  结论: b \ a ∆ b = a ⊓ b
  证明: by
  rw [symmDiff_comm]; rw [inf_comm]; rw [sdiff_symmDiff_left]

Depends on / 依赖: inf_comm, sdiff_symmDiff_left, symmDiff_comm
-/
theorem sdiff_symmDiff_right : b \ a ∆ b = a ⊓ b := by
  rw [symmDiff_comm]; rw [inf_comm]; rw [sdiff_symmDiff_left]

/--
theorem `symmDiff_eq_sup` / 定理 `symmDiff_eq_sup`

English:
theorem symmDiff_eq_sup
  statement: a ∆ b = a ⊔ b ↔ Disjoint a b
  proof: by
  refine ⟨fun h => ?_, Disjoint.symmDiff_eq_sup⟩
  rw [symmDiff_eq_sup_sdiff_inf]; rw [sdiff_eq_self_iff_disjoint] at h
  exact h.of_disjoint_inf_of_le le_sup_left

@[simp]

中文:
定理 symmDiff_eq_sup
  结论: a ∆ b = a ⊔ b ↔ Disjoint a b
  证明: by
  refine ⟨fun h => ?_, Disjoint.symmDiff_eq_sup⟩
  rw [symmDiff_eq_sup_sdiff_inf]; rw [sdiff_eq_self_iff_disjoint] at h
  exact h.of_disjoint_inf_of_le le_sup_left

@[simp]

Depends on / 依赖: Disjoint, Disjoint.symmDiff_eq_sup, h.of_disjoint_inf_of_le, le_sup_left, of_disjoint_inf_of_le, sdiff_eq_self_iff_disjoint, symmDiff_eq_sup, symmDiff_eq_sup_sdiff_inf
-/
theorem symmDiff_eq_sup : a ∆ b = a ⊔ b ↔ Disjoint a b := by
  refine ⟨fun h => ?_, Disjoint.symmDiff_eq_sup⟩
  rw [symmDiff_eq_sup_sdiff_inf]; rw [sdiff_eq_self_iff_disjoint] at h
  exact h.of_disjoint_inf_of_le le_sup_left

@[simp]
/--
theorem `le_symmDiff_iff_left` / 定理 `le_symmDiff_iff_left`

English:
theorem le_symmDiff_iff_left
  statement: a <= a ∆ b ↔ Disjoint a b
  proof: by
  refine ⟨fun h => ?_, fun h => h.symmDiff_eq_sup.symm ▸ le_sup_left⟩
  rw [symmDiff_eq_sup_sdiff_inf] at h
  exact disjoint_iff_inf_le.mpr (le_sdiff_right.1 <| inf_le_of_left_le h).le

@[simp]

中文:
定理 le_symmDiff_iff_left
  结论: a <= a ∆ b ↔ Disjoint a b
  证明: by
  refine ⟨fun h => ?_, fun h => h.symmDiff_eq_sup.symm ▸ le_sup_left⟩
  rw [symmDiff_eq_sup_sdiff_inf] at h
  exact disjoint_iff_inf_le.mpr (le_sdiff_right.1 <| inf_le_of_left_le h).le

@[simp]

Depends on / 依赖: disjoint_iff_inf_le, disjoint_iff_inf_le.mpr, h.symmDiff_eq_sup.symm, inf_le_of_left_le, le_sdiff_right, le_sup_left, symmDiff_eq_sup, symmDiff_eq_sup_sdiff_inf
-/
theorem le_symmDiff_iff_left : a <= a ∆ b ↔ Disjoint a b := by
  refine ⟨fun h => ?_, fun h => h.symmDiff_eq_sup.symm ▸ le_sup_left⟩
  rw [symmDiff_eq_sup_sdiff_inf] at h
  exact disjoint_iff_inf_le.mpr (le_sdiff_right.1 <| inf_le_of_left_le h).le

@[simp]
/--
theorem `le_symmDiff_iff_right` / 定理 `le_symmDiff_iff_right`

English:
theorem le_symmDiff_iff_right
  statement: b <= a ∆ b ↔ Disjoint a b
  proof: by
  rw [symmDiff_comm]; rw [le_symmDiff_iff_left]; rw [disjoint_comm]

中文:
定理 le_symmDiff_iff_right
  结论: b <= a ∆ b ↔ Disjoint a b
  证明: by
  rw [symmDiff_comm]; rw [le_symmDiff_iff_left]; rw [disjoint_comm]

Depends on / 依赖: disjoint_comm, le_symmDiff_iff_left, symmDiff_comm
-/
theorem le_symmDiff_iff_right : b <= a ∆ b ↔ Disjoint a b := by
  rw [symmDiff_comm]; rw [le_symmDiff_iff_left]; rw [disjoint_comm]

/--
theorem `symmDiff_symmDiff_left` / 定理 `symmDiff_symmDiff_left`

English:
theorem symmDiff_symmDiff_left
  proof: calc
    a ∆ b ∆ c = a ∆ b \ c ⊔ c \ a ∆ b := symmDiff_def _ _
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ (c \ (a ⊔ b) ⊔ c ⊓ a ⊓ b) := by
        { rw [sdiff_symmDiff', sup_comm (c ⊓ a ⊓ b), symmDiff_sdiff] }
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c := by ac_rfl

中文:
定理 symmDiff_symmDiff_left
  证明: calc
    a ∆ b ∆ c = a ∆ b \ c ⊔ c \ a ∆ b := symmDiff_def _ _
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ (c \ (a ⊔ b) ⊔ c ⊓ a ⊓ b) := by
        { rw [sdiff_symmDiff', sup_comm (c ⊓ a ⊓ b), symmDiff_sdiff] }
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c := by ac_rfl

Depends on / 依赖: sdiff_symmDiff, sup_comm, symmDiff_def, symmDiff_sdiff
-/
theorem symmDiff_symmDiff_left :
    a ∆ b ∆ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c :=
  calc
    a ∆ b ∆ c = a ∆ b \ c ⊔ c \ a ∆ b := symmDiff_def _ _
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ (c \ (a ⊔ b) ⊔ c ⊓ a ⊓ b) := by
        { rw [sdiff_symmDiff', sup_comm (c ⊓ a ⊓ b), symmDiff_sdiff] }
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c := by ac_rfl

/--
theorem `symmDiff_symmDiff_right` / 定理 `symmDiff_symmDiff_right`

English:
theorem symmDiff_symmDiff_right
  proof: calc
    a ∆ (b ∆ c) = a \ b ∆ c ⊔ b ∆ c \ a := symmDiff_def _ _
    _ = a \ (b ⊔ c) ⊔ a ⊓ b ⊓ c ⊔ (b \ (c ⊔ a) ⊔ c \ (b ⊔ a)) := by
        { rw [sdiff_symmDiff', sup_comm (a ⊓ b ⊓ c), symmDiff_sdiff] }
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c := by ac_rfl

中文:
定理 symmDiff_symmDiff_right
  证明: calc
    a ∆ (b ∆ c) = a \ b ∆ c ⊔ b ∆ c \ a := symmDiff_def _ _
    _ = a \ (b ⊔ c) ⊔ a ⊓ b ⊓ c ⊔ (b \ (c ⊔ a) ⊔ c \ (b ⊔ a)) := by
        { rw [sdiff_symmDiff', sup_comm (a ⊓ b ⊓ c), symmDiff_sdiff] }
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c := by ac_rfl

Depends on / 依赖: sdiff_symmDiff, sup_comm, symmDiff_def, symmDiff_sdiff
-/
theorem symmDiff_symmDiff_right :
    a ∆ (b ∆ c) = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c :=
  calc
    a ∆ (b ∆ c) = a \ b ∆ c ⊔ b ∆ c \ a := symmDiff_def _ _
    _ = a \ (b ⊔ c) ⊔ a ⊓ b ⊓ c ⊔ (b \ (c ⊔ a) ⊔ c \ (b ⊔ a)) := by
        { rw [sdiff_symmDiff', sup_comm (a ⊓ b ⊓ c), symmDiff_sdiff] }
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c := by ac_rfl

/--
theorem `symmDiff_assoc` / 定理 `symmDiff_assoc`

English:
theorem symmDiff_assoc
  statement: a ∆ b ∆ c = a ∆ (b ∆ c)
  proof: by
  rw [symmDiff_symmDiff_left]; rw [symmDiff_symmDiff_right]

中文:
定理 symmDiff_assoc
  结论: a ∆ b ∆ c = a ∆ (b ∆ c)
  证明: by
  rw [symmDiff_symmDiff_left]; rw [symmDiff_symmDiff_right]

Depends on / 依赖: symmDiff_symmDiff_left, symmDiff_symmDiff_right
-/
theorem symmDiff_assoc : a ∆ b ∆ c = a ∆ (b ∆ c) := by
  rw [symmDiff_symmDiff_left]; rw [symmDiff_symmDiff_right]

/--
Instance `symmDiff_isAssociative` / 实例 `symmDiff_isAssociative`

English:
instance symmDiff_isAssociative
  signature: : Std.Associative (α := α) (· ∆ ·)
  body: ⟨symmDiff_assoc⟩

中文:
实例 symmDiff_isAssociative
  签名: : Std.结合 (α := α) (· ∆ ·)
  定义体: ⟨symmDiff_assoc⟩
-/
instance symmDiff_isAssociative : Std.Associative (α := α) (· ∆ ·) :=
  ⟨symmDiff_assoc⟩

/--
theorem `symmDiff_left_comm` / 定理 `symmDiff_left_comm`

English:
theorem symmDiff_left_comm
  statement: a ∆ (b ∆ c) = b ∆ (a ∆ c)
  proof: by
  simp_rw [← symmDiff_assoc, symmDiff_comm]

中文:
定理 symmDiff_left_comm
  结论: a ∆ (b ∆ c) = b ∆ (a ∆ c)
  证明: by
  simp_rw [← symmDiff_assoc, symmDiff_comm]

Depends on / 依赖: simp_rw, symmDiff_assoc, symmDiff_comm
-/
theorem symmDiff_left_comm : a ∆ (b ∆ c) = b ∆ (a ∆ c) := by
  simp_rw [← symmDiff_assoc, symmDiff_comm]

/--
theorem `symmDiff_right_comm` / 定理 `symmDiff_right_comm`

English:
theorem symmDiff_right_comm
  statement: a ∆ b ∆ c = a ∆ c ∆ b
  proof: by simp_rw [symmDiff_assoc, symmDiff_comm]

中文:
定理 symmDiff_right_comm
  结论: a ∆ b ∆ c = a ∆ c ∆ b
  证明: by simp_rw [symmDiff_assoc, symmDiff_comm]

Depends on / 依赖: simp_rw, symmDiff_assoc, symmDiff_comm
-/
theorem symmDiff_right_comm : a ∆ b ∆ c = a ∆ c ∆ b := by simp_rw [symmDiff_assoc, symmDiff_comm]

/--
theorem `symmDiff_symmDiff_symmDiff_comm` / 定理 `symmDiff_symmDiff_symmDiff_comm`

English:
theorem symmDiff_symmDiff_symmDiff_comm
  statement: a ∆ b ∆ (c ∆ d) = a ∆ c ∆ (b ∆ d)
  proof: by
  simp_rw [symmDiff_assoc, symmDiff_left_comm]

@[simp]

中文:
定理 symmDiff_symmDiff_symmDiff_comm
  结论: a ∆ b ∆ (c ∆ d) = a ∆ c ∆ (b ∆ d)
  证明: by
  simp_rw [symmDiff_assoc, symmDiff_left_comm]

@[simp]

Depends on / 依赖: simp_rw, symmDiff_assoc, symmDiff_left_comm
-/
theorem symmDiff_symmDiff_symmDiff_comm : a ∆ b ∆ (c ∆ d) = a ∆ c ∆ (b ∆ d) := by
  simp_rw [symmDiff_assoc, symmDiff_left_comm]

@[simp]
/--
theorem `symmDiff_symmDiff_cancel_left` / 定理 `symmDiff_symmDiff_cancel_left`

English:
theorem symmDiff_symmDiff_cancel_left
  statement: a ∆ (a ∆ b) = b
  proof: by simp [← symmDiff_assoc]

@[simp]

中文:
定理 symmDiff_symmDiff_cancel_left
  结论: a ∆ (a ∆ b) = b
  证明: by simp [← symmDiff_assoc]

@[simp]

Depends on / 依赖: symmDiff_assoc
-/
theorem symmDiff_symmDiff_cancel_left : a ∆ (a ∆ b) = b := by simp [← symmDiff_assoc]

@[simp]
/--
theorem `symmDiff_symmDiff_cancel_right` / 定理 `symmDiff_symmDiff_cancel_right`

English:
theorem symmDiff_symmDiff_cancel_right
  statement: b ∆ a ∆ a = b
  proof: by simp [symmDiff_assoc]

@[simp]

中文:
定理 symmDiff_symmDiff_cancel_right
  结论: b ∆ a ∆ a = b
  证明: by simp [symmDiff_assoc]

@[simp]

Depends on / 依赖: symmDiff_assoc
-/
theorem symmDiff_symmDiff_cancel_right : b ∆ a ∆ a = b := by simp [symmDiff_assoc]

@[simp]
/--
theorem `symmDiff_symmDiff_self'` / 定理 `symmDiff_symmDiff_self'`

English:
theorem symmDiff_symmDiff_self'
  statement: a ∆ b ∆ a = b
  proof: by
  rw [symmDiff_comm]; rw [symmDiff_symmDiff_cancel_left]

中文:
定理 symmDiff_symmDiff_self'
  结论: a ∆ b ∆ a = b
  证明: by
  rw [symmDiff_comm]; rw [symmDiff_symmDiff_cancel_left]

Depends on / 依赖: symmDiff_comm, symmDiff_symmDiff_cancel_left
-/
theorem symmDiff_symmDiff_self' : a ∆ b ∆ a = b := by
  rw [symmDiff_comm]; rw [symmDiff_symmDiff_cancel_left]

/--
theorem `symmDiff_left_involutive` / 定理 `symmDiff_left_involutive`

English:
theorem symmDiff_left_involutive
  given: (a : α)
  statement: Involutive (· ∆ a)
  proof: symmDiff_symmDiff_cancel_right _

中文:
定理 symmDiff_left_involutive
  条件: (a : α)
  结论: 对合 (· ∆ a)
  证明: symmDiff_symmDiff_cancel_right _

Depends on / 依赖: symmDiff_symmDiff_cancel_right
-/
theorem symmDiff_left_involutive (a : α) : Involutive (· ∆ a) :=
  symmDiff_symmDiff_cancel_right _

/--
theorem `symmDiff_right_involutive` / 定理 `symmDiff_right_involutive`

English:
theorem symmDiff_right_involutive
  given: (a : α)
  statement: Involutive (a ∆ ·)
  proof: symmDiff_symmDiff_cancel_left _

中文:
定理 symmDiff_right_involutive
  条件: (a : α)
  结论: 对合 (a ∆ ·)
  证明: symmDiff_symmDiff_cancel_left _

Depends on / 依赖: symmDiff_symmDiff_cancel_left
-/
theorem symmDiff_right_involutive (a : α) : Involutive (a ∆ ·) :=
  symmDiff_symmDiff_cancel_left _

/--
theorem `symmDiff_left_injective` / 定理 `symmDiff_left_injective`

English:
theorem symmDiff_left_injective
  given: (a : α)
  statement: Injective (· ∆ a)
  proof: Function.Involutive.injective (symmDiff_left_involutive a)

中文:
定理 symmDiff_left_injective
  条件: (a : α)
  结论: 单射 (· ∆ a)
  证明: Function.Involutive.injective (symmDiff_left_involutive a)

Depends on / 依赖: Function, Function.Involutive.injective, Involutive, injective, symmDiff_left_involutive
-/
theorem symmDiff_left_injective (a : α) : Injective (· ∆ a) :=
  Function.Involutive.injective (symmDiff_left_involutive a)

/--
theorem `symmDiff_right_injective` / 定理 `symmDiff_right_injective`

English:
theorem symmDiff_right_injective
  given: (a : α)
  statement: Injective (a ∆ ·)
  proof: Function.Involutive.injective (symmDiff_right_involutive _)

中文:
定理 symmDiff_right_injective
  条件: (a : α)
  结论: 单射 (a ∆ ·)
  证明: Function.Involutive.injective (symmDiff_right_involutive _)

Depends on / 依赖: Function, Function.Involutive.injective, Involutive, injective, symmDiff_right_involutive
-/
theorem symmDiff_right_injective (a : α) : Injective (a ∆ ·) :=
  Function.Involutive.injective (symmDiff_right_involutive _)

/--
theorem `symmDiff_left_surjective` / 定理 `symmDiff_left_surjective`

English:
theorem symmDiff_left_surjective
  given: (a : α)
  statement: Surjective (· ∆ a)
  proof: Function.Involutive.surjective (symmDiff_left_involutive _)

中文:
定理 symmDiff_left_surjective
  条件: (a : α)
  结论: 满射 (· ∆ a)
  证明: Function.Involutive.surjective (symmDiff_left_involutive _)

Depends on / 依赖: Function, Function.Involutive.surjective, Involutive, surjective, symmDiff_left_involutive
-/
theorem symmDiff_left_surjective (a : α) : Surjective (· ∆ a) :=
  Function.Involutive.surjective (symmDiff_left_involutive _)

/--
theorem `symmDiff_right_surjective` / 定理 `symmDiff_right_surjective`

English:
theorem symmDiff_right_surjective
  given: (a : α)
  statement: Surjective (a ∆ ·)
  proof: Function.Involutive.surjective (symmDiff_right_involutive _)

中文:
定理 symmDiff_right_surjective
  条件: (a : α)
  结论: 满射 (a ∆ ·)
  证明: Function.Involutive.surjective (symmDiff_right_involutive _)

Depends on / 依赖: Function, Function.Involutive.surjective, Involutive, surjective, symmDiff_right_involutive
-/
theorem symmDiff_right_surjective (a : α) : Surjective (a ∆ ·) :=
  Function.Involutive.surjective (symmDiff_right_involutive _)

variable {a b c}

@[simp]
/--
theorem `symmDiff_left_inj` / 定理 `symmDiff_left_inj`

English:
theorem symmDiff_left_inj
  statement: a ∆ b = c ∆ b ↔ a = c
  proof: (symmDiff_left_injective _).eq_iff

@[simp]

中文:
定理 symmDiff_left_inj
  结论: a ∆ b = c ∆ b ↔ a = c
  证明: (symmDiff_left_injective _).eq_iff

@[simp]

Depends on / 依赖: eq_iff, symmDiff_left_injective
-/
theorem symmDiff_left_inj : a ∆ b = c ∆ b ↔ a = c :=
  (symmDiff_left_injective _).eq_iff

@[simp]
/--
theorem `symmDiff_right_inj` / 定理 `symmDiff_right_inj`

English:
theorem symmDiff_right_inj
  statement: a ∆ b = a ∆ c ↔ b = c
  proof: (symmDiff_right_injective _).eq_iff

@[simp]

中文:
定理 symmDiff_right_inj
  结论: a ∆ b = a ∆ c ↔ b = c
  证明: (symmDiff_right_injective _).eq_iff

@[simp]

Depends on / 依赖: eq_iff, symmDiff_right_injective
-/
theorem symmDiff_right_inj : a ∆ b = a ∆ c ↔ b = c :=
  (symmDiff_right_injective _).eq_iff

@[simp]
/--
theorem `symmDiff_eq_left` / 定理 `symmDiff_eq_left`

English:
theorem symmDiff_eq_left
  statement: a ∆ b = a ↔ b = ⊥
  proof: calc
    a ∆ b = a ↔ a ∆ b = a ∆ ⊥ := by rw [symmDiff_bot]
    _ ↔ b = ⊥ := by rw [symmDiff_right_inj]

@[simp]

中文:
定理 symmDiff_eq_left
  结论: a ∆ b = a ↔ b = ⊥
  证明: calc
    a ∆ b = a ↔ a ∆ b = a ∆ ⊥ := by rw [symmDiff_bot]
    _ ↔ b = ⊥ := by rw [symmDiff_right_inj]

@[simp]

Depends on / 依赖: symmDiff_bot, symmDiff_right_inj
-/
theorem symmDiff_eq_left : a ∆ b = a ↔ b = ⊥ :=
  calc
    a ∆ b = a ↔ a ∆ b = a ∆ ⊥ := by rw [symmDiff_bot]
    _ ↔ b = ⊥ := by rw [symmDiff_right_inj]

@[simp]
/--
theorem `symmDiff_eq_right` / 定理 `symmDiff_eq_right`

English:
theorem symmDiff_eq_right
  statement: a ∆ b = b ↔ a = ⊥
  proof: by rw [symmDiff_comm, symmDiff_eq_left]

中文:
定理 symmDiff_eq_right
  结论: a ∆ b = b ↔ a = ⊥
  证明: by rw [symmDiff_comm, symmDiff_eq_left]

Depends on / 依赖: symmDiff_comm, symmDiff_eq_left
-/
theorem symmDiff_eq_right : a ∆ b = b ↔ a = ⊥ := by rw [symmDiff_comm, symmDiff_eq_left]

/--
theorem `Disjoint.symmDiff_left` / 定理 `Disjoint.symmDiff_left`

English:
theorem Disjoint.symmDiff_left
  given: (ha : Disjoint a c) (hb : Disjoint b c)
  proof: by
  rw [symmDiff_eq_sup_sdiff_inf]
  exact (ha.sup_left hb).disjoint_sdiff_left

中文:
定理 Disjoint.symmDiff_left
  条件: (ha : Disjoint a c) (hb : Disjoint b c)
  证明: by
  rw [symmDiff_eq_sup_sdiff_inf]
  exact (ha.sup_left hb).disjoint_sdiff_left
-/
protected theorem Disjoint.symmDiff_left (ha : Disjoint a c) (hb : Disjoint b c) :
    Disjoint (a ∆ b) c := by
  rw [symmDiff_eq_sup_sdiff_inf]
  exact (ha.sup_left hb).disjoint_sdiff_left

/--
theorem `Disjoint.symmDiff_right` / 定理 `Disjoint.symmDiff_right`

English:
theorem Disjoint.symmDiff_right
  given: (ha : Disjoint a b) (hb : Disjoint a c)
  proof: (ha.symm.symmDiff_left hb.symm).symm

中文:
定理 Disjoint.symmDiff_right
  条件: (ha : Disjoint a b) (hb : Disjoint a c)
  证明: (ha.symm.symmDiff_left hb.symm).symm
-/
protected theorem Disjoint.symmDiff_right (ha : Disjoint a b) (hb : Disjoint a c) :
    Disjoint a (b ∆ c) :=
  (ha.symm.symmDiff_left hb.symm).symm

/--
theorem `symmDiff_eq_iff_sdiff_eq` / 定理 `symmDiff_eq_iff_sdiff_eq`

English:
theorem symmDiff_eq_iff_sdiff_eq
  given: (ha : a <= c)
  statement: a ∆ b = c ↔ c \ a = b
  proof: by
  rw [← symmDiff_of_le ha]
  exact ((symmDiff_right_involutive a).toPerm _).eq_symm_apply.symm.trans eq_comm

中文:
定理 symmDiff_eq_iff_sdiff_eq
  条件: (ha : a <= c)
  结论: a ∆ b = c ↔ c \ a = b
  证明: by
  rw [← symmDiff_of_le ha]
  exact ((symmDiff_right_involutive a).toPerm _).eq_symm_apply.symm.trans eq_comm

Depends on / 依赖: eq_comm, eq_symm_apply, eq_symm_apply.symm.trans, symmDiff_of_le, symmDiff_right_involutive, toPerm
-/
theorem symmDiff_eq_iff_sdiff_eq (ha : a <= c) : a ∆ b = c ↔ c \ a = b := by
  rw [← symmDiff_of_le ha]
  exact ((symmDiff_right_involutive a).toPerm _).eq_symm_apply.symm.trans eq_comm

end GeneralizedBooleanAlgebra

section BooleanAlgebra

variable [BooleanAlgebra α] (a b c d : α)

/-! `CogeneralizedBooleanAlgebra` isn't actually a typeclass, but the lemmas in here are dual to
the `GeneralizedBooleanAlgebra` ones -/
section CogeneralizedBooleanAlgebra

@[simp]
/--
theorem `inf_himp_bihimp` / 定理 `inf_himp_bihimp`

English:
theorem inf_himp_bihimp
  statement: a ⇔ b ⇨ a ⊓ b = a ⊔ b
  proof: @sup_sdiff_symmDiff αᵒᵈ _ _ _

中文:
定理 inf_himp_bihimp
  结论: a ⇔ b ⇨ a ⊓ b = a ⊔ b
  证明: @sup_sdiff_symmDiff αᵒᵈ _ _ _

Depends on / 依赖: sup_sdiff_symmDiff
-/
theorem inf_himp_bihimp : a ⇔ b ⇨ a ⊓ b = a ⊔ b :=
  @sup_sdiff_symmDiff αᵒᵈ _ _ _

/--
theorem `codisjoint_bihimp_sup` / 定理 `codisjoint_bihimp_sup`

English:
theorem codisjoint_bihimp_sup
  statement: Codisjoint (a ⇔ b) (a ⊔ b)
  proof: @disjoint_symmDiff_inf αᵒᵈ _ _ _

@[simp]

中文:
定理 codisjoint_bihimp_sup
  结论: Codisjoint (a ⇔ b) (a ⊔ b)
  证明: @disjoint_symmDiff_inf αᵒᵈ _ _ _

@[simp]

Depends on / 依赖: disjoint_symmDiff_inf
-/
theorem codisjoint_bihimp_sup : Codisjoint (a ⇔ b) (a ⊔ b) :=
  @disjoint_symmDiff_inf αᵒᵈ _ _ _

@[simp]
/--
theorem `himp_bihimp_left` / 定理 `himp_bihimp_left`

English:
theorem himp_bihimp_left
  statement: a ⇨ a ⇔ b = a ⇨ b
  proof: @symmDiff_sdiff_left αᵒᵈ _ _ _

@[simp]

中文:
定理 himp_bihimp_left
  结论: a ⇨ a ⇔ b = a ⇨ b
  证明: @symmDiff_sdiff_left αᵒᵈ _ _ _

@[simp]

Depends on / 依赖: symmDiff_sdiff_left
-/
theorem himp_bihimp_left : a ⇨ a ⇔ b = a ⇨ b :=
  @symmDiff_sdiff_left αᵒᵈ _ _ _

@[simp]
/--
theorem `himp_bihimp_right` / 定理 `himp_bihimp_right`

English:
theorem himp_bihimp_right
  statement: b ⇨ a ⇔ b = b ⇨ a
  proof: @symmDiff_sdiff_right αᵒᵈ _ _ _

@[simp]

中文:
定理 himp_bihimp_right
  结论: b ⇨ a ⇔ b = b ⇨ a
  证明: @symmDiff_sdiff_right αᵒᵈ _ _ _

@[simp]

Depends on / 依赖: symmDiff_sdiff_right
-/
theorem himp_bihimp_right : b ⇨ a ⇔ b = b ⇨ a :=
  @symmDiff_sdiff_right αᵒᵈ _ _ _

@[simp]
/--
theorem `bihimp_himp_left` / 定理 `bihimp_himp_left`

English:
theorem bihimp_himp_left
  statement: a ⇔ b ⇨ a = a ⊔ b
  proof: @sdiff_symmDiff_left αᵒᵈ _ _ _

@[simp]

中文:
定理 bihimp_himp_left
  结论: a ⇔ b ⇨ a = a ⊔ b
  证明: @sdiff_symmDiff_left αᵒᵈ _ _ _

@[simp]

Depends on / 依赖: sdiff_symmDiff_left
-/
theorem bihimp_himp_left : a ⇔ b ⇨ a = a ⊔ b :=
  @sdiff_symmDiff_left αᵒᵈ _ _ _

@[simp]
/--
theorem `bihimp_himp_right` / 定理 `bihimp_himp_right`

English:
theorem bihimp_himp_right
  statement: a ⇔ b ⇨ b = a ⊔ b
  proof: @sdiff_symmDiff_right αᵒᵈ _ _ _

@[simp]

中文:
定理 bihimp_himp_right
  结论: a ⇔ b ⇨ b = a ⊔ b
  证明: @sdiff_symmDiff_right αᵒᵈ _ _ _

@[simp]

Depends on / 依赖: sdiff_symmDiff_right
-/
theorem bihimp_himp_right : a ⇔ b ⇨ b = a ⊔ b :=
  @sdiff_symmDiff_right αᵒᵈ _ _ _

@[simp]
/--
theorem `bihimp_eq_inf` / 定理 `bihimp_eq_inf`

English:
theorem bihimp_eq_inf
  statement: a ⇔ b = a ⊓ b ↔ Codisjoint a b
  proof: @symmDiff_eq_sup αᵒᵈ _ _ _

@[simp]

中文:
定理 bihimp_eq_inf
  结论: a ⇔ b = a ⊓ b ↔ Codisjoint a b
  证明: @symmDiff_eq_sup αᵒᵈ _ _ _

@[simp]

Depends on / 依赖: symmDiff_eq_sup
-/
theorem bihimp_eq_inf : a ⇔ b = a ⊓ b ↔ Codisjoint a b :=
  @symmDiff_eq_sup αᵒᵈ _ _ _

@[simp]
/--
theorem `bihimp_le_iff_left` / 定理 `bihimp_le_iff_left`

English:
theorem bihimp_le_iff_left
  statement: a ⇔ b <= a ↔ Codisjoint a b
  proof: @le_symmDiff_iff_left αᵒᵈ _ _ _

@[simp]

中文:
定理 bihimp_le_iff_left
  结论: a ⇔ b <= a ↔ Codisjoint a b
  证明: @le_symmDiff_iff_left αᵒᵈ _ _ _

@[simp]

Depends on / 依赖: le_symmDiff_iff_left
-/
theorem bihimp_le_iff_left : a ⇔ b <= a ↔ Codisjoint a b :=
  @le_symmDiff_iff_left αᵒᵈ _ _ _

@[simp]
/--
theorem `bihimp_le_iff_right` / 定理 `bihimp_le_iff_right`

English:
theorem bihimp_le_iff_right
  statement: a ⇔ b <= b ↔ Codisjoint a b
  proof: @le_symmDiff_iff_right αᵒᵈ _ _ _

中文:
定理 bihimp_le_iff_right
  结论: a ⇔ b <= b ↔ Codisjoint a b
  证明: @le_symmDiff_iff_right αᵒᵈ _ _ _

Depends on / 依赖: le_symmDiff_iff_right
-/
theorem bihimp_le_iff_right : a ⇔ b <= b ↔ Codisjoint a b :=
  @le_symmDiff_iff_right αᵒᵈ _ _ _

/--
theorem `bihimp_assoc` / 定理 `bihimp_assoc`

English:
theorem bihimp_assoc
  statement: a ⇔ b ⇔ c = a ⇔ (b ⇔ c)
  proof: @symmDiff_assoc αᵒᵈ _ _ _ _

中文:
定理 bihimp_assoc
  结论: a ⇔ b ⇔ c = a ⇔ (b ⇔ c)
  证明: @symmDiff_assoc αᵒᵈ _ _ _ _

Depends on / 依赖: symmDiff_assoc
-/
theorem bihimp_assoc : a ⇔ b ⇔ c = a ⇔ (b ⇔ c) :=
  @symmDiff_assoc αᵒᵈ _ _ _ _

/--
Instance `bihimp_isAssociative` / 实例 `bihimp_isAssociative`

English:
instance bihimp_isAssociative
  signature: : Std.Associative (α := α) (· ⇔ ·)
  body: ⟨bihimp_assoc⟩

中文:
实例 bihimp_isAssociative
  签名: : Std.结合 (α := α) (· ⇔ ·)
  定义体: ⟨bihimp_assoc⟩
-/
instance bihimp_isAssociative : Std.Associative (α := α) (· ⇔ ·) :=
  ⟨bihimp_assoc⟩

/--
theorem `bihimp_left_comm` / 定理 `bihimp_left_comm`

English:
theorem bihimp_left_comm
  statement: a ⇔ (b ⇔ c) = b ⇔ (a ⇔ c)
  proof: by simp_rw [← bihimp_assoc, bihimp_comm]

中文:
定理 bihimp_left_comm
  结论: a ⇔ (b ⇔ c) = b ⇔ (a ⇔ c)
  证明: by simp_rw [← bihimp_assoc, bihimp_comm]

Depends on / 依赖: bihimp_assoc, bihimp_comm, simp_rw
-/
theorem bihimp_left_comm : a ⇔ (b ⇔ c) = b ⇔ (a ⇔ c) := by simp_rw [← bihimp_assoc, bihimp_comm]

/--
theorem `bihimp_right_comm` / 定理 `bihimp_right_comm`

English:
theorem bihimp_right_comm
  statement: a ⇔ b ⇔ c = a ⇔ c ⇔ b
  proof: by simp_rw [bihimp_assoc, bihimp_comm]

中文:
定理 bihimp_right_comm
  结论: a ⇔ b ⇔ c = a ⇔ c ⇔ b
  证明: by simp_rw [bihimp_assoc, bihimp_comm]

Depends on / 依赖: bihimp_assoc, bihimp_comm, simp_rw
-/
theorem bihimp_right_comm : a ⇔ b ⇔ c = a ⇔ c ⇔ b := by simp_rw [bihimp_assoc, bihimp_comm]

/--
theorem `bihimp_bihimp_bihimp_comm` / 定理 `bihimp_bihimp_bihimp_comm`

English:
theorem bihimp_bihimp_bihimp_comm
  statement: a ⇔ b ⇔ (c ⇔ d) = a ⇔ c ⇔ (b ⇔ d)
  proof: by
  simp_rw [bihimp_assoc, bihimp_left_comm]

@[simp]

中文:
定理 bihimp_bihimp_bihimp_comm
  结论: a ⇔ b ⇔ (c ⇔ d) = a ⇔ c ⇔ (b ⇔ d)
  证明: by
  simp_rw [bihimp_assoc, bihimp_left_comm]

@[simp]

Depends on / 依赖: bihimp_assoc, bihimp_left_comm, simp_rw
-/
theorem bihimp_bihimp_bihimp_comm : a ⇔ b ⇔ (c ⇔ d) = a ⇔ c ⇔ (b ⇔ d) := by
  simp_rw [bihimp_assoc, bihimp_left_comm]

@[simp]
/--
theorem `bihimp_bihimp_cancel_left` / 定理 `bihimp_bihimp_cancel_left`

English:
theorem bihimp_bihimp_cancel_left
  statement: a ⇔ (a ⇔ b) = b
  proof: by simp [← bihimp_assoc]

@[simp]

中文:
定理 bihimp_bihimp_cancel_left
  结论: a ⇔ (a ⇔ b) = b
  证明: by simp [← bihimp_assoc]

@[simp]

Depends on / 依赖: bihimp_assoc
-/
theorem bihimp_bihimp_cancel_left : a ⇔ (a ⇔ b) = b := by simp [← bihimp_assoc]

@[simp]
/--
theorem `bihimp_bihimp_cancel_right` / 定理 `bihimp_bihimp_cancel_right`

English:
theorem bihimp_bihimp_cancel_right
  statement: b ⇔ a ⇔ a = b
  proof: by simp [bihimp_assoc]

@[simp]

中文:
定理 bihimp_bihimp_cancel_right
  结论: b ⇔ a ⇔ a = b
  证明: by simp [bihimp_assoc]

@[simp]

Depends on / 依赖: bihimp_assoc
-/
theorem bihimp_bihimp_cancel_right : b ⇔ a ⇔ a = b := by simp [bihimp_assoc]

@[simp]
/--
theorem `bihimp_bihimp_self` / 定理 `bihimp_bihimp_self`

English:
theorem bihimp_bihimp_self
  statement: a ⇔ b ⇔ a = b
  proof: by rw [bihimp_comm, bihimp_bihimp_cancel_left]

中文:
定理 bihimp_bihimp_self
  结论: a ⇔ b ⇔ a = b
  证明: by rw [bihimp_comm, bihimp_bihimp_cancel_left]

Depends on / 依赖: bihimp_bihimp_cancel_left, bihimp_comm
-/
theorem bihimp_bihimp_self : a ⇔ b ⇔ a = b := by rw [bihimp_comm, bihimp_bihimp_cancel_left]

/--
theorem `bihimp_left_involutive` / 定理 `bihimp_left_involutive`

English:
theorem bihimp_left_involutive
  given: (a : α)
  statement: Involutive (· ⇔ a)
  proof: bihimp_bihimp_cancel_right _

中文:
定理 bihimp_left_involutive
  条件: (a : α)
  结论: 对合 (· ⇔ a)
  证明: bihimp_bihimp_cancel_right _

Depends on / 依赖: bihimp_bihimp_cancel_right
-/
theorem bihimp_left_involutive (a : α) : Involutive (· ⇔ a) :=
  bihimp_bihimp_cancel_right _

/--
theorem `bihimp_right_involutive` / 定理 `bihimp_right_involutive`

English:
theorem bihimp_right_involutive
  given: (a : α)
  statement: Involutive (a ⇔ ·)
  proof: bihimp_bihimp_cancel_left _

中文:
定理 bihimp_right_involutive
  条件: (a : α)
  结论: 对合 (a ⇔ ·)
  证明: bihimp_bihimp_cancel_left _

Depends on / 依赖: bihimp_bihimp_cancel_left
-/
theorem bihimp_right_involutive (a : α) : Involutive (a ⇔ ·) :=
  bihimp_bihimp_cancel_left _

/--
theorem `bihimp_left_injective` / 定理 `bihimp_left_injective`

English:
theorem bihimp_left_injective
  given: (a : α)
  statement: Injective (· ⇔ a)
  proof: @symmDiff_left_injective αᵒᵈ _ _

中文:
定理 bihimp_left_injective
  条件: (a : α)
  结论: 单射 (· ⇔ a)
  证明: @symmDiff_left_injective αᵒᵈ _ _

Depends on / 依赖: symmDiff_left_injective
-/
theorem bihimp_left_injective (a : α) : Injective (· ⇔ a) :=
  @symmDiff_left_injective αᵒᵈ _ _

/--
theorem `bihimp_right_injective` / 定理 `bihimp_right_injective`

English:
theorem bihimp_right_injective
  given: (a : α)
  statement: Injective (a ⇔ ·)
  proof: @symmDiff_right_injective αᵒᵈ _ _

中文:
定理 bihimp_right_injective
  条件: (a : α)
  结论: 单射 (a ⇔ ·)
  证明: @symmDiff_right_injective αᵒᵈ _ _

Depends on / 依赖: symmDiff_right_injective
-/
theorem bihimp_right_injective (a : α) : Injective (a ⇔ ·) :=
  @symmDiff_right_injective αᵒᵈ _ _

/--
theorem `bihimp_left_surjective` / 定理 `bihimp_left_surjective`

English:
theorem bihimp_left_surjective
  given: (a : α)
  statement: Surjective (· ⇔ a)
  proof: @symmDiff_left_surjective αᵒᵈ _ _

中文:
定理 bihimp_left_surjective
  条件: (a : α)
  结论: 满射 (· ⇔ a)
  证明: @symmDiff_left_surjective αᵒᵈ _ _

Depends on / 依赖: symmDiff_left_surjective
-/
theorem bihimp_left_surjective (a : α) : Surjective (· ⇔ a) :=
  @symmDiff_left_surjective αᵒᵈ _ _

/--
theorem `bihimp_right_surjective` / 定理 `bihimp_right_surjective`

English:
theorem bihimp_right_surjective
  given: (a : α)
  statement: Surjective (a ⇔ ·)
  proof: @symmDiff_right_surjective αᵒᵈ _ _

中文:
定理 bihimp_right_surjective
  条件: (a : α)
  结论: 满射 (a ⇔ ·)
  证明: @symmDiff_right_surjective αᵒᵈ _ _

Depends on / 依赖: symmDiff_right_surjective
-/
theorem bihimp_right_surjective (a : α) : Surjective (a ⇔ ·) :=
  @symmDiff_right_surjective αᵒᵈ _ _

variable {a b c}

@[simp]
/--
theorem `bihimp_left_inj` / 定理 `bihimp_left_inj`

English:
theorem bihimp_left_inj
  statement: a ⇔ b = c ⇔ b ↔ a = c
  proof: (bihimp_left_injective _).eq_iff

@[simp]

中文:
定理 bihimp_left_inj
  结论: a ⇔ b = c ⇔ b ↔ a = c
  证明: (bihimp_left_injective _).eq_iff

@[simp]

Depends on / 依赖: bihimp_left_injective, eq_iff
-/
theorem bihimp_left_inj : a ⇔ b = c ⇔ b ↔ a = c :=
  (bihimp_left_injective _).eq_iff

@[simp]
/--
theorem `bihimp_right_inj` / 定理 `bihimp_right_inj`

English:
theorem bihimp_right_inj
  statement: a ⇔ b = a ⇔ c ↔ b = c
  proof: (bihimp_right_injective _).eq_iff

@[simp]

中文:
定理 bihimp_right_inj
  结论: a ⇔ b = a ⇔ c ↔ b = c
  证明: (bihimp_right_injective _).eq_iff

@[simp]

Depends on / 依赖: bihimp_right_injective, eq_iff
-/
theorem bihimp_right_inj : a ⇔ b = a ⇔ c ↔ b = c :=
  (bihimp_right_injective _).eq_iff

@[simp]
/--
theorem `bihimp_eq_left` / 定理 `bihimp_eq_left`

English:
theorem bihimp_eq_left
  statement: a ⇔ b = a ↔ b = ⊤
  proof: @symmDiff_eq_left αᵒᵈ _ _ _

@[simp]

中文:
定理 bihimp_eq_left
  结论: a ⇔ b = a ↔ b = ⊤
  证明: @symmDiff_eq_left αᵒᵈ _ _ _

@[simp]

Depends on / 依赖: symmDiff_eq_left
-/
theorem bihimp_eq_left : a ⇔ b = a ↔ b = ⊤ :=
  @symmDiff_eq_left αᵒᵈ _ _ _

@[simp]
/--
theorem `bihimp_eq_right` / 定理 `bihimp_eq_right`

English:
theorem bihimp_eq_right
  statement: a ⇔ b = b ↔ a = ⊤
  proof: @symmDiff_eq_right αᵒᵈ _ _ _

中文:
定理 bihimp_eq_right
  结论: a ⇔ b = b ↔ a = ⊤
  证明: @symmDiff_eq_right αᵒᵈ _ _ _

Depends on / 依赖: symmDiff_eq_right
-/
theorem bihimp_eq_right : a ⇔ b = b ↔ a = ⊤ :=
  @symmDiff_eq_right αᵒᵈ _ _ _

/--
theorem `Codisjoint.bihimp_left` / 定理 `Codisjoint.bihimp_left`

English:
theorem Codisjoint.bihimp_left
  given: (ha : Codisjoint a c) (hb : Codisjoint b c)
  proof: (ha.inf_left hb).mono_left inf_le_bihimp

中文:
定理 Codisjoint.bihimp_left
  条件: (ha : Codisjoint a c) (hb : Codisjoint b c)
  证明: (ha.inf_left hb).mono_left inf_le_bihimp
-/
protected theorem Codisjoint.bihimp_left (ha : Codisjoint a c) (hb : Codisjoint b c) :
    Codisjoint (a ⇔ b) c :=
  (ha.inf_left hb).mono_left inf_le_bihimp

/--
theorem `Codisjoint.bihimp_right` / 定理 `Codisjoint.bihimp_right`

English:
theorem Codisjoint.bihimp_right
  given: (ha : Codisjoint a b) (hb : Codisjoint a c)
  proof: (ha.inf_right hb).mono_right inf_le_bihimp

中文:
定理 Codisjoint.bihimp_right
  条件: (ha : Codisjoint a b) (hb : Codisjoint a c)
  证明: (ha.inf_right hb).mono_right inf_le_bihimp
-/
protected theorem Codisjoint.bihimp_right (ha : Codisjoint a b) (hb : Codisjoint a c) :
    Codisjoint a (b ⇔ c) :=
  (ha.inf_right hb).mono_right inf_le_bihimp

end CogeneralizedBooleanAlgebra

/--
theorem `symmDiff_eq` / 定理 `symmDiff_eq`

English:
theorem symmDiff_eq
  statement: a ∆ b = a ⊓ bᶜ ⊔ b ⊓ aᶜ
  proof: by simp only [(· ∆ ·), sdiff_eq]

中文:
定理 symmDiff_eq
  结论: a ∆ b = a ⊓ bᶜ ⊔ b ⊓ aᶜ
  证明: by simp only [(· ∆ ·), sdiff_eq]

Depends on / 依赖: sdiff_eq
-/
theorem symmDiff_eq : a ∆ b = a ⊓ bᶜ ⊔ b ⊓ aᶜ := by simp only [(· ∆ ·), sdiff_eq]

/--
theorem `bihimp_eq` / 定理 `bihimp_eq`

English:
theorem bihimp_eq
  statement: a ⇔ b = (a ⊔ bᶜ) ⊓ (b ⊔ aᶜ)
  proof: by simp only [(· ⇔ ·), himp_eq]

中文:
定理 bihimp_eq
  结论: a ⇔ b = (a ⊔ bᶜ) ⊓ (b ⊔ aᶜ)
  证明: by simp only [(· ⇔ ·), himp_eq]

Depends on / 依赖: Module, himp_eq
-/
theorem bihimp_eq : a ⇔ b = (a ⊔ bᶜ) ⊓ (b ⊔ aᶜ) := by simp only [(· ⇔ ·), himp_eq]

/--
theorem `symmDiff_eq'` / 定理 `symmDiff_eq'`

English:
theorem symmDiff_eq'
  statement: a ∆ b = (a ⊔ b) ⊓ (aᶜ ⊔ bᶜ)
  proof: by
  rw [symmDiff_eq_sup_sdiff_inf]; rw [sdiff_eq]; rw [compl_inf]

中文:
定理 symmDiff_eq'
  结论: a ∆ b = (a ⊔ b) ⊓ (aᶜ ⊔ bᶜ)
  证明: by
  rw [symmDiff_eq_sup_sdiff_inf]; rw [sdiff_eq]; rw [compl_inf]

Depends on / 依赖: IsScalarTower, compl_inf, sdiff_eq, symmDiff_eq_sup_sdiff_inf
-/
theorem symmDiff_eq' : a ∆ b = (a ⊔ b) ⊓ (aᶜ ⊔ bᶜ) := by
  rw [symmDiff_eq_sup_sdiff_inf]; rw [sdiff_eq]; rw [compl_inf]

/--
theorem `bihimp_eq'` / 定理 `bihimp_eq'`

English:
theorem bihimp_eq'
  statement: a ⇔ b = a ⊓ b ⊔ aᶜ ⊓ bᶜ
  proof: @symmDiff_eq' αᵒᵈ _ _ _

@[simp]

中文:
定理 bihimp_eq'
  结论: a ⇔ b = a ⊓ b ⊔ aᶜ ⊓ bᶜ
  证明: @symmDiff_eq' αᵒᵈ _ _ _

@[simp]

Depends on / 依赖: symmDiff_eq
-/
theorem bihimp_eq' : a ⇔ b = a ⊓ b ⊔ aᶜ ⊓ bᶜ :=
  @symmDiff_eq' αᵒᵈ _ _ _

@[simp]
/--
theorem `compl_symmDiff` / 定理 `compl_symmDiff`

English:
theorem compl_symmDiff
  statement: (a ∆ b)ᶜ = a ⇔ b
  proof: by
  simp_rw [symmDiff, compl_sup_distrib, compl_sdiff, bihimp, inf_comm]

@[simp]

中文:
定理 compl_symmDiff
  结论: (a ∆ b)ᶜ = a ⇔ b
  证明: by
  simp_rw [symmDiff, compl_sup_distrib, compl_sdiff, bihimp, inf_comm]

@[simp]

Depends on / 依赖: bihimp, compl_sdiff, compl_sup_distrib, inf_comm, simp_rw, symmDiff
-/
theorem compl_symmDiff : (a ∆ b)ᶜ = a ⇔ b := by
  simp_rw [symmDiff, compl_sup_distrib, compl_sdiff, bihimp, inf_comm]

@[simp]
/--
theorem `compl_bihimp` / 定理 `compl_bihimp`

English:
theorem compl_bihimp
  statement: (a ⇔ b)ᶜ = a ∆ b
  proof: @compl_symmDiff αᵒᵈ _ _ _

@[simp]

中文:
定理 compl_bihimp
  结论: (a ⇔ b)ᶜ = a ∆ b
  证明: @compl_symmDiff αᵒᵈ _ _ _

@[simp]

Depends on / 依赖: compl_symmDiff
-/
theorem compl_bihimp : (a ⇔ b)ᶜ = a ∆ b :=
  @compl_symmDiff αᵒᵈ _ _ _

@[simp]
/--
theorem `compl_symmDiff_compl` / 定理 `compl_symmDiff_compl`

English:
theorem compl_symmDiff_compl
  statement: aᶜ ∆ bᶜ = a ∆ b
  proof: (sup_comm _ _).trans by simp_rw [compl_sdiff_compl, sdiff_eq, symmDiff_eq]

@[simp]

中文:
定理 compl_symmDiff_compl
  结论: aᶜ ∆ bᶜ = a ∆ b
  证明: (sup_comm _ _).trans by simp_rw [compl_sdiff_compl, sdiff_eq, symmDiff_eq]

@[simp]

Depends on / 依赖: compl_sdiff_compl, sdiff_eq, simp_rw, sup_comm, symmDiff_eq
-/
theorem compl_symmDiff_compl : aᶜ ∆ bᶜ = a ∆ b :=
(sup_comm _ _).trans by simp_rw [compl_sdiff_compl, sdiff_eq, symmDiff_eq]

@[simp]
/--
theorem `compl_bihimp_compl` / 定理 `compl_bihimp_compl`

English:
theorem compl_bihimp_compl
  statement: aᶜ ⇔ bᶜ = a ⇔ b
  proof: @compl_symmDiff_compl αᵒᵈ _ _ _

@[simp]

中文:
定理 compl_bihimp_compl
  结论: aᶜ ⇔ bᶜ = a ⇔ b
  证明: @compl_symmDiff_compl αᵒᵈ _ _ _

@[simp]

Depends on / 依赖: compl_symmDiff_compl
-/
theorem compl_bihimp_compl : aᶜ ⇔ bᶜ = a ⇔ b :=
  @compl_symmDiff_compl αᵒᵈ _ _ _

@[simp]
/--
theorem `symmDiff_eq_top` / 定理 `symmDiff_eq_top`

English:
theorem symmDiff_eq_top
  statement: a ∆ b = ⊤ ↔ IsCompl a b
  proof: by
  rw [symmDiff_eq']; rw [← compl_inf]; rw [inf_eq_top_iff]; rw [compl_eq_top]; rw [isCompl_iff]; rw [disjoint_iff]; rw [codisjoint_iff]; rw [and_comm]

@[simp]

中文:
定理 symmDiff_eq_top
  结论: a ∆ b = ⊤ ↔ 是补集 a b
  证明: by
  rw [symmDiff_eq']; rw [← compl_inf]; rw [inf_eq_top_iff]; rw [compl_eq_top]; rw [isCompl_iff]; rw [disjoint_iff]; rw [codisjoint_iff]; rw [and_comm]

@[simp]

Depends on / 依赖: and_comm, codisjoint_iff, compl_eq_top, compl_inf, disjoint_iff, inf_eq_top_iff, isCompl_iff, symmDiff_eq
-/
theorem symmDiff_eq_top : a ∆ b = ⊤ ↔ IsCompl a b := by
  rw [symmDiff_eq']; rw [← compl_inf]; rw [inf_eq_top_iff]; rw [compl_eq_top]; rw [isCompl_iff]; rw [disjoint_iff]; rw [codisjoint_iff]; rw [and_comm]

@[simp]
/--
theorem `bihimp_eq_bot` / 定理 `bihimp_eq_bot`

English:
theorem bihimp_eq_bot
  statement: a ⇔ b = ⊥ ↔ IsCompl a b
  proof: by
  rw [bihimp_eq']; rw [← compl_sup]; rw [sup_eq_bot_iff]; rw [compl_eq_bot]; rw [isCompl_iff]; rw [disjoint_iff]; rw [codisjoint_iff]

@[simp]

中文:
定理 bihimp_eq_bot
  结论: a ⇔ b = ⊥ ↔ 是补集 a b
  证明: by
  rw [bihimp_eq']; rw [← compl_sup]; rw [sup_eq_bot_iff]; rw [compl_eq_bot]; rw [isCompl_iff]; rw [disjoint_iff]; rw [codisjoint_iff]

@[simp]

Depends on / 依赖: bihimp_eq, codisjoint_iff, compl_eq_bot, compl_sup, disjoint_iff, isCompl_iff, sup_eq_bot_iff
-/
theorem bihimp_eq_bot : a ⇔ b = ⊥ ↔ IsCompl a b := by
  rw [bihimp_eq']; rw [← compl_sup]; rw [sup_eq_bot_iff]; rw [compl_eq_bot]; rw [isCompl_iff]; rw [disjoint_iff]; rw [codisjoint_iff]

@[simp]
/--
theorem `compl_symmDiff_self` / 定理 `compl_symmDiff_self`

English:
theorem compl_symmDiff_self
  statement: aᶜ ∆ a = ⊤
  proof: hnot_symmDiff_self _

@[simp]

中文:
定理 compl_symmDiff_self
  结论: aᶜ ∆ a = ⊤
  证明: hnot_symmDiff_self _

@[simp]

Depends on / 依赖: hnot_symmDiff_self
-/
theorem compl_symmDiff_self : aᶜ ∆ a = ⊤ :=
  hnot_symmDiff_self _

@[simp]
/--
theorem `symmDiff_compl_self` / 定理 `symmDiff_compl_self`

English:
theorem symmDiff_compl_self
  statement: a ∆ aᶜ = ⊤
  proof: symmDiff_hnot_self _

中文:
定理 symmDiff_compl_self
  结论: a ∆ aᶜ = ⊤
  证明: symmDiff_hnot_self _

Depends on / 依赖: symmDiff_hnot_self
-/
theorem symmDiff_compl_self : a ∆ aᶜ = ⊤ :=
  symmDiff_hnot_self _

/--
theorem `symmDiff_symmDiff_right'` / 定理 `symmDiff_symmDiff_right'`

English:
theorem symmDiff_symmDiff_right'
  proof: calc
    a ∆ (b ∆ c) = a ⊓ (b ⊓ c ⊔ bᶜ ⊓ cᶜ) ⊔ (b ⊓ cᶜ ⊔ c ⊓ bᶜ) ⊓ aᶜ := by
        { rw [symmDiff_eq, compl_symmDiff, bihimp_eq', symmDiff_eq] }
    _ = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ b ⊓ cᶜ ⊓ aᶜ ⊔ c ⊓ bᶜ ⊓ aᶜ := by
        { rw [inf_sup_left, inf_sup_right, ← sup_assoc, ← inf_assoc, ← inf_assoc] }
    _ = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ aᶜ ⊓ b ⊓ cᶜ ⊔ aᶜ ⊓ bᶜ ⊓ c := (by
      congr 1
      · congr 1
        rw [inf_comm]; rw [inf_assoc]
      · apply inf_left_right_swap)

中文:
定理 symmDiff_symmDiff_right'
  证明: calc
    a ∆ (b ∆ c) = a ⊓ (b ⊓ c ⊔ bᶜ ⊓ cᶜ) ⊔ (b ⊓ cᶜ ⊔ c ⊓ bᶜ) ⊓ aᶜ := by
        { rw [symmDiff_eq, compl_symmDiff, bihimp_eq', symmDiff_eq] }
    _ = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ b ⊓ cᶜ ⊓ aᶜ ⊔ c ⊓ bᶜ ⊓ aᶜ := by
        { rw [inf_sup_left, inf_sup_right, ← sup_assoc, ← inf_assoc, ← inf_assoc] }
    _ = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ aᶜ ⊓ b ⊓ cᶜ ⊔ aᶜ ⊓ bᶜ ⊓ c := (by
      congr 1
      · congr 1
        rw [inf_comm]; rw [inf_assoc]
      · apply inf_left_right_swap)

Depends on / 依赖: bihimp_eq, compl_symmDiff, inf_assoc, inf_comm, inf_left_right_swap, inf_sup_left, inf_sup_right, sup_assoc, symmDiff_eq
-/
theorem symmDiff_symmDiff_right' :
    a ∆ (b ∆ c) = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ aᶜ ⊓ b ⊓ cᶜ ⊔ aᶜ ⊓ bᶜ ⊓ c :=
  calc
    a ∆ (b ∆ c) = a ⊓ (b ⊓ c ⊔ bᶜ ⊓ cᶜ) ⊔ (b ⊓ cᶜ ⊔ c ⊓ bᶜ) ⊓ aᶜ := by
        { rw [symmDiff_eq, compl_symmDiff, bihimp_eq', symmDiff_eq] }
    _ = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ b ⊓ cᶜ ⊓ aᶜ ⊔ c ⊓ bᶜ ⊓ aᶜ := by
        { rw [inf_sup_left, inf_sup_right, ← sup_assoc, ← inf_assoc, ← inf_assoc] }
    _ = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ aᶜ ⊓ b ⊓ cᶜ ⊔ aᶜ ⊓ bᶜ ⊓ c := (by
      congr 1
      · congr 1
        rw [inf_comm]; rw [inf_assoc]
      · apply inf_left_right_swap)

variable {a b c}

/--
theorem `Disjoint.le_symmDiff_sup_symmDiff_left` / 定理 `Disjoint.le_symmDiff_sup_symmDiff_left`

English:
theorem Disjoint.le_symmDiff_sup_symmDiff_left
  given: (h : Disjoint a b)
  statement: c <= a ∆ c ⊔ b ∆ c
  proof: by
  trans c \ (a ⊓ b)
  · rw [h.eq_bot, sdiff_bot]
  · rw [sdiff_inf]
    exact sup_le_sup le_sup_right le_sup_right

中文:
定理 Disjoint.le_symmDiff_sup_symmDiff_left
  条件: (h : Disjoint a b)
  结论: c <= a ∆ c ⊔ b ∆ c
  证明: by
  trans c \ (a ⊓ b)
  · rw [h.eq_bot, sdiff_bot]
  · rw [sdiff_inf]
    exact sup_le_sup le_sup_right le_sup_right

Depends on / 依赖: eq_bot, h.eq_bot, le_sup_right, sdiff_bot, sdiff_inf, sup_le_sup
-/
theorem Disjoint.le_symmDiff_sup_symmDiff_left (h : Disjoint a b) : c <= a ∆ c ⊔ b ∆ c := by
  trans c \ (a ⊓ b)
  · rw [h.eq_bot, sdiff_bot]
  · rw [sdiff_inf]
    exact sup_le_sup le_sup_right le_sup_right

/--
theorem `Disjoint.le_symmDiff_sup_symmDiff_right` / 定理 `Disjoint.le_symmDiff_sup_symmDiff_right`

English:
theorem Disjoint.le_symmDiff_sup_symmDiff_right
  given: (h : Disjoint b c)
  statement: a <= a ∆ b ⊔ a ∆ c
  proof: by
  simp_rw [symmDiff_comm a]
  exact h.le_symmDiff_sup_symmDiff_left

中文:
定理 Disjoint.le_symmDiff_sup_symmDiff_right
  条件: (h : Disjoint b c)
  结论: a <= a ∆ b ⊔ a ∆ c
  证明: by
  simp_rw [symmDiff_comm a]
  exact h.le_symmDiff_sup_symmDiff_left

Depends on / 依赖: h.le_symmDiff_sup_symmDiff_left, le_symmDiff_sup_symmDiff_left, simp_rw, symmDiff_comm
-/
theorem Disjoint.le_symmDiff_sup_symmDiff_right (h : Disjoint b c) : a <= a ∆ b ⊔ a ∆ c := by
  simp_rw [symmDiff_comm a]
  exact h.le_symmDiff_sup_symmDiff_left

/--
theorem `Codisjoint.bihimp_inf_bihimp_le_left` / 定理 `Codisjoint.bihimp_inf_bihimp_le_left`

English:
theorem Codisjoint.bihimp_inf_bihimp_le_left
  given: (h : Codisjoint a b)
  statement: a ⇔ c ⊓ b ⇔ c <= c
  proof: h.dual.le_symmDiff_sup_symmDiff_left

中文:
定理 Codisjoint.bihimp_inf_bihimp_le_left
  条件: (h : Codisjoint a b)
  结论: a ⇔ c ⊓ b ⇔ c <= c
  证明: h.dual.le_symmDiff_sup_symmDiff_left

Depends on / 依赖: h.dual.le_symmDiff_sup_symmDiff_left, le_symmDiff_sup_symmDiff_left
-/
theorem Codisjoint.bihimp_inf_bihimp_le_left (h : Codisjoint a b) : a ⇔ c ⊓ b ⇔ c <= c :=
  h.dual.le_symmDiff_sup_symmDiff_left

/--
theorem `Codisjoint.bihimp_inf_bihimp_le_right` / 定理 `Codisjoint.bihimp_inf_bihimp_le_right`

English:
theorem Codisjoint.bihimp_inf_bihimp_le_right
  given: (h : Codisjoint b c)
  statement: a ⇔ b ⊓ a ⇔ c <= a
  proof: h.dual.le_symmDiff_sup_symmDiff_right

中文:
定理 Codisjoint.bihimp_inf_bihimp_le_right
  条件: (h : Codisjoint b c)
  结论: a ⇔ b ⊓ a ⇔ c <= a
  证明: h.dual.le_symmDiff_sup_symmDiff_right

Depends on / 依赖: h.dual.le_symmDiff_sup_symmDiff_right, le_symmDiff_sup_symmDiff_right
-/
theorem Codisjoint.bihimp_inf_bihimp_le_right (h : Codisjoint b c) : a ⇔ b ⊓ a ⇔ c <= a :=
  h.dual.le_symmDiff_sup_symmDiff_right

end BooleanAlgebra

/-! ### Prod -/


section Prod

@[to_dual (attr := simp)]
/--
theorem `symmDiff_fst` / 定理 `symmDiff_fst`

English:
theorem symmDiff_fst
  statement: [GeneralizedCoheytingAlgebra α] [GeneralizedCoheytingAlgebra β]
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 symmDiff_fst
  结论: [GeneralizedCoheyting代数 α] [GeneralizedCoheyting代数 β]
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem symmDiff_fst [GeneralizedCoheytingAlgebra α] [GeneralizedCoheytingAlgebra β]
    (a b : α × β) : (a ∆ b).1 = a.1 ∆ b.1 :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `symmDiff_snd` / 定理 `symmDiff_snd`

English:
theorem symmDiff_snd
  statement: [GeneralizedCoheytingAlgebra α] [GeneralizedCoheytingAlgebra β]
  proof: rfl

中文:
定理 symmDiff_snd
  结论: [GeneralizedCoheyting代数 α] [GeneralizedCoheyting代数 β]
  证明: rfl
-/
theorem symmDiff_snd [GeneralizedCoheytingAlgebra α] [GeneralizedCoheytingAlgebra β]
    (a b : α × β) : (a ∆ b).2 = a.2 ∆ b.2 :=
  rfl

end Prod

/-! ### Pi -/


namespace Pi

@[to_dual (attr := push ←)]
/--
theorem `symmDiff_def` / 定理 `symmDiff_def`

English:
theorem symmDiff_def
  given: [forall i, GeneralizedCoheytingAlgebra (π i)] (a b : forall i, π i)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 symmDiff_def
  条件: [对任意 i, GeneralizedCoheyting代数 (π i)] (a b : 对任意 i, π i)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem symmDiff_def [forall i, GeneralizedCoheytingAlgebra (π i)] (a b : forall i, π i) :
    a ∆ b = fun i => a i ∆ b i :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `symmDiff_apply` / 定理 `symmDiff_apply`

English:
theorem symmDiff_apply
  given: [forall i, GeneralizedCoheytingAlgebra (π i)] (a b : forall i, π i) (i : ι)
  proof: rfl

中文:
定理 symmDiff_apply
  条件: [对任意 i, GeneralizedCoheyting代数 (π i)] (a b : 对任意 i, π i) (i : ι)
  证明: rfl
-/
theorem symmDiff_apply [forall i, GeneralizedCoheytingAlgebra (π i)] (a b : forall i, π i) (i : ι) :
    (a ∆ b) i = a i ∆ b i :=
  rfl

end Pi
