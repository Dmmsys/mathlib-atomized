/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Order.Group.Lattice
public meta import Mathlib.Tactic.ToDual

/-!
# Absolute values in ordered groups

The absolute value of an element in a group which is also a lattice is its supremum with its
negation. This generalizes the usual absolute value on real numbers (`|x| = max x (-x)`).

## Notation

- `|a|`: The *absolute value* of an element `a` of an additive lattice ordered group
- `|a|ₘ`: The *absolute value* of an element `a` of a multiplicative lattice ordered group
-/

@[expose] public section

open Function

variable {α : Type*}

section Lattice
variable [Lattice α]

section Group
variable [Group α] {a b : α}

/-- `mabs a`, denoted `|a|ₘ`, is the absolute value of `a`. -/
@[to_additive (attr := grind) /-- `abs a`, denoted `|a|`, is the absolute value of `a` -/]
/--
Definition of `mabs` / `mabs` 的定义

English:
definition mabs
  signature: (a : α)
  body: a ⊔ a⁻¹

@[inherit_doc mabs]
macro:max atomic("|" noWs) a:term noWs "|ₘ" : term => `(mabs $a)

@[inherit_doc abs]
macro:max atomic("|" noWs) a:term noWs "|" : term => `(abs $a)

中文:
定义 mabs
  签名: (a : α)
  定义体: a ⊔ a⁻¹

@[inherit_doc mabs]
macro:max atomic("|" noWs) a:term noWs "|ₘ" : term => `(mabs $a)

@[inherit_doc abs]
macro:max atomic("|" noWs) a:term noWs "|" : term => `(abs $a)
-/
def mabs (a : α) : α := a ⊔ a⁻¹

@[inherit_doc mabs]
macro:max atomic("|" noWs) a:term noWs "|ₘ" : term => `(mabs $a)

@[inherit_doc abs]
macro:max atomic("|" noWs) a:term noWs "|" : term => `(abs $a)

/-- Unexpander for the notation `|a|ₘ` for `mabs a`.
Tries to add discretionary parentheses in unparsable cases. -/
@[app_unexpander mabs]
meta def mabs.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) =>
    match a with
    | `(|$_|) | `(|$_|ₘ) | `(-$_) => `(|($a)|ₘ)
    | _ => `(|$a|ₘ)
  | _ => throw ()

/-- Unexpander for the notation `|a|` for `abs a`.
Tries to add discretionary parentheses in unparsable cases. -/
@[app_unexpander abs]
meta def abs.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) =>
    match a with
    | `(|$_|) | `(|$_|ₘ) | `(-$_) => `(|($a)|)
    | _ => `(|$a|)
  | _ => throw ()

/--
lemma `mabs_le'` / 引理 `mabs_le'`

English:
lemma mabs_le'
  statement: |a|ₘ <= b ↔ a <= b ∧ a⁻¹ <= b
  proof: sup_le_iff

中文:
引理 mabs_le'
  结论: |a|ₘ <= b ↔ a <= b ∧ a⁻¹ <= b
  证明: sup_le_iff
-/
@[to_additive] lemma mabs_le' : |a|ₘ <= b ↔ a <= b ∧ a⁻¹ <= b := sup_le_iff

/--
lemma `le_mabs_self` / 引理 `le_mabs_self`

English:
lemma le_mabs_self
  given: (a : α)
  statement: a <= |a|ₘ
  proof: le_sup_left

中文:
引理 le_mabs_self
  条件: (a : α)
  结论: a <= |a|ₘ
  证明: le_sup_left
-/
@[to_additive] lemma le_mabs_self (a : α) : a <= |a|ₘ := le_sup_left

/--
lemma `inv_le_mabs` / 引理 `inv_le_mabs`

English:
lemma inv_le_mabs
  given: (a : α)
  statement: a⁻¹ <= |a|ₘ
  proof: le_sup_right

中文:
引理 inv_le_mabs
  条件: (a : α)
  结论: a⁻¹ <= |a|ₘ
  证明: le_sup_right
-/
@[to_additive] lemma inv_le_mabs (a : α) : a⁻¹ <= |a|ₘ := le_sup_right

/--
lemma `mabs_le_mabs` / 引理 `mabs_le_mabs`

English:
lemma mabs_le_mabs
  given: (h₀ : a <= b) (h₁ : a⁻¹ <= b)
  statement: |a|ₘ <= |b|ₘ
  proof: (mabs_le'.2 ⟨h₀, h₁⟩).trans (le_mabs_self b)

中文:
引理 mabs_le_mabs
  条件: (h₀ : a <= b) (h₁ : a⁻¹ <= b)
  结论: |a|ₘ <= |b|ₘ
  证明: (mabs_le'.2 ⟨h₀, h₁⟩).trans (le_mabs_self b)
-/
@[to_additive] lemma mabs_le_mabs (h₀ : a <= b) (h₁ : a⁻¹ <= b) : |a|ₘ <= |b|ₘ :=
  (mabs_le'.2 ⟨h₀, h₁⟩).trans (le_mabs_self b)

/--
lemma `mabs_inv` / 引理 `mabs_inv`

English:
lemma mabs_inv
  given: (a : α)
  statement: |a⁻¹|ₘ = |a|ₘ
  proof: by simp [mabs, sup_comm]

中文:
引理 mabs_inv
  条件: (a : α)
  结论: |a⁻¹|ₘ = |a|ₘ
  证明: by simp [mabs, sup_comm]
-/
@[to_additive (attr := simp)] lemma mabs_inv (a : α) : |a⁻¹|ₘ = |a|ₘ := by simp [mabs, sup_comm]

/--
lemma `mabs_div_comm` / 引理 `mabs_div_comm`

English:
lemma mabs_div_comm
  given: (a b : α)
  statement: |a / b|ₘ = |b / a|ₘ
  proof: by rw [← mabs_inv, inv_div]

中文:
引理 mabs_div_comm
  条件: (a b : α)
  结论: |a / b|ₘ = |b / a|ₘ
  证明: by rw [← mabs_inv, inv_div]
-/
@[to_additive] lemma mabs_div_comm (a b : α) : |a / b|ₘ = |b / a|ₘ := by rw [← mabs_inv, inv_div]

/--
lemma `mabs_ite` / 引理 `mabs_ite`

English:
lemma mabs_ite
  given: (p : Prop) [Decidable p]
  proof: apply_ite _ _ _ _

中文:
引理 mabs_ite
  条件: (p : 命题) [Decidable p]
  证明: apply_ite _ _ _ _
-/
@[to_additive] lemma mabs_ite (p : Prop) [Decidable p] :
    |if p then a else b|ₘ = if p then |a|ₘ else |b|ₘ :=
  apply_ite _ _ _ _

/--
lemma `mabs_dite` / 引理 `mabs_dite`

English:
lemma mabs_dite
  given: (p : Prop) [Decidable p] (a : p -> α) (b : ¬p -> α)
  proof: apply_dite _ _ _ _

中文:
引理 mabs_dite
  条件: (p : 命题) [Decidable p] (a : p -> α) (b : ¬p -> α)
  证明: apply_dite _ _ _ _
-/
@[to_additive] lemma mabs_dite (p : Prop) [Decidable p] (a : p -> α) (b : ¬p -> α) :
    |if h : p then a h else b h|ₘ = if h : p then |a h|ₘ else |b h|ₘ :=
  apply_dite _ _ _ _

variable [MulLeftMono α]

/--
lemma `mabs_of_one_le` / 引理 `mabs_of_one_le`

English:
lemma mabs_of_one_le
  given: (h : 1 <= a)
  statement: |a|ₘ = a
  proof: sup_eq_left.2 (inv_le_one'.2 h).trans h

中文:
引理 mabs_of_one_le
  条件: (h : 1 <= a)
  结论: |a|ₘ = a
  证明: sup_eq_left.2 (inv_le_one'.2 h).trans h

Depends on / 依赖: CanonicallyOrderedMul, CanonicallyOrderedMul.toMulLeftMono, toMulLeftMono
-/
@[to_additive] lemma mabs_of_one_le (h : 1 <= a) : |a|ₘ = a :=
sup_eq_left.2 (inv_le_one'.2 h).trans h

/--
lemma `mabs_of_one_lt` / 引理 `mabs_of_one_lt`

English:
lemma mabs_of_one_lt
  given: (h : 1 < a)
  statement: |a|ₘ = a
  proof: mabs_of_one_le h.le

中文:
引理 mabs_of_one_lt
  条件: (h : 1 < a)
  结论: |a|ₘ = a
  证明: mabs_of_one_le h.le
-/
@[to_additive] lemma mabs_of_one_lt (h : 1 < a) : |a|ₘ = a := mabs_of_one_le h.le

/--
lemma `mabs_of_le_one` / 引理 `mabs_of_le_one`

English:
lemma mabs_of_le_one
  given: (h : a <= 1)
  statement: |a|ₘ = a⁻¹
  proof: sup_eq_right.2 h.trans (one_le_inv'.2 h)

中文:
引理 mabs_of_le_one
  条件: (h : a <= 1)
  结论: |a|ₘ = a⁻¹
  证明: sup_eq_right.2 h.trans (one_le_inv'.2 h)
-/
@[to_additive] lemma mabs_of_le_one (h : a <= 1) : |a|ₘ = a⁻¹ :=
sup_eq_right.2 h.trans (one_le_inv'.2 h)

/--
lemma `mabs_of_lt_one` / 引理 `mabs_of_lt_one`

English:
lemma mabs_of_lt_one
  given: (h : a < 1)
  statement: |a|ₘ = a⁻¹
  proof: mabs_of_le_one h.le

中文:
引理 mabs_of_lt_one
  条件: (h : a < 1)
  结论: |a|ₘ = a⁻¹
  证明: mabs_of_le_one h.le
-/
@[to_additive] lemma mabs_of_lt_one (h : a < 1) : |a|ₘ = a⁻¹ := mabs_of_le_one h.le

/--
lemma `mabs_le_mabs_of_one_le` / 引理 `mabs_le_mabs_of_one_le`

English:
lemma mabs_le_mabs_of_one_le
  given: (ha : 1 <= a) (hab : a <= b)
  statement: |a|ₘ <= |b|ₘ
  proof: by
  rwa [mabs_of_one_le ha, mabs_of_one_le (ha.trans hab)]

中文:
引理 mabs_le_mabs_of_one_le
  条件: (ha : 1 <= a) (hab : a <= b)
  结论: |a|ₘ <= |b|ₘ
  证明: by
  rwa [mabs_of_one_le ha, mabs_of_one_le (ha.trans hab)]
-/
@[to_additive] lemma mabs_le_mabs_of_one_le (ha : 1 <= a) (hab : a <= b) : |a|ₘ <= |b|ₘ := by
  rwa [mabs_of_one_le ha, mabs_of_one_le (ha.trans hab)]

attribute [gcongr] abs_le_abs_of_nonneg

/--
lemma `mabs_one` / 引理 `mabs_one`

English:
lemma mabs_one
  statement: |(1 : α)|ₘ = 1
  proof: mabs_of_one_le le_rfl

中文:
引理 mabs_one
  结论: |(1 : α)|ₘ = 1
  证明: mabs_of_one_le le_rfl
-/
@[to_additive (attr := simp)] lemma mabs_one : |(1 : α)|ₘ = 1 := mabs_of_one_le le_rfl

variable [MulRightMono α]

/--
lemma `one_le_mabs` / 引理 `one_le_mabs`

English:
lemma one_le_mabs
  given: (a : α)
  statement: 1 <= |a|ₘ
  proof: by
  apply pow_two_semiclosed _
  rw [mabs]; rw [pow_two]; rw [mul_sup]; rw [sup_mul]; rw [← pow_two]; rw [inv_mul_cancel]; rw [sup_comm]; rw [← sup_assoc]
  apply le_sup_right

中文:
引理 one_le_mabs
  条件: (a : α)
  结论: 1 <= |a|ₘ
  证明: by
  apply pow_two_semiclosed _
  rw [mabs]; rw [pow_two]; rw [mul_sup]; rw [sup_mul]; rw [← pow_two]; rw [inv_mul_cancel]; rw [sup_comm]; rw [← sup_assoc]
  apply le_sup_right
-/
@[to_additive (attr := simp) abs_nonneg] lemma one_le_mabs (a : α) : 1 <= |a|ₘ := by
  apply pow_two_semiclosed _
  rw [mabs]; rw [pow_two]; rw [mul_sup]; rw [sup_mul]; rw [← pow_two]; rw [inv_mul_cancel]; rw [sup_comm]; rw [← sup_assoc]
  apply le_sup_right

/--
lemma `mabs_mabs` / 引理 `mabs_mabs`

English:
lemma mabs_mabs
  given: (a : α)
  statement: |(|a|ₘ)|ₘ = |a|ₘ
  proof: mabs_of_one_le one_le_mabs a

中文:
引理 mabs_mabs
  条件: (a : α)
  结论: |(|a|ₘ)|ₘ = |a|ₘ
  证明: mabs_of_one_le one_le_mabs a
-/
@[to_additive (attr := simp)] lemma mabs_mabs (a : α) : |(|a|ₘ)|ₘ = |a|ₘ :=
mabs_of_one_le one_le_mabs a

end Group

section CommGroup
variable [CommGroup α] [MulLeftMono α]

-- Banasiak Proposition 2.12, Zaanen 2nd lecture
/-- The absolute value satisfies the triangle inequality. -/
@[to_additive /-- The absolute value satisfies the triangle inequality. -/]
/--
lemma `mabs_mul_le` / 引理 `mabs_mul_le`

English:
lemma mabs_mul_le
  given: (a b : α)
  statement: |a * b|ₘ <= |a|ₘ * |b|ₘ
  proof: by
  apply sup_le
  · exact mul_le_mul' (le_mabs_self a) (le_mabs_self b)
  · rw [mul_inv]
    exact mul_le_mul' (inv_le_mabs _) (inv_le_mabs _)

@[to_additive]

中文:
引理 mabs_mul_le
  条件: (a b : α)
  结论: |a * b|ₘ <= |a|ₘ * |b|ₘ
  证明: by
  apply sup_le
  · exact mul_le_mul' (le_mabs_self a) (le_mabs_self b)
  · rw [mul_inv]
    exact mul_le_mul' (inv_le_mabs _) (inv_le_mabs _)

@[to_additive]

Depends on / 依赖: inv_le_mabs, le_mabs_self, mul_inv, mul_le_mul, sup_le
-/
lemma mabs_mul_le (a b : α) : |a * b|ₘ <= |a|ₘ * |b|ₘ := by
  apply sup_le
  · exact mul_le_mul' (le_mabs_self a) (le_mabs_self b)
  · rw [mul_inv]
    exact mul_le_mul' (inv_le_mabs _) (inv_le_mabs _)

@[to_additive]
/--
lemma `mabs_mabs_div_mabs_le` / 引理 `mabs_mabs_div_mabs_le`

English:
lemma mabs_mabs_div_mabs_le
  given: (a b : α)
  statement: |(|a|ₘ / |b|ₘ)|ₘ <= |a / b|ₘ
  proof: by
  rw [mabs]; rw [sup_le_iff]
  constructor
  · apply div_le_iff_le_mul.2
    convert! mabs_mul_le (a / b) b
    rw [div_mul_cancel]
  · rw [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_le_iff_le_mul, mabs_div_comm]
    convert! mabs_mul_le (b / a) a
    · rw [div_mul_cancel]

中文:
引理 mabs_mabs_div_mabs_le
  条件: (a b : α)
  结论: |(|a|ₘ / |b|ₘ)|ₘ <= |a / b|ₘ
  证明: by
  rw [mabs]; rw [sup_le_iff]
  constructor
  · apply div_le_iff_le_mul.2
    convert! mabs_mul_le (a / b) b
    rw [div_mul_cancel]
  · rw [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_le_iff_le_mul, mabs_div_comm]
    convert! mabs_mul_le (b / a) a
    · rw [div_mul_cancel]

Depends on / 依赖: convert, div_eq_mul_inv, div_le_iff_le_mul, div_mul_cancel, inv_inv, mabs_div_comm, mabs_mul_le, mul_inv_le_iff_le_mul, mul_inv_rev, sup_le_iff
-/
lemma mabs_mabs_div_mabs_le (a b : α) : |(|a|ₘ / |b|ₘ)|ₘ <= |a / b|ₘ := by
  rw [mabs]; rw [sup_le_iff]
  constructor
  · apply div_le_iff_le_mul.2
    convert! mabs_mul_le (a / b) b
    rw [div_mul_cancel]
  · rw [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_le_iff_le_mul, mabs_div_comm]
    convert! mabs_mul_le (b / a) a
    · rw [div_mul_cancel]

/--
lemma `sup_div_inf_eq_mabs_div` / 引理 `sup_div_inf_eq_mabs_div`

English:
lemma sup_div_inf_eq_mabs_div
  given: (a b : α)
  statement: (a ⊔ b) / (a ⊓ b) = |b / a|ₘ
  proof: by
  simp_rw [sup_div, div_inf, div_self', sup_comm, sup_sup_sup_comm, sup_idem]
  rw [← inv_div]; rw [sup_comm (b := _ / _)]; rw [← mabs]; rw [sup_eq_left]
  exact one_le_mabs _

@[to_additive two_nsmul_sup_eq_add_add_abs_sub]

中文:
引理 sup_div_inf_eq_mabs_div
  条件: (a b : α)
  结论: (a ⊔ b) / (a ⊓ b) = |b / a|ₘ
  证明: by
  simp_rw [sup_div, div_inf, div_self', sup_comm, sup_sup_sup_comm, sup_idem]
  rw [← inv_div]; rw [sup_comm (b := _ / _)]; rw [← mabs]; rw [sup_eq_left]
  exact one_le_mabs _

@[to_additive two_nsmul_sup_eq_add_add_abs_sub]
-/
@[to_additive] lemma sup_div_inf_eq_mabs_div (a b : α) : (a ⊔ b) / (a ⊓ b) = |b / a|ₘ := by
  simp_rw [sup_div, div_inf, div_self', sup_comm, sup_sup_sup_comm, sup_idem]
  rw [← inv_div]; rw [sup_comm (b := _ / _)]; rw [← mabs]; rw [sup_eq_left]
  exact one_le_mabs _

@[to_additive two_nsmul_sup_eq_add_add_abs_sub]
/--
lemma `sup_sq_eq_mul_mul_mabs_div` / 引理 `sup_sq_eq_mul_mul_mabs_div`

English:
lemma sup_sq_eq_mul_mul_mabs_div
  given: (a b : α)
  statement: (a ⊔ b) ^ 2 = a * b * |b / a|ₘ
  proof: by
  rw [← inf_mul_sup a b]; rw [← sup_div_inf_eq_mabs_div]; rw [div_eq_mul_inv]; rw [← mul_assoc]; rw [mul_comm]; rw [mul_assoc]; rw [← pow_two]; rw [inv_mul_cancel_left]

@[to_additive two_nsmul_inf_eq_add_sub_abs_sub]

中文:
引理 sup_sq_eq_mul_mul_mabs_div
  条件: (a b : α)
  结论: (a ⊔ b) ^ 2 = a * b * |b / a|ₘ
  证明: by
  rw [← inf_mul_sup a b]; rw [← sup_div_inf_eq_mabs_div]; rw [div_eq_mul_inv]; rw [← mul_assoc]; rw [mul_comm]; rw [mul_assoc]; rw [← pow_two]; rw [inv_mul_cancel_left]

@[to_additive two_nsmul_inf_eq_add_sub_abs_sub]

Depends on / 依赖: div_eq_mul_inv, inf_mul_sup, inv_mul_cancel_left, mul_assoc, mul_comm, pow_two, sup_div_inf_eq_mabs_div
-/
lemma sup_sq_eq_mul_mul_mabs_div (a b : α) : (a ⊔ b) ^ 2 = a * b * |b / a|ₘ := by
  rw [← inf_mul_sup a b]; rw [← sup_div_inf_eq_mabs_div]; rw [div_eq_mul_inv]; rw [← mul_assoc]; rw [mul_comm]; rw [mul_assoc]; rw [← pow_two]; rw [inv_mul_cancel_left]

@[to_additive two_nsmul_inf_eq_add_sub_abs_sub]
/--
lemma `inf_sq_eq_mul_div_mabs_div` / 引理 `inf_sq_eq_mul_div_mabs_div`

English:
lemma inf_sq_eq_mul_div_mabs_div
  given: (a b : α)
  statement: (a ⊓ b) ^ 2 = a * b / |b / a|ₘ
  proof: by
  rw [← inf_mul_sup a b]; rw [← sup_div_inf_eq_mabs_div]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_inv_rev]; rw [inv_inv]; rw [mul_assoc]; rw [mul_inv_cancel_comm_assoc]; rw [← pow_two]

中文:
引理 inf_sq_eq_mul_div_mabs_div
  条件: (a b : α)
  结论: (a ⊓ b) ^ 2 = a * b / |b / a|ₘ
  证明: by
  rw [← inf_mul_sup a b]; rw [← sup_div_inf_eq_mabs_div]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_inv_rev]; rw [inv_inv]; rw [mul_assoc]; rw [mul_inv_cancel_comm_assoc]; rw [← pow_two]

Depends on / 依赖: div_eq_mul_inv, inf_mul_sup, inv_inv, mul_assoc, mul_inv_cancel_comm_assoc, mul_inv_rev, pow_two, sup_div_inf_eq_mabs_div
-/
lemma inf_sq_eq_mul_div_mabs_div (a b : α) : (a ⊓ b) ^ 2 = a * b / |b / a|ₘ := by
  rw [← inf_mul_sup a b]; rw [← sup_div_inf_eq_mabs_div]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_inv_rev]; rw [inv_inv]; rw [mul_assoc]; rw [mul_inv_cancel_comm_assoc]; rw [← pow_two]

-- See, e.g. Zaanen, Lectures on Riesz Spaces
-- 3rd lecture
@[to_additive]
/--
lemma `mabs_div_sup_mul_mabs_div_inf` / 引理 `mabs_div_sup_mul_mabs_div_inf`

English:
lemma mabs_div_sup_mul_mabs_div_inf
  given: (a b c : α)
  proof: by
  let : DistribLattice α := CommGroup.toDistribLattice α
  calc
    |(a ⊔ c) / (b ⊔ c)|ₘ * |(a ⊓ c) / (b ⊓ c)|ₘ =
        (b ⊔ c ⊔ (a ⊔ c)) / ((b ⊔ c) ⊓ (a ⊔ c)) * |(a ⊓ c) / (b ⊓ c)|ₘ := by
        rw [sup_div_inf_eq_mabs_div]
    _ = (b ⊔ c ⊔ (a ⊔ c)) / ((b ⊔ c) ⊓ (a ⊔ c)) * ((b ⊓ c ⊔ a ⊓ c) / 

中文:
引理 mabs_div_sup_mul_mabs_div_inf
  条件: (a b c : α)
  证明: by
  let : DistribLattice α := CommGroup.toDistribLattice α
  calc
    |(a ⊔ c) / (b ⊔ c)|ₘ * |(a ⊓ c) / (b ⊓ c)|ₘ =
        (b ⊔ c ⊔ (a ⊔ c)) / ((b ⊔ c) ⊓ (a ⊔ c)) * |(a ⊓ c) / (b ⊓ c)|ₘ := by
        rw [sup_div_inf_eq_mabs_div]
    _ = (b ⊔ c ⊔ (a ⊔ c)) / ((b ⊔ c) ⊓ (a ⊔ c)) * ((b ⊓ c ⊔ a ⊓ c) / 

Depends on / 依赖: CommGroup, CommGroup.toDistribLattice, DistribLattice, inf_sup_right, sup_assoc, sup_comm, sup_div_inf_eq_mabs_div, sup_inf_right, toDistribLattice
-/
lemma mabs_div_sup_mul_mabs_div_inf (a b c : α) :
    |(a ⊔ c) / (b ⊔ c)|ₘ * |(a ⊓ c) / (b ⊓ c)|ₘ = |a / b|ₘ := by
  let : DistribLattice α := CommGroup.toDistribLattice α
  calc
    |(a ⊔ c) / (b ⊔ c)|ₘ * |(a ⊓ c) / (b ⊓ c)|ₘ =
        (b ⊔ c ⊔ (a ⊔ c)) / ((b ⊔ c) ⊓ (a ⊔ c)) * |(a ⊓ c) / (b ⊓ c)|ₘ := by
        rw [sup_div_inf_eq_mabs_div]
    _ = (b ⊔ c ⊔ (a ⊔ c)) / ((b ⊔ c) ⊓ (a ⊔ c)) * ((b ⊓ c ⊔ a ⊓ c) / (b ⊓ c ⊓ (a ⊓ c))) := by
        rw [sup_div_inf_eq_mabs_div (b ⊓ c) (a ⊓ c)]
    _ = (b ⊔ a ⊔ c) / (b ⊓ a ⊔ c) * (((b ⊔ a) ⊓ c) / (b ⊓ a ⊓ c)) := by
        rw [← sup_inf_right]; rw [← inf_sup_right]; rw [sup_assoc]; rw [sup_comm c (a ⊔ c)]; rw [sup_right_idem]; rw [sup_assoc]; rw [inf_assoc]; rw [inf_comm c (a ⊓ c)]; rw [inf_right_idem]; rw [inf_assoc]
    _ = (b ⊔ a ⊔ c) * ((b ⊔ a) ⊓ c) / ((b ⊓ a ⊔ c) * (b ⊓ a ⊓ c)) := by rw [div_mul_div_comm]
    _ = (b ⊔ a) * c / ((b ⊓ a) * c) := by
        rw [mul_comm]; rw [inf_mul_sup]; rw [mul_comm (b ⊓ a ⊔ c)]; rw [inf_mul_sup]
    _ = (b ⊔ a) / (b ⊓ a) := by
        rw [div_eq_mul_inv]; rw [mul_inv_rev]; rw [mul_assoc]; rw [mul_inv_cancel_left]; rw [← div_eq_mul_inv]
    _ = |a / b|ₘ := by rw [sup_div_inf_eq_mabs_div]

/--
lemma `mabs_sup_div_sup_le_mabs` / 引理 `mabs_sup_div_sup_le_mabs`

English:
lemma mabs_sup_div_sup_le_mabs
  given: (a b c : α)
  statement: |(a ⊔ c) / (b ⊔ c)|ₘ <= |a / b|ₘ
  proof: by
  apply le_of_mul_le_of_one_le_left _ (one_le_mabs _); rw [mabs_div_sup_mul_mabs_div_inf]

中文:
引理 mabs_sup_div_sup_le_mabs
  条件: (a b c : α)
  结论: |(a ⊔ c) / (b ⊔ c)|ₘ <= |a / b|ₘ
  证明: by
  apply le_of_mul_le_of_one_le_left _ (one_le_mabs _); rw [mabs_div_sup_mul_mabs_div_inf]
-/
@[to_additive] lemma mabs_sup_div_sup_le_mabs (a b c : α) : |(a ⊔ c) / (b ⊔ c)|ₘ <= |a / b|ₘ := by
  apply le_of_mul_le_of_one_le_left _ (one_le_mabs _); rw [mabs_div_sup_mul_mabs_div_inf]

/--
lemma `mabs_inf_div_inf_le_mabs` / 引理 `mabs_inf_div_inf_le_mabs`

English:
lemma mabs_inf_div_inf_le_mabs
  given: (a b c : α)
  statement: |(a ⊓ c) / (b ⊓ c)|ₘ <= |a / b|ₘ
  proof: by
  apply le_of_mul_le_of_one_le_right _ (one_le_mabs _); rw [mabs_div_sup_mul_mabs_div_inf]

中文:
引理 mabs_inf_div_inf_le_mabs
  条件: (a b c : α)
  结论: |(a ⊓ c) / (b ⊓ c)|ₘ <= |a / b|ₘ
  证明: by
  apply le_of_mul_le_of_one_le_right _ (one_le_mabs _); rw [mabs_div_sup_mul_mabs_div_inf]
-/
@[to_additive] lemma mabs_inf_div_inf_le_mabs (a b c : α) : |(a ⊓ c) / (b ⊓ c)|ₘ <= |a / b|ₘ := by
  apply le_of_mul_le_of_one_le_right _ (one_le_mabs _); rw [mabs_div_sup_mul_mabs_div_inf]

-- Commutative case, Zaanen, 3rd lecture
-- For the non-commutative case, see Birkhoff Theorem 19 (27)
@[to_additive Birkhoff_inequalities]
/--
lemma `m_Birkhoff_inequalities` / 引理 `m_Birkhoff_inequalities`

English:
lemma m_Birkhoff_inequalities
  given: (a b c : α)
  proof: sup_le (mabs_sup_div_sup_le_mabs a b c) (mabs_inf_div_inf_le_mabs a b c)

中文:
引理 m_Birkhoff_inequalities
  条件: (a b c : α)
  证明: sup_le (mabs_sup_div_sup_le_mabs a b c) (mabs_inf_div_inf_le_mabs a b c)

Depends on / 依赖: mabs_inf_div_inf_le_mabs, mabs_sup_div_sup_le_mabs, sup_le
-/
lemma m_Birkhoff_inequalities (a b c : α) :
    |(a ⊔ c) / (b ⊔ c)|ₘ ⊔ |(a ⊓ c) / (b ⊓ c)|ₘ <= |a / b|ₘ :=
  sup_le (mabs_sup_div_sup_le_mabs a b c) (mabs_inf_div_inf_le_mabs a b c)

end CommGroup
end Lattice

section LinearOrder
variable [Group α] [LinearOrder α] {a b : α}

/--
lemma `mabs_choice` / 引理 `mabs_choice`

English:
lemma mabs_choice
  given: (x : α)
  statement: |x|ₘ = x ∨ |x|ₘ = x⁻¹
  proof: max_choice _ _

中文:
引理 mabs_choice
  条件: (x : α)
  结论: |x|ₘ = x ∨ |x|ₘ = x⁻¹
  证明: max_choice _ _
-/
@[to_additive] lemma mabs_choice (x : α) : |x|ₘ = x ∨ |x|ₘ = x⁻¹ := max_choice _ _

/--
lemma `le_mabs` / 引理 `le_mabs`

English:
lemma le_mabs
  statement: a <= |b|ₘ ↔ a <= b ∨ a <= b⁻¹
  proof: le_max_iff

中文:
引理 le_mabs
  结论: a <= |b|ₘ ↔ a <= b ∨ a <= b⁻¹
  证明: le_max_iff
-/
@[to_additive] lemma le_mabs : a <= |b|ₘ ↔ a <= b ∨ a <= b⁻¹ := le_max_iff

/--
lemma `mabs_eq_max_inv` / 引理 `mabs_eq_max_inv`

English:
lemma mabs_eq_max_inv
  statement: |a|ₘ = max a a⁻¹
  proof: rfl

中文:
引理 mabs_eq_max_inv
  结论: |a|ₘ = max a a⁻¹
  证明: rfl
-/
@[to_additive] lemma mabs_eq_max_inv : |a|ₘ = max a a⁻¹ := rfl

/--
lemma `lt_mabs` / 引理 `lt_mabs`

English:
lemma lt_mabs
  statement: a < |b|ₘ ↔ a < b ∨ a < b⁻¹
  proof: lt_max_iff

中文:
引理 lt_mabs
  结论: a < |b|ₘ ↔ a < b ∨ a < b⁻¹
  证明: lt_max_iff
-/
@[to_additive] lemma lt_mabs : a < |b|ₘ ↔ a < b ∨ a < b⁻¹ := lt_max_iff

/--
lemma `mabs_by_cases` / 引理 `mabs_by_cases`

English:
lemma mabs_by_cases
  given: (P : α -> Prop) (h1 : P a) (h2 : P a⁻¹)
  statement: P |a|ₘ
  proof: sup_ind _ _ h1 h2

中文:
引理 mabs_by_cases
  条件: (P : α -> 命题) (h1 : P a) (h2 : P a⁻¹)
  结论: P |a|ₘ
  证明: sup_ind _ _ h1 h2
-/
@[to_additive] lemma mabs_by_cases (P : α -> Prop) (h1 : P a) (h2 : P a⁻¹) : P |a|ₘ :=
  sup_ind _ _ h1 h2

/--
lemma `eq_or_eq_inv_of_mabs_eq` / 引理 `eq_or_eq_inv_of_mabs_eq`

English:
lemma eq_or_eq_inv_of_mabs_eq
  given: (h : |a|ₘ = b)
  statement: a = b ∨ a = b⁻¹
  proof: by
  simpa only [← h, eq_comm (a := |a|ₘ), inv_eq_iff_eq_inv] using mabs_choice a

中文:
引理 eq_or_eq_inv_of_mabs_eq
  条件: (h : |a|ₘ = b)
  结论: a = b ∨ a = b⁻¹
  证明: by
  simpa only [← h, eq_comm (a := |a|ₘ), inv_eq_iff_eq_inv] using mabs_choice a
-/
@[to_additive] lemma eq_or_eq_inv_of_mabs_eq (h : |a|ₘ = b) : a = b ∨ a = b⁻¹ := by
  simpa only [← h, eq_comm (a := |a|ₘ), inv_eq_iff_eq_inv] using mabs_choice a

/--
lemma `mabs_eq_mabs` / 引理 `mabs_eq_mabs`

English:
lemma mabs_eq_mabs
  statement: |a|ₘ = |b|ₘ ↔ a = b ∨ a = b⁻¹
  proof: by
  refine ⟨fun h => ?_, by rintro (h | h) <;> simp [h]⟩
  obtain rfl | rfl := eq_or_eq_inv_of_mabs_eq h <;>
    simpa only [inv_eq_iff_eq_inv (a := |b|ₘ), inv_inv, inv_inj, or_comm] using mabs_choice b

中文:
引理 mabs_eq_mabs
  结论: |a|ₘ = |b|ₘ ↔ a = b ∨ a = b⁻¹
  证明: by
  refine ⟨fun h => ?_, by rintro (h | h) <;> simp [h]⟩
  obtain rfl | rfl := eq_or_eq_inv_of_mabs_eq h <;>
    simpa only [inv_eq_iff_eq_inv (a := |b|ₘ), inv_inv, inv_inj, or_comm] using mabs_choice b
-/
@[to_additive] lemma mabs_eq_mabs : |a|ₘ = |b|ₘ ↔ a = b ∨ a = b⁻¹ := by
  refine ⟨fun h => ?_, by rintro (h | h) <;> simp [h]⟩
  obtain rfl | rfl := eq_or_eq_inv_of_mabs_eq h <;>
    simpa only [inv_eq_iff_eq_inv (a := |b|ₘ), inv_inv, inv_inj, or_comm] using mabs_choice b

/--
lemma `isSquare_mabs` / 引理 `isSquare_mabs`

English:
lemma isSquare_mabs
  statement: IsSquare |a|ₘ ↔ IsSquare a
  proof: mabs_by_cases (IsSquare · ↔ _) Iff.rfl isSquare_inv

中文:
引理 isSquare_mabs
  结论: IsSquare |a|ₘ ↔ IsSquare a
  证明: mabs_by_cases (IsSquare · ↔ _) Iff.rfl isSquare_inv
-/
@[to_additive] lemma isSquare_mabs : IsSquare |a|ₘ ↔ IsSquare a :=
  mabs_by_cases (IsSquare · ↔ _) Iff.rfl isSquare_inv

/--
lemma `lt_of_mabs_lt` / 引理 `lt_of_mabs_lt`

English:
lemma lt_of_mabs_lt
  statement: |a|ₘ < b -> a < b
  proof: (le_mabs_self _).trans_lt

中文:
引理 lt_of_mabs_lt
  结论: |a|ₘ < b -> a < b
  证明: (le_mabs_self _).trans_lt
-/
@[to_additive] lemma lt_of_mabs_lt : |a|ₘ < b -> a < b := (le_mabs_self _).trans_lt

/--
lemma `map_mabs` / 引理 `map_mabs`

English:
lemma map_mabs
  statement: {β F : Type*} [Group β] [LinearOrder β] [FunLike F α β]
  proof: by
  rw [mabs]; rw [mabs]; rw [(OrderHomClass.mono f).map_max]; rw [map_inv]

中文:
引理 map_mabs
  结论: {β F : 类型} [Group β] [LinearOrder β] [FunLike F α β]
  证明: by
  rw [mabs]; rw [mabs]; rw [(OrderHomClass.mono f).map_max]; rw [map_inv]
-/
@[to_additive (attr := simp)] lemma map_mabs {β F : Type*} [Group β] [LinearOrder β] [FunLike F α β]
    [OrderHomClass F α β] [MonoidHomClass F α β] (f : F) (a : α) :
    f |a|ₘ = |f a|ₘ := by
  rw [mabs]; rw [mabs]; rw [(OrderHomClass.mono f).map_max]; rw [map_inv]

variable [MulLeftMono α] {a b : α}

/--
lemma `one_lt_mabs` / 引理 `one_lt_mabs`

English:
lemma one_lt_mabs
  statement: 1 < |a|ₘ ↔ a != 1
  proof: by
  obtain ha | rfl | ha := lt_trichotomy a 1
  · simp [mabs_of_lt_one ha, ha.ne, ha]
  · simp
  · simp [mabs_of_one_lt ha, ha, ha.ne']

中文:
引理 one_lt_mabs
  结论: 1 < |a|ₘ ↔ a != 1
  证明: by
  obtain ha | rfl | ha := lt_trichotomy a 1
  · simp [mabs_of_lt_one ha, ha.ne, ha]
  · simp
  · simp [mabs_of_one_lt ha, ha, ha.ne']
-/
@[to_additive (attr := simp) abs_pos] lemma one_lt_mabs : 1 < |a|ₘ ↔ a != 1 := by
  obtain ha | rfl | ha := lt_trichotomy a 1
  · simp [mabs_of_lt_one ha, ha.ne, ha]
  · simp
  · simp [mabs_of_one_lt ha, ha, ha.ne']

/--
lemma `one_lt_mabs_pos_of_one_lt` / 引理 `one_lt_mabs_pos_of_one_lt`

English:
lemma one_lt_mabs_pos_of_one_lt
  given: (h : 1 < a)
  statement: 1 < |a|ₘ
  proof: one_lt_mabs.2 h.ne'

中文:
引理 one_lt_mabs_pos_of_one_lt
  条件: (h : 1 < a)
  结论: 1 < |a|ₘ
  证明: one_lt_mabs.2 h.ne'
-/
@[to_additive abs_pos_of_pos] lemma one_lt_mabs_pos_of_one_lt (h : 1 < a) : 1 < |a|ₘ :=
  one_lt_mabs.2 h.ne'

/--
lemma `one_lt_mabs_of_lt_one` / 引理 `one_lt_mabs_of_lt_one`

English:
lemma one_lt_mabs_of_lt_one
  given: (h : a < 1)
  statement: 1 < |a|ₘ
  proof: one_lt_mabs.2 h.ne

中文:
引理 one_lt_mabs_of_lt_one
  条件: (h : a < 1)
  结论: 1 < |a|ₘ
  证明: one_lt_mabs.2 h.ne
-/
@[to_additive abs_pos_of_neg] lemma one_lt_mabs_of_lt_one (h : a < 1) : 1 < |a|ₘ :=
  one_lt_mabs.2 h.ne

/--
lemma `inv_mabs_le` / 引理 `inv_mabs_le`

English:
lemma inv_mabs_le
  given: (a : α)
  statement: |a|ₘ⁻¹ <= a
  proof: by
  obtain h | h := le_total 1 a
  · simpa [mabs_of_one_le h] using (inv_le_one'.2 h).trans h
  · simp [mabs_of_le_one h]

中文:
引理 inv_mabs_le
  条件: (a : α)
  结论: |a|ₘ⁻¹ <= a
  证明: by
  obtain h | h := le_total 1 a
  · simpa [mabs_of_one_le h] using (inv_le_one'.2 h).trans h
  · simp [mabs_of_le_one h]
-/
@[to_additive] lemma inv_mabs_le (a : α) : |a|ₘ⁻¹ <= a := by
  obtain h | h := le_total 1 a
  · simpa [mabs_of_one_le h] using (inv_le_one'.2 h).trans h
  · simp [mabs_of_le_one h]

/--
lemma `one_le_mul_mabs` / 引理 `one_le_mul_mabs`

English:
lemma one_le_mul_mabs
  given: (a : α)
  statement: 1 <= a * |a|ₘ
  proof: by
  grw [← mul_inv_cancel a, inv_le_mabs a]

中文:
引理 one_le_mul_mabs
  条件: (a : α)
  结论: 1 <= a * |a|ₘ
  证明: by
  grw [← mul_inv_cancel a, inv_le_mabs a]
-/
@[to_additive add_abs_nonneg] lemma one_le_mul_mabs (a : α) : 1 <= a * |a|ₘ := by
  grw [← mul_inv_cancel a, inv_le_mabs a]

/--
lemma `inv_mabs_le_inv` / 引理 `inv_mabs_le_inv`

English:
lemma inv_mabs_le_inv
  given: (a : α)
  statement: |a|ₘ⁻¹ <= a⁻¹
  proof: by simpa using inv_mabs_le a⁻¹

中文:
引理 inv_mabs_le_inv
  条件: (a : α)
  结论: |a|ₘ⁻¹ <= a⁻¹
  证明: by simpa using inv_mabs_le a⁻¹
-/
@[to_additive] lemma inv_mabs_le_inv (a : α) : |a|ₘ⁻¹ <= a⁻¹ := by simpa using inv_mabs_le a⁻¹

variable [MulRightMono α]

/--
lemma `mabs_ne_one` / 引理 `mabs_ne_one`

English:
lemma mabs_ne_one
  statement: |a|ₘ != 1 ↔ a != 1
  proof: (one_le_mabs a).lt_iff_ne'.symm.trans one_lt_mabs

中文:
引理 mabs_ne_one
  结论: |a|ₘ != 1 ↔ a != 1
  证明: (one_le_mabs a).lt_iff_ne'.symm.trans one_lt_mabs
-/
@[to_additive] lemma mabs_ne_one : |a|ₘ != 1 ↔ a != 1 :=
  (one_le_mabs a).lt_iff_ne'.symm.trans one_lt_mabs

/--
lemma `mabs_eq_one` / 引理 `mabs_eq_one`

English:
lemma mabs_eq_one
  statement: |a|ₘ = 1 ↔ a = 1
  proof: not_iff_not.1 mabs_ne_one

中文:
引理 mabs_eq_one
  结论: |a|ₘ = 1 ↔ a = 1
  证明: not_iff_not.1 mabs_ne_one
-/
@[to_additive (attr := simp)] lemma mabs_eq_one : |a|ₘ = 1 ↔ a = 1 := not_iff_not.1 mabs_ne_one

/--
lemma `mabs_le_one` / 引理 `mabs_le_one`

English:
lemma mabs_le_one
  statement: |a|ₘ <= 1 ↔ a = 1
  proof: (one_le_mabs a).ge_iff_eq'.trans mabs_eq_one

中文:
引理 mabs_le_one
  结论: |a|ₘ <= 1 ↔ a = 1
  证明: (one_le_mabs a).ge_iff_eq'.trans mabs_eq_one
-/
@[to_additive (attr := simp) abs_nonpos_iff] lemma mabs_le_one : |a|ₘ <= 1 ↔ a = 1 :=
  (one_le_mabs a).ge_iff_eq'.trans mabs_eq_one

/--
lemma `mabs_le_mabs_of_le_one` / 引理 `mabs_le_mabs_of_le_one`

English:
lemma mabs_le_mabs_of_le_one
  given: (ha : a <= 1) (hab : b <= a)
  statement: |a|ₘ <= |b|ₘ
  proof: by
  rw [mabs_of_le_one ha]; rw [mabs_of_le_one (hab.trans ha)]; exact inv_le_inv_iff.mpr hab

中文:
引理 mabs_le_mabs_of_le_one
  条件: (ha : a <= 1) (hab : b <= a)
  结论: |a|ₘ <= |b|ₘ
  证明: by
  rw [mabs_of_le_one ha]; rw [mabs_of_le_one (hab.trans ha)]; exact inv_le_inv_iff.mpr hab
-/
@[to_additive] lemma mabs_le_mabs_of_le_one (ha : a <= 1) (hab : b <= a) : |a|ₘ <= |b|ₘ := by
  rw [mabs_of_le_one ha]; rw [mabs_of_le_one (hab.trans ha)]; exact inv_le_inv_iff.mpr hab

/--
lemma `mabs_lt` / 引理 `mabs_lt`

English:
lemma mabs_lt
  statement: |a|ₘ < b ↔ b⁻¹ < a ∧ a < b
  proof: max_lt_iff.trans and_comm.trans by rw [inv_lt']

中文:
引理 mabs_lt
  结论: |a|ₘ < b ↔ b⁻¹ < a ∧ a < b
  证明: max_lt_iff.trans and_comm.trans by rw [inv_lt']
-/
@[to_additive] lemma mabs_lt : |a|ₘ < b ↔ b⁻¹ < a ∧ a < b :=
max_lt_iff.trans and_comm.trans by rw [inv_lt']

/--
lemma `inv_lt_of_mabs_lt` / 引理 `inv_lt_of_mabs_lt`

English:
lemma inv_lt_of_mabs_lt
  given: (h : |a|ₘ < b)
  statement: b⁻¹ < a
  proof: (mabs_lt.mp h).1

中文:
引理 inv_lt_of_mabs_lt
  条件: (h : |a|ₘ < b)
  结论: b⁻¹ < a
  证明: (mabs_lt.mp h).1
-/
@[to_additive] lemma inv_lt_of_mabs_lt (h : |a|ₘ < b) : b⁻¹ < a := (mabs_lt.mp h).1

/--
lemma `max_div_min_eq_mabs'` / 引理 `max_div_min_eq_mabs'`

English:
lemma max_div_min_eq_mabs'
  given: (a b : α)
  statement: max a b / min a b = |a / b|ₘ
  proof: by
  rcases le_total a b with ab | ba
  · rw [max_eq_right ab, min_eq_left ab, mabs_of_le_one, inv_div]
    rwa [div_le_one']
  · rw [max_eq_left ba, min_eq_right ba, mabs_of_one_le]
    rwa [one_le_div']

中文:
引理 max_div_min_eq_mabs'
  条件: (a b : α)
  结论: max a b / min a b = |a / b|ₘ
  证明: by
  rcases le_total a b with ab | ba
  · rw [max_eq_right ab, min_eq_left ab, mabs_of_le_one, inv_div]
    rwa [div_le_one']
  · rw [max_eq_left ba, min_eq_right ba, mabs_of_one_le]
    rwa [one_le_div']
-/
@[to_additive] lemma max_div_min_eq_mabs' (a b : α) : max a b / min a b = |a / b|ₘ := by
  rcases le_total a b with ab | ba
  · rw [max_eq_right ab, min_eq_left ab, mabs_of_le_one, inv_div]
    rwa [div_le_one']
  · rw [max_eq_left ba, min_eq_right ba, mabs_of_one_le]
    rwa [one_le_div']

/--
lemma `max_div_min_eq_mabs` / 引理 `max_div_min_eq_mabs`

English:
lemma max_div_min_eq_mabs
  given: (a b : α)
  statement: max a b / min a b = |b / a|ₘ
  proof: by
  rw [mabs_div_comm]; rw [max_div_min_eq_mabs']

中文:
引理 max_div_min_eq_mabs
  条件: (a b : α)
  结论: max a b / min a b = |b / a|ₘ
  证明: by
  rw [mabs_div_comm]; rw [max_div_min_eq_mabs']
-/
@[to_additive] lemma max_div_min_eq_mabs (a b : α) : max a b / min a b = |b / a|ₘ := by
  rw [mabs_div_comm]; rw [max_div_min_eq_mabs']

end LinearOrder

namespace LatticeOrderedAddCommGroup
variable [Lattice α] [AddCommGroup α] {s t : Set α}

/--
Definition of `IsSolid` / `IsSolid` 的定义

English:
definition IsSolid
  signature: (s : Set α)
  body: forall ⦃x⦄, x in s -> forall ⦃y⦄, |y| <= |x| -> y in s

中文:
定义 IsSolid
  签名: (s : Set α)
  定义体: forall ⦃x⦄, x in s -> forall ⦃y⦄, |y| <= |x| -> y in s
-/
def IsSolid (s : Set α) : Prop := forall ⦃x⦄, x in s -> forall ⦃y⦄, |y| <= |x| -> y in s

/--
Definition of `solidClosure` / `solidClosure` 的定义

English:
definition solidClosure
  signature: (s : Set α)
  body: {y | exists x in s, |y| <= |x|}

中文:
定义 solidClosure
  签名: (s : Set α)
  定义体: {y | exists x in s, |y| <= |x|}
-/
def solidClosure (s : Set α) : Set α := {y | exists x in s, |y| <= |x|}

/--
lemma `isSolid_solidClosure` / 引理 `isSolid_solidClosure`

English:
lemma isSolid_solidClosure
  given: (s : Set α)
  statement: IsSolid (solidClosure s)
  proof: fun _ ⟨y, hy, hxy⟩ _ hzx => ⟨y, hy, hzx.trans hxy⟩

中文:
引理 isSolid_solidClosure
  条件: (s : Set α)
  结论: IsSolid (solidClosure s)
  证明: fun _ ⟨y, hy, hxy⟩ _ hzx => ⟨y, hy, hzx.trans hxy⟩

Depends on / 依赖: hzx.trans
-/
lemma isSolid_solidClosure (s : Set α) : IsSolid (solidClosure s) :=
  fun _ ⟨y, hy, hxy⟩ _ hzx => ⟨y, hy, hzx.trans hxy⟩

/--
lemma `solidClosure_min` / 引理 `solidClosure_min`

English:
lemma solidClosure_min
  given: (hst : s subseteq t) (ht : IsSolid t)
  statement: solidClosure s subseteq t
  proof: fun _ ⟨_, hy, hxy⟩ => ht (hst hy) hxy

中文:
引理 solidClosure_min
  条件: (hst : s subseteq t) (ht : IsSolid t)
  结论: solidClosure s subseteq t
  证明: fun _ ⟨_, hy, hxy⟩ => ht (hst hy) hxy
-/
lemma solidClosure_min (hst : s subseteq t) (ht : IsSolid t) : solidClosure s subseteq t :=
  fun _ ⟨_, hy, hxy⟩ => ht (hst hy) hxy

end LatticeOrderedAddCommGroup

namespace Pi

variable {ι : Type*} {α : ι -> Type*} [forall i, Group (α i)] (f : (i : ι) -> α i)

@[to_additive (attr := simp)]
/--
lemma `mabs_apply` / 引理 `mabs_apply`

English:
lemma mabs_apply
  given: [forall i, Lattice (α i)] (i : ι)
  statement: |f|ₘ i = |f i|ₘ
  proof: rfl

@[to_additive (attr := push ←)]

中文:
引理 mabs_apply
  条件: [对任意 i, Lattice (α i)] (i : ι)
  结论: |f|ₘ i = |f i|ₘ
  证明: rfl

@[to_additive (attr := push ←)]
-/
lemma mabs_apply [forall i, Lattice (α i)] (i : ι) : |f|ₘ i = |f i|ₘ := rfl

@[to_additive (attr := push ←)]
/--
lemma `mabs_def` / 引理 `mabs_def`

English:
lemma mabs_def
  given: [forall i, Lattice (α i)]
  statement: |f|ₘ = fun i => |f i|ₘ
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 mabs_def
  条件: [对任意 i, Lattice (α i)]
  结论: |f|ₘ = fun i => |f i|ₘ
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma mabs_def [forall i, Lattice (α i)] : |f|ₘ = fun i => |f i|ₘ := rfl

@[to_additive (attr := simp)]
/--
lemma `mabs_eq_one` / 引理 `mabs_eq_one`

English:
lemma mabs_eq_one
  given: [forall i, LinearOrder (α i)] [forall i, MulLeftMono (α i)] [forall i, MulRightMono (α i)]
  proof: ⟨fun h => funext fun i => by simpa using congr_fun h i, fun h => funext fun i => by simp [h]⟩

中文:
引理 mabs_eq_one
  条件: [对任意 i, LinearOrder (α i)] [对任意 i, MulLeftMono (α i)] [对任意 i, MulRightMono (α i)]
  证明: ⟨fun h => funext fun i => by simpa using congr_fun h i, fun h => funext fun i => by simp [h]⟩

Depends on / 依赖: congr_fun
-/
lemma mabs_eq_one [forall i, LinearOrder (α i)] [forall i, MulLeftMono (α i)] [forall i, MulRightMono (α i)] :
    |f|ₘ = 1 ↔ f = 1 :=
  ⟨fun h => funext fun i => by simpa using congr_fun h i, fun h => funext fun i => by simp [h]⟩

end Pi
