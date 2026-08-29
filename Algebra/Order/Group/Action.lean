/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Results about `CovariantClass G α HSMul.hSMul LE.le`

When working with group actions rather than modules, we drop the `0 < c` condition.

Notably these are relevant for pointwise actions on set-like objects.
-/

public section

variable {ι : Sort*} {M α : Type*}

/--
theorem `smul_mono_right` / 定理 `smul_mono_right`

English:
theorem smul_mono_right
  statement: [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LE.le]
  proof: fun _ _ => CovariantClass.elim _

中文:
定理 smul_mono_right
  结论: [标量乘法 M α] [预序 α] [协变类 M α 异质标量乘法.hSMul LE.le]
  证明: fun _ _ => CovariantClass.elim _

Depends on / 依赖: CovariantClass, CovariantClass.elim
-/
theorem smul_mono_right [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LE.le]
    (m : M) : Monotone (HSMul.hSMul m : α -> α) :=
  fun _ _ => CovariantClass.elim _

/-- A copy of `smul_mono_right` that is understood by `gcongr`. -/
@[gcongr]
/--
theorem `smul_le_smul_left` / 定理 `smul_le_smul_left`

English:
theorem smul_le_smul_left
  statement: [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LE.le]
  proof: smul_mono_right _ h

中文:
定理 smul_le_smul_left
  结论: [标量乘法 M α] [预序 α] [协变类 M α 异质标量乘法.hSMul LE.le]
  证明: smul_mono_right _ h

Depends on / 依赖: smul_mono_right
-/
theorem smul_le_smul_left [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LE.le]
    (m : M) {a b : α} (h : a <= b) :
    m • a <= m • b :=
  smul_mono_right _ h

/--
theorem `smul_inf_le` / 定理 `smul_inf_le`

English:
theorem smul_inf_le
  statement: [SMul M α] [SemilatticeInf α] [CovariantClass M α HSMul.hSMul LE.le]
  proof: (smul_mono_right _).map_inf_le _ _

中文:
定理 smul_inf_le
  结论: [标量乘法 M α] [SemilatticeInf α] [协变类 M α 异质标量乘法.hSMul LE.le]
  证明: (smul_mono_right _).map_inf_le _ _

Depends on / 依赖: map_inf_le, smul_mono_right
-/
theorem smul_inf_le [SMul M α] [SemilatticeInf α] [CovariantClass M α HSMul.hSMul LE.le]
    (m : M) (a₁ a₂ : α) : m • (a₁ ⊓ a₂) <= m • a₁ ⊓ m • a₂ :=
  (smul_mono_right _).map_inf_le _ _

/--
theorem `smul_iInf_le` / 定理 `smul_iInf_le`

English:
theorem smul_iInf_le
  statement: [SMul M α] [CompleteLattice α] [CovariantClass M α HSMul.hSMul LE.le]
  proof: le_iInf fun _ => smul_mono_right _ (iInf_le _ _)

中文:
定理 smul_iInf_le
  结论: [标量乘法 M α] [完备格 α] [协变类 M α 异质标量乘法.hSMul LE.le]
  证明: le_iInf fun _ => smul_mono_right _ (iInf_le _ _)

Depends on / 依赖: iInf_le, le_iInf, smul_mono_right
-/
theorem smul_iInf_le [SMul M α] [CompleteLattice α] [CovariantClass M α HSMul.hSMul LE.le]
    {m : M} {t : ι -> α} :
    m • iInf t <= ⨅ i, m • t i :=
  le_iInf fun _ => smul_mono_right _ (iInf_le _ _)

/--
theorem `smul_strictMono_right` / 定理 `smul_strictMono_right`

English:
theorem smul_strictMono_right
  statement: [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LT.lt]
  proof: fun _ _ => CovariantClass.elim _

中文:
定理 smul_strictMono_right
  结论: [标量乘法 M α] [预序 α] [协变类 M α 异质标量乘法.hSMul LT.lt]
  证明: fun _ _ => CovariantClass.elim _

Depends on / 依赖: CovariantClass, CovariantClass.elim
-/
theorem smul_strictMono_right [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LT.lt]
    (m : M) : StrictMono (HSMul.hSMul m : α -> α) :=
  fun _ _ => CovariantClass.elim _

/--
lemma `le_pow_smul` / 引理 `le_pow_smul`

English:
lemma le_pow_smul
  statement: {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α}
  proof: by
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ n hn =>
    rw [pow_succ']; rw [mul_smul]
    exact h.trans (smul_mono_right g hn)

中文:
引理 le_pow_smul
  结论: {G : 类型} [幺半群 G] {α : 类型} [预序 α] {g : G} {a : α}
  证明: by
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ n hn =>
    rw [pow_succ']; rw [mul_smul]
    exact h.trans (smul_mono_right g hn)

Depends on / 依赖: h.trans, mul_smul, one_smul, pow_succ, pow_zero, smul_mono_right
-/
lemma le_pow_smul {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : a <= g • a) (n : Nat) : a <= g ^ n • a := by
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ n hn =>
    rw [pow_succ']; rw [mul_smul]
    exact h.trans (smul_mono_right g hn)

/--
lemma `pow_smul_le` / 引理 `pow_smul_le`

English:
lemma pow_smul_le
  statement: {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α}
  proof: by
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ n hn =>
    rw [pow_succ']; rw [mul_smul]
    exact (smul_mono_right g hn).trans h

中文:
引理 pow_smul_le
  结论: {G : 类型} [幺半群 G] {α : 类型} [预序 α] {g : G} {a : α}
  证明: by
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ n hn =>
    rw [pow_succ']; rw [mul_smul]
    exact (smul_mono_right g hn).trans h

Depends on / 依赖: mul_smul, one_smul, pow_succ, pow_zero, smul_mono_right
-/
lemma pow_smul_le {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : g • a <= a) (n : Nat) : g ^ n • a <= a := by
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ n hn =>
    rw [pow_succ']; rw [mul_smul]
    exact (smul_mono_right g hn).trans h
