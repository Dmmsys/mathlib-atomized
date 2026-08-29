/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual

/-!
# Conditionally complete lattices and groups.

-/

public section

open Set

section Mul

variable {α : Type*} {ι : Sort*} [Nonempty ι] [ConditionallyCompleteLattice α] [Mul α]

@[to_additive]
/--
lemma `ciSup_mul_le_ciSup_mul_ciSup` / 引理 `ciSup_mul_le_ciSup_mul_ciSup`

English:
lemma ciSup_mul_le_ciSup_mul_ciSup
  statement: [MulLeftMono α] [MulRightMono α]
  proof: ciSup_le fun i => mul_le_mul' (le_ciSup hf i) (le_ciSup hg i)

@[to_additive]

中文:
引理 ciSup_mul_le_ciSup_mul_ciSup
  结论: [MulLeftMono α] [MulRightMono α]
  证明: ciSup_le fun i => mul_le_mul' (le_ciSup hf i) (le_ciSup hg i)

@[to_additive]

Depends on / 依赖: ciSup_le, le_ciSup, mul_le_mul
-/
lemma ciSup_mul_le_ciSup_mul_ciSup [MulLeftMono α] [MulRightMono α]
    {f g : ι -> α} (hf : BddAbove (range f)) (hg : BddAbove (range g)) :
    ⨆ i, f i * g i <= (⨆ i, f i) * ⨆ i, g i :=
  ciSup_le fun i => mul_le_mul' (le_ciSup hf i) (le_ciSup hg i)

@[to_additive]
/--
lemma `ciInf_mul_ciInf_le_ciInf_mul` / 引理 `ciInf_mul_ciInf_le_ciInf_mul`

English:
lemma ciInf_mul_ciInf_le_ciInf_mul
  statement: [MulLeftMono α] [MulRightMono α]
  proof: le_ciInf fun i => mul_le_mul' (ciInf_le hf i) (ciInf_le hg i)

中文:
引理 ciInf_mul_ciInf_le_ciInf_mul
  结论: [MulLeftMono α] [MulRightMono α]
  证明: le_ciInf fun i => mul_le_mul' (ciInf_le hf i) (ciInf_le hg i)

Depends on / 依赖: ciInf_le, le_ciInf, mul_le_mul
-/
lemma ciInf_mul_ciInf_le_ciInf_mul [MulLeftMono α] [MulRightMono α]
    {f g : ι -> α} (hf : BddBelow (range f)) (hg : BddBelow (range g)) :
    (⨅ i, f i) * ⨅ i, g i <= ⨅ i, f i * g i :=
  le_ciInf fun i => mul_le_mul' (ciInf_le hf i) (ciInf_le hg i)

end Mul

section Group

variable {α : Type*} {ι : Sort*} {ι' : Sort*} [Nonempty ι] [Nonempty ι']
  [ConditionallyCompleteLattice α] [Group α]

@[to_additive]
/--
theorem `le_mul_ciInf` / 定理 `le_mul_ciInf`

English:
theorem le_mul_ciInf
  statement: [MulLeftMono α] {a : α} {g : α} {h : ι -> α}
  proof: inv_mul_le_iff_le_mul.mp le_ciInf fun _ => inv_mul_le_iff_le_mul.mpr H _

@[to_additive]

中文:
定理 le_mul_ciInf
  结论: [MulLeftMono α] {a : α} {g : α} {h : ι -> α}
  证明: inv_mul_le_iff_le_mul.mp le_ciInf fun _ => inv_mul_le_iff_le_mul.mpr H _

@[to_additive]

Depends on / 依赖: inv_mul_le_iff_le_mul, inv_mul_le_iff_le_mul.mp, inv_mul_le_iff_le_mul.mpr, le_ciInf
-/
theorem le_mul_ciInf [MulLeftMono α] {a : α} {g : α} {h : ι -> α}
    (H : forall j, a <= g * h j) : a <= g * iInf h :=
inv_mul_le_iff_le_mul.mp le_ciInf fun _ => inv_mul_le_iff_le_mul.mpr H _

@[to_additive]
/--
theorem `mul_ciSup_le` / 定理 `mul_ciSup_le`

English:
theorem mul_ciSup_le
  statement: [MulLeftMono α] {a : α} {g : α} {h : ι -> α}
  proof: le_mul_ciInf (α := αᵒᵈ) H

@[to_additive]

中文:
定理 mul_ciSup_le
  结论: [MulLeftMono α] {a : α} {g : α} {h : ι -> α}
  证明: le_mul_ciInf (α := αᵒᵈ) H

@[to_additive]

Depends on / 依赖: le_mul_ciInf
-/
theorem mul_ciSup_le [MulLeftMono α] {a : α} {g : α} {h : ι -> α}
    (H : forall j, g * h j <= a) : g * iSup h <= a :=
  le_mul_ciInf (α := αᵒᵈ) H

@[to_additive]
/--
theorem `le_ciInf_mul` / 定理 `le_ciInf_mul`

English:
theorem le_ciInf_mul
  statement: [MulRightMono α] {a : α} {g : ι -> α}
  proof: mul_inv_le_iff_le_mul.mp le_ciInf fun _ => mul_inv_le_iff_le_mul.mpr H _

@[to_additive]

中文:
定理 le_ciInf_mul
  结论: [MulRightMono α] {a : α} {g : ι -> α}
  证明: mul_inv_le_iff_le_mul.mp le_ciInf fun _ => mul_inv_le_iff_le_mul.mpr H _

@[to_additive]

Depends on / 依赖: le_ciInf, mul_inv_le_iff_le_mul, mul_inv_le_iff_le_mul.mp, mul_inv_le_iff_le_mul.mpr
-/
theorem le_ciInf_mul [MulRightMono α] {a : α} {g : ι -> α}
    {h : α} (H : forall i, a <= g i * h) : a <= iInf g * h :=
mul_inv_le_iff_le_mul.mp le_ciInf fun _ => mul_inv_le_iff_le_mul.mpr H _

@[to_additive]
/--
theorem `ciSup_mul_le` / 定理 `ciSup_mul_le`

English:
theorem ciSup_mul_le
  statement: [MulRightMono α] {a : α} {g : ι -> α}
  proof: le_ciInf_mul (α := αᵒᵈ) H

@[to_additive]

中文:
定理 ciSup_mul_le
  结论: [MulRightMono α] {a : α} {g : ι -> α}
  证明: le_ciInf_mul (α := αᵒᵈ) H

@[to_additive]

Depends on / 依赖: le_ciInf_mul
-/
theorem ciSup_mul_le [MulRightMono α] {a : α} {g : ι -> α}
    {h : α} (H : forall i, g i * h <= a) : iSup g * h <= a :=
  le_ciInf_mul (α := αᵒᵈ) H

@[to_additive]
/--
theorem `le_ciInf_mul_ciInf` / 定理 `le_ciInf_mul_ciInf`

English:
theorem le_ciInf_mul_ciInf
  statement: [MulLeftMono α] [MulRightMono α] {a : α} {g : ι -> α} {h : ι' -> α}
  proof: le_ciInf_mul fun _ => le_mul_ciInf H _

@[to_additive]

中文:
定理 le_ciInf_mul_ciInf
  结论: [MulLeftMono α] [MulRightMono α] {a : α} {g : ι -> α} {h : ι' -> α}
  证明: le_ciInf_mul fun _ => le_mul_ciInf H _

@[to_additive]

Depends on / 依赖: le_ciInf_mul, le_mul_ciInf
-/
theorem le_ciInf_mul_ciInf [MulLeftMono α] [MulRightMono α] {a : α} {g : ι -> α} {h : ι' -> α}
    (H : forall i j, a <= g i * h j) : a <= iInf g * iInf h :=
le_ciInf_mul fun _ => le_mul_ciInf H _

@[to_additive]
/--
theorem `ciSup_mul_ciSup_le` / 定理 `ciSup_mul_ciSup_le`

English:
theorem ciSup_mul_ciSup_le
  statement: [MulLeftMono α] [MulRightMono α] {a : α} {g : ι -> α} {h : ι' -> α}
  proof: ciSup_mul_le fun _ => mul_ciSup_le H _

中文:
定理 ciSup_mul_ciSup_le
  结论: [MulLeftMono α] [MulRightMono α] {a : α} {g : ι -> α} {h : ι' -> α}
  证明: ciSup_mul_le fun _ => mul_ciSup_le H _

Depends on / 依赖: ciSup_mul_le, mul_ciSup_le
-/
theorem ciSup_mul_ciSup_le [MulLeftMono α] [MulRightMono α] {a : α} {g : ι -> α} {h : ι' -> α}
    (H : forall i j, g i * h j <= a) : iSup g * iSup h <= a :=
ciSup_mul_le fun _ => mul_ciSup_le H _

end Group
