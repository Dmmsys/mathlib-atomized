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
/-
**ciSup_mul_le_ciSup_mul_ciSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ciSup_mul_le_ciSup_mul_ciSup [MulLeftMono α] [MulRightMono α] {f g : ι -> 
α} (hf : BddAbove (range f)) (hg : BddAbove (range g)) : ⨆ i, f i * g i <= (⨆ i,
 f i) * ⨆ i, g i
参数：hf : BddAbove (range f)；hg : BddAbove (range g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
-/
lemma ciSup_mul_le_ciSup_mul_ciSup [MulLeftMono α] [MulRightMono α]
    {f g : ι → α} (hf : BddAbove (range f)) (hg : BddAbove (range g)) :
    ⨆ i, f i * g i ≤ (⨆ i, f i) * ⨆ i, g i :=
  ciSup_le fun i ↦ mul_le_mul' (le_ciSup hf i) (le_ciSup hg i)

@[to_additive]
/-
**ciInf_mul_ciInf_le_ciInf_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ciInf_mul_ciInf_le_ciInf_mul [MulLeftMono α] [MulRightMono α] {f g : ι -> 
α} (hf : BddBelow (range f)) (hg : BddBelow (range g)) : (⨅ i, f i) * ⨅ i, g i <
= ⨅ i, f i * g i
参数：hf : BddBelow (range f)；hg : BddBelow (range g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `ciInf_le`：ciInf_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) : iInf 
f <= f c
-/
lemma ciInf_mul_ciInf_le_ciInf_mul [MulLeftMono α] [MulRightMono α]
    {f g : ι → α} (hf : BddBelow (range f)) (hg : BddBelow (range g)) :
    (⨅ i, f i) * ⨅ i, g i ≤ ⨅ i, f i * g i :=
  le_ciInf fun i ↦ mul_le_mul' (ciInf_le hf i) (ciInf_le hg i)

end Mul

section Group

variable {α : Type*} {ι : Sort*} {ι' : Sort*} [Nonempty ι] [Nonempty ι']
  [ConditionallyCompleteLattice α] [Group α]

@[to_additive]
/-
**le_mul_ciInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_ciInf [MulLeftMono α] {a : α} {g : α} {h : ι -> α} (H : forall j, a
 <= g * h j) : a <= g * iInf h
参数：H : forall j, a <= g * h j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inv_mul_le_iff_le_mul`：inv_mul_le_iff_le_mul : b⁻¹ * a <= c ↔ a <= b * c
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem le_mul_ciInf [MulLeftMono α] {a : α} {g : α} {h : ι → α}
    (H : ∀ j, a ≤ g * h j) : a ≤ g * iInf h :=
  inv_mul_le_iff_le_mul.mp <| le_ciInf fun _ => inv_mul_le_iff_le_mul.mpr <| H _

@[to_additive]
/-
**mul_ciSup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_ciSup_le [MulLeftMono α] {a : α} {g : α} {h : ι -> α} (H : forall j, g
 * h j <= a) : g * iSup h <= a
参数：H : forall j, g * h j <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_mul_ciInf`：le_mul_ciInf [MulLeftMono α] {a : α} {g : α} {h : ι -> α} 
(H : forall j, a <= g * h j) : a <= g * iInf h
-/
theorem mul_ciSup_le [MulLeftMono α] {a : α} {g : α} {h : ι → α}
    (H : ∀ j, g * h j ≤ a) : g * iSup h ≤ a :=
  le_mul_ciInf (α := αᵒᵈ) H

@[to_additive]
/-
**le_ciInf_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_ciInf_mul [MulRightMono α] {a : α} {g : ι -> α} {h : α} (H : forall i, 
a <= g i * h) : a <= iInf g * h
参数：H : forall i, a <= g i * h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_inv_le_iff_le_mul`：mul_inv_le_iff_le_mul : a * b⁻¹ <= c ↔ a <= c * b
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem le_ciInf_mul [MulRightMono α] {a : α} {g : ι → α}
    {h : α} (H : ∀ i, a ≤ g i * h) : a ≤ iInf g * h :=
  mul_inv_le_iff_le_mul.mp <| le_ciInf fun _ => mul_inv_le_iff_le_mul.mpr <| H _

@[to_additive]
/-
**ciSup_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_mul_le [MulRightMono α] {a : α} {g : ι -> α} {h : α} (H : forall i, 
g i * h <= a) : iSup g * h <= a
参数：H : forall i, g i * h <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciInf_mul`：le_ciInf_mul [MulRightMono α] {a : α} {g : ι -> α} {h : α}
 (H : forall i, a <= g i * h) : a <= iInf g * h
-/
theorem ciSup_mul_le [MulRightMono α] {a : α} {g : ι → α}
    {h : α} (H : ∀ i, g i * h ≤ a) : iSup g * h ≤ a :=
  le_ciInf_mul (α := αᵒᵈ) H

@[to_additive]
/-
**le_ciInf_mul_ciInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_ciInf_mul_ciInf [MulLeftMono α] [MulRightMono α] {a : α} {g : ι -> α} {
h : ι' -> α} (H : forall i j, a <= g i * h j) : a <= iInf g * iInf h
参数：H : forall i j, a <= g i * h j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciInf_mul`：le_ciInf_mul [MulRightMono α] {a : α} {g : ι -> α} {h : α}
 (H : forall i, a <= g i * h) : a <= iInf g * h
· 使用定理 `le_mul_ciInf`：le_mul_ciInf [MulLeftMono α] {a : α} {g : α} {h : ι -> α} 
(H : forall j, a <= g * h j) : a <= g * iInf h
-/
theorem le_ciInf_mul_ciInf [MulLeftMono α] [MulRightMono α] {a : α} {g : ι → α} {h : ι' → α}
    (H : ∀ i j, a ≤ g i * h j) : a ≤ iInf g * iInf h :=
  le_ciInf_mul fun _ => le_mul_ciInf <| H _

@[to_additive]
/-
**ciSup_mul_ciSup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_mul_ciSup_le [MulLeftMono α] [MulRightMono α] {a : α} {g : ι -> α} {
h : ι' -> α} (H : forall i j, g i * h j <= a) : iSup g * iSup h <= a
参数：H : forall i j, g i * h j <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_mul_le`：ciSup_mul_le [MulRightMono α] {a : α} {g : ι -> α} {h : α}
 (H : forall i, g i * h <= a) : iSup g * h <= a
· 使用定理 `mul_ciSup_le`：mul_ciSup_le [MulLeftMono α] {a : α} {g : α} {h : ι -> α} 
(H : forall j, g * h j <= a) : g * iSup h <= a
-/
theorem ciSup_mul_ciSup_le [MulLeftMono α] [MulRightMono α] {a : α} {g : ι → α} {h : ι' → α}
    (H : ∀ i j, g i * h j ≤ a) : iSup g * iSup h ≤ a :=
  ciSup_mul_le fun _ => mul_ciSup_le <| H _

end Group

