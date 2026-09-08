/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.NNReal.Defs

/-!
# Specific lemmas about convexity over `ℝ≥0`

This file collects some specific results about convexity over the ring `ℝ≥0`.
Expand as needed.
-/

public section

open Set
open scoped NNReal

namespace NNReal

/-
**NNReal.Icc_subset_segment** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {x y : NNReal}, Set.Icc x y ⊆ segment NNReal x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonneg.Icc_subset_segment`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : L
inearOrder 𝕜] [inst_2 : IsStrictOrderedRing 𝕜] {x y : { t // 0 ≤ t }},   Set.Icc
 x y ⊆ segment …
-/
protected lemma Icc_subset_segment {x y : ℝ≥0} :
    Icc x y ⊆ segment ℝ≥0 x y :=
  Nonneg.Icc_subset_segment
/-
**NNReal.segment_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {x y : NNReal}, x ≤ y → segment NNReal x y = Set.Icc x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonneg.segment_eq_Icc`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : Linea
rOrder 𝕜] [inst_2 : IsStrictOrderedRing 𝕜] {x y : { t // 0 ≤ t }},   x ≤ y → seg
ment { t //…
-/
protected lemma segment_eq_Icc {x y : ℝ≥0} (hxy : x ≤ y) :
    segment ℝ≥0 x y = Icc x y :=
  Nonneg.segment_eq_Icc hxy
/-
**NNReal.segment_eq_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {x y : NNReal}, segment NNReal x y = Set.uIcc x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonneg.segment_eq_uIcc`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : Line
arOrder 𝕜] [inst_2 : IsStrictOrderedRing 𝕜] {x y : { t // 0 ≤ t }},   segment { 
t // 0 ≤ t }…
-/
protected lemma segment_eq_uIcc {x y : ℝ≥0} :
    segment ℝ≥0 x y = uIcc x y :=
  Nonneg.segment_eq_uIcc

set_option backward.isDefEq.respectTransparency false in
/-
**NNReal.convex_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_1 : _root_.Module ℝ M] {s 
: Set M}, Convex NNReal s ↔ Convex ℝ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Convex.lift`：Convex.lift [SMulPosMono R 𝕜] {s : Set E} (hs : Convex 𝕜 s)
 : Convex R s
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `IsOrderedModule.toSMulPosMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
-/
protected lemma convex_iff {M : Type*} [AddCommMonoid M] [Module ℝ M] {s : Set M} :
    Convex ℝ≥0 s ↔ Convex ℝ s := by
  refine ⟨fun H ↦ ?_, Convex.lift ℝ≥0⟩
  intro _ hx _ hy a b ha hb hab
  exact H hx hy (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) zero_le zero_le (by ext; simpa)

end NNReal

