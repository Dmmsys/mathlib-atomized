/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Patrick Massot
-/
module

public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Order.LocalExtr

/-!
# Local maxima from monotonicity and antitonicity

In this file we prove a lemma that is useful for the First Derivative Test in calculus,
and its dual.

## Main statements

* `isLocalMax_of_mono_anti` : if a function `f` is monotone to the left of `x`
  and antitone to the right of `x` then `f` has a local maximum at `x`.

* `isLocalMin_of_anti_mono` : the dual statement for minima.

-/

public section

open Set

/-- If `f` is monotone on `Ioc a b` and antitone on `Ico b c` then `f` has
a local maximum at `b`. -/
/-
**isLocalMax_of_mono_anti** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocalMax_of_mono_anti {α : Type*} [TopologicalSpace α] [LinearOrder α] [
OrderClosedTopology α] {β : Type*} [Preorder β] {a b c : α} (g₀ : a < b) (g₁ : b
 < c) {f : α -> β} (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f (Ico b c)) :
 IsLocalMax f b
参数：g₀ : a < b；g₁ : b < c；h₀ : MonotoneOn f (Ioc a b)；h₁ : AntitoneOn f (Ico b c)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxOn.isLocalMax`：IsMaxOn.isLocalMax (hf : IsMaxOn f s a) (hs : s in 𝓝
 a) : IsLocalMax f a
· 使用引理 `isMaxOn_Ioo_of_mono_anti`：isMaxOn_Ioo_of_mono_anti (h₀ : MonotoneOn f (I
oc a b)) (h₁ : AntitoneOn f (Ico b c)) : IsMaxOn f (Ioo a c) b
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x

--- 原说明 ---
If `f` is monotone on `Ioc a b` and antitone on `Ico b c` then `f` has
a local maximum at `b`.
-/
lemma isLocalMax_of_mono_anti
    {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {β : Type*} [Preorder β]
    {a b c : α} (g₀ : a < b) (g₁ : b < c) {f : α → β}
    (h₀ : MonotoneOn f (Ioc a b))
    (h₁ : AntitoneOn f (Ico b c)) : IsLocalMax f b :=
  (isMaxOn_Ioo_of_mono_anti h₀ h₁).isLocalMax (Ioo_mem_nhds g₀ g₁)

/-- If `f` is antitone on `Ioc a b` and monotone on `Ico b c` then `f` has
a local minimum at `b`. -/
/-
**isLocalMin_of_anti_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocalMin_of_anti_mono {α : Type*} [TopologicalSpace α] [LinearOrder α] [
OrderClosedTopology α] {β : Type*} [Preorder β] {a b c : α} (g₀ : a < b) (g₁ : b
 < c) {f : α -> β} (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Ico b c)) :
 IsLocalMin f b
参数：g₀ : a < b；g₁ : b < c；h₀ : AntitoneOn f (Ioc a b)；h₁ : MonotoneOn f (Ico b c)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isLocalMax_of_mono_anti`：isLocalMax_of_mono_anti {α : Type*} [Topologica
lSpace α] [LinearOrder α] [OrderClosedTopology α] {β : Type*} [Preorder β] {a b 
c : α} (g₀ : …

--- 原说明 ---
If `f` is antitone on `Ioc a b` and monotone on `Ico b c` then `f` has
a local minimum at `b`.
-/
lemma isLocalMin_of_anti_mono
    {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {β : Type*} [Preorder β] {a b c : α} (g₀ : a < b) (g₁ : b < c) {f : α → β}
    (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Ico b c)) : IsLocalMin f b :=
  isLocalMax_of_mono_anti (β := βᵒᵈ) g₀ g₁ h₀ h₁
