/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Interval.Set.Disjoint

/-!
# Disjointness of `Filter.atTop` and `Filter.atBot`
-/

public section

assert_not_exists Finset

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

@[to_dual disjoint_atTop_principal_Iio]
/-
**Filter.disjoint_atBot_principal_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：disjoint_atBot_principal_Ioi [Preorder α] (x : α) : Disjoint atBot (𝓟 (Ioi
 x))
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.disjoint_of_disjoint_of_mem`：disjoint_of_disjoint_of_mem {f g : F
ilter α} {s t : Set α} (h : Disjoint s t) (hs : s in f) (ht : t in g) : Disjoint
 f g
· 使用定理 `Set.Iic_disjoint_Ioi`：Iic_disjoint_Ioi (h : a <= b) : Disjoint (Iic a) (
Ioi b)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Filter.Iic_mem_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α), Set.
Iic a ∈ Filter.atBot
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
-/
theorem disjoint_atBot_principal_Ioi [Preorder α] (x : α) : Disjoint atBot (𝓟 (Ioi x)) :=
  disjoint_of_disjoint_of_mem (Iic_disjoint_Ioi le_rfl) (Iic_mem_atBot x) (mem_principal_self _)

@[to_dual disjoint_atBot_principal_Ici]
/-
**Filter.disjoint_atTop_principal_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：disjoint_atTop_principal_Iic [Preorder α] [NoTopOrder α] (x : α) : Disjoin
t atTop (𝓟 (Iic x))
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.disjoint_of_disjoint_of_mem`：disjoint_of_disjoint_of_mem {f g : F
ilter α} {s t : Set α} (h : Disjoint s t) (hs : s in f) (ht : t in g) : Disjoint
 f g
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Set.Iic_disjoint_Ioi`：Iic_disjoint_Ioi (h : a <= b) : Disjoint (Iic a) (
Ioi b)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
-/
theorem disjoint_atTop_principal_Iic [Preorder α] [NoTopOrder α] (x : α) :
    Disjoint atTop (𝓟 (Iic x)) :=
  disjoint_of_disjoint_of_mem (Iic_disjoint_Ioi le_rfl).symm (Ioi_mem_atTop x)
    (mem_principal_self _)

@[to_dual disjoint_pure_atBot]
/-
**Filter.disjoint_pure_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：disjoint_pure_atTop [Preorder α] [NoTopOrder α] (x : α) : Disjoint (pure x
) atTop
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.mem_pure`：mem_pure {a : α} {s : Set α} : s in (pure a : Filter α)
 ↔ a in s
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
· 使用定理 `Filter.disjoint_atTop_principal_Iic`：disjoint_atTop_principal_Iic [Preor
der α] [NoTopOrder α] (x : α) : Disjoint atTop (𝓟 (Iic x))
-/
theorem disjoint_pure_atTop [Preorder α] [NoTopOrder α] (x : α) : Disjoint (pure x) atTop :=
  Disjoint.symm <| (disjoint_atTop_principal_Iic x).mono_right <| le_principal_iff.2 <|
    mem_pure.2 self_mem_Iic

@[to_dual disjoint_atTop_atBot]
/-
**Filter.disjoint_atBot_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：disjoint_atBot_atTop [PartialOrder α] [Nontrivial α] : Disjoint (atBot : F
ilter α) atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `Filter.disjoint_of_disjoint_of_mem`：disjoint_of_disjoint_of_mem {f g : F
ilter α} {s t : Set α} (h : Disjoint s t) (hs : s in f) (ht : t in g) : Disjoint
 f g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Iic_disjoint_Ici`：∀ {α : Type v} [inst : Preorder α] {a b : α}, Disj
oint (Set.Iic a) (Set.Ici b) ↔ ¬b ≤ a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Filter.Iic_mem_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α), Set.
Iic a ∈ Filter.atBot
· 使用定理 `Filter.Ici_mem_atTop`：Ici_mem_atTop [Preorder α] (a : α) : Ici a in (atT
op : Filter α)
-/
theorem disjoint_atBot_atTop [PartialOrder α] [Nontrivial α] :
    Disjoint (atBot : Filter α) atTop := by
  rcases exists_pair_ne α with ⟨x, y, hne⟩
  by_cases hle : x ≤ y
  · refine disjoint_of_disjoint_of_mem ?_ (Iic_mem_atBot x) (Ici_mem_atTop y)
    exact Iic_disjoint_Ici.2 (hle.lt_of_ne hne).not_ge
  · refine disjoint_of_disjoint_of_mem ?_ (Iic_mem_atBot y) (Ici_mem_atTop x)
    exact Iic_disjoint_Ici.2 hle

end Filter

