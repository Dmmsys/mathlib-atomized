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
/--
theorem `disjoint_atBot_principal_Ioi` / 定理 `disjoint_atBot_principal_Ioi`

English:
theorem disjoint_atBot_principal_Ioi
  given: [Preorder α] (x : α)
  statement: Disjoint atBot (𝓟 (Ioi x))
  proof: disjoint_of_disjoint_of_mem (Iic_disjoint_Ioi le_rfl) (Iic_mem_atBot x) (mem_principal_self _)

@[to_dual disjoint_atBot_principal_Ici]

中文:
定理 disjoint_atBot_principal_Ioi
  条件: [预序 α] (x : α)
  结论: Disjoint atBot (𝓟 (左开右无界区间 x))
  证明: disjoint_of_disjoint_of_mem (Iic_disjoint_Ioi le_rfl) (Iic_mem_atBot x) (mem_principal_self _)

@[to_dual disjoint_atBot_principal_Ici]

Depends on / 依赖: Iic_disjoint_Ioi, Iic_mem_atBot, disjoint_of_disjoint_of_mem, le_rfl, mem_principal_self
-/
theorem disjoint_atBot_principal_Ioi [Preorder α] (x : α) : Disjoint atBot (𝓟 (Ioi x)) :=
  disjoint_of_disjoint_of_mem (Iic_disjoint_Ioi le_rfl) (Iic_mem_atBot x) (mem_principal_self _)

@[to_dual disjoint_atBot_principal_Ici]
/--
theorem `disjoint_atTop_principal_Iic` / 定理 `disjoint_atTop_principal_Iic`

English:
theorem disjoint_atTop_principal_Iic
  given: [Preorder α] [NoTopOrder α] (x : α)
  proof: disjoint_of_disjoint_of_mem (Iic_disjoint_Ioi le_rfl).symm (Ioi_mem_atTop x)
    (mem_principal_self _)

@[to_dual disjoint_pure_atBot]

中文:
定理 disjoint_atTop_principal_Iic
  条件: [预序 α] [无顶序 α] (x : α)
  证明: disjoint_of_disjoint_of_mem (Iic_disjoint_Ioi le_rfl).symm (Ioi_mem_atTop x)
    (mem_principal_self _)

@[to_dual disjoint_pure_atBot]

Depends on / 依赖: Iic_disjoint_Ioi, Ioi_mem_atTop, disjoint_of_disjoint_of_mem, le_rfl, mem_principal_self
-/
theorem disjoint_atTop_principal_Iic [Preorder α] [NoTopOrder α] (x : α) :
    Disjoint atTop (𝓟 (Iic x)) :=
  disjoint_of_disjoint_of_mem (Iic_disjoint_Ioi le_rfl).symm (Ioi_mem_atTop x)
    (mem_principal_self _)

@[to_dual disjoint_pure_atBot]
/--
theorem `disjoint_pure_atTop` / 定理 `disjoint_pure_atTop`

English:
theorem disjoint_pure_atTop
  given: [Preorder α] [NoTopOrder α] (x : α)
  statement: Disjoint (pure x) atTop
  proof: Disjoint.symm (disjoint_atTop_principal_Iic x).mono_right le_principal_iff.2
    mem_pure.2 self_mem_Iic

@[to_dual disjoint_atTop_atBot]

中文:
定理 disjoint_pure_atTop
  条件: [预序 α] [无顶序 α] (x : α)
  结论: Disjoint (pure x) atTop
  证明: Disjoint.symm (disjoint_atTop_principal_Iic x).mono_right le_principal_iff.2
    mem_pure.2 self_mem_Iic

@[to_dual disjoint_atTop_atBot]

Depends on / 依赖: Disjoint, Disjoint.symm, disjoint_atTop_principal_Iic, le_principal_iff, mem_pure, mono_right, self_mem_Iic
-/
theorem disjoint_pure_atTop [Preorder α] [NoTopOrder α] (x : α) : Disjoint (pure x) atTop :=
Disjoint.symm (disjoint_atTop_principal_Iic x).mono_right le_principal_iff.2
    mem_pure.2 self_mem_Iic

@[to_dual disjoint_atTop_atBot]
/--
theorem `disjoint_atBot_atTop` / 定理 `disjoint_atBot_atTop`

English:
theorem disjoint_atBot_atTop
  given: [PartialOrder α] [Nontrivial α]
  proof: by
  rcases exists_pair_ne α with ⟨x, y, hne⟩
  by_cases hle : x <= y
  · refine disjoint_of_disjoint_of_mem ?_ (Iic_mem_atBot x) (Ici_mem_atTop y)
    exact Iic_disjoint_Ici.2 (hle.lt_of_ne hne).not_ge
  · refine disjoint_of_disjoint_of_mem ?_ (Iic_mem_atBot y) (Ici_mem_atTop x)
    exact Iic_disjo

中文:
定理 disjoint_atBot_atTop
  条件: [偏序 α] [非平凡 α]
  证明: by
  rcases exists_pair_ne α with ⟨x, y, hne⟩
  by_cases hle : x <= y
  · refine disjoint_of_disjoint_of_mem ?_ (Iic_mem_atBot x) (Ici_mem_atTop y)
    exact Iic_disjoint_Ici.2 (hle.lt_of_ne hne).not_ge
  · refine disjoint_of_disjoint_of_mem ?_ (Iic_mem_atBot y) (Ici_mem_atTop x)
    exact Iic_disjo

Depends on / 依赖: Ici_mem_atTop, Iic_disjoint_Ici, Iic_mem_atBot, disjoint_of_disjoint_of_mem, exists_pair_ne, hle.lt_of_ne, lt_of_ne, not_ge
-/
theorem disjoint_atBot_atTop [PartialOrder α] [Nontrivial α] :
    Disjoint (atBot : Filter α) atTop := by
  rcases exists_pair_ne α with ⟨x, y, hne⟩
  by_cases hle : x <= y
  · refine disjoint_of_disjoint_of_mem ?_ (Iic_mem_atBot x) (Ici_mem_atTop y)
    exact Iic_disjoint_Ici.2 (hle.lt_of_ne hne).not_ge
  · refine disjoint_of_disjoint_of_mem ?_ (Iic_mem_atBot y) (Ici_mem_atTop x)
    exact Iic_disjoint_Ici.2 hle

end Filter
