/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Interval.Finset.Basic
public import Mathlib.Order.Interval.Multiset

/-!
# Algebraic properties of multiset intervals

This file provides results about the interaction of algebra with `Multiset.Ixx`.
-/

public section

variable {α : Type*}

namespace Multiset
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  [ExistsAddOfLE α] [LocallyFiniteOrder α]

/--
lemma `map_add_left_Icc` / 引理 `map_add_left_Icc`

English:
lemma map_add_left_Icc
  given: (a b c : α)
  statement: (Icc a b).map (c + ·) = Icc (c + a) (c + b)
  proof: by
  classical rw [Icc, Icc, ← Finset.image_add_left_Icc, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

中文:
引理 map_add_left_Icc
  条件: (a b c : α)
  结论: (闭区间 a b).map (c + ·) = 闭区间 (c + a) (c + b)
  证明: by
  classical rw [Icc, Icc, ← Finset.image_add_left_Icc, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

Depends on / 依赖: Finset, Finset.image_add_left_Icc, Finset.image_val, Finset.nodup, add_right_injective, classical, image_add_left_Icc, image_val
-/
lemma map_add_left_Icc (a b c : α) : (Icc a b).map (c + ·) = Icc (c + a) (c + b) := by
  classical rw [Icc, Icc, ← Finset.image_add_left_Icc, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

/--
lemma `map_add_left_Ico` / 引理 `map_add_left_Ico`

English:
lemma map_add_left_Ico
  given: (a b c : α)
  statement: (Ico a b).map (c + ·) = Ico (c + a) (c + b)
  proof: by
  classical rw [Ico, Ico, ← Finset.image_add_left_Ico, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

中文:
引理 map_add_left_Ico
  条件: (a b c : α)
  结论: (左闭右开区间 a b).map (c + ·) = 左闭右开区间 (c + a) (c + b)
  证明: by
  classical rw [Ico, Ico, ← Finset.image_add_left_Ico, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

Depends on / 依赖: Finset, Finset.image_add_left_Ico, Finset.image_val, Finset.nodup, add_right_injective, classical, image_add_left_Ico, image_val
-/
lemma map_add_left_Ico (a b c : α) : (Ico a b).map (c + ·) = Ico (c + a) (c + b) := by
  classical rw [Ico, Ico, ← Finset.image_add_left_Ico, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

/--
lemma `map_add_left_Ioc` / 引理 `map_add_left_Ioc`

English:
lemma map_add_left_Ioc
  given: (a b c : α)
  statement: (Ioc a b).map (c + ·) = Ioc (c + a) (c + b)
  proof: by
  classical rw [Ioc, Ioc, ← Finset.image_add_left_Ioc, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

中文:
引理 map_add_left_Ioc
  条件: (a b c : α)
  结论: (左开右闭区间 a b).map (c + ·) = 左开右闭区间 (c + a) (c + b)
  证明: by
  classical rw [Ioc, Ioc, ← Finset.image_add_left_Ioc, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

Depends on / 依赖: Finset, Finset.image_add_left_Ioc, Finset.image_val, Finset.nodup, add_right_injective, classical, image_add_left_Ioc, image_val
-/
lemma map_add_left_Ioc (a b c : α) : (Ioc a b).map (c + ·) = Ioc (c + a) (c + b) := by
  classical rw [Ioc, Ioc, ← Finset.image_add_left_Ioc, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

/--
lemma `map_add_left_Ioo` / 引理 `map_add_left_Ioo`

English:
lemma map_add_left_Ioo
  given: (a b c : α)
  statement: (Ioo a b).map (c + ·) = Ioo (c + a) (c + b)
  proof: by
  classical rw [Ioo, Ioo, ← Finset.image_add_left_Ioo, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

中文:
引理 map_add_left_Ioo
  条件: (a b c : α)
  结论: (开区间 a b).map (c + ·) = 开区间 (c + a) (c + b)
  证明: by
  classical rw [Ioo, Ioo, ← Finset.image_add_left_Ioo, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

Depends on / 依赖: Finset, Finset.image_add_left_Ioo, Finset.image_val, Finset.nodup, add_right_injective, classical, image_add_left_Ioo, image_val
-/
lemma map_add_left_Ioo (a b c : α) : (Ioo a b).map (c + ·) = Ioo (c + a) (c + b) := by
  classical rw [Ioo, Ioo, ← Finset.image_add_left_Ioo, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

/--
lemma `map_add_right_Icc` / 引理 `map_add_right_Icc`

English:
lemma map_add_right_Icc
  given: (a b c : α)
  statement: ((Icc a b).map fun x => x + c) = Icc (a + c) (b + c)
  proof: by
  simp_rw [add_comm _ c]
  exact map_add_left_Icc _ _ _

中文:
引理 map_add_right_Icc
  条件: (a b c : α)
  结论: ((闭区间 a b).map fun x => x + c) = 闭区间 (a + c) (b + c)
  证明: by
  simp_rw [add_comm _ c]
  exact map_add_left_Icc _ _ _

Depends on / 依赖: add_comm, map_add_left_Icc, simp_rw
-/
lemma map_add_right_Icc (a b c : α) : ((Icc a b).map fun x => x + c) = Icc (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Icc _ _ _

/--
lemma `map_add_right_Ico` / 引理 `map_add_right_Ico`

English:
lemma map_add_right_Ico
  given: (a b c : α)
  statement: ((Ico a b).map fun x => x + c) = Ico (a + c) (b + c)
  proof: by
  simp_rw [add_comm _ c]
  exact map_add_left_Ico _ _ _

中文:
引理 map_add_right_Ico
  条件: (a b c : α)
  结论: ((左闭右开区间 a b).map fun x => x + c) = 左闭右开区间 (a + c) (b + c)
  证明: by
  simp_rw [add_comm _ c]
  exact map_add_left_Ico _ _ _

Depends on / 依赖: add_comm, map_add_left_Ico, simp_rw
-/
lemma map_add_right_Ico (a b c : α) : ((Ico a b).map fun x => x + c) = Ico (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Ico _ _ _

/--
lemma `map_add_right_Ioc` / 引理 `map_add_right_Ioc`

English:
lemma map_add_right_Ioc
  given: (a b c : α)
  statement: ((Ioc a b).map fun x => x + c) = Ioc (a + c) (b + c)
  proof: by
  simp_rw [add_comm _ c]
  exact map_add_left_Ioc _ _ _

中文:
引理 map_add_right_Ioc
  条件: (a b c : α)
  结论: ((左开右闭区间 a b).map fun x => x + c) = 左开右闭区间 (a + c) (b + c)
  证明: by
  simp_rw [add_comm _ c]
  exact map_add_left_Ioc _ _ _

Depends on / 依赖: add_comm, map_add_left_Ioc, simp_rw
-/
lemma map_add_right_Ioc (a b c : α) : ((Ioc a b).map fun x => x + c) = Ioc (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Ioc _ _ _

/--
lemma `map_add_right_Ioo` / 引理 `map_add_right_Ioo`

English:
lemma map_add_right_Ioo
  given: (a b c : α)
  statement: ((Ioo a b).map fun x => x + c) = Ioo (a + c) (b + c)
  proof: by
  simp_rw [add_comm _ c]
  exact map_add_left_Ioo _ _ _

中文:
引理 map_add_right_Ioo
  条件: (a b c : α)
  结论: ((开区间 a b).map fun x => x + c) = 开区间 (a + c) (b + c)
  证明: by
  simp_rw [add_comm _ c]
  exact map_add_left_Ioo _ _ _

Depends on / 依赖: add_comm, map_add_left_Ioo, simp_rw
-/
lemma map_add_right_Ioo (a b c : α) : ((Ioo a b).map fun x => x + c) = Ioo (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Ioo _ _ _

end Multiset
