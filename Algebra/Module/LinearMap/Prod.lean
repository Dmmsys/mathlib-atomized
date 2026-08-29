/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.Algebra.Module.Prod
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Addition and subtraction are linear maps from the product space

Note that these results use `IsLinearMap`, which is mostly discouraged.

## Tags
linear algebra, vector space, module

-/

public section

variable {R : Type*} {M : Type*} [Semiring R]

namespace IsLinearMap

/--
theorem `isLinearMap_add` / 定理 `isLinearMap_add`

English:
theorem isLinearMap_add
  given: [AddCommMonoid M] [Module R M]
  proof: by
  apply IsLinearMap.mk
  · intro x y
    simp only [Prod.fst_add, Prod.snd_add]
    abel
  · simp [smul_add]

中文:
定理 isLinearMap_add
  条件: [AddCommMonoid M] [Module R M]
  证明: by
  apply IsLinearMap.mk
  · intro x y
    simp only [Prod.fst_add, Prod.snd_add]
    abel
  · simp [smul_add]

Depends on / 依赖: IsLinearMap, IsLinearMap.mk, Prod.fst_add, Prod.snd_add, fst_add, smul_add, snd_add
-/
theorem isLinearMap_add [AddCommMonoid M] [Module R M] :
    IsLinearMap R fun x : M × M => x.1 + x.2 := by
  apply IsLinearMap.mk
  · intro x y
    simp only [Prod.fst_add, Prod.snd_add]
    abel
  · simp [smul_add]

/--
theorem `isLinearMap_sub` / 定理 `isLinearMap_sub`

English:
theorem isLinearMap_sub
  given: [AddCommGroup M] [Module R M]
  proof: by
  apply IsLinearMap.mk
  · simp [add_comm, add_assoc, add_left_comm, sub_eq_add_neg]
  · simp [smul_sub]

中文:
定理 isLinearMap_sub
  条件: [AddCommGroup M] [Module R M]
  证明: by
  apply IsLinearMap.mk
  · simp [add_comm, add_assoc, add_left_comm, sub_eq_add_neg]
  · simp [smul_sub]

Depends on / 依赖: IsLinearMap, IsLinearMap.mk, add_assoc, add_comm, add_left_comm, smul_sub, sub_eq_add_neg
-/
theorem isLinearMap_sub [AddCommGroup M] [Module R M] :
    IsLinearMap R fun x : M × M => x.1 - x.2 := by
  apply IsLinearMap.mk
  · simp [add_comm, add_assoc, add_left_comm, sub_eq_add_neg]
  · simp [smul_sub]

end IsLinearMap
