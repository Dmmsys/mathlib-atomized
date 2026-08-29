/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Operations

/-!
# Fixed points of a self-map

In this file we define the set `Function.fixedPoints` of fixed points of a function `f : α → α`.
The related predicate `IsFixedPt` is defined in `Mathlib.Logic.Function.Defs`.

## Tags

fixed point
-/

@[expose] public section

namespace Function

variable {α : Type*} {x : α} {f g : α -> α}

/--
Definition of `fixedPoints` / `fixedPoints` 的定义

English:
definition fixedPoints
  signature: (f : α -> α)
  body: { x : α | IsFixedPt f x }

中文:
定义 fixedPoints
  签名: (f : α -> α)
  定义体: { x : α | IsFixedPt f x }

Depends on / 依赖: IsFixedPt
-/
def fixedPoints (f : α -> α) : Set α :=
  { x : α | IsFixedPt f x }

/--
Instance `fixedPoints.decidable` / 实例 `fixedPoints.decidable`

English:
instance fixedPoints.decidable
  signature: [DecidableEq α] (f : α -> α) (x : α)
  body: IsFixedPt.decidable

@[simp]

中文:
实例 fixedPoints.decidable
  签名: [DecidableEq α] (f : α -> α) (x : α)
  定义体: IsFixedPt.decidable

@[simp]

Depends on / 依赖: IsFixedPt, IsFixedPt.decidable, decidable
-/
instance fixedPoints.decidable [DecidableEq α] (f : α -> α) (x : α) :
    Decidable (x in fixedPoints f) :=
  IsFixedPt.decidable

@[simp]
/--
theorem `mem_fixedPoints` / 定理 `mem_fixedPoints`

English:
theorem mem_fixedPoints
  statement: x in fixedPoints f ↔ IsFixedPt f x
  proof: .rfl

中文:
定理 mem_fixedPoints
  结论: x in fixedPoints f ↔ IsFixedPt f x
  证明: .rfl
-/
theorem mem_fixedPoints : x in fixedPoints f ↔ IsFixedPt f x :=
  .rfl

/--
theorem `mem_fixedPoints_iff` / 定理 `mem_fixedPoints_iff`

English:
theorem mem_fixedPoints_iff
  given: {α : Type*} {f : α -> α} {x : α}
  statement: x in fixedPoints f ↔ f x = x
  proof: .rfl

@[simp]

中文:
定理 mem_fixedPoints_iff
  条件: {α : 类型} {f : α -> α} {x : α}
  结论: x in fixedPoints f ↔ f x = x
  证明: .rfl

@[simp]
-/
theorem mem_fixedPoints_iff {α : Type*} {f : α -> α} {x : α} : x in fixedPoints f ↔ f x = x :=
  .rfl

@[simp]
/--
theorem `fixedPoints_id` / 定理 `fixedPoints_id`

English:
theorem fixedPoints_id
  statement: fixedPoints (@id α) = Set.univ
  proof: Set.ext fun _ => by simpa using isFixedPt_id _

@[simp]

中文:
定理 fixedPoints_id
  结论: fixedPoints (@id α) = 集合.univ
  证明: Set.ext fun _ => by simpa using isFixedPt_id _

@[simp]

Depends on / 依赖: Set.ext, isFixedPt_id
-/
theorem fixedPoints_id : fixedPoints (@id α) = Set.univ :=
  Set.ext fun _ => by simpa using isFixedPt_id _

@[simp]
/--
theorem `inter_subset_fixedPoints_comp` / 定理 `inter_subset_fixedPoints_comp`

English:
theorem inter_subset_fixedPoints_comp
  statement: fixedPoints f inter fixedPoints g subseteq fixedPoints (f ∘ g)
  proof: by
  rintro x ⟨hf, hg⟩
  rw [mem_fixedPoints_iff] at *
  rw [comp_apply]; rw [hg]; rw [hf]

中文:
定理 inter_subset_fixedPoints_comp
  结论: fixedPoints f inter fixedPoints g subseteq fixedPoints (f ∘ g)
  证明: by
  rintro x ⟨hf, hg⟩
  rw [mem_fixedPoints_iff] at *
  rw [comp_apply]; rw [hg]; rw [hf]

Depends on / 依赖: comp_apply, mem_fixedPoints_iff
-/
theorem inter_subset_fixedPoints_comp : fixedPoints f inter fixedPoints g subseteq fixedPoints (f ∘ g) := by
  rintro x ⟨hf, hg⟩
  rw [mem_fixedPoints_iff] at *
  rw [comp_apply]; rw [hg]; rw [hf]

/--
theorem `fixedPoints_subset_range` / 定理 `fixedPoints_subset_range`

English:
theorem fixedPoints_subset_range
  statement: fixedPoints f subseteq Set.range f
  proof: fun x hx => ⟨x, hx⟩

中文:
定理 fixedPoints_subset_range
  结论: fixedPoints f subseteq 集合.range f
  证明: fun x hx => ⟨x, hx⟩
-/
theorem fixedPoints_subset_range : fixedPoints f subseteq Set.range f := fun x hx => ⟨x, hx⟩

end Function
