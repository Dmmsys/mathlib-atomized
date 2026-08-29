/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Nonneg.Ring
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Ray

import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# Segments in vector spaces

In a 𝕜-vector space, we define the following objects and properties.
* `segment 𝕜 x y`: Closed segment joining `x` and `y`.
* `openSegment 𝕜 x y`: Open segment joining `x` and `y`.

## Notation

We provide the following notation:
* `[x -[𝕜] y] = segment 𝕜 x y` in scope `Convex`

## TODO

Generalize all this file to affine spaces.

Should we rename `segment` and `openSegment` to `convex.Icc` and `convex.Ioo`? Should we also
define `clopenSegment`/`convex.Ico`/`convex.Ioc`?
-/

@[expose] public section

variable {𝕜 E F G ι : Type*} {M : ι -> Type*}

open Function Module Set
open scoped Pointwise Convex

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]

section SMul

variable (𝕜) [SMul 𝕜 E] {s : Set E} {x y : E}

/--
Definition of `segment` / `segment` 的定义

English:
definition segment
  signature: (x y : E)
  body: { z : E | exists a b : 𝕜, 0 <= a ∧ 0 <= b ∧ a + b = 1 ∧ a • x + b • y = z }

中文:
定义 segment
  签名: (x y : E)
  定义体: { z : E | exists a b : 𝕜, 0 <= a ∧ 0 <= b ∧ a + b = 1 ∧ a • x + b • y = z }
-/
def segment (x y : E) : Set E :=
  { z : E | exists a b : 𝕜, 0 <= a ∧ 0 <= b ∧ a + b = 1 ∧ a • x + b • y = z }

/--
Definition of `openSegment` / `openSegment` 的定义

English:
definition openSegment
  signature: (x y : E)
  body: { z : E | exists a b : 𝕜, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a • x + b • y = z }

@[inherit_doc] scoped[Convex] notation (priority := high) "[" x " -[" 𝕜 "] " y "]" => segment 𝕜 x y

中文:
定义 openSegment
  签名: (x y : E)
  定义体: { z : E | exists a b : 𝕜, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a • x + b • y = z }

@[inherit_doc] scoped[Convex] notation (priority := high) "[" x " -[" 𝕜 "] " y "]" => segment 𝕜 x y
-/
def openSegment (x y : E) : Set E :=
  { z : E | exists a b : 𝕜, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a • x + b • y = z }

@[inherit_doc] scoped[Convex] notation (priority := high) "[" x " -[" 𝕜 "] " y "]" => segment 𝕜 x y

/--
theorem `segment_eq_image₂` / 定理 `segment_eq_image₂`

English:
theorem segment_eq_image₂
  given: (x y : E)
  proof: by
  simp only [segment, image, Prod.exists, mem_ofPred_eq, and_assoc]

中文:
定理 segment_eq_image₂
  条件: (x y : E)
  证明: by
  simp only [segment, image, Prod.exists, mem_ofPred_eq, and_assoc]

Depends on / 依赖: Prod.exists, and_assoc, mem_ofPred_eq, segment
-/
theorem segment_eq_image₂ (x y : E) :
    [x -[𝕜] y] =
      (fun p : 𝕜 × 𝕜 => p.1 • x + p.2 • y) '' { p | 0 <= p.1 ∧ 0 <= p.2 ∧ p.1 + p.2 = 1 } := by
  simp only [segment, image, Prod.exists, mem_ofPred_eq, and_assoc]

/--
theorem `openSegment_eq_image₂` / 定理 `openSegment_eq_image₂`

English:
theorem openSegment_eq_image₂
  given: (x y : E)
  proof: by
  simp only [openSegment, image, Prod.exists, mem_ofPred_eq, and_assoc]

中文:
定理 openSegment_eq_image₂
  条件: (x y : E)
  证明: by
  simp only [openSegment, image, Prod.exists, mem_ofPred_eq, and_assoc]

Depends on / 依赖: Prod.exists, and_assoc, mem_ofPred_eq, openSegment
-/
theorem openSegment_eq_image₂ (x y : E) :
    openSegment 𝕜 x y =
      (fun p : 𝕜 × 𝕜 => p.1 • x + p.2 • y) '' { p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 = 1 } := by
  simp only [openSegment, image, Prod.exists, mem_ofPred_eq, and_assoc]

/--
theorem `segment_symm` / 定理 `segment_symm`

English:
theorem segment_symm
  given: (x y : E)
  statement: [x -[𝕜] y] = [y -[𝕜] x]
  proof: Set.ext fun _ =>
    ⟨fun ⟨a, b, ha, hb, hab, H⟩ => ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩,
      fun ⟨a, b, ha, hb, hab, H⟩ =>
      ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩⟩

中文:
定理 segment_symm
  条件: (x y : E)
  结论: [x -[𝕜] y] = [y -[𝕜] x]
  证明: Set.ext fun _ =>
    ⟨fun ⟨a, b, ha, hb, hab, H⟩ => ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩,
      fun ⟨a, b, ha, hb, hab, H⟩ =>
      ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩⟩

Depends on / 依赖: Set.ext, add_comm
-/
theorem segment_symm (x y : E) : [x -[𝕜] y] = [y -[𝕜] x] :=
  Set.ext fun _ =>
    ⟨fun ⟨a, b, ha, hb, hab, H⟩ => ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩,
      fun ⟨a, b, ha, hb, hab, H⟩ =>
      ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩⟩

/--
theorem `openSegment_symm` / 定理 `openSegment_symm`

English:
theorem openSegment_symm
  given: (x y : E)
  statement: openSegment 𝕜 x y = openSegment 𝕜 y x
  proof: Set.ext fun _ =>
    ⟨fun ⟨a, b, ha, hb, hab, H⟩ => ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩,
      fun ⟨a, b, ha, hb, hab, H⟩ =>
      ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩⟩

中文:
定理 openSegment_symm
  条件: (x y : E)
  结论: openSegment 𝕜 x y = openSegment 𝕜 y x
  证明: Set.ext fun _ =>
    ⟨fun ⟨a, b, ha, hb, hab, H⟩ => ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩,
      fun ⟨a, b, ha, hb, hab, H⟩ =>
      ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩⟩

Depends on / 依赖: Set.ext, add_comm
-/
theorem openSegment_symm (x y : E) : openSegment 𝕜 x y = openSegment 𝕜 y x :=
  Set.ext fun _ =>
    ⟨fun ⟨a, b, ha, hb, hab, H⟩ => ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩,
      fun ⟨a, b, ha, hb, hab, H⟩ =>
      ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩⟩

/--
theorem `openSegment_subset_segment` / 定理 `openSegment_subset_segment`

English:
theorem openSegment_subset_segment
  given: (x y : E)
  statement: openSegment 𝕜 x y subseteq [x -[𝕜] y]
  proof: fun _ ⟨a, b, ha, hb, hab, hz⟩ => ⟨a, b, ha.le, hb.le, hab, hz⟩

中文:
定理 openSegment_subset_segment
  条件: (x y : E)
  结论: openSegment 𝕜 x y subseteq [x -[𝕜] y]
  证明: fun _ ⟨a, b, ha, hb, hab, hz⟩ => ⟨a, b, ha.le, hb.le, hab, hz⟩

Depends on / 依赖: ha.le, hb.le
-/
theorem openSegment_subset_segment (x y : E) : openSegment 𝕜 x y subseteq [x -[𝕜] y] :=
  fun _ ⟨a, b, ha, hb, hab, hz⟩ => ⟨a, b, ha.le, hb.le, hab, hz⟩

/--
theorem `segment_subset_iff` / 定理 `segment_subset_iff`

English:
theorem segment_subset_iff
  proof: ⟨fun H a b ha hb hab => H ⟨a, b, ha, hb, hab, rfl⟩, fun H _ ⟨a, b, ha, hb, hab, hz⟩ =>
    hz ▸ H a b ha hb hab⟩

中文:
定理 segment_subset_iff
  证明: ⟨fun H a b ha hb hab => H ⟨a, b, ha, hb, hab, rfl⟩, fun H _ ⟨a, b, ha, hb, hab, hz⟩ =>
    hz ▸ H a b ha hb hab⟩
-/
theorem segment_subset_iff :
    [x -[𝕜] y] subseteq s ↔ forall a b : 𝕜, 0 <= a -> 0 <= b -> a + b = 1 -> a • x + b • y in s :=
  ⟨fun H a b ha hb hab => H ⟨a, b, ha, hb, hab, rfl⟩, fun H _ ⟨a, b, ha, hb, hab, hz⟩ =>
    hz ▸ H a b ha hb hab⟩

/--
theorem `openSegment_subset_iff` / 定理 `openSegment_subset_iff`

English:
theorem openSegment_subset_iff
  proof: ⟨fun H a b ha hb hab => H ⟨a, b, ha, hb, hab, rfl⟩, fun H _ ⟨a, b, ha, hb, hab, hz⟩ =>
    hz ▸ H a b ha hb hab⟩

中文:
定理 openSegment_subset_iff
  证明: ⟨fun H a b ha hb hab => H ⟨a, b, ha, hb, hab, rfl⟩, fun H _ ⟨a, b, ha, hb, hab, hz⟩ =>
    hz ▸ H a b ha hb hab⟩
-/
theorem openSegment_subset_iff :
    openSegment 𝕜 x y subseteq s ↔ forall a b : 𝕜, 0 < a -> 0 < b -> a + b = 1 -> a • x + b • y in s :=
  ⟨fun H a b ha hb hab => H ⟨a, b, ha, hb, hab, rfl⟩, fun H _ ⟨a, b, ha, hb, hab, hz⟩ =>
    hz ▸ H a b ha hb hab⟩

end SMul

open Convex

section MulActionWithZero

variable (𝕜)
variable [ZeroLEOneClass 𝕜] [MulActionWithZero 𝕜 E]

/--
theorem `left_mem_segment` / 定理 `left_mem_segment`

English:
theorem left_mem_segment
  given: (x y : E)
  statement: x in [x -[𝕜] y]
  proof: ⟨1, 0, zero_le_one, le_refl 0, add_zero 1, by rw [zero_smul, one_smul, add_zero]⟩

中文:
定理 left_mem_segment
  条件: (x y : E)
  结论: x in [x -[𝕜] y]
  证明: ⟨1, 0, zero_le_one, le_refl 0, add_zero 1, by rw [zero_smul, one_smul, add_zero]⟩

Depends on / 依赖: add_zero, le_refl, one_smul, zero_le_one, zero_smul
-/
theorem left_mem_segment (x y : E) : x in [x -[𝕜] y] :=
  ⟨1, 0, zero_le_one, le_refl 0, add_zero 1, by rw [zero_smul, one_smul, add_zero]⟩

/--
theorem `right_mem_segment` / 定理 `right_mem_segment`

English:
theorem right_mem_segment
  given: (x y : E)
  statement: y in [x -[𝕜] y]
  proof: segment_symm 𝕜 y x ▸ left_mem_segment 𝕜 y x

中文:
定理 right_mem_segment
  条件: (x y : E)
  结论: y in [x -[𝕜] y]
  证明: segment_symm 𝕜 y x ▸ left_mem_segment 𝕜 y x

Depends on / 依赖: left_mem_segment, segment_symm
-/
theorem right_mem_segment (x y : E) : y in [x -[𝕜] y] :=
  segment_symm 𝕜 y x ▸ left_mem_segment 𝕜 y x

end MulActionWithZero

section Module

variable (𝕜)
variable [ZeroLEOneClass 𝕜] [Module 𝕜 E] {s : Set E} {x y z : E}

@[simp]
/--
theorem `segment_same` / 定理 `segment_same`

English:
theorem segment_same
  given: (x : E)
  statement: [x -[𝕜] x] = {x}
  proof: Set.ext fun z =>
    ⟨fun ⟨a, b, _, _, hab, hz⟩ => by
      simpa only [(add_smul _ _ _).symm, mem_singleton_iff, hab, one_smul, eq_comm] using hz,
      fun h => mem_singleton_iff.1 h ▸ left_mem_segment 𝕜 z z⟩

中文:
定理 segment_same
  条件: (x : E)
  结论: [x -[𝕜] x] = {x}
  证明: Set.ext fun z =>
    ⟨fun ⟨a, b, _, _, hab, hz⟩ => by
      simpa only [(add_smul _ _ _).symm, mem_singleton_iff, hab, one_smul, eq_comm] using hz,
      fun h => mem_singleton_iff.1 h ▸ left_mem_segment 𝕜 z z⟩

Depends on / 依赖: Set.ext, add_smul, eq_comm, left_mem_segment, mem_singleton_iff, one_smul
-/
theorem segment_same (x : E) : [x -[𝕜] x] = {x} :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, _, _, hab, hz⟩ => by
      simpa only [(add_smul _ _ _).symm, mem_singleton_iff, hab, one_smul, eq_comm] using hz,
      fun h => mem_singleton_iff.1 h ▸ left_mem_segment 𝕜 z z⟩

/--
theorem `insert_endpoints_openSegment` / 定理 `insert_endpoints_openSegment`

English:
theorem insert_endpoints_openSegment
  given: (x y : E)
  proof: by
  simp only [subset_antisymm_iff, insert_subset_iff, left_mem_segment, right_mem_segment,
    openSegment_subset_segment, true_and]
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  refine hb.eq_or_lt.imp ?_ fun hb' => ha.eq_or_lt.imp ?_ fun ha' => ?_
  · rintro rfl
    rw [← add_zero a]; rw [hab]; rw [one_s

中文:
定理 insert_endpoints_openSegment
  条件: (x y : E)
  证明: by
  simp only [subset_antisymm_iff, insert_subset_iff, left_mem_segment, right_mem_segment,
    openSegment_subset_segment, true_and]
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  refine hb.eq_or_lt.imp ?_ fun hb' => ha.eq_or_lt.imp ?_ fun ha' => ?_
  · rintro rfl
    rw [← add_zero a]; rw [hab]; rw [one_s

Depends on / 依赖: add_zero, eq_or_lt, ha.eq_or_lt.imp, hb.eq_or_lt.imp, insert_subset_iff, left_mem_segment, one_smul, openSegment_subset_segment, right_mem_segment, subset_antisymm_iff, true_and, zero_add, zero_smul
-/
theorem insert_endpoints_openSegment (x y : E) :
    insert x (insert y (openSegment 𝕜 x y)) = [x -[𝕜] y] := by
  simp only [subset_antisymm_iff, insert_subset_iff, left_mem_segment, right_mem_segment,
    openSegment_subset_segment, true_and]
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  refine hb.eq_or_lt.imp ?_ fun hb' => ha.eq_or_lt.imp ?_ fun ha' => ?_
  · rintro rfl
    rw [← add_zero a]; rw [hab]; rw [one_smul]; rw [zero_smul]; rw [add_zero]
  · rintro rfl
    rw [← zero_add b]; rw [hab]; rw [one_smul]; rw [zero_smul]; rw [zero_add]
  · exact ⟨a, b, ha', hb', hab, rfl⟩

variable {𝕜}

/--
theorem `mem_openSegment_of_ne_left_right` / 定理 `mem_openSegment_of_ne_left_right`

English:
theorem mem_openSegment_of_ne_left_right
  given: (hx : x != z) (hy : y != z) (hz : z in [x -[𝕜] y])
  proof: by
  rw [← insert_endpoints_openSegment] at hz
  exact (hz.resolve_left hx.symm).resolve_left hy.symm

中文:
定理 mem_openSegment_of_ne_left_right
  条件: (hx : x != z) (hy : y != z) (hz : z in [x -[𝕜] y])
  证明: by
  rw [← insert_endpoints_openSegment] at hz
  exact (hz.resolve_left hx.symm).resolve_left hy.symm

Depends on / 依赖: hx.symm, hy.symm, hz.resolve_left, insert_endpoints_openSegment, resolve_left
-/
theorem mem_openSegment_of_ne_left_right (hx : x != z) (hy : y != z) (hz : z in [x -[𝕜] y]) :
    z in openSegment 𝕜 x y := by
  rw [← insert_endpoints_openSegment] at hz
  exact (hz.resolve_left hx.symm).resolve_left hy.symm

/--
theorem `openSegment_subset_iff_segment_subset` / 定理 `openSegment_subset_iff_segment_subset`

English:
theorem openSegment_subset_iff_segment_subset
  given: (hx : x in s) (hy : y in s)
  proof: by
  simp only [← insert_endpoints_openSegment, insert_subset_iff, *, true_and]

中文:
定理 openSegment_subset_iff_segment_subset
  条件: (hx : x in s) (hy : y in s)
  证明: by
  simp only [← insert_endpoints_openSegment, insert_subset_iff, *, true_and]

Depends on / 依赖: insert_endpoints_openSegment, insert_subset_iff, true_and
-/
theorem openSegment_subset_iff_segment_subset (hx : x in s) (hy : y in s) :
    openSegment 𝕜 x y subseteq s ↔ [x -[𝕜] y] subseteq s := by
  simp only [← insert_endpoints_openSegment, insert_subset_iff, *, true_and]

section lift

variable (R : Type*) [Semiring R] [PartialOrder R] [Module R E]
variable [Module R 𝕜] [IsScalarTower R 𝕜 E]

/--
theorem `segment.lift` / 定理 `segment.lift`

English:
theorem segment.lift
  given: [SMulPosMono R 𝕜] (x y : E)
  statement: segment R x y subseteq segment 𝕜 x y
  proof: by
  rintro z ⟨a, b, ha, hb, hab, hxy⟩
  refine ⟨_, _, ?_, ?_, by simpa [add_smul] using congr($(hab) • (1 : 𝕜)), by simpa⟩
  all_goals exact zero_smul R (1 : 𝕜) ▸ smul_le_smul_of_nonneg_right ‹_› zero_le_one

中文:
定理 segment.lift
  条件: [标量乘正递增 R 𝕜] (x y : E)
  结论: segment R x y subseteq segment 𝕜 x y
  证明: by
  rintro z ⟨a, b, ha, hb, hab, hxy⟩
  refine ⟨_, _, ?_, ?_, by simpa [add_smul] using congr($(hab) • (1 : 𝕜)), by simpa⟩
  all_goals exact zero_smul R (1 : 𝕜) ▸ smul_le_smul_of_nonneg_right ‹_› zero_le_one

Depends on / 依赖: add_smul, all_goals, smul_le_smul_of_nonneg_right, zero_le_one, zero_smul
-/
theorem segment.lift [SMulPosMono R 𝕜] (x y : E) : segment R x y subseteq segment 𝕜 x y := by
  rintro z ⟨a, b, ha, hb, hab, hxy⟩
  refine ⟨_, _, ?_, ?_, by simpa [add_smul] using congr($(hab) • (1 : 𝕜)), by simpa⟩
  all_goals exact zero_smul R (1 : 𝕜) ▸ smul_le_smul_of_nonneg_right ‹_› zero_le_one

/--
theorem `openSegment.lift` / 定理 `openSegment.lift`

English:
theorem openSegment.lift
  given: [Nontrivial 𝕜] [SMulPosStrictMono R 𝕜] (x y : E)
  proof: by
  rintro z ⟨a, b, ha, hb, hab, hxy⟩
  refine ⟨_, _, ?_, ?_, by simpa [add_smul] using congr($(hab) • (1 : 𝕜)), by simpa⟩
  all_goals exact zero_smul R (1 : 𝕜) ▸ smul_lt_smul_of_pos_right ‹_› zero_lt_one

中文:
定理 openSegment.lift
  条件: [非平凡 𝕜] [标量乘正严格递增 R 𝕜] (x y : E)
  证明: by
  rintro z ⟨a, b, ha, hb, hab, hxy⟩
  refine ⟨_, _, ?_, ?_, by simpa [add_smul] using congr($(hab) • (1 : 𝕜)), by simpa⟩
  all_goals exact zero_smul R (1 : 𝕜) ▸ smul_lt_smul_of_pos_right ‹_› zero_lt_one

Depends on / 依赖: add_smul, all_goals, smul_lt_smul_of_pos_right, zero_lt_one, zero_smul
-/
theorem openSegment.lift [Nontrivial 𝕜] [SMulPosStrictMono R 𝕜] (x y : E) :
    openSegment R x y subseteq openSegment 𝕜 x y := by
  rintro z ⟨a, b, ha, hb, hab, hxy⟩
  refine ⟨_, _, ?_, ?_, by simpa [add_smul] using congr($(hab) • (1 : 𝕜)), by simpa⟩
  all_goals exact zero_smul R (1 : 𝕜) ▸ smul_lt_smul_of_pos_right ‹_› zero_lt_one

end lift

end Module

end OrderedSemiring

open Convex

section OrderedRing

variable (𝕜) [Ring 𝕜] [PartialOrder 𝕜] [AddRightMono 𝕜]
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [Module 𝕜 E] [Module 𝕜 F]

section DenselyOrdered

variable [ZeroLEOneClass 𝕜] [Nontrivial 𝕜] [DenselyOrdered 𝕜]

@[simp]
/--
theorem `openSegment_same` / 定理 `openSegment_same`

English:
theorem openSegment_same
  given: (x : E)
  statement: openSegment 𝕜 x x = {x}
  proof: Set.ext fun z =>
    ⟨fun ⟨a, b, _, _, hab, hz⟩ => by
      simpa only [← add_smul, mem_singleton_iff, hab, one_smul, eq_comm] using hz,
    fun h : z = x => by
      obtain ⟨a, ha₀, ha₁⟩ := DenselyOrdered.dense (0 : 𝕜) 1 zero_lt_one
      refine ⟨a, 1 - a, ha₀, sub_pos_of_lt ha₁, add_sub_cancel _ _

中文:
定理 openSegment_same
  条件: (x : E)
  结论: openSegment 𝕜 x x = {x}
  证明: Set.ext fun z =>
    ⟨fun ⟨a, b, _, _, hab, hz⟩ => by
      simpa only [← add_smul, mem_singleton_iff, hab, one_smul, eq_comm] using hz,
    fun h : z = x => by
      obtain ⟨a, ha₀, ha₁⟩ := DenselyOrdered.dense (0 : 𝕜) 1 zero_lt_one
      refine ⟨a, 1 - a, ha₀, sub_pos_of_lt ha₁, add_sub_cancel _ _

Depends on / 依赖: DenselyOrdered, DenselyOrdered.dense, Set.ext, add_smul, add_sub_cancel, eq_comm, mem_singleton_iff, one_smul, sub_pos_of_lt, zero_lt_one
-/
theorem openSegment_same (x : E) : openSegment 𝕜 x x = {x} :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, _, _, hab, hz⟩ => by
      simpa only [← add_smul, mem_singleton_iff, hab, one_smul, eq_comm] using hz,
    fun h : z = x => by
      obtain ⟨a, ha₀, ha₁⟩ := DenselyOrdered.dense (0 : 𝕜) 1 zero_lt_one
      refine ⟨a, 1 - a, ha₀, sub_pos_of_lt ha₁, add_sub_cancel _ _, ?_⟩
      rw [← add_smul]; rw [add_sub_cancel]; rw [one_smul]; rw [h]⟩

end DenselyOrdered

/--
theorem `segment_eq_image` / 定理 `segment_eq_image`

English:
theorem segment_eq_image
  given: (x y : E)
  proof: Set.ext fun _ =>
    ⟨fun ⟨a, b, ha, hb, hab, hz⟩ =>
      ⟨b, ⟨hb, hab ▸ le_add_of_nonneg_left ha⟩, hab ▸ hz ▸ by simp only [add_sub_cancel_right]⟩,
      fun ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩ => ⟨1 - θ, θ, sub_nonneg.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩

中文:
定理 segment_eq_image
  条件: (x y : E)
  证明: Set.ext fun _ =>
    ⟨fun ⟨a, b, ha, hb, hab, hz⟩ =>
      ⟨b, ⟨hb, hab ▸ le_add_of_nonneg_left ha⟩, hab ▸ hz ▸ by simp only [add_sub_cancel_right]⟩,
      fun ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩ => ⟨1 - θ, θ, sub_nonneg.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩

Depends on / 依赖: Set.ext, add_sub_cancel_right, le_add_of_nonneg_left, sub_add_cancel, sub_nonneg
-/
theorem segment_eq_image (x y : E) :
    [x -[𝕜] y] = (fun θ : 𝕜 => (1 - θ) • x + θ • y) '' Icc (0 : 𝕜) 1 :=
  Set.ext fun _ =>
    ⟨fun ⟨a, b, ha, hb, hab, hz⟩ =>
      ⟨b, ⟨hb, hab ▸ le_add_of_nonneg_left ha⟩, hab ▸ hz ▸ by simp only [add_sub_cancel_right]⟩,
      fun ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩ => ⟨1 - θ, θ, sub_nonneg.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩

/--
theorem `openSegment_eq_image` / 定理 `openSegment_eq_image`

English:
theorem openSegment_eq_image
  given: (x y : E)
  proof: Set.ext fun _ =>
    ⟨fun ⟨a, b, ha, hb, hab, hz⟩ =>
      ⟨b, ⟨hb, hab ▸ lt_add_of_pos_left _ ha⟩, hab ▸ hz ▸ by simp only [add_sub_cancel_right]⟩,
      fun ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩ => ⟨1 - θ, θ, sub_pos.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩

中文:
定理 openSegment_eq_image
  条件: (x y : E)
  证明: Set.ext fun _ =>
    ⟨fun ⟨a, b, ha, hb, hab, hz⟩ =>
      ⟨b, ⟨hb, hab ▸ lt_add_of_pos_left _ ha⟩, hab ▸ hz ▸ by simp only [add_sub_cancel_right]⟩,
      fun ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩ => ⟨1 - θ, θ, sub_pos.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩

Depends on / 依赖: Set.ext, add_sub_cancel_right, lt_add_of_pos_left, sub_add_cancel, sub_pos
-/
theorem openSegment_eq_image (x y : E) :
    openSegment 𝕜 x y = (fun θ : 𝕜 => (1 - θ) • x + θ • y) '' Ioo (0 : 𝕜) 1 :=
  Set.ext fun _ =>
    ⟨fun ⟨a, b, ha, hb, hab, hz⟩ =>
      ⟨b, ⟨hb, hab ▸ lt_add_of_pos_left _ ha⟩, hab ▸ hz ▸ by simp only [add_sub_cancel_right]⟩,
      fun ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩ => ⟨1 - θ, θ, sub_pos.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩

/--
theorem `segment_eq_image'` / 定理 `segment_eq_image'`

English:
theorem segment_eq_image'
  given: (x y : E)
  proof: by
  convert! segment_eq_image 𝕜 x y using 2
  simp only [smul_sub, sub_smul, one_smul]
  abel

中文:
定理 segment_eq_image'
  条件: (x y : E)
  证明: by
  convert! segment_eq_image 𝕜 x y using 2
  simp only [smul_sub, sub_smul, one_smul]
  abel

Depends on / 依赖: convert, one_smul, segment_eq_image, smul_sub, sub_smul
-/
theorem segment_eq_image' (x y : E) :
    [x -[𝕜] y] = (fun θ : 𝕜 => x + θ • (y - x)) '' Icc (0 : 𝕜) 1 := by
  convert! segment_eq_image 𝕜 x y using 2
  simp only [smul_sub, sub_smul, one_smul]
  abel

/--
theorem `openSegment_eq_image'` / 定理 `openSegment_eq_image'`

English:
theorem openSegment_eq_image'
  given: (x y : E)
  proof: by
  convert! openSegment_eq_image 𝕜 x y using 2
  simp only [smul_sub, sub_smul, one_smul]
  abel

中文:
定理 openSegment_eq_image'
  条件: (x y : E)
  证明: by
  convert! openSegment_eq_image 𝕜 x y using 2
  simp only [smul_sub, sub_smul, one_smul]
  abel

Depends on / 依赖: convert, one_smul, openSegment_eq_image, smul_sub, sub_smul
-/
theorem openSegment_eq_image' (x y : E) :
    openSegment 𝕜 x y = (fun θ : 𝕜 => x + θ • (y - x)) '' Ioo (0 : 𝕜) 1 := by
  convert! openSegment_eq_image 𝕜 x y using 2
  simp only [smul_sub, sub_smul, one_smul]
  abel

set_option backward.isDefEq.respectTransparency false in
/--
theorem `segment_eq_image_lineMap` / 定理 `segment_eq_image_lineMap`

English:
theorem segment_eq_image_lineMap
  given: (x y : E)
  statement: [x -[𝕜] y] =
  proof: by
  convert segment_eq_image 𝕜 x y
  exact AffineMap.lineMap_apply_module _ _ _

中文:
定理 segment_eq_image_lineMap
  条件: (x y : E)
  结论: [x -[𝕜] y] =
  证明: by
  convert segment_eq_image 𝕜 x y
  exact AffineMap.lineMap_apply_module _ _ _

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply_module, convert, lineMap_apply_module, segment_eq_image
-/
theorem segment_eq_image_lineMap (x y : E) : [x -[𝕜] y] =
    AffineMap.lineMap x y '' Icc (0 : 𝕜) 1 := by
  convert segment_eq_image 𝕜 x y
  exact AffineMap.lineMap_apply_module _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `openSegment_eq_image_lineMap` / 定理 `openSegment_eq_image_lineMap`

English:
theorem openSegment_eq_image_lineMap
  given: (x y : E)
  proof: by
  convert openSegment_eq_image 𝕜 x y
  exact AffineMap.lineMap_apply_module _ _ _

中文:
定理 openSegment_eq_image_lineMap
  条件: (x y : E)
  证明: by
  convert openSegment_eq_image 𝕜 x y
  exact AffineMap.lineMap_apply_module _ _ _

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply_module, convert, lineMap_apply_module, openSegment_eq_image
-/
theorem openSegment_eq_image_lineMap (x y : E) :
    openSegment 𝕜 x y = AffineMap.lineMap x y '' Ioo (0 : 𝕜) 1 := by
  convert openSegment_eq_image 𝕜 x y
  exact AffineMap.lineMap_apply_module _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_mem_openSegment` / 定理 `lineMap_mem_openSegment`

English:
theorem lineMap_mem_openSegment
  given: (a b : E) {t : 𝕜} (ht : t in Ioo 0 1)
  proof: openSegment_eq_image_lineMap 𝕜 a b ▸ mem_image_of_mem _ ht

中文:
定理 lineMap_mem_openSegment
  条件: (a b : E) {t : 𝕜} (ht : t in 开区间 0 1)
  证明: openSegment_eq_image_lineMap 𝕜 a b ▸ mem_image_of_mem _ ht

Depends on / 依赖: mem_image_of_mem, openSegment_eq_image_lineMap
-/
theorem lineMap_mem_openSegment (a b : E) {t : 𝕜} (ht : t in Ioo 0 1) :
    AffineMap.lineMap a b t in openSegment 𝕜 a b :=
  openSegment_eq_image_lineMap 𝕜 a b ▸ mem_image_of_mem _ ht

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `lineMap_mem_segment` / 定理 `lineMap_mem_segment`

English:
theorem lineMap_mem_segment
  given: (a b : E) {t : 𝕜} (ht : t in Icc 0 1)
  proof: segment_eq_image_lineMap 𝕜 a b ▸ mem_image_of_mem _ ht

@[simp]

中文:
定理 lineMap_mem_segment
  条件: (a b : E) {t : 𝕜} (ht : t in 闭区间 0 1)
  证明: segment_eq_image_lineMap 𝕜 a b ▸ mem_image_of_mem _ ht

@[simp]

Depends on / 依赖: mem_image_of_mem, segment_eq_image_lineMap
-/
theorem lineMap_mem_segment (a b : E) {t : 𝕜} (ht : t in Icc 0 1) :
    AffineMap.lineMap a b t in [a -[𝕜] b] :=
  segment_eq_image_lineMap 𝕜 a b ▸ mem_image_of_mem _ ht

@[simp]
/--
theorem `image_segment` / 定理 `image_segment`

English:
theorem image_segment
  given: (f : E ->ᵃ[𝕜] F) (a b : E)
  statement: f '' [a -[𝕜] b] = [f a -[𝕜] f b]
  proof: Set.ext fun x => by
    simp_rw [segment_eq_image_lineMap, mem_image, exists_exists_and_eq_and, AffineMap.apply_lineMap]

@[simp]

中文:
定理 image_segment
  条件: (f : E ->ᵃ[𝕜] F) (a b : E)
  结论: f '' [a -[𝕜] b] = [f a -[𝕜] f b]
  证明: Set.ext fun x => by
    simp_rw [segment_eq_image_lineMap, mem_image, exists_exists_and_eq_and, AffineMap.apply_lineMap]

@[simp]

Depends on / 依赖: AffineMap, AffineMap.apply_lineMap, Set.ext, apply_lineMap, exists_exists_and_eq_and, mem_image, segment_eq_image_lineMap, simp_rw
-/
theorem image_segment (f : E ->ᵃ[𝕜] F) (a b : E) : f '' [a -[𝕜] b] = [f a -[𝕜] f b] :=
  Set.ext fun x => by
    simp_rw [segment_eq_image_lineMap, mem_image, exists_exists_and_eq_and, AffineMap.apply_lineMap]

@[simp]
/--
theorem `image_openSegment` / 定理 `image_openSegment`

English:
theorem image_openSegment
  given: (f : E ->ᵃ[𝕜] F) (a b : E)
  proof: Set.ext fun x => by
    simp_rw [openSegment_eq_image_lineMap, mem_image, exists_exists_and_eq_and,
      AffineMap.apply_lineMap]

@[simp]

中文:
定理 image_openSegment
  条件: (f : E ->ᵃ[𝕜] F) (a b : E)
  证明: Set.ext fun x => by
    simp_rw [openSegment_eq_image_lineMap, mem_image, exists_exists_and_eq_and,
      AffineMap.apply_lineMap]

@[simp]

Depends on / 依赖: AffineMap, AffineMap.apply_lineMap, Set.ext, apply_lineMap, exists_exists_and_eq_and, mem_image, openSegment_eq_image_lineMap, simp_rw
-/
theorem image_openSegment (f : E ->ᵃ[𝕜] F) (a b : E) :
    f '' openSegment 𝕜 a b = openSegment 𝕜 (f a) (f b) :=
  Set.ext fun x => by
    simp_rw [openSegment_eq_image_lineMap, mem_image, exists_exists_and_eq_and,
      AffineMap.apply_lineMap]

@[simp]
/--
theorem `vadd_segment` / 定理 `vadd_segment`

English:
theorem vadd_segment
  given: [AddTorsor G E] [VAddCommClass G E E] (a : G) (b c : E)
  proof: #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12286/
  we didn't need this `let` statement. -/
  let : AddTorsor E E := AddGroup.instAddTorsor E
  image_segment 𝕜 ⟨_, LinearMap.id, fun _ _ => vadd_comm _ _ _⟩ b c

@[simp]

中文:
定理 vadd_segment
  条件: [加法Torsor G E] [VAddComm类 G E E] (a : G) (b c : E)
  证明: #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12286/
  we didn't need this `let` statement. -/
  let : AddTorsor E E := AddGroup.instAddTorsor E
  image_segment 𝕜 ⟨_, LinearMap.id, fun _ _ => vadd_comm _ _ _⟩ b c

@[simp]

Depends on / 依赖: AddGroup, AddGroup.instAddTorsor, AddTorsor, LinearMap, LinearMap.id, adaptation_note, github, github.com, image_segment, instAddTorsor, leanprover, statement, vadd_comm
-/
theorem vadd_segment [AddTorsor G E] [VAddCommClass G E E] (a : G) (b c : E) :
    a +ᵥ [b -[𝕜] c] = [a +ᵥ b -[𝕜] a +ᵥ c] :=
  #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12286/
  we didn't need this `let` statement. -/
  let : AddTorsor E E := AddGroup.instAddTorsor E
  image_segment 𝕜 ⟨_, LinearMap.id, fun _ _ => vadd_comm _ _ _⟩ b c

@[simp]
/--
theorem `vadd_openSegment` / 定理 `vadd_openSegment`

English:
theorem vadd_openSegment
  given: [AddTorsor G E] [VAddCommClass G E E] (a : G) (b c : E)
  proof: #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12286/
  we didn't need this `let` statement. -/
  let : AddTorsor E E := AddGroup.instAddTorsor E
  image_openSegment 𝕜 ⟨_, LinearMap.id, fun _ _ => vadd_comm _ _ _⟩ b c

@[simp]

中文:
定理 vadd_openSegment
  条件: [加法Torsor G E] [VAddComm类 G E E] (a : G) (b c : E)
  证明: #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12286/
  we didn't need this `let` statement. -/
  let : AddTorsor E E := AddGroup.instAddTorsor E
  image_openSegment 𝕜 ⟨_, LinearMap.id, fun _ _ => vadd_comm _ _ _⟩ b c

@[simp]

Depends on / 依赖: AddGroup, AddGroup.instAddTorsor, AddTorsor, LinearMap, LinearMap.id, adaptation_note, github, github.com, image_openSegment, instAddTorsor, leanprover, statement, vadd_comm
-/
theorem vadd_openSegment [AddTorsor G E] [VAddCommClass G E E] (a : G) (b c : E) :
    a +ᵥ openSegment 𝕜 b c = openSegment 𝕜 (a +ᵥ b) (a +ᵥ c) :=
  #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12286/
  we didn't need this `let` statement. -/
  let : AddTorsor E E := AddGroup.instAddTorsor E
  image_openSegment 𝕜 ⟨_, LinearMap.id, fun _ _ => vadd_comm _ _ _⟩ b c

@[simp]
/--
theorem `mem_segment_translate` / 定理 `mem_segment_translate`

English:
theorem mem_segment_translate
  given: (a : E) {x b c}
  statement: a + x in [a + b -[𝕜] a + c] ↔ x in [b -[𝕜] c]
  proof: by
  simp_rw [← vadd_eq_add, ← vadd_segment, vadd_mem_vadd_set_iff]

@[simp]

中文:
定理 mem_segment_translate
  条件: (a : E) {x b c}
  结论: a + x in [a + b -[𝕜] a + c] ↔ x in [b -[𝕜] c]
  证明: by
  simp_rw [← vadd_eq_add, ← vadd_segment, vadd_mem_vadd_set_iff]

@[simp]

Depends on / 依赖: simp_rw, vadd_eq_add, vadd_mem_vadd_set_iff, vadd_segment
-/
theorem mem_segment_translate (a : E) {x b c} : a + x in [a + b -[𝕜] a + c] ↔ x in [b -[𝕜] c] := by
  simp_rw [← vadd_eq_add, ← vadd_segment, vadd_mem_vadd_set_iff]

@[simp]
/--
theorem `mem_openSegment_translate` / 定理 `mem_openSegment_translate`

English:
theorem mem_openSegment_translate
  given: (a : E) {x b c : E}
  proof: by
  simp_rw [← vadd_eq_add, ← vadd_openSegment, vadd_mem_vadd_set_iff]

中文:
定理 mem_openSegment_translate
  条件: (a : E) {x b c : E}
  证明: by
  simp_rw [← vadd_eq_add, ← vadd_openSegment, vadd_mem_vadd_set_iff]

Depends on / 依赖: simp_rw, vadd_eq_add, vadd_mem_vadd_set_iff, vadd_openSegment
-/
theorem mem_openSegment_translate (a : E) {x b c : E} :
    a + x in openSegment 𝕜 (a + b) (a + c) ↔ x in openSegment 𝕜 b c := by
  simp_rw [← vadd_eq_add, ← vadd_openSegment, vadd_mem_vadd_set_iff]

/--
theorem `segment_translate_preimage` / 定理 `segment_translate_preimage`

English:
theorem segment_translate_preimage
  given: (a b c : E)
  proof: Set.ext fun _ => mem_segment_translate 𝕜 a

中文:
定理 segment_translate_preimage
  条件: (a b c : E)
  证明: Set.ext fun _ => mem_segment_translate 𝕜 a

Depends on / 依赖: Set.ext, mem_segment_translate
-/
theorem segment_translate_preimage (a b c : E) :
    (fun x => a + x) ⁻¹' [a + b -[𝕜] a + c] = [b -[𝕜] c] :=
  Set.ext fun _ => mem_segment_translate 𝕜 a

/--
theorem `openSegment_translate_preimage` / 定理 `openSegment_translate_preimage`

English:
theorem openSegment_translate_preimage
  given: (a b c : E)
  proof: Set.ext fun _ => mem_openSegment_translate 𝕜 a

中文:
定理 openSegment_translate_preimage
  条件: (a b c : E)
  证明: Set.ext fun _ => mem_openSegment_translate 𝕜 a

Depends on / 依赖: Set.ext, mem_openSegment_translate
-/
theorem openSegment_translate_preimage (a b c : E) :
    (fun x => a + x) ⁻¹' openSegment 𝕜 (a + b) (a + c) = openSegment 𝕜 b c :=
  Set.ext fun _ => mem_openSegment_translate 𝕜 a

/--
theorem `segment_translate_image` / 定理 `segment_translate_image`

English:
theorem segment_translate_image
  given: (a b c : E)
  statement: (fun x => a + x) '' [b -[𝕜] c] = [a + b -[𝕜] a + c]
  proof: segment_translate_preimage 𝕜 a b c ▸ image_preimage_eq _ add_left_surjective a

中文:
定理 segment_translate_image
  条件: (a b c : E)
  结论: (fun x => a + x) '' [b -[𝕜] c] = [a + b -[𝕜] a + c]
  证明: segment_translate_preimage 𝕜 a b c ▸ image_preimage_eq _ add_left_surjective a

Depends on / 依赖: add_left_surjective, image_preimage_eq, segment_translate_preimage
-/
theorem segment_translate_image (a b c : E) : (fun x => a + x) '' [b -[𝕜] c] = [a + b -[𝕜] a + c] :=
segment_translate_preimage 𝕜 a b c ▸ image_preimage_eq _ add_left_surjective a

/--
theorem `openSegment_translate_image` / 定理 `openSegment_translate_image`

English:
theorem openSegment_translate_image
  given: (a b c : E)
  proof: openSegment_translate_preimage 𝕜 a b c ▸ image_preimage_eq _ add_left_surjective a

中文:
定理 openSegment_translate_image
  条件: (a b c : E)
  证明: openSegment_translate_preimage 𝕜 a b c ▸ image_preimage_eq _ add_left_surjective a

Depends on / 依赖: add_left_surjective, image_preimage_eq, openSegment_translate_preimage
-/
theorem openSegment_translate_image (a b c : E) :
    (fun x => a + x) '' openSegment 𝕜 b c = openSegment 𝕜 (a + b) (a + c) :=
openSegment_translate_preimage 𝕜 a b c ▸ image_preimage_eq _ add_left_surjective a

/--
lemma `segment_inter_subset_endpoint_of_linearIndependent_sub` / 引理 `segment_inter_subset_endpoint_of_linearIndependent_sub`

English:
lemma segment_inter_subset_endpoint_of_linearIndependent_sub
  proof: by
  intro z ⟨hzt, hzs⟩
  rw [segment_eq_image]; rw [mem_image] at hzt hzs
  rcases hzt with ⟨p, ⟨p0, p1⟩, rfl⟩
  rcases hzs with ⟨q, ⟨q0, q1⟩, H⟩
  have Hx : x = (x - c) + c := by abel
  have Hy : y = (y - c) + c := by abel
  rw [Hx]; rw [Hy]; rw [smul_add]; rw [smul_add] at H
  have : c + q • (y -

中文:
引理 segment_inter_subset_endpoint_of_linearIndependent_sub
  证明: by
  intro z ⟨hzt, hzs⟩
  rw [segment_eq_image]; rw [mem_image] at hzt hzs
  rcases hzt with ⟨p, ⟨p0, p1⟩, rfl⟩
  rcases hzs with ⟨q, ⟨q0, q1⟩, H⟩
  have Hx : x = (x - c) + c := by abel
  have Hy : y = (y - c) + c := by abel
  rw [Hx]; rw [Hy]; rw [smul_add]; rw [smul_add] at H
  have : c + q • (y -

Depends on / 依赖: add_right_inj, convert, eq_zero_of_pair, h.eq_zero_of_pair, mem_image, segment_eq_image, smul_add, sub_smul
-/
lemma segment_inter_subset_endpoint_of_linearIndependent_sub
    {c x y : E} (h : LinearIndependent 𝕜 ![x - c, y - c]) :
    [c -[𝕜] x] inter [c -[𝕜] y] subseteq {c} := by
  intro z ⟨hzt, hzs⟩
  rw [segment_eq_image]; rw [mem_image] at hzt hzs
  rcases hzt with ⟨p, ⟨p0, p1⟩, rfl⟩
  rcases hzs with ⟨q, ⟨q0, q1⟩, H⟩
  have Hx : x = (x - c) + c := by abel
  have Hy : y = (y - c) + c := by abel
  rw [Hx]; rw [Hy]; rw [smul_add]; rw [smul_add] at H
  have : c + q • (y - c) = c + p • (x - c) := by
    convert! H using 1 <;> simp [sub_smul]
  obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := h.eq_zero_of_pair' ((add_right_inj c).1 this).symm
  simp

/--
lemma `segment_inter_eq_endpoint_of_linearIndependent_sub` / 引理 `segment_inter_eq_endpoint_of_linearIndependent_sub`

English:
lemma segment_inter_eq_endpoint_of_linearIndependent_sub
  statement: [ZeroLEOneClass 𝕜]
  proof: by
  refine (segment_inter_subset_endpoint_of_linearIndependent_sub 𝕜 h).antisymm ?_
  simp [singleton_subset_iff, left_mem_segment]

中文:
引理 segment_inter_eq_endpoint_of_linearIndependent_sub
  结论: [ZeroLEOne类 𝕜]
  证明: by
  refine (segment_inter_subset_endpoint_of_linearIndependent_sub 𝕜 h).antisymm ?_
  simp [singleton_subset_iff, left_mem_segment]

Depends on / 依赖: antisymm, left_mem_segment, segment_inter_subset_endpoint_of_linearIndependent_sub, singleton_subset_iff
-/
lemma segment_inter_eq_endpoint_of_linearIndependent_sub [ZeroLEOneClass 𝕜]
    {c x y : E} (h : LinearIndependent 𝕜 ![x - c, y - c]) :
    [c -[𝕜] x] inter [c -[𝕜] y] = {c} := by
  refine (segment_inter_subset_endpoint_of_linearIndependent_sub 𝕜 h).antisymm ?_
  simp [singleton_subset_iff, left_mem_segment]

end OrderedRing

/--
theorem `sameRay_of_mem_segment` / 定理 `sameRay_of_mem_segment`

English:
theorem sameRay_of_mem_segment
  statement: [CommRing 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
  proof: by
  rw [segment_eq_image'] at h
  rcases h with ⟨θ, ⟨hθ₀, hθ₁⟩, rfl⟩
  simpa only [add_sub_cancel_left, ← sub_sub, sub_smul, one_smul] using
    (SameRay.sameRay_nonneg_smul_left (z - y) hθ₀).nonneg_smul_right (sub_nonneg.2 hθ₁)

中文:
定理 sameRay_of_mem_segment
  结论: [交换环 𝕜] [偏序 𝕜] [是StrictOrdered环 𝕜]
  证明: by
  rw [segment_eq_image'] at h
  rcases h with ⟨θ, ⟨hθ₀, hθ₁⟩, rfl⟩
  simpa only [add_sub_cancel_left, ← sub_sub, sub_smul, one_smul] using
    (SameRay.sameRay_nonneg_smul_left (z - y) hθ₀).nonneg_smul_right (sub_nonneg.2 hθ₁)

Depends on / 依赖: SameRay, SameRay.sameRay_nonneg_smul_left, add_sub_cancel_left, nonneg_smul_right, one_smul, sameRay_nonneg_smul_left, segment_eq_image, sub_nonneg, sub_smul, sub_sub
-/
theorem sameRay_of_mem_segment [CommRing 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] {x y z : E}
    (h : x in [y -[𝕜] z]) : SameRay 𝕜 (x - y) (z - x) := by
  rw [segment_eq_image'] at h
  rcases h with ⟨θ, ⟨hθ₀, hθ₁⟩, rfl⟩
  simpa only [add_sub_cancel_left, ← sub_sub, sub_smul, one_smul] using
    (SameRay.sameRay_nonneg_smul_left (z - y) hθ₀).nonneg_smul_right (sub_nonneg.2 hθ₁)

/--
lemma `segment_inter_eq_endpoint_of_linearIndependent_of_ne` / 引理 `segment_inter_eq_endpoint_of_linearIndependent_of_ne`

English:
lemma segment_inter_eq_endpoint_of_linearIndependent_of_ne
  proof: by
  apply segment_inter_eq_endpoint_of_linearIndependent_sub
  simp only [add_sub_add_left_eq_sub]
  suffices H : LinearIndependent 𝕜 ![(-1 : 𝕜) • x + t • y, (-1 : 𝕜) • x + s • y] by
    convert! H using 1; simp only [neg_smul, one_smul]; abel_nf
  nontriviality 𝕜
  rw [LinearIndependent.pair_add_s

中文:
引理 segment_inter_eq_endpoint_of_linearIndependent_of_ne
  证明: by
  apply segment_inter_eq_endpoint_of_linearIndependent_sub
  simp only [add_sub_add_left_eq_sub]
  suffices H : LinearIndependent 𝕜 ![(-1 : 𝕜) • x + t • y, (-1 : 𝕜) • x + s • y] by
    convert! H using 1; simp only [neg_smul, one_smul]; abel_nf
  nontriviality 𝕜
  rw [LinearIndependent.pair_add_s

Depends on / 依赖: LinearIndependent, LinearIndependent.pair_add_smul_add_smul_iff, abel_nf, add_sub_add_left_eq_sub, convert, neg_smul, nontriviality, one_smul, pair_add_smul_add_smul_iff, segment_inter_eq_endpoint_of_linearIndependent_sub
-/
lemma segment_inter_eq_endpoint_of_linearIndependent_of_ne
    [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜] [IsDomain 𝕜] [AddCommGroup E] [Module 𝕜 E]
    {x y : E} (h : LinearIndependent 𝕜 ![x, y]) {s t : 𝕜} (hs : s != t) (c : E) :
    [c + x -[𝕜] c + t • y] inter [c + x -[𝕜] c + s • y] = {c + x} := by
  apply segment_inter_eq_endpoint_of_linearIndependent_sub
  simp only [add_sub_add_left_eq_sub]
  suffices H : LinearIndependent 𝕜 ![(-1 : 𝕜) • x + t • y, (-1 : 𝕜) • x + s • y] by
    convert! H using 1; simp only [neg_smul, one_smul]; abel_nf
  nontriviality 𝕜
  rw [LinearIndependent.pair_add_smul_add_smul_iff]
  aesop

section LinearOrderedRing

variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {x y : E}

/--
theorem `midpoint_mem_openSegment` / 定理 `midpoint_mem_openSegment`

English:
theorem midpoint_mem_openSegment
  given: [Invertible (2 : 𝕜)] (x y : E)
  proof: by
  rw [openSegment_eq_image_lineMap]
  exact ⟨⅟2, ⟨invOf_pos.mpr two_pos, invOf_lt_one one_lt_two⟩, rfl⟩

中文:
定理 midpoint_mem_openSegment
  条件: [可逆 (2 : 𝕜)] (x y : E)
  证明: by
  rw [openSegment_eq_image_lineMap]
  exact ⟨⅟2, ⟨invOf_pos.mpr two_pos, invOf_lt_one one_lt_two⟩, rfl⟩

Depends on / 依赖: invOf_lt_one, invOf_pos, invOf_pos.mpr, one_lt_two, openSegment_eq_image_lineMap, two_pos
-/
theorem midpoint_mem_openSegment [Invertible (2 : 𝕜)] (x y : E) :
    midpoint 𝕜 x y in openSegment 𝕜 x y := by
  rw [openSegment_eq_image_lineMap]
  exact ⟨⅟2, ⟨invOf_pos.mpr two_pos, invOf_lt_one one_lt_two⟩, rfl⟩

/--
theorem `midpoint_mem_segment` / 定理 `midpoint_mem_segment`

English:
theorem midpoint_mem_segment
  given: [Invertible (2 : 𝕜)] (x y : E)
  statement: midpoint 𝕜 x y in [x -[𝕜] y]
  proof: openSegment_subset_segment _ _ _ midpoint_mem_openSegment _ _

中文:
定理 midpoint_mem_segment
  条件: [可逆 (2 : 𝕜)] (x y : E)
  结论: midpoint 𝕜 x y in [x -[𝕜] y]
  证明: openSegment_subset_segment _ _ _ midpoint_mem_openSegment _ _

Depends on / 依赖: midpoint_mem_openSegment, openSegment_subset_segment
-/
theorem midpoint_mem_segment [Invertible (2 : 𝕜)] (x y : E) : midpoint 𝕜 x y in [x -[𝕜] y] :=
openSegment_subset_segment _ _ _ midpoint_mem_openSegment _ _

/--
theorem `mem_openSegment_sub_add` / 定理 `mem_openSegment_sub_add`

English:
theorem mem_openSegment_sub_add
  given: [Invertible (2 : 𝕜)] (x y : E)
  proof: by
  convert! midpoint_mem_openSegment (𝕜 := 𝕜) (x - y) (x + y)
  rw [midpoint_sub_add]

中文:
定理 mem_openSegment_sub_add
  条件: [可逆 (2 : 𝕜)] (x y : E)
  证明: by
  convert! midpoint_mem_openSegment (𝕜 := 𝕜) (x - y) (x + y)
  rw [midpoint_sub_add]

Depends on / 依赖: convert, midpoint_mem_openSegment, midpoint_sub_add
-/
theorem mem_openSegment_sub_add [Invertible (2 : 𝕜)] (x y : E) :
    x in openSegment 𝕜 (x - y) (x + y) := by
  convert! midpoint_mem_openSegment (𝕜 := 𝕜) (x - y) (x + y)
  rw [midpoint_sub_add]

/--
theorem `mem_segment_sub_add` / 定理 `mem_segment_sub_add`

English:
theorem mem_segment_sub_add
  given: [Invertible (2 : 𝕜)] (x y : E)
  statement: x in [x - y -[𝕜] x + y]
  proof: openSegment_subset_segment _ _ _ mem_openSegment_sub_add _ _

中文:
定理 mem_segment_sub_add
  条件: [可逆 (2 : 𝕜)] (x y : E)
  结论: x in [x - y -[𝕜] x + y]
  证明: openSegment_subset_segment _ _ _ mem_openSegment_sub_add _ _

Depends on / 依赖: mem_openSegment_sub_add, openSegment_subset_segment
-/
theorem mem_segment_sub_add [Invertible (2 : 𝕜)] (x y : E) : x in [x - y -[𝕜] x + y] :=
openSegment_subset_segment _ _ _ mem_openSegment_sub_add _ _

/--
theorem `mem_openSegment_add_sub` / 定理 `mem_openSegment_add_sub`

English:
theorem mem_openSegment_add_sub
  given: [Invertible (2 : 𝕜)] (x y : E)
  proof: by
  convert! midpoint_mem_openSegment (𝕜 := 𝕜) (x + y) (x - y)
  rw [midpoint_add_sub]

中文:
定理 mem_openSegment_add_sub
  条件: [可逆 (2 : 𝕜)] (x y : E)
  证明: by
  convert! midpoint_mem_openSegment (𝕜 := 𝕜) (x + y) (x - y)
  rw [midpoint_add_sub]

Depends on / 依赖: convert, midpoint_add_sub, midpoint_mem_openSegment
-/
theorem mem_openSegment_add_sub [Invertible (2 : 𝕜)] (x y : E) :
    x in openSegment 𝕜 (x + y) (x - y) := by
  convert! midpoint_mem_openSegment (𝕜 := 𝕜) (x + y) (x - y)
  rw [midpoint_add_sub]

/--
theorem `mem_segment_add_sub` / 定理 `mem_segment_add_sub`

English:
theorem mem_segment_add_sub
  given: [Invertible (2 : 𝕜)] (x y : E)
  statement: x in [x + y -[𝕜] x - y]
  proof: openSegment_subset_segment _ _ _ mem_openSegment_add_sub _ _

@[simp]

中文:
定理 mem_segment_add_sub
  条件: [可逆 (2 : 𝕜)] (x y : E)
  结论: x in [x + y -[𝕜] x - y]
  证明: openSegment_subset_segment _ _ _ mem_openSegment_add_sub _ _

@[simp]

Depends on / 依赖: mem_openSegment_add_sub, openSegment_subset_segment
-/
theorem mem_segment_add_sub [Invertible (2 : 𝕜)] (x y : E) : x in [x + y -[𝕜] x - y] :=
openSegment_subset_segment _ _ _ mem_openSegment_add_sub _ _

@[simp]
/--
theorem `left_mem_openSegment_iff` / 定理 `left_mem_openSegment_iff`

English:
theorem left_mem_openSegment_iff
  given: [DenselyOrdered 𝕜] [IsTorsionFree 𝕜 E]
  proof: by
  constructor
  · rintro ⟨a, b, _, hb, hab, hx⟩
    refine smul_right_injective _ hb.ne' ((add_right_inj (a • x)).1 ?_)
    rw [hx]; rw [← add_smul]; rw [hab]; rw [one_smul]
  · rintro rfl
    rw [openSegment_same]
    exact mem_singleton _

@[simp]

中文:
定理 left_mem_openSegment_iff
  条件: [稠密序 𝕜] [是无挠 𝕜 E]
  证明: by
  constructor
  · rintro ⟨a, b, _, hb, hab, hx⟩
    refine smul_right_injective _ hb.ne' ((add_right_inj (a • x)).1 ?_)
    rw [hx]; rw [← add_smul]; rw [hab]; rw [one_smul]
  · rintro rfl
    rw [openSegment_same]
    exact mem_singleton _

@[simp]

Depends on / 依赖: add_right_inj, add_smul, hb.ne, mem_singleton, one_smul, openSegment_same, smul_right_injective
-/
theorem left_mem_openSegment_iff [DenselyOrdered 𝕜] [IsTorsionFree 𝕜 E] :
    x in openSegment 𝕜 x y ↔ x = y := by
  constructor
  · rintro ⟨a, b, _, hb, hab, hx⟩
    refine smul_right_injective _ hb.ne' ((add_right_inj (a • x)).1 ?_)
    rw [hx]; rw [← add_smul]; rw [hab]; rw [one_smul]
  · rintro rfl
    rw [openSegment_same]
    exact mem_singleton _

@[simp]
/--
theorem `right_mem_openSegment_iff` / 定理 `right_mem_openSegment_iff`

English:
theorem right_mem_openSegment_iff
  given: [DenselyOrdered 𝕜] [IsTorsionFree 𝕜 E]
  proof: by rw [openSegment_symm, left_mem_openSegment_iff, eq_comm]

中文:
定理 right_mem_openSegment_iff
  条件: [稠密序 𝕜] [是无挠 𝕜 E]
  证明: by rw [openSegment_symm, left_mem_openSegment_iff, eq_comm]

Depends on / 依赖: eq_comm, left_mem_openSegment_iff, openSegment_symm
-/
theorem right_mem_openSegment_iff [DenselyOrdered 𝕜] [IsTorsionFree 𝕜 E] :
    y in openSegment 𝕜 x y ↔ x = y := by rw [openSegment_symm, left_mem_openSegment_iff, eq_comm]

end LinearOrderedRing

section LinearOrderedSemifield

variable [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  {x y z : E}

/--
theorem `mem_segment_iff_div` / 定理 `mem_segment_iff_div`

English:
theorem mem_segment_iff_div
  proof: by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    use a, b, ha, hb
    simp [*]
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨a / (a + b), b / (a + b), by positivity, by positivity, ?_, rfl⟩
    rw [← add_div]; rw [div_self hab.ne']

中文:
定理 mem_segment_iff_div
  证明: by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    use a, b, ha, hb
    simp [*]
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨a / (a + b), b / (a + b), by positivity, by positivity, ?_, rfl⟩
    rw [← add_div]; rw [div_self hab.ne']

Depends on / 依赖: add_div, div_self, hab.ne
-/
theorem mem_segment_iff_div :
    x in [y -[𝕜] z] ↔
      exists a b : 𝕜, 0 <= a ∧ 0 <= b ∧ 0 < a + b ∧ (a / (a + b)) • y + (b / (a + b)) • z = x := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    use a, b, ha, hb
    simp [*]
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨a / (a + b), b / (a + b), by positivity, by positivity, ?_, rfl⟩
    rw [← add_div]; rw [div_self hab.ne']

/--
theorem `mem_openSegment_iff_div` / 定理 `mem_openSegment_iff_div`

English:
theorem mem_openSegment_iff_div
  statement: x in openSegment 𝕜 y z ↔
  proof: by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    use a, b, ha, hb
    rw [hab]; rw [div_one]; rw [div_one]
  · rintro ⟨a, b, ha, hb, rfl⟩
    have hab : 0 < a + b := add_pos' ha hb
    refine ⟨a / (a + b), b / (a + b), by positivity, by positivity, ?_, rfl⟩
    rw [← add_div]; rw [div_self h

中文:
定理 mem_openSegment_iff_div
  结论: x in openSegment 𝕜 y z ↔
  证明: by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    use a, b, ha, hb
    rw [hab]; rw [div_one]; rw [div_one]
  · rintro ⟨a, b, ha, hb, rfl⟩
    have hab : 0 < a + b := add_pos' ha hb
    refine ⟨a / (a + b), b / (a + b), by positivity, by positivity, ?_, rfl⟩
    rw [← add_div]; rw [div_self h

Depends on / 依赖: add_div, add_pos, div_one, div_self, hab.ne
-/
theorem mem_openSegment_iff_div : x in openSegment 𝕜 y z ↔
    exists a b : 𝕜, 0 < a ∧ 0 < b ∧ (a / (a + b)) • y + (b / (a + b)) • z = x := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    use a, b, ha, hb
    rw [hab]; rw [div_one]; rw [div_one]
  · rintro ⟨a, b, ha, hb, rfl⟩
    have hab : 0 < a + b := add_pos' ha hb
    refine ⟨a / (a + b), b / (a + b), by positivity, by positivity, ?_, rfl⟩
    rw [← add_div]; rw [div_self hab.ne']

end LinearOrderedSemifield

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {x y z : E}

/--
theorem `mem_segment_iff_sameRay` / 定理 `mem_segment_iff_sameRay`

English:
theorem mem_segment_iff_sameRay
  statement: x in [y -[𝕜] z] ↔ SameRay 𝕜 (x - y) (z - x)
  proof: by
  refine ⟨sameRay_of_mem_segment, fun h => ?_⟩
  rcases h.exists_eq_smul_add with ⟨a, b, ha, hb, hab, hxy, hzx⟩
  rw [add_comm]; rw [sub_add_sub_cancel] at hxy hzx
  rw [← mem_segment_translate _ (-x)]; rw [neg_add_cancel]
  refine ⟨b, a, hb, ha, add_comm a b ▸ hab, ?_⟩
  rw [← sub_eq_neg_add]; r

中文:
定理 mem_segment_iff_sameRay
  结论: x in [y -[𝕜] z] ↔ SameRay 𝕜 (x - y) (z - x)
  证明: by
  refine ⟨sameRay_of_mem_segment, fun h => ?_⟩
  rcases h.exists_eq_smul_add with ⟨a, b, ha, hb, hab, hxy, hzx⟩
  rw [add_comm]; rw [sub_add_sub_cancel] at hxy hzx
  rw [← mem_segment_translate _ (-x)]; rw [neg_add_cancel]
  refine ⟨b, a, hb, ha, add_comm a b ▸ hab, ?_⟩
  rw [← sub_eq_neg_add]; r

Depends on / 依赖: add_comm, exists_eq_smul_add, h.exists_eq_smul_add, mem_segment_translate, neg_add_cancel, neg_sub, sameRay_of_mem_segment, smul_comm, smul_neg, sub_add_sub_cancel, sub_eq_neg_add
-/
theorem mem_segment_iff_sameRay : x in [y -[𝕜] z] ↔ SameRay 𝕜 (x - y) (z - x) := by
  refine ⟨sameRay_of_mem_segment, fun h => ?_⟩
  rcases h.exists_eq_smul_add with ⟨a, b, ha, hb, hab, hxy, hzx⟩
  rw [add_comm]; rw [sub_add_sub_cancel] at hxy hzx
  rw [← mem_segment_translate _ (-x)]; rw [neg_add_cancel]
  refine ⟨b, a, hb, ha, add_comm a b ▸ hab, ?_⟩
  rw [← sub_eq_neg_add]; rw [← neg_sub]; rw [hxy]; rw [← sub_eq_neg_add]; rw [hzx]; rw [smul_neg]; rw [smul_comm]; rw [neg_add_cancel]

open AffineMap

set_option backward.isDefEq.respectTransparency false in
/--
theorem `openSegment_subset_union` / 定理 `openSegment_subset_union`

English:
theorem openSegment_subset_union
  given: (x y : E) {z : E} (hz : z in range (lineMap x y : 𝕜 -> E))
  proof: by
  rcases hz with ⟨c, rfl⟩
  simp only [openSegment_eq_image_lineMap, ← mapsTo_iff_image_subset]
  rintro a ⟨h₀, h₁⟩
  rcases lt_trichotomy a c with (hac | rfl | hca)
  · right
    left
    have hc : 0 < c := h₀.trans hac
    refine ⟨a / c, ⟨div_pos h₀ hc, (div_lt_one hc).2 hac⟩, ?_⟩
    simp only

中文:
定理 openSegment_subset_union
  条件: (x y : E) {z : E} (hz : z in range (lineMap x y : 𝕜 -> E))
  证明: by
  rcases hz with ⟨c, rfl⟩
  simp only [openSegment_eq_image_lineMap, ← mapsTo_iff_image_subset]
  rintro a ⟨h₀, h₁⟩
  rcases lt_trichotomy a c with (hac | rfl | hca)
  · right
    left
    have hc : 0 < c := h₀.trans hac
    refine ⟨a / c, ⟨div_pos h₀ hc, (div_lt_one hc).2 hac⟩, ?_⟩
    simp only

Depends on / 依赖: div_lt_one, div_pos, hc.ne, hca.trans, homothety_eq_lineMap, homothety_mul_apply, lineMap_apply_one_sub, lt_trichotomy, mapsTo_iff_image_subset, openSegment_eq_image_lineMap, sub_pos
-/
theorem openSegment_subset_union (x y : E) {z : E} (hz : z in range (lineMap x y : 𝕜 -> E)) :
    openSegment 𝕜 x y subseteq insert z (openSegment 𝕜 x z union openSegment 𝕜 z y) := by
  rcases hz with ⟨c, rfl⟩
  simp only [openSegment_eq_image_lineMap, ← mapsTo_iff_image_subset]
  rintro a ⟨h₀, h₁⟩
  rcases lt_trichotomy a c with (hac | rfl | hca)
  · right
    left
    have hc : 0 < c := h₀.trans hac
    refine ⟨a / c, ⟨div_pos h₀ hc, (div_lt_one hc).2 hac⟩, ?_⟩
    simp only [← homothety_eq_lineMap, ← homothety_mul_apply, div_mul_cancel₀ _ hc.ne']
  · left
    rfl
  · right
    right
    have hc : 0 < 1 - c := sub_pos.2 (hca.trans h₁)
    simp only [← lineMap_apply_one_sub y]
    refine
⟨(a - c) / (1 - c), ⟨div_pos (sub_pos.2 hca) hc, (div_lt_one hc).2 sub_lt_sub_right h₁ _⟩,
        ?_⟩
    simp only [← homothety_eq_lineMap, ← homothety_mul_apply, sub_mul, one_mul,
      div_mul_cancel₀ _ hc.ne', sub_sub_sub_cancel_right]

end LinearOrderedField

/-!
#### Segments in an ordered space

Relates `segment`, `openSegment` and `Set.Icc`, `Set.Ico`, `Set.Ioc`, `Set.Ioo`
-/


section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜]

section OrderedAddCommMonoid

variable [AddCommMonoid E] [PartialOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E]
  {x y : E}

/--
theorem `segment_subset_Icc` / 定理 `segment_subset_Icc`

English:
theorem segment_subset_Icc
  given: (h : x <= y)
  statement: [x -[𝕜] y] subseteq Icc x y
  proof: by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  constructor
  · calc
      x = a • x + b • x := (Convex.combo_self hab _).symm
      _ <= a • x + b • y := by gcongr
  · calc
      a • x + b • y <= a • y + b • y := by gcongr
      _ = y := Convex.combo_self hab _

中文:
定理 segment_subset_Icc
  条件: (h : x <= y)
  结论: [x -[𝕜] y] subseteq 闭区间 x y
  证明: by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  constructor
  · calc
      x = a • x + b • x := (Convex.combo_self hab _).symm
      _ <= a • x + b • y := by gcongr
  · calc
      a • x + b • y <= a • y + b • y := by gcongr
      _ = y := Convex.combo_self hab _

Depends on / 依赖: Convex, Convex.combo_self, combo_self
-/
theorem segment_subset_Icc (h : x <= y) : [x -[𝕜] y] subseteq Icc x y := by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  constructor
  · calc
      x = a • x + b • x := (Convex.combo_self hab _).symm
      _ <= a • x + b • y := by gcongr
  · calc
      a • x + b • y <= a • y + b • y := by gcongr
      _ = y := Convex.combo_self hab _

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [AddCommMonoid E] [PartialOrder E] [IsOrderedCancelAddMonoid E]
  [Module 𝕜 E] [PosSMulStrictMono 𝕜 E] {x y : E}

/--
theorem `openSegment_subset_Ioo` / 定理 `openSegment_subset_Ioo`

English:
theorem openSegment_subset_Ioo
  given: (h : x < y)
  statement: openSegment 𝕜 x y subseteq Ioo x y
  proof: by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  constructor
  · calc
      x = a • x + b • x := (Convex.combo_self hab _).symm
      _ < a • x + b • y := by gcongr
  · calc
      a • x + b • y < a • y + b • y := by gcongr
      _ = y := Convex.combo_self hab _

中文:
定理 openSegment_subset_Ioo
  条件: (h : x < y)
  结论: openSegment 𝕜 x y subseteq 开区间 x y
  证明: by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  constructor
  · calc
      x = a • x + b • x := (Convex.combo_self hab _).symm
      _ < a • x + b • y := by gcongr
  · calc
      a • x + b • y < a • y + b • y := by gcongr
      _ = y := Convex.combo_self hab _

Depends on / 依赖: Convex, Convex.combo_self, combo_self
-/
theorem openSegment_subset_Ioo (h : x < y) : openSegment 𝕜 x y subseteq Ioo x y := by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  constructor
  · calc
      x = a • x + b • x := (Convex.combo_self hab _).symm
      _ < a • x + b • y := by gcongr
  · calc
      a • x + b • y < a • y + b • y := by gcongr
      _ = y := Convex.combo_self hab _

end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid

variable [AddCommMonoid E] [LinearOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E]
  {a b : 𝕜}

/--
theorem `segment_subset_uIcc` / 定理 `segment_subset_uIcc`

English:
theorem segment_subset_uIcc
  given: (x y : E)
  statement: [x -[𝕜] y] subseteq uIcc x y
  proof: by
  rcases le_total x y with h | h
  · rw [uIcc_of_le h]
    exact segment_subset_Icc h
  · rw [uIcc_of_ge h, segment_symm]
    exact segment_subset_Icc h

中文:
定理 segment_subset_uIcc
  条件: (x y : E)
  结论: [x -[𝕜] y] subseteq uIcc x y
  证明: by
  rcases le_total x y with h | h
  · rw [uIcc_of_le h]
    exact segment_subset_Icc h
  · rw [uIcc_of_ge h, segment_symm]
    exact segment_subset_Icc h

Depends on / 依赖: le_total, segment_subset_Icc, segment_symm, uIcc_of_ge, uIcc_of_le
-/
theorem segment_subset_uIcc (x y : E) : [x -[𝕜] y] subseteq uIcc x y := by
  rcases le_total x y with h | h
  · rw [uIcc_of_le h]
    exact segment_subset_Icc h
  · rw [uIcc_of_ge h, segment_symm]
    exact segment_subset_Icc h

/--
theorem `Convex.min_le_combo` / 定理 `Convex.min_le_combo`

English:
theorem Convex.min_le_combo
  given: (x y : E) (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1)
  proof: (segment_subset_uIcc x y ⟨_, _, ha, hb, hab, rfl⟩).1

中文:
定理 凸.min_le_combo
  条件: (x y : E) (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1)
  证明: (segment_subset_uIcc x y ⟨_, _, ha, hb, hab, rfl⟩).1

Depends on / 依赖: segment_subset_uIcc
-/
theorem Convex.min_le_combo (x y : E) (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1) :
    min x y <= a • x + b • y :=
  (segment_subset_uIcc x y ⟨_, _, ha, hb, hab, rfl⟩).1

/--
theorem `Convex.combo_le_max` / 定理 `Convex.combo_le_max`

English:
theorem Convex.combo_le_max
  given: (x y : E) (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1)
  proof: (segment_subset_uIcc x y ⟨_, _, ha, hb, hab, rfl⟩).2

中文:
定理 凸.combo_le_max
  条件: (x y : E) (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1)
  证明: (segment_subset_uIcc x y ⟨_, _, ha, hb, hab, rfl⟩).2

Depends on / 依赖: segment_subset_uIcc
-/
theorem Convex.combo_le_max (x y : E) (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1) :
    a • x + b • y <= max x y :=
  (segment_subset_uIcc x y ⟨_, _, ha, hb, hab, rfl⟩).2

end LinearOrderedAddCommMonoid

end OrderedSemiring

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {x y z : 𝕜}

/--
theorem `Icc_subset_segment` / 定理 `Icc_subset_segment`

English:
theorem Icc_subset_segment
  statement: Icc x y subseteq [x -[𝕜] y]
  proof: by
  rintro z ⟨hxz, hyz⟩
  obtain rfl | h := (hxz.trans hyz).eq_or_lt
  · rw [segment_same]
    exact hyz.antisymm hxz
  rw [← sub_nonneg] at hxz hyz
  rw [← sub_pos] at h
  refine ⟨(y - z) / (y - x), (z - x) / (y - x), div_nonneg hyz h.le, div_nonneg hxz h.le, ?_, ?_⟩
  · rw [← add_div, sub_add_sub

中文:
定理 Icc_subset_segment
  结论: 闭区间 x y subseteq [x -[𝕜] y]
  证明: by
  rintro z ⟨hxz, hyz⟩
  obtain rfl | h := (hxz.trans hyz).eq_or_lt
  · rw [segment_same]
    exact hyz.antisymm hxz
  rw [← sub_nonneg] at hxz hyz
  rw [← sub_pos] at h
  refine ⟨(y - z) / (y - x), (z - x) / (y - x), div_nonneg hyz h.le, div_nonneg hxz h.le, ?_, ?_⟩
  · rw [← add_div, sub_add_sub

Depends on / 依赖: add_comm, add_div, antisymm, div_eq_iff, div_nonneg, div_self, eq_or_lt, h.le, h.ne, hxz.trans, hyz.antisymm, mul_comm, mul_div_right_comm, mul_sub, segment_same, smul_eq_mul, sub_add_sub_cancel, sub_mul, sub_nonneg, sub_pos
-/
theorem Icc_subset_segment : Icc x y subseteq [x -[𝕜] y] := by
  rintro z ⟨hxz, hyz⟩
  obtain rfl | h := (hxz.trans hyz).eq_or_lt
  · rw [segment_same]
    exact hyz.antisymm hxz
  rw [← sub_nonneg] at hxz hyz
  rw [← sub_pos] at h
  refine ⟨(y - z) / (y - x), (z - x) / (y - x), div_nonneg hyz h.le, div_nonneg hxz h.le, ?_, ?_⟩
  · rw [← add_div, sub_add_sub_cancel, div_self h.ne']
  · rw [smul_eq_mul, smul_eq_mul, ← mul_div_right_comm, ← mul_div_right_comm, ← add_div,
      div_eq_iff h.ne', add_comm, sub_mul, sub_mul, mul_comm x, sub_add_sub_cancel, mul_sub]

@[simp]
/--
theorem `segment_eq_Icc` / 定理 `segment_eq_Icc`

English:
theorem segment_eq_Icc
  given: (h : x <= y)
  statement: [x -[𝕜] y] = Icc x y
  proof: (segment_subset_Icc h).antisymm Icc_subset_segment

中文:
定理 segment_eq_Icc
  条件: (h : x <= y)
  结论: [x -[𝕜] y] = 闭区间 x y
  证明: (segment_subset_Icc h).antisymm Icc_subset_segment

Depends on / 依赖: Icc_subset_segment, antisymm, segment_subset_Icc
-/
theorem segment_eq_Icc (h : x <= y) : [x -[𝕜] y] = Icc x y :=
  (segment_subset_Icc h).antisymm Icc_subset_segment

/--
theorem `Ioo_subset_openSegment` / 定理 `Ioo_subset_openSegment`

English:
theorem Ioo_subset_openSegment
  statement: Ioo x y subseteq openSegment 𝕜 x y
  proof: fun _ hz =>
mem_openSegment_of_ne_left_right hz.1.ne hz.2.ne' Icc_subset_segment Ioo_subset_Icc_self hz

@[simp]

中文:
定理 Ioo_subset_openSegment
  结论: 开区间 x y subseteq openSegment 𝕜 x y
  证明: fun _ hz =>
mem_openSegment_of_ne_left_right hz.1.ne hz.2.ne' Icc_subset_segment Ioo_subset_Icc_self hz

@[simp]
-/
theorem Ioo_subset_openSegment : Ioo x y subseteq openSegment 𝕜 x y := fun _ hz =>
mem_openSegment_of_ne_left_right hz.1.ne hz.2.ne' Icc_subset_segment Ioo_subset_Icc_self hz

@[simp]
/--
theorem `openSegment_eq_Ioo` / 定理 `openSegment_eq_Ioo`

English:
theorem openSegment_eq_Ioo
  given: (h : x < y)
  statement: openSegment 𝕜 x y = Ioo x y
  proof: (openSegment_subset_Ioo h).antisymm Ioo_subset_openSegment

中文:
定理 openSegment_eq_Ioo
  条件: (h : x < y)
  结论: openSegment 𝕜 x y = 开区间 x y
  证明: (openSegment_subset_Ioo h).antisymm Ioo_subset_openSegment

Depends on / 依赖: Ioo_subset_openSegment, antisymm, openSegment_subset_Ioo
-/
theorem openSegment_eq_Ioo (h : x < y) : openSegment 𝕜 x y = Ioo x y :=
  (openSegment_subset_Ioo h).antisymm Ioo_subset_openSegment

/--
theorem `segment_eq_Icc'` / 定理 `segment_eq_Icc'`

English:
theorem segment_eq_Icc'
  given: (x y : 𝕜)
  statement: [x -[𝕜] y] = Icc (min x y) (max x y)
  proof: by
  rcases le_total x y with h | h
  · rw [segment_eq_Icc h, max_eq_right h, min_eq_left h]
  · rw [segment_symm, segment_eq_Icc h, max_eq_left h, min_eq_right h]

中文:
定理 segment_eq_Icc'
  条件: (x y : 𝕜)
  结论: [x -[𝕜] y] = 闭区间 (最小值 x y) (最大值 x y)
  证明: by
  rcases le_total x y with h | h
  · rw [segment_eq_Icc h, max_eq_right h, min_eq_left h]
  · rw [segment_symm, segment_eq_Icc h, max_eq_left h, min_eq_right h]

Depends on / 依赖: le_total, max_eq_left, max_eq_right, min_eq_left, min_eq_right, segment_eq_Icc, segment_symm
-/
theorem segment_eq_Icc' (x y : 𝕜) : [x -[𝕜] y] = Icc (min x y) (max x y) := by
  rcases le_total x y with h | h
  · rw [segment_eq_Icc h, max_eq_right h, min_eq_left h]
  · rw [segment_symm, segment_eq_Icc h, max_eq_left h, min_eq_right h]

/--
theorem `openSegment_eq_Ioo'` / 定理 `openSegment_eq_Ioo'`

English:
theorem openSegment_eq_Ioo'
  given: (hxy : x != y)
  statement: openSegment 𝕜 x y = Ioo (min x y) (max x y)
  proof: by
  rcases hxy.lt_or_gt with h | h
  · rw [openSegment_eq_Ioo h, max_eq_right h.le, min_eq_left h.le]
  · rw [openSegment_symm, openSegment_eq_Ioo h, max_eq_left h.le, min_eq_right h.le]

中文:
定理 openSegment_eq_Ioo'
  条件: (hxy : x != y)
  结论: openSegment 𝕜 x y = 开区间 (最小值 x y) (最大值 x y)
  证明: by
  rcases hxy.lt_or_gt with h | h
  · rw [openSegment_eq_Ioo h, max_eq_right h.le, min_eq_left h.le]
  · rw [openSegment_symm, openSegment_eq_Ioo h, max_eq_left h.le, min_eq_right h.le]

Depends on / 依赖: h.le, hxy.lt_or_gt, lt_or_gt, max_eq_left, max_eq_right, min_eq_left, min_eq_right, openSegment_eq_Ioo, openSegment_symm
-/
theorem openSegment_eq_Ioo' (hxy : x != y) : openSegment 𝕜 x y = Ioo (min x y) (max x y) := by
  rcases hxy.lt_or_gt with h | h
  · rw [openSegment_eq_Ioo h, max_eq_right h.le, min_eq_left h.le]
  · rw [openSegment_symm, openSegment_eq_Ioo h, max_eq_left h.le, min_eq_right h.le]

/--
theorem `segment_eq_uIcc` / 定理 `segment_eq_uIcc`

English:
theorem segment_eq_uIcc
  given: (x y : 𝕜)
  statement: [x -[𝕜] y] = uIcc x y
  proof: segment_eq_Icc' _ _

中文:
定理 segment_eq_uIcc
  条件: (x y : 𝕜)
  结论: [x -[𝕜] y] = uIcc x y
  证明: segment_eq_Icc' _ _

Depends on / 依赖: segment_eq_Icc
-/
theorem segment_eq_uIcc (x y : 𝕜) : [x -[𝕜] y] = uIcc x y :=
  segment_eq_Icc' _ _

/--
theorem `Convex.mem_Icc` / 定理 `Convex.mem_Icc`

English:
theorem Convex.mem_Icc
  given: (h : x <= y)
  proof: by
  simp only [← segment_eq_Icc h, segment, mem_ofPred_eq, smul_eq_mul, exists_and_left]

中文:
定理 凸.mem_Icc
  条件: (h : x <= y)
  证明: by
  simp only [← segment_eq_Icc h, segment, mem_ofPred_eq, smul_eq_mul, exists_and_left]

Depends on / 依赖: exists_and_left, mem_ofPred_eq, segment, segment_eq_Icc, smul_eq_mul
-/
theorem Convex.mem_Icc (h : x <= y) :
    z in Icc x y ↔ exists a b, 0 <= a ∧ 0 <= b ∧ a + b = 1 ∧ a * x + b * y = z := by
  simp only [← segment_eq_Icc h, segment, mem_ofPred_eq, smul_eq_mul, exists_and_left]

/--
theorem `Convex.mem_Ioo` / 定理 `Convex.mem_Ioo`

English:
theorem Convex.mem_Ioo
  given: (h : x < y)
  proof: by
  simp only [← openSegment_eq_Ioo h, openSegment, smul_eq_mul, exists_and_left, mem_ofPred_eq]

中文:
定理 凸.mem_Ioo
  条件: (h : x < y)
  证明: by
  simp only [← openSegment_eq_Ioo h, openSegment, smul_eq_mul, exists_and_left, mem_ofPred_eq]

Depends on / 依赖: exists_and_left, mem_ofPred_eq, openSegment, openSegment_eq_Ioo, smul_eq_mul
-/
theorem Convex.mem_Ioo (h : x < y) :
    z in Ioo x y ↔ exists a b, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z := by
  simp only [← openSegment_eq_Ioo h, openSegment, smul_eq_mul, exists_and_left, mem_ofPred_eq]

/--
theorem `Convex.mem_Ioc` / 定理 `Convex.mem_Ioc`

English:
theorem Convex.mem_Ioc
  given: (h : x < y)
  proof: by
  refine ⟨fun hz => ?_, ?_⟩
  · obtain ⟨a, b, ha, hb, hab, rfl⟩ := (Convex.mem_Icc h.le).1 (Ioc_subset_Icc_self hz)
    obtain rfl | hb' := hb.eq_or_lt
    · rw [add_zero] at hab
      rw [hab]; rw [one_mul]; rw [zero_mul]; rw [add_zero] at hz
      exact (hz.1.ne rfl).elim
    · exact ⟨a, b, ha,

中文:
定理 凸.mem_Ioc
  条件: (h : x < y)
  证明: by
  refine ⟨fun hz => ?_, ?_⟩
  · obtain ⟨a, b, ha, hb, hab, rfl⟩ := (Convex.mem_Icc h.le).1 (Ioc_subset_Icc_self hz)
    obtain rfl | hb' := hb.eq_or_lt
    · rw [add_zero] at hab
      rw [hab]; rw [one_mul]; rw [zero_mul]; rw [add_zero] at hz
      exact (hz.1.ne rfl).elim
    · exact ⟨a, b, ha,

Depends on / 依赖: Convex, Convex.mem_Icc, Convex.mem_Ioo, Ioc_subset_Icc_self, Ioo_subset_Ioc_self, add_zero, eq_or_lt, h.le, ha.eq_or_lt, hb.eq_or_lt, mem_Icc, mem_Ioo, one_mul, right_mem_Ioc, zero_add, zero_mul
-/
theorem Convex.mem_Ioc (h : x < y) :
    z in Ioc x y ↔ exists a b, 0 <= a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z := by
  refine ⟨fun hz => ?_, ?_⟩
  · obtain ⟨a, b, ha, hb, hab, rfl⟩ := (Convex.mem_Icc h.le).1 (Ioc_subset_Icc_self hz)
    obtain rfl | hb' := hb.eq_or_lt
    · rw [add_zero] at hab
      rw [hab]; rw [one_mul]; rw [zero_mul]; rw [add_zero] at hz
      exact (hz.1.ne rfl).elim
    · exact ⟨a, b, ha, hb', hab, rfl⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    obtain rfl | ha' := ha.eq_or_lt
    · rw [zero_add] at hab
      rwa [hab, one_mul, zero_mul, zero_add, right_mem_Ioc]
    · exact Ioo_subset_Ioc_self ((Convex.mem_Ioo h).2 ⟨a, b, ha', hb, hab, rfl⟩)

/--
theorem `Convex.mem_Ico` / 定理 `Convex.mem_Ico`

English:
theorem Convex.mem_Ico
  given: (h : x < y)
  proof: by
  refine ⟨fun hz => ?_, ?_⟩
  · obtain ⟨a, b, ha, hb, hab, rfl⟩ := (Convex.mem_Icc h.le).1 (Ico_subset_Icc_self hz)
    obtain rfl | ha' := ha.eq_or_lt
    · rw [zero_add] at hab
      rw [hab]; rw [one_mul]; rw [zero_mul]; rw [zero_add] at hz
      exact (hz.2.ne rfl).elim
    · exact ⟨a, b, ha'

中文:
定理 凸.mem_Ico
  条件: (h : x < y)
  证明: by
  refine ⟨fun hz => ?_, ?_⟩
  · obtain ⟨a, b, ha, hb, hab, rfl⟩ := (Convex.mem_Icc h.le).1 (Ico_subset_Icc_self hz)
    obtain rfl | ha' := ha.eq_or_lt
    · rw [zero_add] at hab
      rw [hab]; rw [one_mul]; rw [zero_mul]; rw [zero_add] at hz
      exact (hz.2.ne rfl).elim
    · exact ⟨a, b, ha'

Depends on / 依赖: Convex, Convex.mem_Icc, Convex.mem_Ioo, Ico_subset_Icc_self, Ioo_subset_Ico_self, add_zero, eq_or_lt, h.le, ha.eq_or_lt, hb.eq_or_lt, left_mem_Ico, mem_Icc, mem_Ioo, one_mul, zero_add, zero_mul
-/
theorem Convex.mem_Ico (h : x < y) :
    z in Ico x y ↔ exists a b, 0 < a ∧ 0 <= b ∧ a + b = 1 ∧ a * x + b * y = z := by
  refine ⟨fun hz => ?_, ?_⟩
  · obtain ⟨a, b, ha, hb, hab, rfl⟩ := (Convex.mem_Icc h.le).1 (Ico_subset_Icc_self hz)
    obtain rfl | ha' := ha.eq_or_lt
    · rw [zero_add] at hab
      rw [hab]; rw [one_mul]; rw [zero_mul]; rw [zero_add] at hz
      exact (hz.2.ne rfl).elim
    · exact ⟨a, b, ha', hb, hab, rfl⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    obtain rfl | hb' := hb.eq_or_lt
    · rw [add_zero] at hab
      rwa [hab, one_mul, zero_mul, add_zero, left_mem_Ico]
    · exact Ioo_subset_Ico_self ((Convex.mem_Ioo h).2 ⟨a, b, ha, hb', hab, rfl⟩)

end LinearOrderedField

namespace Nonneg

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {x y z : 𝕜}

/--
lemma `Icc_subset_segment` / 引理 `Icc_subset_segment`

English:
lemma Icc_subset_segment
  given: {x y : {t : 𝕜 // 0 <= t}}
  proof: by
  intro a ⟨hxa, hay⟩
  rw [← Subtype.coe_le_coe] at hxa hay
  rcases Icc_subset_segment ⟨hxa, hay⟩ with ⟨t₁, t₂, t₁_nonneg, t₂_nonneg, t_add, hta⟩
  refine ⟨⟨t₁, t₁_nonneg⟩, ⟨t₂, t₂_nonneg⟩, zero_le, zero_le, ?_, ?_⟩ <;>
  ext <;> simpa

中文:
引理 Icc_subset_segment
  条件: {x y : {t : 𝕜 // 0 <= t}}
  证明: by
  intro a ⟨hxa, hay⟩
  rw [← Subtype.coe_le_coe] at hxa hay
  rcases Icc_subset_segment ⟨hxa, hay⟩ with ⟨t₁, t₂, t₁_nonneg, t₂_nonneg, t_add, hta⟩
  refine ⟨⟨t₁, t₁_nonneg⟩, ⟨t₂, t₂_nonneg⟩, zero_le, zero_le, ?_, ?_⟩ <;>
  ext <;> simpa
-/
protected lemma Icc_subset_segment {x y : {t : 𝕜 // 0 <= t}} :
    Icc x y subseteq segment {t : 𝕜 // 0 <= t} x y := by
  intro a ⟨hxa, hay⟩
  rw [← Subtype.coe_le_coe] at hxa hay
  rcases Icc_subset_segment ⟨hxa, hay⟩ with ⟨t₁, t₂, t₁_nonneg, t₂_nonneg, t_add, hta⟩
  refine ⟨⟨t₁, t₁_nonneg⟩, ⟨t₂, t₂_nonneg⟩, zero_le, zero_le, ?_, ?_⟩ <;>
  ext <;> simpa

/--
lemma `segment_eq_Icc` / 引理 `segment_eq_Icc`

English:
lemma segment_eq_Icc
  given: {x y : {t : 𝕜 // 0 <= t}} (hxy : x <= y)
  proof: by
  refine subset_antisymm (segment_subset_Icc hxy) Nonneg.Icc_subset_segment

中文:
引理 segment_eq_Icc
  条件: {x y : {t : 𝕜 // 0 <= t}} (hxy : x <= y)
  证明: by
  refine subset_antisymm (segment_subset_Icc hxy) Nonneg.Icc_subset_segment
-/
protected lemma segment_eq_Icc {x y : {t : 𝕜 // 0 <= t}} (hxy : x <= y) :
    segment {t : 𝕜 // 0 <= t} x y = Icc x y := by
  refine subset_antisymm (segment_subset_Icc hxy) Nonneg.Icc_subset_segment

/--
lemma `segment_eq_uIcc` / 引理 `segment_eq_uIcc`

English:
lemma segment_eq_uIcc
  given: {x y : {t : 𝕜 // 0 <= t}}
  proof: by
  rcases le_total x y with h | h
  · simp [h, Nonneg.segment_eq_Icc]
  · simp [h, segment_symm _ x y, Nonneg.segment_eq_Icc]

中文:
引理 segment_eq_uIcc
  条件: {x y : {t : 𝕜 // 0 <= t}}
  证明: by
  rcases le_total x y with h | h
  · simp [h, Nonneg.segment_eq_Icc]
  · simp [h, segment_symm _ x y, Nonneg.segment_eq_Icc]
-/
protected lemma segment_eq_uIcc {x y : {t : 𝕜 // 0 <= t}} :
    segment {t : 𝕜 // 0 <= t} x y = uIcc x y := by
  rcases le_total x y with h | h
  · simp [h, Nonneg.segment_eq_Icc]
  · simp [h, segment_symm _ x y, Nonneg.segment_eq_Icc]

end Nonneg

namespace Prod

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F]

/--
theorem `segment_subset` / 定理 `segment_subset`

English:
theorem segment_subset
  given: (x y : E × F)
  statement: segment 𝕜 x y subseteq segment 𝕜 x.1 y.1 ×ˢ segment 𝕜 x.2 y.2
  proof: by
  rintro z ⟨a, b, ha, hb, hab, hz⟩
  exact ⟨⟨a, b, ha, hb, hab, congr_arg Prod.fst hz⟩, a, b, ha, hb, hab, congr_arg Prod.snd hz⟩

中文:
定理 segment_subset
  条件: (x y : E × F)
  结论: segment 𝕜 x y subseteq segment 𝕜 x.1 y.1 ×ˢ segment 𝕜 x.2 y.2
  证明: by
  rintro z ⟨a, b, ha, hb, hab, hz⟩
  exact ⟨⟨a, b, ha, hb, hab, congr_arg Prod.fst hz⟩, a, b, ha, hb, hab, congr_arg Prod.snd hz⟩

Depends on / 依赖: Prod.fst, Prod.snd, congr_arg
-/
theorem segment_subset (x y : E × F) : segment 𝕜 x y subseteq segment 𝕜 x.1 y.1 ×ˢ segment 𝕜 x.2 y.2 := by
  rintro z ⟨a, b, ha, hb, hab, hz⟩
  exact ⟨⟨a, b, ha, hb, hab, congr_arg Prod.fst hz⟩, a, b, ha, hb, hab, congr_arg Prod.snd hz⟩

/--
theorem `openSegment_subset` / 定理 `openSegment_subset`

English:
theorem openSegment_subset
  given: (x y : E × F)
  proof: by
  rintro z ⟨a, b, ha, hb, hab, hz⟩
  exact ⟨⟨a, b, ha, hb, hab, congr_arg Prod.fst hz⟩, a, b, ha, hb, hab, congr_arg Prod.snd hz⟩

中文:
定理 openSegment_subset
  条件: (x y : E × F)
  证明: by
  rintro z ⟨a, b, ha, hb, hab, hz⟩
  exact ⟨⟨a, b, ha, hb, hab, congr_arg Prod.fst hz⟩, a, b, ha, hb, hab, congr_arg Prod.snd hz⟩

Depends on / 依赖: Prod.fst, Prod.snd, congr_arg
-/
theorem openSegment_subset (x y : E × F) :
    openSegment 𝕜 x y subseteq openSegment 𝕜 x.1 y.1 ×ˢ openSegment 𝕜 x.2 y.2 := by
  rintro z ⟨a, b, ha, hb, hab, hz⟩
  exact ⟨⟨a, b, ha, hb, hab, congr_arg Prod.fst hz⟩, a, b, ha, hb, hab, congr_arg Prod.snd hz⟩

/--
theorem `image_mk_segment_left` / 定理 `image_mk_segment_left`

English:
theorem image_mk_segment_left
  given: (x₁ x₂ : E) (y : F)
  proof: by
  rw [segment_eq_image₂]; rw [segment_eq_image₂]; rw [image_image]
  refine EqOn.image_eq fun a ha => ?_
  simp [Convex.combo_self ha.2.2]

中文:
定理 image_mk_segment_left
  条件: (x₁ x₂ : E) (y : F)
  证明: by
  rw [segment_eq_image₂]; rw [segment_eq_image₂]; rw [image_image]
  refine EqOn.image_eq fun a ha => ?_
  simp [Convex.combo_self ha.2.2]

Depends on / 依赖: Convex, Convex.combo_self, EqOn.image_eq, combo_self, image_eq, image_image
-/
theorem image_mk_segment_left (x₁ x₂ : E) (y : F) :
    (fun x => (x, y)) '' [x₁ -[𝕜] x₂] = [(x₁, y) -[𝕜] (x₂, y)] := by
  rw [segment_eq_image₂]; rw [segment_eq_image₂]; rw [image_image]
  refine EqOn.image_eq fun a ha => ?_
  simp [Convex.combo_self ha.2.2]

/--
theorem `image_mk_segment_right` / 定理 `image_mk_segment_right`

English:
theorem image_mk_segment_right
  given: (x : E) (y₁ y₂ : F)
  proof: by
  rw [segment_eq_image₂]; rw [segment_eq_image₂]; rw [image_image]
  refine EqOn.image_eq fun a ha => ?_
  simp [Convex.combo_self ha.2.2]

中文:
定理 image_mk_segment_right
  条件: (x : E) (y₁ y₂ : F)
  证明: by
  rw [segment_eq_image₂]; rw [segment_eq_image₂]; rw [image_image]
  refine EqOn.image_eq fun a ha => ?_
  simp [Convex.combo_self ha.2.2]

Depends on / 依赖: Convex, Convex.combo_self, EqOn.image_eq, combo_self, image_eq, image_image
-/
theorem image_mk_segment_right (x : E) (y₁ y₂ : F) :
    (fun y => (x, y)) '' [y₁ -[𝕜] y₂] = [(x, y₁) -[𝕜] (x, y₂)] := by
  rw [segment_eq_image₂]; rw [segment_eq_image₂]; rw [image_image]
  refine EqOn.image_eq fun a ha => ?_
  simp [Convex.combo_self ha.2.2]

/--
theorem `image_mk_openSegment_left` / 定理 `image_mk_openSegment_left`

English:
theorem image_mk_openSegment_left
  given: (x₁ x₂ : E) (y : F)
  proof: by
  rw [openSegment_eq_image₂]; rw [openSegment_eq_image₂]; rw [image_image]
  refine EqOn.image_eq fun a ha => ?_
  simp [Convex.combo_self ha.2.2]

@[simp]

中文:
定理 image_mk_openSegment_left
  条件: (x₁ x₂ : E) (y : F)
  证明: by
  rw [openSegment_eq_image₂]; rw [openSegment_eq_image₂]; rw [image_image]
  refine EqOn.image_eq fun a ha => ?_
  simp [Convex.combo_self ha.2.2]

@[simp]

Depends on / 依赖: Convex, Convex.combo_self, EqOn.image_eq, combo_self, image_eq, image_image
-/
theorem image_mk_openSegment_left (x₁ x₂ : E) (y : F) :
    (fun x => (x, y)) '' openSegment 𝕜 x₁ x₂ = openSegment 𝕜 (x₁, y) (x₂, y) := by
  rw [openSegment_eq_image₂]; rw [openSegment_eq_image₂]; rw [image_image]
  refine EqOn.image_eq fun a ha => ?_
  simp [Convex.combo_self ha.2.2]

@[simp]
/--
theorem `image_mk_openSegment_right` / 定理 `image_mk_openSegment_right`

English:
theorem image_mk_openSegment_right
  given: (x : E) (y₁ y₂ : F)
  proof: by
  rw [openSegment_eq_image₂]; rw [openSegment_eq_image₂]; rw [image_image]
  refine EqOn.image_eq fun a ha => ?_
  simp [Convex.combo_self ha.2.2]

中文:
定理 image_mk_openSegment_right
  条件: (x : E) (y₁ y₂ : F)
  证明: by
  rw [openSegment_eq_image₂]; rw [openSegment_eq_image₂]; rw [image_image]
  refine EqOn.image_eq fun a ha => ?_
  simp [Convex.combo_self ha.2.2]

Depends on / 依赖: Convex, Convex.combo_self, EqOn.image_eq, combo_self, image_eq, image_image
-/
theorem image_mk_openSegment_right (x : E) (y₁ y₂ : F) :
    (fun y => (x, y)) '' openSegment 𝕜 y₁ y₂ = openSegment 𝕜 (x, y₁) (x, y₂) := by
  rw [openSegment_eq_image₂]; rw [openSegment_eq_image₂]; rw [image_image]
  refine EqOn.image_eq fun a ha => ?_
  simp [Convex.combo_self ha.2.2]

end Prod

namespace Pi

variable [Semiring 𝕜] [PartialOrder 𝕜] [forall i, AddCommMonoid (M i)] [forall i, Module 𝕜 (M i)] {s : Set ι}

/--
theorem `segment_subset` / 定理 `segment_subset`

English:
theorem segment_subset
  given: (x y : forall i, M i)
  statement: segment 𝕜 x y subseteq s.pi fun i => segment 𝕜 (x i) (y i)
  proof: by
  rintro z ⟨a, b, ha, hb, hab, hz⟩ i -
  exact ⟨a, b, ha, hb, hab, congr_fun hz i⟩

中文:
定理 segment_subset
  条件: (x y : 对任意 i, M i)
  结论: segment 𝕜 x y subseteq s.pi fun i => segment 𝕜 (x i) (y i)
  证明: by
  rintro z ⟨a, b, ha, hb, hab, hz⟩ i -
  exact ⟨a, b, ha, hb, hab, congr_fun hz i⟩

Depends on / 依赖: congr_fun
-/
theorem segment_subset (x y : forall i, M i) : segment 𝕜 x y subseteq s.pi fun i => segment 𝕜 (x i) (y i) := by
  rintro z ⟨a, b, ha, hb, hab, hz⟩ i -
  exact ⟨a, b, ha, hb, hab, congr_fun hz i⟩

/--
theorem `openSegment_subset` / 定理 `openSegment_subset`

English:
theorem openSegment_subset
  given: (x y : forall i, M i)
  proof: by
  rintro z ⟨a, b, ha, hb, hab, hz⟩ i -
  exact ⟨a, b, ha, hb, hab, congr_fun hz i⟩

中文:
定理 openSegment_subset
  条件: (x y : 对任意 i, M i)
  证明: by
  rintro z ⟨a, b, ha, hb, hab, hz⟩ i -
  exact ⟨a, b, ha, hb, hab, congr_fun hz i⟩

Depends on / 依赖: congr_fun
-/
theorem openSegment_subset (x y : forall i, M i) :
    openSegment 𝕜 x y subseteq s.pi fun i => openSegment 𝕜 (x i) (y i) := by
  rintro z ⟨a, b, ha, hb, hab, hz⟩ i -
  exact ⟨a, b, ha, hb, hab, congr_fun hz i⟩

variable [DecidableEq ι]

/--
theorem `image_update_segment` / 定理 `image_update_segment`

English:
theorem image_update_segment
  given: (i : ι) (x₁ x₂ : M i) (y : forall i, M i)
  proof: by
  rw [segment_eq_image₂]; rw [segment_eq_image₂]; rw [image_image]
  refine EqOn.image_eq fun a ha => ?_
  simp only [← update_smul, ← update_add, Convex.combo_self ha.2.2]

中文:
定理 image_update_segment
  条件: (i : ι) (x₁ x₂ : M i) (y : 对任意 i, M i)
  证明: by
  rw [segment_eq_image₂]; rw [segment_eq_image₂]; rw [image_image]
  refine EqOn.image_eq fun a ha => ?_
  simp only [← update_smul, ← update_add, Convex.combo_self ha.2.2]

Depends on / 依赖: Convex, Convex.combo_self, EqOn.image_eq, combo_self, image_eq, image_image, update_add, update_smul
-/
theorem image_update_segment (i : ι) (x₁ x₂ : M i) (y : forall i, M i) :
    update y i '' [x₁ -[𝕜] x₂] = [update y i x₁ -[𝕜] update y i x₂] := by
  rw [segment_eq_image₂]; rw [segment_eq_image₂]; rw [image_image]
  refine EqOn.image_eq fun a ha => ?_
  simp only [← update_smul, ← update_add, Convex.combo_self ha.2.2]

/--
theorem `image_update_openSegment` / 定理 `image_update_openSegment`

English:
theorem image_update_openSegment
  given: (i : ι) (x₁ x₂ : M i) (y : forall i, M i)
  proof: by
  rw [openSegment_eq_image₂]; rw [openSegment_eq_image₂]; rw [image_image]
  refine EqOn.image_eq fun a ha => ?_
  simp only [← update_smul, ← update_add, Convex.combo_self ha.2.2]

中文:
定理 image_update_openSegment
  条件: (i : ι) (x₁ x₂ : M i) (y : 对任意 i, M i)
  证明: by
  rw [openSegment_eq_image₂]; rw [openSegment_eq_image₂]; rw [image_image]
  refine EqOn.image_eq fun a ha => ?_
  simp only [← update_smul, ← update_add, Convex.combo_self ha.2.2]

Depends on / 依赖: Convex, Convex.combo_self, EqOn.image_eq, combo_self, image_eq, image_image, update_add, update_smul
-/
theorem image_update_openSegment (i : ι) (x₁ x₂ : M i) (y : forall i, M i) :
    update y i '' openSegment 𝕜 x₁ x₂ = openSegment 𝕜 (update y i x₁) (update y i x₂) := by
  rw [openSegment_eq_image₂]; rw [openSegment_eq_image₂]; rw [image_image]
  refine EqOn.image_eq fun a ha => ?_
  simp only [← update_smul, ← update_add, Convex.combo_self ha.2.2]

end Pi
