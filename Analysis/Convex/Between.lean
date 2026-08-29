/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic.FieldSimp

/-!
# Betweenness in affine spaces

This file defines notions of a point in an affine space being between two given points.

## Main definitions

* `affineSegment R x y`: The segment of points weakly between `x` and `y`.
* `Wbtw R x y z`: The point `y` is weakly between `x` and `z`.
* `Sbtw R x y z`: The point `y` is strictly between `x` and `z`.

-/

@[expose] public section


variable (R : Type*) {V V' P P' : Type*}

open AffineEquiv AffineMap Module

section OrderedRing

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `affineSegment` / `affineSegment` 的定义

English:
definition affineSegment
  signature: [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V]
  body: lineMap x y '' Set.Icc (0 : R) 1

中文:
定义 affineSegment
  签名: [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V]
  定义体: lineMap x y '' Set.Icc (0 : R) 1

Depends on / 依赖: Set.Icc, lineMap
-/
def affineSegment [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V]
    [AddTorsor V P] (x y : P) :=
  lineMap x y '' Set.Icc (0 : R) 1

variable [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V] [AddTorsor V P]
variable [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

/--
lemma `affineSegment_subset_affineSpan` / 引理 `affineSegment_subset_affineSpan`

English:
lemma affineSegment_subset_affineSpan
  given: (x y : P)
  statement: affineSegment R x y subseteq line[R, x, y]
  proof: by
  rw [affineSegment]; rw [Set.subset_def]
  rintro p ⟨r, -, rfl⟩
  exact lineMap_mem_affineSpan_pair _ _ _

中文:
引理 affineSegment_subset_affineSpan
  条件: (x y : P)
  结论: affineSegment R x y subseteq line[R, x, y]
  证明: by
  rw [affineSegment]; rw [Set.subset_def]
  rintro p ⟨r, -, rfl⟩
  exact lineMap_mem_affineSpan_pair _ _ _

Depends on / 依赖: Set.subset_def, affineSegment, lineMap_mem_affineSpan_pair, subset_def
-/
lemma affineSegment_subset_affineSpan (x y : P) : affineSegment R x y subseteq line[R, x, y] := by
  rw [affineSegment]; rw [Set.subset_def]
  rintro p ⟨r, -, rfl⟩
  exact lineMap_mem_affineSpan_pair _ _ _

variable {R} in
@[simp]
/--
theorem `affineSegment_image` / 定理 `affineSegment_image`

English:
theorem affineSegment_image
  given: (f : P ->ᵃ[R] P') (x y : P)
  proof: by
  rw [affineSegment]; rw [affineSegment]; rw [Set.image_image]; rw [← comp_lineMap]
  rfl

@[simp]

中文:
定理 affineSegment_image
  条件: (f : P ->ᵃ[R] P') (x y : P)
  证明: by
  rw [affineSegment]; rw [affineSegment]; rw [Set.image_image]; rw [← comp_lineMap]
  rfl

@[simp]

Depends on / 依赖: Set.image_image, affineSegment, comp_lineMap, image_image
-/
theorem affineSegment_image (f : P ->ᵃ[R] P') (x y : P) :
    f '' affineSegment R x y = affineSegment R (f x) (f y) := by
  rw [affineSegment]; rw [affineSegment]; rw [Set.image_image]; rw [← comp_lineMap]
  rfl

@[simp]
/--
theorem `affineSegment_const_vadd_image` / 定理 `affineSegment_const_vadd_image`

English:
theorem affineSegment_const_vadd_image
  given: (x y : P) (v : V)
  proof: affineSegment_image (AffineEquiv.constVAdd R P v : P ->ᵃ[R] P) x y

@[simp]

中文:
定理 affineSegment_const_vadd_image
  条件: (x y : P) (v : V)
  证明: affineSegment_image (AffineEquiv.constVAdd R P v : P ->ᵃ[R] P) x y

@[simp]

Depends on / 依赖: AffineEquiv, AffineEquiv.constVAdd, affineSegment_image, constVAdd
-/
theorem affineSegment_const_vadd_image (x y : P) (v : V) :
    (v +ᵥ ·) '' affineSegment R x y = affineSegment R (v +ᵥ x) (v +ᵥ y) :=
  affineSegment_image (AffineEquiv.constVAdd R P v : P ->ᵃ[R] P) x y

@[simp]
/--
theorem `affineSegment_vadd_const_image` / 定理 `affineSegment_vadd_const_image`

English:
theorem affineSegment_vadd_const_image
  given: (x y : V) (p : P)
  proof: affineSegment_image (AffineEquiv.vaddConst R p : V ->ᵃ[R] P) x y

@[simp]

中文:
定理 affineSegment_vadd_const_image
  条件: (x y : V) (p : P)
  证明: affineSegment_image (AffineEquiv.vaddConst R p : V ->ᵃ[R] P) x y

@[simp]

Depends on / 依赖: AffineEquiv, AffineEquiv.vaddConst, affineSegment_image, vaddConst
-/
theorem affineSegment_vadd_const_image (x y : V) (p : P) :
    (· +ᵥ p) '' affineSegment R x y = affineSegment R (x +ᵥ p) (y +ᵥ p) :=
  affineSegment_image (AffineEquiv.vaddConst R p : V ->ᵃ[R] P) x y

@[simp]
/--
theorem `affineSegment_const_vsub_image` / 定理 `affineSegment_const_vsub_image`

English:
theorem affineSegment_const_vsub_image
  given: (x y p : P)
  proof: affineSegment_image (AffineEquiv.constVSub R p : P ->ᵃ[R] V) x y

@[simp]

中文:
定理 affineSegment_const_vsub_image
  条件: (x y p : P)
  证明: affineSegment_image (AffineEquiv.constVSub R p : P ->ᵃ[R] V) x y

@[simp]

Depends on / 依赖: AffineEquiv, AffineEquiv.constVSub, affineSegment_image, constVSub
-/
theorem affineSegment_const_vsub_image (x y p : P) :
    (p -ᵥ ·) '' affineSegment R x y = affineSegment R (p -ᵥ x) (p -ᵥ y) :=
  affineSegment_image (AffineEquiv.constVSub R p : P ->ᵃ[R] V) x y

@[simp]
/--
theorem `affineSegment_vsub_const_image` / 定理 `affineSegment_vsub_const_image`

English:
theorem affineSegment_vsub_const_image
  given: (x y p : P)
  proof: affineSegment_image ((AffineEquiv.vaddConst R p).symm : P ->ᵃ[R] V) x y

中文:
定理 affineSegment_vsub_const_image
  条件: (x y p : P)
  证明: affineSegment_image ((AffineEquiv.vaddConst R p).symm : P ->ᵃ[R] V) x y

Depends on / 依赖: AffineEquiv, AffineEquiv.vaddConst, affineSegment_image, vaddConst
-/
theorem affineSegment_vsub_const_image (x y p : P) :
    (· -ᵥ p) '' affineSegment R x y = affineSegment R (x -ᵥ p) (y -ᵥ p) :=
  affineSegment_image ((AffineEquiv.vaddConst R p).symm : P ->ᵃ[R] V) x y

variable {R}

@[simp]
/--
theorem `mem_const_vadd_affineSegment` / 定理 `mem_const_vadd_affineSegment`

English:
theorem mem_const_vadd_affineSegment
  given: {x y z : P} (v : V)
  proof: by
  rw [← affineSegment_const_vadd_image]; rw [(AddAction.injective v).mem_set_image]

@[simp]

中文:
定理 mem_const_vadd_affineSegment
  条件: {x y z : P} (v : V)
  证明: by
  rw [← affineSegment_const_vadd_image]; rw [(AddAction.injective v).mem_set_image]

@[simp]

Depends on / 依赖: AddAction, AddAction.injective, affineSegment_const_vadd_image, injective, mem_set_image
-/
theorem mem_const_vadd_affineSegment {x y z : P} (v : V) :
    v +ᵥ z in affineSegment R (v +ᵥ x) (v +ᵥ y) ↔ z in affineSegment R x y := by
  rw [← affineSegment_const_vadd_image]; rw [(AddAction.injective v).mem_set_image]

@[simp]
/--
theorem `mem_vadd_const_affineSegment` / 定理 `mem_vadd_const_affineSegment`

English:
theorem mem_vadd_const_affineSegment
  given: {x y z : V} (p : P)
  proof: by
  rw [← affineSegment_vadd_const_image]; rw [(vadd_right_injective p).mem_set_image]

@[simp]

中文:
定理 mem_vadd_const_affineSegment
  条件: {x y z : V} (p : P)
  证明: by
  rw [← affineSegment_vadd_const_image]; rw [(vadd_right_injective p).mem_set_image]

@[simp]

Depends on / 依赖: affineSegment_vadd_const_image, mem_set_image, vadd_right_injective
-/
theorem mem_vadd_const_affineSegment {x y z : V} (p : P) :
    z +ᵥ p in affineSegment R (x +ᵥ p) (y +ᵥ p) ↔ z in affineSegment R x y := by
  rw [← affineSegment_vadd_const_image]; rw [(vadd_right_injective p).mem_set_image]

@[simp]
/--
theorem `mem_const_vsub_affineSegment` / 定理 `mem_const_vsub_affineSegment`

English:
theorem mem_const_vsub_affineSegment
  given: {x y z : P} (p : P)
  proof: by
  rw [← affineSegment_const_vsub_image]; rw [(vsub_right_injective p).mem_set_image]

@[simp]

中文:
定理 mem_const_vsub_affineSegment
  条件: {x y z : P} (p : P)
  证明: by
  rw [← affineSegment_const_vsub_image]; rw [(vsub_right_injective p).mem_set_image]

@[simp]

Depends on / 依赖: affineSegment_const_vsub_image, mem_set_image, vsub_right_injective
-/
theorem mem_const_vsub_affineSegment {x y z : P} (p : P) :
    p -ᵥ z in affineSegment R (p -ᵥ x) (p -ᵥ y) ↔ z in affineSegment R x y := by
  rw [← affineSegment_const_vsub_image]; rw [(vsub_right_injective p).mem_set_image]

@[simp]
/--
theorem `mem_vsub_const_affineSegment` / 定理 `mem_vsub_const_affineSegment`

English:
theorem mem_vsub_const_affineSegment
  given: {x y z : P} (p : P)
  proof: by
  rw [← affineSegment_vsub_const_image]; rw [(vsub_left_injective p).mem_set_image]

中文:
定理 mem_vsub_const_affineSegment
  条件: {x y z : P} (p : P)
  证明: by
  rw [← affineSegment_vsub_const_image]; rw [(vsub_left_injective p).mem_set_image]

Depends on / 依赖: affineSegment_vsub_const_image, mem_set_image, vsub_left_injective
-/
theorem mem_vsub_const_affineSegment {x y z : P} (p : P) :
    z -ᵥ p in affineSegment R (x -ᵥ p) (y -ᵥ p) ↔ z in affineSegment R x y := by
  rw [← affineSegment_vsub_const_image]; rw [(vsub_left_injective p).mem_set_image]

variable (R)

section OrderedRing
variable [IsOrderedRing R]

/--
theorem `affineSegment_eq_segment` / 定理 `affineSegment_eq_segment`

English:
theorem affineSegment_eq_segment
  given: (x y : V)
  statement: affineSegment R x y = segment R x y
  proof: by
  rw [segment_eq_image_lineMap]; rw [affineSegment]

中文:
定理 affineSegment_eq_segment
  条件: (x y : V)
  结论: affineSegment R x y = segment R x y
  证明: by
  rw [segment_eq_image_lineMap]; rw [affineSegment]

Depends on / 依赖: affineSegment, segment_eq_image_lineMap
-/
theorem affineSegment_eq_segment (x y : V) : affineSegment R x y = segment R x y := by
  rw [segment_eq_image_lineMap]; rw [affineSegment]

/--
theorem `affineSegment_comm` / 定理 `affineSegment_comm`

English:
theorem affineSegment_comm
  given: (x y : P)
  statement: affineSegment R x y = affineSegment R y x
  proof: by
  refine Set.ext fun z => ?_
  constructor <;>
    · rintro ⟨t, ht, hxy⟩
      refine ⟨1 - t, ?_, ?_⟩
      · rwa [Set.sub_mem_Icc_iff_right, sub_self, sub_zero]
      · rwa [lineMap_apply_one_sub]

中文:
定理 affineSegment_comm
  条件: (x y : P)
  结论: affineSegment R x y = affineSegment R y x
  证明: by
  refine Set.ext fun z => ?_
  constructor <;>
    · rintro ⟨t, ht, hxy⟩
      refine ⟨1 - t, ?_, ?_⟩
      · rwa [Set.sub_mem_Icc_iff_right, sub_self, sub_zero]
      · rwa [lineMap_apply_one_sub]

Depends on / 依赖: Set.ext, Set.sub_mem_Icc_iff_right, lineMap_apply_one_sub, sub_mem_Icc_iff_right, sub_self, sub_zero
-/
theorem affineSegment_comm (x y : P) : affineSegment R x y = affineSegment R y x := by
  refine Set.ext fun z => ?_
  constructor <;>
    · rintro ⟨t, ht, hxy⟩
      refine ⟨1 - t, ?_, ?_⟩
      · rwa [Set.sub_mem_Icc_iff_right, sub_self, sub_zero]
      · rwa [lineMap_apply_one_sub]

/--
theorem `left_mem_affineSegment` / 定理 `left_mem_affineSegment`

English:
theorem left_mem_affineSegment
  given: (x y : P)
  statement: x in affineSegment R x y
  proof: ⟨0, Set.left_mem_Icc.2 zero_le_one, lineMap_apply_zero _ _⟩

中文:
定理 left_mem_affineSegment
  条件: (x y : P)
  结论: x in affineSegment R x y
  证明: ⟨0, Set.left_mem_Icc.2 zero_le_one, lineMap_apply_zero _ _⟩

Depends on / 依赖: Set.left_mem_Icc, left_mem_Icc, lineMap_apply_zero, zero_le_one
-/
theorem left_mem_affineSegment (x y : P) : x in affineSegment R x y :=
  ⟨0, Set.left_mem_Icc.2 zero_le_one, lineMap_apply_zero _ _⟩

/--
theorem `right_mem_affineSegment` / 定理 `right_mem_affineSegment`

English:
theorem right_mem_affineSegment
  given: (x y : P)
  statement: y in affineSegment R x y
  proof: ⟨1, Set.right_mem_Icc.2 zero_le_one, lineMap_apply_one _ _⟩

@[simp]

中文:
定理 right_mem_affineSegment
  条件: (x y : P)
  结论: y in affineSegment R x y
  证明: ⟨1, Set.right_mem_Icc.2 zero_le_one, lineMap_apply_one _ _⟩

@[simp]

Depends on / 依赖: Set.right_mem_Icc, lineMap_apply_one, right_mem_Icc, zero_le_one
-/
theorem right_mem_affineSegment (x y : P) : y in affineSegment R x y :=
  ⟨1, Set.right_mem_Icc.2 zero_le_one, lineMap_apply_one _ _⟩

@[simp]
/--
theorem `affineSegment_same` / 定理 `affineSegment_same`

English:
theorem affineSegment_same
  given: (x : P)
  statement: affineSegment R x x = {x}
  proof: by
  simp_rw [affineSegment, lineMap_same, AffineMap.coe_const, Function.const,
    (Set.nonempty_Icc.mpr zero_le_one).image_const]

中文:
定理 affineSegment_same
  条件: (x : P)
  结论: affineSegment R x x = {x}
  证明: by
  simp_rw [affineSegment, lineMap_same, AffineMap.coe_const, Function.const,
    (Set.nonempty_Icc.mpr zero_le_one).image_const]

Depends on / 依赖: AffineMap, AffineMap.coe_const, Function, Function.const, Set.nonempty_Icc.mpr, affineSegment, coe_const, image_const, lineMap_same, nonempty_Icc, simp_rw, zero_le_one
-/
theorem affineSegment_same (x : P) : affineSegment R x x = {x} := by
  simp_rw [affineSegment, lineMap_same, AffineMap.coe_const, Function.const,
    (Set.nonempty_Icc.mpr zero_le_one).image_const]

end OrderedRing

/--
Definition of `Wbtw` / `Wbtw` 的定义

English:
definition Wbtw
  signature: (x y z : P)
  body: y in affineSegment R x z

中文:
定义 Wbtw
  签名: (x y z : P)
  定义体: y in affineSegment R x z

Depends on / 依赖: affineSegment
-/
def Wbtw (x y z : P) : Prop :=
  y in affineSegment R x z

/--
Definition of `Sbtw` / `Sbtw` 的定义

English:
definition Sbtw
  signature: (x y z : P)
  body: Wbtw R x y z ∧ y != x ∧ y != z

中文:
定义 Sbtw
  签名: (x y z : P)
  定义体: Wbtw R x y z ∧ y != x ∧ y != z
-/
def Sbtw (x y z : P) : Prop :=
  Wbtw R x y z ∧ y != x ∧ y != z

variable {R}

section OrderedRing

variable [IsOrderedRing R]

/--
lemma `mem_segment_iff_wbtw` / 引理 `mem_segment_iff_wbtw`

English:
lemma mem_segment_iff_wbtw
  given: {x y z : V}
  statement: y in segment R x z ↔ Wbtw R x y z
  proof: by
  rw [Wbtw]; rw [affineSegment_eq_segment]

alias ⟨_, Wbtw.mem_segment⟩ := mem_segment_iff_wbtw

中文:
引理 mem_segment_iff_wbtw
  条件: {x y z : V}
  结论: y in segment R x z ↔ Wbtw R x y z
  证明: by
  rw [Wbtw]; rw [affineSegment_eq_segment]

alias ⟨_, Wbtw.mem_segment⟩ := mem_segment_iff_wbtw

Depends on / 依赖: affineSegment_eq_segment
-/
lemma mem_segment_iff_wbtw {x y z : V} : y in segment R x z ↔ Wbtw R x y z := by
  rw [Wbtw]; rw [affineSegment_eq_segment]

alias ⟨_, Wbtw.mem_segment⟩ := mem_segment_iff_wbtw

/--
lemma `Convex.mem_of_wbtw` / 引理 `Convex.mem_of_wbtw`

English:
lemma Convex.mem_of_wbtw
  statement: {p₀ p₁ p₂ : V} {s : Set V} (hs : Convex R s) (h₀₁₂ : Wbtw R p₀ p₁ p₂)
  proof: hs.segment_subset h₀ h₂ h₀₁₂.mem_segment

中文:
引理 Convex.mem_of_wbtw
  结论: {p₀ p₁ p₂ : V} {s : Set V} (hs : Convex R s) (h₀₁₂ : Wbtw R p₀ p₁ p₂)
  证明: hs.segment_subset h₀ h₂ h₀₁₂.mem_segment

Depends on / 依赖: hs.segment_subset, mem_segment, segment_subset
-/
lemma Convex.mem_of_wbtw {p₀ p₁ p₂ : V} {s : Set V} (hs : Convex R s) (h₀₁₂ : Wbtw R p₀ p₁ p₂)
    (h₀ : p₀ in s) (h₂ : p₂ in s) : p₁ in s := hs.segment_subset h₀ h₂ h₀₁₂.mem_segment

/--
theorem `wbtw_comm` / 定理 `wbtw_comm`

English:
theorem wbtw_comm
  given: {x y z : P}
  statement: Wbtw R x y z ↔ Wbtw R z y x
  proof: by
  rw [Wbtw]; rw [Wbtw]; rw [affineSegment_comm]

alias ⟨Wbtw.symm, _⟩ := wbtw_comm

中文:
定理 wbtw_comm
  条件: {x y z : P}
  结论: Wbtw R x y z ↔ Wbtw R z y x
  证明: by
  rw [Wbtw]; rw [Wbtw]; rw [affineSegment_comm]

alias ⟨Wbtw.symm, _⟩ := wbtw_comm

Depends on / 依赖: affineSegment_comm
-/
theorem wbtw_comm {x y z : P} : Wbtw R x y z ↔ Wbtw R z y x := by
  rw [Wbtw]; rw [Wbtw]; rw [affineSegment_comm]

alias ⟨Wbtw.symm, _⟩ := wbtw_comm

/--
theorem `sbtw_comm` / 定理 `sbtw_comm`

English:
theorem sbtw_comm
  given: {x y z : P}
  statement: Sbtw R x y z ↔ Sbtw R z y x
  proof: by
  rw [Sbtw]; rw [Sbtw]; rw [wbtw_comm]; rw [← and_assoc]; rw [← and_assoc]; rw [and_right_comm]

alias ⟨Sbtw.symm, _⟩ := sbtw_comm

中文:
定理 sbtw_comm
  条件: {x y z : P}
  结论: Sbtw R x y z ↔ Sbtw R z y x
  证明: by
  rw [Sbtw]; rw [Sbtw]; rw [wbtw_comm]; rw [← and_assoc]; rw [← and_assoc]; rw [and_right_comm]

alias ⟨Sbtw.symm, _⟩ := sbtw_comm

Depends on / 依赖: and_assoc, and_right_comm, wbtw_comm
-/
theorem sbtw_comm {x y z : P} : Sbtw R x y z ↔ Sbtw R z y x := by
  rw [Sbtw]; rw [Sbtw]; rw [wbtw_comm]; rw [← and_assoc]; rw [← and_assoc]; rw [and_right_comm]

alias ⟨Sbtw.symm, _⟩ := sbtw_comm

end OrderedRing

/--
lemma `AffineSubspace.mem_of_wbtw` / 引理 `AffineSubspace.mem_of_wbtw`

English:
lemma AffineSubspace.mem_of_wbtw
  statement: {s : AffineSubspace R P} {x y z : P} (hxyz : Wbtw R x y z)
  proof: by obtain ⟨ε, -, rfl⟩ := hxyz; exact lineMap_mem _ hx hz

中文:
引理 AffineSubspace.mem_of_wbtw
  结论: {s : AffineSubspace R P} {x y z : P} (hxyz : Wbtw R x y z)
  证明: by obtain ⟨ε, -, rfl⟩ := hxyz; exact lineMap_mem _ hx hz

Depends on / 依赖: lineMap_mem
-/
lemma AffineSubspace.mem_of_wbtw {s : AffineSubspace R P} {x y z : P} (hxyz : Wbtw R x y z)
    (hx : x in s) (hz : z in s) : y in s := by obtain ⟨ε, -, rfl⟩ := hxyz; exact lineMap_mem _ hx hz

/--
theorem `Wbtw.map` / 定理 `Wbtw.map`

English:
theorem Wbtw.map
  given: {x y z : P} (h : Wbtw R x y z) (f : P ->ᵃ[R] P')
  statement: Wbtw R (f x) (f y) (f z)
  proof: by
  rw [Wbtw]; rw [← affineSegment_image]
  exact Set.mem_image_of_mem _ h

中文:
定理 Wbtw.map
  条件: {x y z : P} (h : Wbtw R x y z) (f : P ->ᵃ[R] P')
  结论: Wbtw R (f x) (f y) (f z)
  证明: by
  rw [Wbtw]; rw [← affineSegment_image]
  exact Set.mem_image_of_mem _ h

Depends on / 依赖: Set.mem_image_of_mem, affineSegment_image, mem_image_of_mem
-/
theorem Wbtw.map {x y z : P} (h : Wbtw R x y z) (f : P ->ᵃ[R] P') : Wbtw R (f x) (f y) (f z) := by
  rw [Wbtw]; rw [← affineSegment_image]
  exact Set.mem_image_of_mem _ h

/--
theorem `Function.Injective.wbtw_map_iff` / 定理 `Function.Injective.wbtw_map_iff`

English:
theorem Function.Injective.wbtw_map_iff
  given: {x y z : P} {f : P ->ᵃ[R] P'} (hf : Function.Injective f)
  proof: by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  rwa [Wbtw, ← affineSegment_image, hf.mem_set_image] at h

中文:
定理 Function.Injective.wbtw_map_iff
  条件: {x y z : P} {f : P ->ᵃ[R] P'} (hf : Function.Injective f)
  证明: by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  rwa [Wbtw, ← affineSegment_image, hf.mem_set_image] at h

Depends on / 依赖: InnerProductSpace, InnerProductSpace.toUniformConvexSpace, UniformConvexSpace, affineSegment_image, h.map, hf.mem_set_image, mem_set_image, toUniformConvexSpace
-/
theorem Function.Injective.wbtw_map_iff {x y z : P} {f : P ->ᵃ[R] P'} (hf : Function.Injective f) :
    Wbtw R (f x) (f y) (f z) ↔ Wbtw R x y z := by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  rwa [Wbtw, ← affineSegment_image, hf.mem_set_image] at h

/--
theorem `Function.Injective.sbtw_map_iff` / 定理 `Function.Injective.sbtw_map_iff`

English:
theorem Function.Injective.sbtw_map_iff
  given: {x y z : P} {f : P ->ᵃ[R] P'} (hf : Function.Injective f)
  proof: by
  simp_rw [Sbtw, hf.wbtw_map_iff, hf.ne_iff]

中文:
定理 Function.Injective.sbtw_map_iff
  条件: {x y z : P} {f : P ->ᵃ[R] P'} (hf : Function.Injective f)
  证明: by
  simp_rw [Sbtw, hf.wbtw_map_iff, hf.ne_iff]

Depends on / 依赖: cd.inner, hf.ne_iff, hf.wbtw_map_iff, ne_iff, simp_rw, wbtw_map_iff
-/
theorem Function.Injective.sbtw_map_iff {x y z : P} {f : P ->ᵃ[R] P'} (hf : Function.Injective f) :
    Sbtw R (f x) (f y) (f z) ↔ Sbtw R x y z := by
  simp_rw [Sbtw, hf.wbtw_map_iff, hf.ne_iff]

/--
lemma `Set.InjOn.wbtw_map_iff` / 引理 `Set.InjOn.wbtw_map_iff`

English:
lemma Set.InjOn.wbtw_map_iff
  statement: {x y z : P} {f : P ->ᵃ[R] P'} {s : AffineSubspace R P}
  proof: by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  rwa [Wbtw, ← affineSegment_image, hf.mem_image_iff
    ((affineSegment_subset_affineSpan R x z).trans (affineSpan_le.2 (Set.pair_subset hx hz))) hy]
    at h

中文:
引理 Set.InjOn.wbtw_map_iff
  结论: {x y z : P} {f : P ->ᵃ[R] P'} {s : AffineSubspace R P}
  证明: by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  rwa [Wbtw, ← affineSegment_image, hf.mem_image_iff
    ((affineSegment_subset_affineSpan R x z).trans (affineSpan_le.2 (Set.pair_subset hx hz))) hy]
    at h

Depends on / 依赖: Set.pair_subset, affineSegment_image, affineSegment_subset_affineSpan, affineSpan_le, h.map, hf.mem_image_iff, mem_image_iff, pair_subset
-/
lemma Set.InjOn.wbtw_map_iff {x y z : P} {f : P ->ᵃ[R] P'} {s : AffineSubspace R P}
    (hf : Set.InjOn f s) (hx : x in s) (hy : y in s) (hz : z in s) :
    Wbtw R (f x) (f y) (f z) ↔ Wbtw R x y z := by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  rwa [Wbtw, ← affineSegment_image, hf.mem_image_iff
    ((affineSegment_subset_affineSpan R x z).trans (affineSpan_le.2 (Set.pair_subset hx hz))) hy]
    at h

/--
lemma `Set.InjOn.sbtw_map_iff` / 引理 `Set.InjOn.sbtw_map_iff`

English:
lemma Set.InjOn.sbtw_map_iff
  statement: {x y z : P} {f : P ->ᵃ[R] P'} {s : AffineSubspace R P}
  proof: by
  simp_rw [Sbtw, hf.wbtw_map_iff hx hy hz, hf.ne_iff hy hx, hf.ne_iff hy hz]

@[simp]

中文:
引理 Set.InjOn.sbtw_map_iff
  结论: {x y z : P} {f : P ->ᵃ[R] P'} {s : AffineSubspace R P}
  证明: by
  simp_rw [Sbtw, hf.wbtw_map_iff hx hy hz, hf.ne_iff hy hx, hf.ne_iff hy hz]

@[simp]

Depends on / 依赖: hf.ne_iff, hf.wbtw_map_iff, ne_iff, simp_rw, wbtw_map_iff
-/
lemma Set.InjOn.sbtw_map_iff {x y z : P} {f : P ->ᵃ[R] P'} {s : AffineSubspace R P}
    (hf : Set.InjOn f s) (hx : x in s) (hy : y in s) (hz : z in s) :
    Sbtw R (f x) (f y) (f z) ↔ Sbtw R x y z := by
  simp_rw [Sbtw, hf.wbtw_map_iff hx hy hz, hf.ne_iff hy hx, hf.ne_iff hy hz]

@[simp]
/--
theorem `AffineEquiv.wbtw_map_iff` / 定理 `AffineEquiv.wbtw_map_iff`

English:
theorem AffineEquiv.wbtw_map_iff
  given: {x y z : P} (f : P ≃ᵃ[R] P')
  proof: by
  have : Function.Injective f.toAffineMap := f.injective
  -- `refine` or `exact` are very slow, `apply` is fast. Please check before golfing.
  apply this.wbtw_map_iff

@[simp]

中文:
定理 AffineEquiv.wbtw_map_iff
  条件: {x y z : P} (f : P ≃ᵃ[R] P')
  证明: by
  have : Function.Injective f.toAffineMap := f.injective
  -- `refine` or `exact` are very slow, `apply` is fast. Please check before golfing.
  apply this.wbtw_map_iff

@[simp]

Depends on / 依赖: Function, Function.Injective, Injective, f.injective, f.toAffineMap, injective, toAffineMap
-/
theorem AffineEquiv.wbtw_map_iff {x y z : P} (f : P ≃ᵃ[R] P') :
    Wbtw R (f x) (f y) (f z) ↔ Wbtw R x y z := by
  have : Function.Injective f.toAffineMap := f.injective
  -- `refine` or `exact` are very slow, `apply` is fast. Please check before golfing.
  apply this.wbtw_map_iff

@[simp]
/--
theorem `AffineEquiv.sbtw_map_iff` / 定理 `AffineEquiv.sbtw_map_iff`

English:
theorem AffineEquiv.sbtw_map_iff
  given: {x y z : P} (f : P ≃ᵃ[R] P')
  proof: by
  have : Function.Injective f.toAffineMap := f.injective
  -- `refine` or `exact` are very slow, `apply` is fast. Please check before golfing.
  apply this.sbtw_map_iff

@[simp]

中文:
定理 AffineEquiv.sbtw_map_iff
  条件: {x y z : P} (f : P ≃ᵃ[R] P')
  证明: by
  have : Function.Injective f.toAffineMap := f.injective
  -- `refine` or `exact` are very slow, `apply` is fast. Please check before golfing.
  apply this.sbtw_map_iff

@[simp]

Depends on / 依赖: Function, Function.Injective, Injective, f.injective, f.toAffineMap, injective, toAffineMap
-/
theorem AffineEquiv.sbtw_map_iff {x y z : P} (f : P ≃ᵃ[R] P') :
    Sbtw R (f x) (f y) (f z) ↔ Sbtw R x y z := by
  have : Function.Injective f.toAffineMap := f.injective
  -- `refine` or `exact` are very slow, `apply` is fast. Please check before golfing.
  apply this.sbtw_map_iff

@[simp]
/--
theorem `wbtw_const_vadd_iff` / 定理 `wbtw_const_vadd_iff`

English:
theorem wbtw_const_vadd_iff
  given: {x y z : P} (v : V)
  proof: mem_const_vadd_affineSegment _

alias ⟨_, Wbtw.const_vadd⟩ := wbtw_const_vadd_iff

@[simp]

中文:
定理 wbtw_const_vadd_iff
  条件: {x y z : P} (v : V)
  证明: mem_const_vadd_affineSegment _

alias ⟨_, Wbtw.const_vadd⟩ := wbtw_const_vadd_iff

@[simp]

Depends on / 依赖: mem_const_vadd_affineSegment
-/
theorem wbtw_const_vadd_iff {x y z : P} (v : V) :
    Wbtw R (v +ᵥ x) (v +ᵥ y) (v +ᵥ z) ↔ Wbtw R x y z :=
  mem_const_vadd_affineSegment _

alias ⟨_, Wbtw.const_vadd⟩ := wbtw_const_vadd_iff

@[simp]
/--
theorem `wbtw_const_add_iff` / 定理 `wbtw_const_add_iff`

English:
theorem wbtw_const_add_iff
  given: {x y z : V} (v : V)
  proof: wbtw_const_vadd_iff v

alias ⟨_, Wbtw.const_add⟩ := wbtw_const_add_iff

@[simp]

中文:
定理 wbtw_const_add_iff
  条件: {x y z : V} (v : V)
  证明: wbtw_const_vadd_iff v

alias ⟨_, Wbtw.const_add⟩ := wbtw_const_add_iff

@[simp]

Depends on / 依赖: wbtw_const_vadd_iff
-/
theorem wbtw_const_add_iff {x y z : V} (v : V) :
    Wbtw R (v + x) (v + y) (v + z) ↔ Wbtw R x y z :=
  wbtw_const_vadd_iff v

alias ⟨_, Wbtw.const_add⟩ := wbtw_const_add_iff

@[simp]
/--
theorem `wbtw_vadd_const_iff` / 定理 `wbtw_vadd_const_iff`

English:
theorem wbtw_vadd_const_iff
  given: {x y z : V} (p : P)
  proof: mem_vadd_const_affineSegment _

alias ⟨_, Wbtw.vadd_const⟩ := wbtw_vadd_const_iff

@[simp]

中文:
定理 wbtw_vadd_const_iff
  条件: {x y z : V} (p : P)
  证明: mem_vadd_const_affineSegment _

alias ⟨_, Wbtw.vadd_const⟩ := wbtw_vadd_const_iff

@[simp]

Depends on / 依赖: mem_vadd_const_affineSegment
-/
theorem wbtw_vadd_const_iff {x y z : V} (p : P) :
    Wbtw R (x +ᵥ p) (y +ᵥ p) (z +ᵥ p) ↔ Wbtw R x y z :=
  mem_vadd_const_affineSegment _

alias ⟨_, Wbtw.vadd_const⟩ := wbtw_vadd_const_iff

@[simp]
/--
theorem `wbtw_add_const_iff` / 定理 `wbtw_add_const_iff`

English:
theorem wbtw_add_const_iff
  given: {x y z : V} (v : V)
  proof: wbtw_vadd_const_iff v

alias ⟨_, Wbtw.add_const⟩ := wbtw_add_const_iff

@[simp]

中文:
定理 wbtw_add_const_iff
  条件: {x y z : V} (v : V)
  证明: wbtw_vadd_const_iff v

alias ⟨_, Wbtw.add_const⟩ := wbtw_add_const_iff

@[simp]

Depends on / 依赖: wbtw_vadd_const_iff
-/
theorem wbtw_add_const_iff {x y z : V} (v : V) :
    Wbtw R (x + v) (y + v) (z + v) ↔ Wbtw R x y z :=
  wbtw_vadd_const_iff v

alias ⟨_, Wbtw.add_const⟩ := wbtw_add_const_iff

@[simp]
/--
theorem `wbtw_const_vsub_iff` / 定理 `wbtw_const_vsub_iff`

English:
theorem wbtw_const_vsub_iff
  given: {x y z : P} (p : P)
  proof: mem_const_vsub_affineSegment _

alias ⟨_, Wbtw.const_vsub⟩ := wbtw_const_vsub_iff

@[simp]

中文:
定理 wbtw_const_vsub_iff
  条件: {x y z : P} (p : P)
  证明: mem_const_vsub_affineSegment _

alias ⟨_, Wbtw.const_vsub⟩ := wbtw_const_vsub_iff

@[simp]

Depends on / 依赖: mem_const_vsub_affineSegment
-/
theorem wbtw_const_vsub_iff {x y z : P} (p : P) :
    Wbtw R (p -ᵥ x) (p -ᵥ y) (p -ᵥ z) ↔ Wbtw R x y z :=
  mem_const_vsub_affineSegment _

alias ⟨_, Wbtw.const_vsub⟩ := wbtw_const_vsub_iff

@[simp]
/--
theorem `wbtw_const_sub_iff` / 定理 `wbtw_const_sub_iff`

English:
theorem wbtw_const_sub_iff
  given: {x y z : V} (v : V)
  proof: wbtw_const_vsub_iff v

alias ⟨_, Wbtw.const_sub⟩ := wbtw_const_sub_iff

@[simp]

中文:
定理 wbtw_const_sub_iff
  条件: {x y z : V} (v : V)
  证明: wbtw_const_vsub_iff v

alias ⟨_, Wbtw.const_sub⟩ := wbtw_const_sub_iff

@[simp]

Depends on / 依赖: wbtw_const_vsub_iff
-/
theorem wbtw_const_sub_iff {x y z : V} (v : V) :
    Wbtw R (v - x) (v - y) (v - z) ↔ Wbtw R x y z :=
  wbtw_const_vsub_iff v

alias ⟨_, Wbtw.const_sub⟩ := wbtw_const_sub_iff

@[simp]
/--
theorem `wbtw_neg_iff` / 定理 `wbtw_neg_iff`

English:
theorem wbtw_neg_iff
  given: {x y z : V}
  proof: by
  simp only [← zero_sub, wbtw_const_sub_iff]

alias ⟨_, Wbtw.neg⟩ := wbtw_neg_iff

@[simp]

中文:
定理 wbtw_neg_iff
  条件: {x y z : V}
  证明: by
  simp only [← zero_sub, wbtw_const_sub_iff]

alias ⟨_, Wbtw.neg⟩ := wbtw_neg_iff

@[simp]

Depends on / 依赖: wbtw_const_sub_iff, zero_sub
-/
theorem wbtw_neg_iff {x y z : V} :
    Wbtw R (-x) (-y) (-z) ↔ Wbtw R x y z := by
  simp only [← zero_sub, wbtw_const_sub_iff]

alias ⟨_, Wbtw.neg⟩ := wbtw_neg_iff

@[simp]
/--
theorem `wbtw_vsub_const_iff` / 定理 `wbtw_vsub_const_iff`

English:
theorem wbtw_vsub_const_iff
  given: {x y z : P} (p : P)
  proof: mem_vsub_const_affineSegment _

alias ⟨_, Wbtw.vsub_const⟩ := wbtw_vsub_const_iff

@[simp]

中文:
定理 wbtw_vsub_const_iff
  条件: {x y z : P} (p : P)
  证明: mem_vsub_const_affineSegment _

alias ⟨_, Wbtw.vsub_const⟩ := wbtw_vsub_const_iff

@[simp]

Depends on / 依赖: mem_vsub_const_affineSegment
-/
theorem wbtw_vsub_const_iff {x y z : P} (p : P) :
    Wbtw R (x -ᵥ p) (y -ᵥ p) (z -ᵥ p) ↔ Wbtw R x y z :=
  mem_vsub_const_affineSegment _

alias ⟨_, Wbtw.vsub_const⟩ := wbtw_vsub_const_iff

@[simp]
/--
theorem `wbtw_sub_const_iff` / 定理 `wbtw_sub_const_iff`

English:
theorem wbtw_sub_const_iff
  given: {x y z : V} (v : V)
  proof: wbtw_vsub_const_iff v

alias ⟨_, Wbtw.sub_const⟩ := wbtw_sub_const_iff

@[simp]

中文:
定理 wbtw_sub_const_iff
  条件: {x y z : V} (v : V)
  证明: wbtw_vsub_const_iff v

alias ⟨_, Wbtw.sub_const⟩ := wbtw_sub_const_iff

@[simp]

Depends on / 依赖: wbtw_vsub_const_iff
-/
theorem wbtw_sub_const_iff {x y z : V} (v : V) :
    Wbtw R (x - v) (y - v) (z - v) ↔ Wbtw R x y z :=
  wbtw_vsub_const_iff v

alias ⟨_, Wbtw.sub_const⟩ := wbtw_sub_const_iff

@[simp]
/--
theorem `sbtw_const_vadd_iff` / 定理 `sbtw_const_vadd_iff`

English:
theorem sbtw_const_vadd_iff
  given: {x y z : P} (v : V)
  proof: by
  rw [Sbtw]; rw [Sbtw]; rw [wbtw_const_vadd_iff]; rw [(AddAction.injective v).ne_iff]; rw [(AddAction.injective v).ne_iff]

alias ⟨_, Sbtw.const_vadd⟩ := sbtw_const_vadd_iff

@[simp]

中文:
定理 sbtw_const_vadd_iff
  条件: {x y z : P} (v : V)
  证明: by
  rw [Sbtw]; rw [Sbtw]; rw [wbtw_const_vadd_iff]; rw [(AddAction.injective v).ne_iff]; rw [(AddAction.injective v).ne_iff]

alias ⟨_, Sbtw.const_vadd⟩ := sbtw_const_vadd_iff

@[simp]

Depends on / 依赖: AddAction, AddAction.injective, injective, ne_iff, wbtw_const_vadd_iff
-/
theorem sbtw_const_vadd_iff {x y z : P} (v : V) :
    Sbtw R (v +ᵥ x) (v +ᵥ y) (v +ᵥ z) ↔ Sbtw R x y z := by
  rw [Sbtw]; rw [Sbtw]; rw [wbtw_const_vadd_iff]; rw [(AddAction.injective v).ne_iff]; rw [(AddAction.injective v).ne_iff]

alias ⟨_, Sbtw.const_vadd⟩ := sbtw_const_vadd_iff

@[simp]
/--
theorem `sbtw_const_add_iff` / 定理 `sbtw_const_add_iff`

English:
theorem sbtw_const_add_iff
  given: {x y z : V} (v : V)
  proof: sbtw_const_vadd_iff v

alias ⟨_, Sbtw.const_add⟩ := sbtw_const_add_iff

@[simp]

中文:
定理 sbtw_const_add_iff
  条件: {x y z : V} (v : V)
  证明: sbtw_const_vadd_iff v

alias ⟨_, Sbtw.const_add⟩ := sbtw_const_add_iff

@[simp]

Depends on / 依赖: sbtw_const_vadd_iff
-/
theorem sbtw_const_add_iff {x y z : V} (v : V) :
    Sbtw R (v + x) (v + y) (v + z) ↔ Sbtw R x y z :=
  sbtw_const_vadd_iff v

alias ⟨_, Sbtw.const_add⟩ := sbtw_const_add_iff

@[simp]
/--
theorem `sbtw_vadd_const_iff` / 定理 `sbtw_vadd_const_iff`

English:
theorem sbtw_vadd_const_iff
  given: {x y z : V} (p : P)
  proof: by
  rw [Sbtw]; rw [Sbtw]; rw [wbtw_vadd_const_iff]; rw [(vadd_right_injective p).ne_iff]; rw [(vadd_right_injective p).ne_iff]

alias ⟨_, Sbtw.vadd_const⟩ := sbtw_vadd_const_iff

@[simp]

中文:
定理 sbtw_vadd_const_iff
  条件: {x y z : V} (p : P)
  证明: by
  rw [Sbtw]; rw [Sbtw]; rw [wbtw_vadd_const_iff]; rw [(vadd_right_injective p).ne_iff]; rw [(vadd_right_injective p).ne_iff]

alias ⟨_, Sbtw.vadd_const⟩ := sbtw_vadd_const_iff

@[simp]

Depends on / 依赖: ne_iff, vadd_right_injective, wbtw_vadd_const_iff
-/
theorem sbtw_vadd_const_iff {x y z : V} (p : P) :
    Sbtw R (x +ᵥ p) (y +ᵥ p) (z +ᵥ p) ↔ Sbtw R x y z := by
  rw [Sbtw]; rw [Sbtw]; rw [wbtw_vadd_const_iff]; rw [(vadd_right_injective p).ne_iff]; rw [(vadd_right_injective p).ne_iff]

alias ⟨_, Sbtw.vadd_const⟩ := sbtw_vadd_const_iff

@[simp]
/--
theorem `sbtw_add_const_iff` / 定理 `sbtw_add_const_iff`

English:
theorem sbtw_add_const_iff
  given: {x y z : V} (v : V)
  proof: sbtw_vadd_const_iff v

alias ⟨_, Sbtw.add_const⟩ := sbtw_add_const_iff

@[simp]

中文:
定理 sbtw_add_const_iff
  条件: {x y z : V} (v : V)
  证明: sbtw_vadd_const_iff v

alias ⟨_, Sbtw.add_const⟩ := sbtw_add_const_iff

@[simp]

Depends on / 依赖: sbtw_vadd_const_iff
-/
theorem sbtw_add_const_iff {x y z : V} (v : V) :
    Sbtw R (x + v) (y + v) (z + v) ↔ Sbtw R x y z :=
  sbtw_vadd_const_iff v

alias ⟨_, Sbtw.add_const⟩ := sbtw_add_const_iff

@[simp]
/--
theorem `sbtw_const_vsub_iff` / 定理 `sbtw_const_vsub_iff`

English:
theorem sbtw_const_vsub_iff
  given: {x y z : P} (p : P)
  proof: by
  rw [Sbtw]; rw [Sbtw]; rw [wbtw_const_vsub_iff]; rw [(vsub_right_injective p).ne_iff]; rw [(vsub_right_injective p).ne_iff]

alias ⟨_, Sbtw.const_vsub⟩ := sbtw_const_vsub_iff

@[simp]

中文:
定理 sbtw_const_vsub_iff
  条件: {x y z : P} (p : P)
  证明: by
  rw [Sbtw]; rw [Sbtw]; rw [wbtw_const_vsub_iff]; rw [(vsub_right_injective p).ne_iff]; rw [(vsub_right_injective p).ne_iff]

alias ⟨_, Sbtw.const_vsub⟩ := sbtw_const_vsub_iff

@[simp]

Depends on / 依赖: ne_iff, vsub_right_injective, wbtw_const_vsub_iff
-/
theorem sbtw_const_vsub_iff {x y z : P} (p : P) :
    Sbtw R (p -ᵥ x) (p -ᵥ y) (p -ᵥ z) ↔ Sbtw R x y z := by
  rw [Sbtw]; rw [Sbtw]; rw [wbtw_const_vsub_iff]; rw [(vsub_right_injective p).ne_iff]; rw [(vsub_right_injective p).ne_iff]

alias ⟨_, Sbtw.const_vsub⟩ := sbtw_const_vsub_iff

@[simp]
/--
theorem `sbtw_const_sub_iff` / 定理 `sbtw_const_sub_iff`

English:
theorem sbtw_const_sub_iff
  given: {x y z : V} (v : V)
  proof: sbtw_const_vsub_iff v

alias ⟨_, Sbtw.const_sub⟩ := sbtw_const_sub_iff

@[simp]

中文:
定理 sbtw_const_sub_iff
  条件: {x y z : V} (v : V)
  证明: sbtw_const_vsub_iff v

alias ⟨_, Sbtw.const_sub⟩ := sbtw_const_sub_iff

@[simp]

Depends on / 依赖: sbtw_const_vsub_iff
-/
theorem sbtw_const_sub_iff {x y z : V} (v : V) :
    Sbtw R (v - x) (v - y) (v - z) ↔ Sbtw R x y z :=
  sbtw_const_vsub_iff v

alias ⟨_, Sbtw.const_sub⟩ := sbtw_const_sub_iff

@[simp]
/--
theorem `sbtw_neg_iff` / 定理 `sbtw_neg_iff`

English:
theorem sbtw_neg_iff
  given: {x y z : V}
  proof: by
  simp only [← zero_sub, sbtw_const_sub_iff]

alias ⟨_, Sbtw.neg⟩ := sbtw_neg_iff

@[simp]

中文:
定理 sbtw_neg_iff
  条件: {x y z : V}
  证明: by
  simp only [← zero_sub, sbtw_const_sub_iff]

alias ⟨_, Sbtw.neg⟩ := sbtw_neg_iff

@[simp]

Depends on / 依赖: sbtw_const_sub_iff, zero_sub
-/
theorem sbtw_neg_iff {x y z : V} :
    Sbtw R (-x) (-y) (-z) ↔ Sbtw R x y z := by
  simp only [← zero_sub, sbtw_const_sub_iff]

alias ⟨_, Sbtw.neg⟩ := sbtw_neg_iff

@[simp]
/--
theorem `sbtw_vsub_const_iff` / 定理 `sbtw_vsub_const_iff`

English:
theorem sbtw_vsub_const_iff
  given: {x y z : P} (p : P)
  proof: by
  rw [Sbtw]; rw [Sbtw]; rw [wbtw_vsub_const_iff]; rw [(vsub_left_injective p).ne_iff]; rw [(vsub_left_injective p).ne_iff]

alias ⟨_, Sbtw.vsub_const⟩ := sbtw_vsub_const_iff

@[simp]

中文:
定理 sbtw_vsub_const_iff
  条件: {x y z : P} (p : P)
  证明: by
  rw [Sbtw]; rw [Sbtw]; rw [wbtw_vsub_const_iff]; rw [(vsub_left_injective p).ne_iff]; rw [(vsub_left_injective p).ne_iff]

alias ⟨_, Sbtw.vsub_const⟩ := sbtw_vsub_const_iff

@[simp]

Depends on / 依赖: ne_iff, vsub_left_injective, wbtw_vsub_const_iff
-/
theorem sbtw_vsub_const_iff {x y z : P} (p : P) :
    Sbtw R (x -ᵥ p) (y -ᵥ p) (z -ᵥ p) ↔ Sbtw R x y z := by
  rw [Sbtw]; rw [Sbtw]; rw [wbtw_vsub_const_iff]; rw [(vsub_left_injective p).ne_iff]; rw [(vsub_left_injective p).ne_iff]

alias ⟨_, Sbtw.vsub_const⟩ := sbtw_vsub_const_iff

@[simp]
/--
theorem `sbtw_sub_const_iff` / 定理 `sbtw_sub_const_iff`

English:
theorem sbtw_sub_const_iff
  given: {x y z : V} (v : V)
  proof: sbtw_vsub_const_iff v

alias ⟨_, Sbtw.sub_const⟩ := sbtw_sub_const_iff

中文:
定理 sbtw_sub_const_iff
  条件: {x y z : V} (v : V)
  证明: sbtw_vsub_const_iff v

alias ⟨_, Sbtw.sub_const⟩ := sbtw_sub_const_iff

Depends on / 依赖: sbtw_vsub_const_iff
-/
theorem sbtw_sub_const_iff {x y z : V} (v : V) :
    Sbtw R (x - v) (y - v) (z - v) ↔ Sbtw R x y z :=
  sbtw_vsub_const_iff v

alias ⟨_, Sbtw.sub_const⟩ := sbtw_sub_const_iff

/--
theorem `Sbtw.wbtw` / 定理 `Sbtw.wbtw`

English:
theorem Sbtw.wbtw
  given: {x y z : P} (h : Sbtw R x y z)
  statement: Wbtw R x y z
  proof: h.1

中文:
定理 Sbtw.wbtw
  条件: {x y z : P} (h : Sbtw R x y z)
  结论: Wbtw R x y z
  证明: h.1
-/
theorem Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z :=
  h.1

/--
theorem `Sbtw.ne_left` / 定理 `Sbtw.ne_left`

English:
theorem Sbtw.ne_left
  given: {x y z : P} (h : Sbtw R x y z)
  statement: y != x
  proof: h.2.1

中文:
定理 Sbtw.ne_left
  条件: {x y z : P} (h : Sbtw R x y z)
  结论: y != x
  证明: h.2.1
-/
theorem Sbtw.ne_left {x y z : P} (h : Sbtw R x y z) : y != x :=
  h.2.1

/--
theorem `Sbtw.left_ne` / 定理 `Sbtw.left_ne`

English:
theorem Sbtw.left_ne
  given: {x y z : P} (h : Sbtw R x y z)
  statement: x != y
  proof: h.2.1.symm

中文:
定理 Sbtw.left_ne
  条件: {x y z : P} (h : Sbtw R x y z)
  结论: x != y
  证明: h.2.1.symm
-/
theorem Sbtw.left_ne {x y z : P} (h : Sbtw R x y z) : x != y :=
  h.2.1.symm

/--
theorem `Sbtw.ne_right` / 定理 `Sbtw.ne_right`

English:
theorem Sbtw.ne_right
  given: {x y z : P} (h : Sbtw R x y z)
  statement: y != z
  proof: h.2.2

中文:
定理 Sbtw.ne_right
  条件: {x y z : P} (h : Sbtw R x y z)
  结论: y != z
  证明: h.2.2
-/
theorem Sbtw.ne_right {x y z : P} (h : Sbtw R x y z) : y != z :=
  h.2.2

/--
theorem `Sbtw.right_ne` / 定理 `Sbtw.right_ne`

English:
theorem Sbtw.right_ne
  given: {x y z : P} (h : Sbtw R x y z)
  statement: z != y
  proof: h.2.2.symm

中文:
定理 Sbtw.right_ne
  条件: {x y z : P} (h : Sbtw R x y z)
  结论: z != y
  证明: h.2.2.symm
-/
theorem Sbtw.right_ne {x y z : P} (h : Sbtw R x y z) : z != y :=
  h.2.2.symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Sbtw.mem_image_Ioo` / 定理 `Sbtw.mem_image_Ioo`

English:
theorem Sbtw.mem_image_Ioo
  given: {x y z : P} (h : Sbtw R x y z)
  proof: by
  rcases h with ⟨⟨t, ht, rfl⟩, hyx, hyz⟩
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc ht with (rfl | rfl | ho)
  · exfalso
    exact hyx (lineMap_apply_zero _ _)
  · exfalso
    exact hyz (lineMap_apply_one _ _)
  · exact ⟨t, ho, rfl⟩

中文:
定理 Sbtw.mem_image_Ioo
  条件: {x y z : P} (h : Sbtw R x y z)
  证明: by
  rcases h with ⟨⟨t, ht, rfl⟩, hyx, hyz⟩
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc ht with (rfl | rfl | ho)
  · exfalso
    exact hyx (lineMap_apply_zero _ _)
  · exfalso
    exact hyz (lineMap_apply_one _ _)
  · exact ⟨t, ho, rfl⟩

Depends on / 依赖: Set.eq_endpoints_or_mem_Ioo_of_mem_Icc, eq_endpoints_or_mem_Ioo_of_mem_Icc, lineMap_apply_one, lineMap_apply_zero
-/
theorem Sbtw.mem_image_Ioo {x y z : P} (h : Sbtw R x y z) :
    y in lineMap x z '' Set.Ioo (0 : R) 1 := by
  rcases h with ⟨⟨t, ht, rfl⟩, hyx, hyz⟩
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc ht with (rfl | rfl | ho)
  · exfalso
    exact hyx (lineMap_apply_zero _ _)
  · exfalso
    exact hyz (lineMap_apply_one _ _)
  · exact ⟨t, ho, rfl⟩

/--
theorem `Wbtw.mem_affineSpan` / 定理 `Wbtw.mem_affineSpan`

English:
theorem Wbtw.mem_affineSpan
  given: {x y z : P} (h : Wbtw R x y z)
  statement: y in line[R, x, z]
  proof: by
  rcases h with ⟨r, ⟨-, rfl⟩⟩
  exact lineMap_mem_affineSpan_pair _ _ _

中文:
定理 Wbtw.mem_affineSpan
  条件: {x y z : P} (h : Wbtw R x y z)
  结论: y in line[R, x, z]
  证明: by
  rcases h with ⟨r, ⟨-, rfl⟩⟩
  exact lineMap_mem_affineSpan_pair _ _ _

Depends on / 依赖: lineMap_mem_affineSpan_pair
-/
theorem Wbtw.mem_affineSpan {x y z : P} (h : Wbtw R x y z) : y in line[R, x, z] := by
  rcases h with ⟨r, ⟨-, rfl⟩⟩
  exact lineMap_mem_affineSpan_pair _ _ _

variable (R)

section OrderedRing

variable [IsOrderedRing R]

@[simp]
/--
theorem `wbtw_self_left` / 定理 `wbtw_self_left`

English:
theorem wbtw_self_left
  given: (x y : P)
  statement: Wbtw R x x y
  proof: left_mem_affineSegment _ _ _

@[simp]

中文:
定理 wbtw_self_left
  条件: (x y : P)
  结论: Wbtw R x x y
  证明: left_mem_affineSegment _ _ _

@[simp]

Depends on / 依赖: left_mem_affineSegment
-/
theorem wbtw_self_left (x y : P) : Wbtw R x x y :=
  left_mem_affineSegment _ _ _

@[simp]
/--
theorem `wbtw_self_right` / 定理 `wbtw_self_right`

English:
theorem wbtw_self_right
  given: (x y : P)
  statement: Wbtw R x y y
  proof: right_mem_affineSegment _ _ _

中文:
定理 wbtw_self_right
  条件: (x y : P)
  结论: Wbtw R x y y
  证明: right_mem_affineSegment _ _ _

Depends on / 依赖: right_mem_affineSegment
-/
theorem wbtw_self_right (x y : P) : Wbtw R x y y :=
  right_mem_affineSegment _ _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `wbtw_self_iff` / 定理 `wbtw_self_iff`

English:
theorem wbtw_self_iff
  given: {x y : P}
  statement: Wbtw R x y x ↔ y = x
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa [Wbtw, affineSegment] using h
  · rw [h]
    exact wbtw_self_left R x x

中文:
定理 wbtw_self_iff
  条件: {x y : P}
  结论: Wbtw R x y x ↔ y = x
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa [Wbtw, affineSegment] using h
  · rw [h]
    exact wbtw_self_left R x x

Depends on / 依赖: affineSegment, wbtw_self_left
-/
theorem wbtw_self_iff {x y : P} : Wbtw R x y x ↔ y = x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa [Wbtw, affineSegment] using h
  · rw [h]
    exact wbtw_self_left R x x

end OrderedRing

section lift

variable [ZeroLEOneClass R]
variable (R' : Type*) [Ring R'] [PartialOrder R']
variable [Module R' V] [Module R' R] [IsScalarTower R' R V] [SMulPosMono R' R]

/--
theorem `affineSegment.lift` / 定理 `affineSegment.lift`

English:
theorem affineSegment.lift
  given: (x y : P)
  statement: affineSegment R' x y subseteq affineSegment R x y
  proof: by
  rintro p ⟨a, ⟨⟨ha₀, ha₁⟩, rfl⟩⟩
  refine ⟨a • 1, ⟨?_, ?_⟩, by simp [lineMap_apply]⟩
  · rw [← zero_smul R' (1 : R)]
    exact smul_le_smul_of_nonneg_right ha₀ zero_le_one
  · nth_rw 2 [← one_smul R' 1]
    exact smul_le_smul_of_nonneg_right ha₁ zero_le_one

中文:
定理 affineSegment.lift
  条件: (x y : P)
  结论: affineSegment R' x y subseteq affineSegment R x y
  证明: by
  rintro p ⟨a, ⟨⟨ha₀, ha₁⟩, rfl⟩⟩
  refine ⟨a • 1, ⟨?_, ?_⟩, by simp [lineMap_apply]⟩
  · rw [← zero_smul R' (1 : R)]
    exact smul_le_smul_of_nonneg_right ha₀ zero_le_one
  · nth_rw 2 [← one_smul R' 1]
    exact smul_le_smul_of_nonneg_right ha₁ zero_le_one

Depends on / 依赖: lineMap_apply, nth_rw, one_smul, smul_le_smul_of_nonneg_right, zero_le_one, zero_smul
-/
theorem affineSegment.lift (x y : P) : affineSegment R' x y subseteq affineSegment R x y := by
  rintro p ⟨a, ⟨⟨ha₀, ha₁⟩, rfl⟩⟩
  refine ⟨a • 1, ⟨?_, ?_⟩, by simp [lineMap_apply]⟩
  · rw [← zero_smul R' (1 : R)]
    exact smul_le_smul_of_nonneg_right ha₀ zero_le_one
  · nth_rw 2 [← one_smul R' 1]
    exact smul_le_smul_of_nonneg_right ha₁ zero_le_one

variable {R'} in
/--
theorem `Wbtw.lift` / 定理 `Wbtw.lift`

English:
theorem Wbtw.lift
  given: {x y z : P} (h : Wbtw R' x y z)
  statement: Wbtw R x y z
  proof: affineSegment.lift R R' x z h

中文:
定理 Wbtw.lift
  条件: {x y z : P} (h : Wbtw R' x y z)
  结论: Wbtw R x y z
  证明: affineSegment.lift R R' x z h

Depends on / 依赖: affineSegment, affineSegment.lift
-/
theorem Wbtw.lift {x y z : P} (h : Wbtw R' x y z) : Wbtw R x y z :=
  affineSegment.lift R R' x z h

variable {R'} in
/--
theorem `Sbtw.lift` / 定理 `Sbtw.lift`

English:
theorem Sbtw.lift
  given: {x y z : P} (h : Sbtw R' x y z)
  statement: Sbtw R x y z
  proof: ⟨h.wbtw.lift R, h.2⟩

中文:
定理 Sbtw.lift
  条件: {x y z : P} (h : Sbtw R' x y z)
  结论: Sbtw R x y z
  证明: ⟨h.wbtw.lift R, h.2⟩

Depends on / 依赖: h.wbtw.lift
-/
theorem Sbtw.lift {x y z : P} (h : Sbtw R' x y z) : Sbtw R x y z :=
  ⟨h.wbtw.lift R, h.2⟩

end lift

@[simp]
/--
theorem `not_sbtw_self_left` / 定理 `not_sbtw_self_left`

English:
theorem not_sbtw_self_left
  given: (x y : P)
  statement: ¬Sbtw R x x y
  proof: fun h => h.ne_left rfl

@[simp]

中文:
定理 not_sbtw_self_left
  条件: (x y : P)
  结论: ¬Sbtw R x x y
  证明: fun h => h.ne_left rfl

@[simp]

Depends on / 依赖: h.ne_left, ne_left
-/
theorem not_sbtw_self_left (x y : P) : ¬Sbtw R x x y :=
  fun h => h.ne_left rfl

@[simp]
/--
theorem `not_sbtw_self_right` / 定理 `not_sbtw_self_right`

English:
theorem not_sbtw_self_right
  given: (x y : P)
  statement: ¬Sbtw R x y y
  proof: fun h => h.ne_right rfl

中文:
定理 not_sbtw_self_right
  条件: (x y : P)
  结论: ¬Sbtw R x y y
  证明: fun h => h.ne_right rfl

Depends on / 依赖: h.ne_right, ne_right
-/
theorem not_sbtw_self_right (x y : P) : ¬Sbtw R x y y :=
  fun h => h.ne_right rfl

variable {R}
variable [IsOrderedRing R]

/--
theorem `Wbtw.left_ne_right_of_ne_left` / 定理 `Wbtw.left_ne_right_of_ne_left`

English:
theorem Wbtw.left_ne_right_of_ne_left
  given: {x y z : P} (h : Wbtw R x y z) (hne : y != x)
  statement: x != z
  proof: by
  rintro rfl
  rw [wbtw_self_iff] at h
  exact hne h

中文:
定理 Wbtw.left_ne_right_of_ne_left
  条件: {x y z : P} (h : Wbtw R x y z) (hne : y != x)
  结论: x != z
  证明: by
  rintro rfl
  rw [wbtw_self_iff] at h
  exact hne h

Depends on / 依赖: wbtw_self_iff
-/
theorem Wbtw.left_ne_right_of_ne_left {x y z : P} (h : Wbtw R x y z) (hne : y != x) : x != z := by
  rintro rfl
  rw [wbtw_self_iff] at h
  exact hne h

/--
theorem `Wbtw.left_ne_right_of_ne_right` / 定理 `Wbtw.left_ne_right_of_ne_right`

English:
theorem Wbtw.left_ne_right_of_ne_right
  given: {x y z : P} (h : Wbtw R x y z) (hne : y != z)
  statement: x != z
  proof: by
  rintro rfl
  rw [wbtw_self_iff] at h
  exact hne h

中文:
定理 Wbtw.left_ne_right_of_ne_right
  条件: {x y z : P} (h : Wbtw R x y z) (hne : y != z)
  结论: x != z
  证明: by
  rintro rfl
  rw [wbtw_self_iff] at h
  exact hne h

Depends on / 依赖: wbtw_self_iff
-/
theorem Wbtw.left_ne_right_of_ne_right {x y z : P} (h : Wbtw R x y z) (hne : y != z) : x != z := by
  rintro rfl
  rw [wbtw_self_iff] at h
  exact hne h

/--
theorem `Sbtw.left_ne_right` / 定理 `Sbtw.left_ne_right`

English:
theorem Sbtw.left_ne_right
  given: {x y z : P} (h : Sbtw R x y z)
  statement: x != z
  proof: h.wbtw.left_ne_right_of_ne_left h.2.1

中文:
定理 Sbtw.left_ne_right
  条件: {x y z : P} (h : Sbtw R x y z)
  结论: x != z
  证明: h.wbtw.left_ne_right_of_ne_left h.2.1

Depends on / 依赖: h.wbtw.left_ne_right_of_ne_left, left_ne_right_of_ne_left
-/
theorem Sbtw.left_ne_right {x y z : P} (h : Sbtw R x y z) : x != z :=
  h.wbtw.left_ne_right_of_ne_left h.2.1

variable (R) in
@[simp]
/--
theorem `not_sbtw_self` / 定理 `not_sbtw_self`

English:
theorem not_sbtw_self
  given: (x y : P)
  statement: ¬Sbtw R x y x
  proof: fun h => h.left_ne_right rfl

omit [IsOrderedRing R] in
@[simp]

中文:
定理 not_sbtw_self
  条件: (x y : P)
  结论: ¬Sbtw R x y x
  证明: fun h => h.left_ne_right rfl

omit [IsOrderedRing R] in
@[simp]

Depends on / 依赖: h.left_ne_right, left_ne_right
-/
theorem not_sbtw_self (x y : P) : ¬Sbtw R x y x :=
  fun h => h.left_ne_right rfl

omit [IsOrderedRing R] in
@[simp]
/--
theorem `wbtw_zero_one_iff` / 定理 `wbtw_zero_one_iff`

English:
theorem wbtw_zero_one_iff
  given: {x : R}
  statement: Wbtw R 0 x 1 ↔ x in Set.Icc (0 : R) 1
  proof: by
  rw [Wbtw]; rw [affineSegment]; rw [Set.mem_image]
  simp_rw [lineMap_apply_ring]
  simp

@[simp]

中文:
定理 wbtw_zero_one_iff
  条件: {x : R}
  结论: Wbtw R 0 x 1 ↔ x in Set.Icc (0 : R) 1
  证明: by
  rw [Wbtw]; rw [affineSegment]; rw [Set.mem_image]
  simp_rw [lineMap_apply_ring]
  simp

@[simp]

Depends on / 依赖: Set.mem_image, affineSegment, lineMap_apply_ring, mem_image, simp_rw
-/
theorem wbtw_zero_one_iff {x : R} : Wbtw R 0 x 1 ↔ x in Set.Icc (0 : R) 1 := by
  rw [Wbtw]; rw [affineSegment]; rw [Set.mem_image]
  simp_rw [lineMap_apply_ring]
  simp

@[simp]
/--
theorem `wbtw_one_zero_iff` / 定理 `wbtw_one_zero_iff`

English:
theorem wbtw_one_zero_iff
  given: {x : R}
  statement: Wbtw R 1 x 0 ↔ x in Set.Icc (0 : R) 1
  proof: by
  rw [wbtw_comm]; rw [wbtw_zero_one_iff]

omit [IsOrderedRing R] in
@[simp]

中文:
定理 wbtw_one_zero_iff
  条件: {x : R}
  结论: Wbtw R 1 x 0 ↔ x in Set.Icc (0 : R) 1
  证明: by
  rw [wbtw_comm]; rw [wbtw_zero_one_iff]

omit [IsOrderedRing R] in
@[simp]

Depends on / 依赖: wbtw_comm, wbtw_zero_one_iff
-/
theorem wbtw_one_zero_iff {x : R} : Wbtw R 1 x 0 ↔ x in Set.Icc (0 : R) 1 := by
  rw [wbtw_comm]; rw [wbtw_zero_one_iff]

omit [IsOrderedRing R] in
@[simp]
/--
theorem `sbtw_zero_one_iff` / 定理 `sbtw_zero_one_iff`

English:
theorem sbtw_zero_one_iff
  given: {x : R}
  statement: Sbtw R 0 x 1 ↔ x in Set.Ioo (0 : R) 1
  proof: by
  rw [Sbtw]; rw [wbtw_zero_one_iff]; rw [Set.mem_Icc]; rw [Set.mem_Ioo]
  exact
    ⟨fun h => ⟨h.1.1.lt_of_ne (Ne.symm h.2.1), h.1.2.lt_of_ne h.2.2⟩, fun h =>
      ⟨⟨h.1.le, h.2.le⟩, h.1.ne', h.2.ne⟩⟩

@[simp]

中文:
定理 sbtw_zero_one_iff
  条件: {x : R}
  结论: Sbtw R 0 x 1 ↔ x in Set.Ioo (0 : R) 1
  证明: by
  rw [Sbtw]; rw [wbtw_zero_one_iff]; rw [Set.mem_Icc]; rw [Set.mem_Ioo]
  exact
    ⟨fun h => ⟨h.1.1.lt_of_ne (Ne.symm h.2.1), h.1.2.lt_of_ne h.2.2⟩, fun h =>
      ⟨⟨h.1.le, h.2.le⟩, h.1.ne', h.2.ne⟩⟩

@[simp]

Depends on / 依赖: Ne.symm, Set.mem_Icc, Set.mem_Ioo, lt_of_ne, mem_Icc, mem_Ioo, wbtw_zero_one_iff
-/
theorem sbtw_zero_one_iff {x : R} : Sbtw R 0 x 1 ↔ x in Set.Ioo (0 : R) 1 := by
  rw [Sbtw]; rw [wbtw_zero_one_iff]; rw [Set.mem_Icc]; rw [Set.mem_Ioo]
  exact
    ⟨fun h => ⟨h.1.1.lt_of_ne (Ne.symm h.2.1), h.1.2.lt_of_ne h.2.2⟩, fun h =>
      ⟨⟨h.1.le, h.2.le⟩, h.1.ne', h.2.ne⟩⟩

@[simp]
/--
theorem `sbtw_one_zero_iff` / 定理 `sbtw_one_zero_iff`

English:
theorem sbtw_one_zero_iff
  given: {x : R}
  statement: Sbtw R 1 x 0 ↔ x in Set.Ioo (0 : R) 1
  proof: by
  rw [sbtw_comm]; rw [sbtw_zero_one_iff]

中文:
定理 sbtw_one_zero_iff
  条件: {x : R}
  结论: Sbtw R 1 x 0 ↔ x in Set.Ioo (0 : R) 1
  证明: by
  rw [sbtw_comm]; rw [sbtw_zero_one_iff]

Depends on / 依赖: sbtw_comm, sbtw_zero_one_iff
-/
theorem sbtw_one_zero_iff {x : R} : Sbtw R 1 x 0 ↔ x in Set.Ioo (0 : R) 1 := by
  rw [sbtw_comm]; rw [sbtw_zero_one_iff]

/--
theorem `Wbtw.trans_left` / 定理 `Wbtw.trans_left`

English:
theorem Wbtw.trans_left
  given: {w x y z : P} (h₁ : Wbtw R w y z) (h₂ : Wbtw R w x y)
  statement: Wbtw R w x z
  proof: by
  rcases h₁ with ⟨t₁, ht₁, rfl⟩
  rcases h₂ with ⟨t₂, ht₂, rfl⟩
  refine ⟨t₂ * t₁, ⟨mul_nonneg ht₂.1 ht₁.1, mul_le_one₀ ht₂.2 ht₁.1 ht₁.2⟩, ?_⟩
  rw [lineMap_apply]; rw [lineMap_apply]; rw [lineMap_vsub_left]; rw [smul_smul]

中文:
定理 Wbtw.trans_left
  条件: {w x y z : P} (h₁ : Wbtw R w y z) (h₂ : Wbtw R w x y)
  结论: Wbtw R w x z
  证明: by
  rcases h₁ with ⟨t₁, ht₁, rfl⟩
  rcases h₂ with ⟨t₂, ht₂, rfl⟩
  refine ⟨t₂ * t₁, ⟨mul_nonneg ht₂.1 ht₁.1, mul_le_one₀ ht₂.2 ht₁.1 ht₁.2⟩, ?_⟩
  rw [lineMap_apply]; rw [lineMap_apply]; rw [lineMap_vsub_left]; rw [smul_smul]

Depends on / 依赖: lineMap_apply, lineMap_vsub_left, mul_nonneg, smul_smul
-/
theorem Wbtw.trans_left {w x y z : P} (h₁ : Wbtw R w y z) (h₂ : Wbtw R w x y) : Wbtw R w x z := by
  rcases h₁ with ⟨t₁, ht₁, rfl⟩
  rcases h₂ with ⟨t₂, ht₂, rfl⟩
  refine ⟨t₂ * t₁, ⟨mul_nonneg ht₂.1 ht₁.1, mul_le_one₀ ht₂.2 ht₁.1 ht₁.2⟩, ?_⟩
  rw [lineMap_apply]; rw [lineMap_apply]; rw [lineMap_vsub_left]; rw [smul_smul]

/--
theorem `Wbtw.trans_right` / 定理 `Wbtw.trans_right`

English:
theorem Wbtw.trans_right
  given: {w x y z : P} (h₁ : Wbtw R w x z) (h₂ : Wbtw R x y z)
  statement: Wbtw R w y z
  proof: by
  rw [wbtw_comm] at *
  exact h₁.trans_left h₂

中文:
定理 Wbtw.trans_right
  条件: {w x y z : P} (h₁ : Wbtw R w x z) (h₂ : Wbtw R x y z)
  结论: Wbtw R w y z
  证明: by
  rw [wbtw_comm] at *
  exact h₁.trans_left h₂

Depends on / 依赖: trans_left, wbtw_comm
-/
theorem Wbtw.trans_right {w x y z : P} (h₁ : Wbtw R w x z) (h₂ : Wbtw R x y z) : Wbtw R w y z := by
  rw [wbtw_comm] at *
  exact h₁.trans_left h₂

section IsTorsionFree
variable [IsDomain R] [IsTorsionFree R V] {w x y z : P} {r : R}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sbtw_iff_mem_image_Ioo_and_ne` / 定理 `sbtw_iff_mem_image_Ioo_and_ne`

English:
theorem sbtw_iff_mem_image_Ioo_and_ne
  proof: by
  refine ⟨fun h => ⟨h.mem_image_Ioo, h.left_ne_right⟩, fun h => ?_⟩
  rcases h with ⟨⟨t, ht, rfl⟩, hxz⟩
  refine ⟨⟨t, Set.mem_Icc_of_Ioo ht, rfl⟩, ?_⟩
  rw [lineMap_apply]; rw [← @vsub_ne_zero V]; rw [← @vsub_ne_zero V _ _ _ _ z]; rw [vadd_vsub_assoc]; rw [vsub_self]; rw [vadd_vsub_assoc]; rw [← 

中文:
定理 sbtw_iff_mem_image_Ioo_and_ne
  证明: by
  refine ⟨fun h => ⟨h.mem_image_Ioo, h.left_ne_right⟩, fun h => ?_⟩
  rcases h with ⟨⟨t, ht, rfl⟩, hxz⟩
  refine ⟨⟨t, Set.mem_Icc_of_Ioo ht, rfl⟩, ?_⟩
  rw [lineMap_apply]; rw [← @vsub_ne_zero V]; rw [← @vsub_ne_zero V _ _ _ _ z]; rw [vadd_vsub_assoc]; rw [vsub_self]; rw [vadd_vsub_assoc]; rw [← 

Depends on / 依赖: Set.mem_Icc_of_Ioo, add_smul, h.left_ne_right, h.mem_image_Ioo, hxz.symm, left_ne_right, lineMap_apply, mem_Icc_of_Ioo, mem_image_Ioo, ne.symm, neg_one_smul, neg_vsub_eq_vsub_rev, sub_eq_add_neg, sub_eq_zero, vadd_vsub_assoc, vsub_ne_zero, vsub_self
-/
theorem sbtw_iff_mem_image_Ioo_and_ne :
    Sbtw R x y z ↔ y in lineMap x z '' Set.Ioo (0 : R) 1 ∧ x != z := by
  refine ⟨fun h => ⟨h.mem_image_Ioo, h.left_ne_right⟩, fun h => ?_⟩
  rcases h with ⟨⟨t, ht, rfl⟩, hxz⟩
  refine ⟨⟨t, Set.mem_Icc_of_Ioo ht, rfl⟩, ?_⟩
  rw [lineMap_apply]; rw [← @vsub_ne_zero V]; rw [← @vsub_ne_zero V _ _ _ _ z]; rw [vadd_vsub_assoc]; rw [vsub_self]; rw [vadd_vsub_assoc]; rw [← neg_vsub_eq_vsub_rev z x]; rw [← @neg_one_smul R]; rw [← add_smul]; rw [← sub_eq_add_neg]
  simp [sub_eq_zero, ht.1.ne.symm, ht.2.ne, hxz.symm]

variable (R z) in
/--
theorem `wbtw_swap_left_iff` / 定理 `wbtw_swap_left_iff`

English:
theorem wbtw_swap_left_iff
  statement: Wbtw R x y z ∧ Wbtw R y x z ↔ x = y
  proof: by
  constructor
  · rintro ⟨hxyz, hyxz⟩
    rcases hxyz with ⟨ty, hty, rfl⟩
    rcases hyxz with ⟨tx, htx, hx⟩
    rw [lineMap_apply]; rw [lineMap_apply]; rw [← add_vadd] at hx
    rw [← @vsub_eq_zero_iff_eq V]; rw [vadd_vsub]; rw [vsub_vadd_eq_vsub_sub]; rw [smul_sub]; rw [smul_smul]; rw [← sub_sm

中文:
定理 wbtw_swap_left_iff
  结论: Wbtw R x y z ∧ Wbtw R y x z ↔ x = y
  证明: by
  constructor
  · rintro ⟨hxyz, hyxz⟩
    rcases hxyz with ⟨ty, hty, rfl⟩
    rcases hyxz with ⟨tx, htx, hx⟩
    rw [lineMap_apply]; rw [lineMap_apply]; rw [← add_vadd] at hx
    rw [← @vsub_eq_zero_iff_eq V]; rw [vadd_vsub]; rw [vsub_vadd_eq_vsub_sub]; rw [smul_sub]; rw [smul_smul]; rw [← sub_sm

Depends on / 依赖: Left.n, add_eq_zero_iff_neg_eq, add_smul, add_vadd, le_antisymm, lineMap_apply, mul_one, mul_sub, nth_rw, smul_eq_zero, smul_smul, smul_sub, sub_smul, vadd_vsub, vsub_eq_zero_iff_eq, vsub_vadd_eq_vsub_sub
-/
theorem wbtw_swap_left_iff : Wbtw R x y z ∧ Wbtw R y x z ↔ x = y := by
  constructor
  · rintro ⟨hxyz, hyxz⟩
    rcases hxyz with ⟨ty, hty, rfl⟩
    rcases hyxz with ⟨tx, htx, hx⟩
    rw [lineMap_apply]; rw [lineMap_apply]; rw [← add_vadd] at hx
    rw [← @vsub_eq_zero_iff_eq V]; rw [vadd_vsub]; rw [vsub_vadd_eq_vsub_sub]; rw [smul_sub]; rw [smul_smul]; rw [← sub_smul]; rw [← add_smul]; rw [smul_eq_zero] at hx
    rcases hx with (h | h)
    · nth_rw 1 [← mul_one tx] at h
      rw [← mul_sub]; rw [add_eq_zero_iff_neg_eq] at h
      have h' : ty = 0 := by
        refine le_antisymm ?_ hty.1
        rw [← h]; rw [Left.neg_nonpos_iff]
        exact mul_nonneg htx.1 (sub_nonneg.2 hty.2)
      simp [h']
    · rw [vsub_eq_zero_iff_eq] at h
      rw [h]; rw [lineMap_same_apply]
  · rintro rfl
    exact ⟨wbtw_self_left _ _ _, wbtw_self_left _ _ _⟩

variable (R x) in
/--
theorem `wbtw_swap_right_iff` / 定理 `wbtw_swap_right_iff`

English:
theorem wbtw_swap_right_iff
  statement: Wbtw R x y z ∧ Wbtw R x z y ↔ y = z
  proof: by
  rw [wbtw_comm]; rw [wbtw_comm (z := y)]; rw [eq_comm]
  exact wbtw_swap_left_iff R x

中文:
定理 wbtw_swap_right_iff
  结论: Wbtw R x y z ∧ Wbtw R x z y ↔ y = z
  证明: by
  rw [wbtw_comm]; rw [wbtw_comm (z := y)]; rw [eq_comm]
  exact wbtw_swap_left_iff R x

Depends on / 依赖: eq_comm, wbtw_comm, wbtw_swap_left_iff
-/
theorem wbtw_swap_right_iff : Wbtw R x y z ∧ Wbtw R x z y ↔ y = z := by
  rw [wbtw_comm]; rw [wbtw_comm (z := y)]; rw [eq_comm]
  exact wbtw_swap_left_iff R x

variable (R x) in
/--
theorem `wbtw_rotate_iff` / 定理 `wbtw_rotate_iff`

English:
theorem wbtw_rotate_iff
  given: (x : P)
  statement: Wbtw R x y z ∧ Wbtw R z x y ↔ x = y
  proof: by
  rw [wbtw_comm]; rw [wbtw_swap_right_iff]; rw [eq_comm]

中文:
定理 wbtw_rotate_iff
  条件: (x : P)
  结论: Wbtw R x y z ∧ Wbtw R z x y ↔ x = y
  证明: by
  rw [wbtw_comm]; rw [wbtw_swap_right_iff]; rw [eq_comm]

Depends on / 依赖: eq_comm, wbtw_comm, wbtw_swap_right_iff
-/
theorem wbtw_rotate_iff (x : P) : Wbtw R x y z ∧ Wbtw R z x y ↔ x = y := by
  rw [wbtw_comm]; rw [wbtw_swap_right_iff]; rw [eq_comm]

/--
theorem `Wbtw.swap_left_iff` / 定理 `Wbtw.swap_left_iff`

English:
theorem Wbtw.swap_left_iff
  given: (h : Wbtw R x y z)
  statement: Wbtw R y x z ↔ x = y
  proof: by
  rw [← wbtw_swap_left_iff R z]; rw [and_iff_right h]

中文:
定理 Wbtw.swap_left_iff
  条件: (h : Wbtw R x y z)
  结论: Wbtw R y x z ↔ x = y
  证明: by
  rw [← wbtw_swap_left_iff R z]; rw [and_iff_right h]

Depends on / 依赖: and_iff_right, wbtw_swap_left_iff
-/
theorem Wbtw.swap_left_iff (h : Wbtw R x y z) : Wbtw R y x z ↔ x = y := by
  rw [← wbtw_swap_left_iff R z]; rw [and_iff_right h]

/--
theorem `Wbtw.swap_right_iff` / 定理 `Wbtw.swap_right_iff`

English:
theorem Wbtw.swap_right_iff
  given: (h : Wbtw R x y z)
  statement: Wbtw R x z y ↔ y = z
  proof: by
  rw [← wbtw_swap_right_iff R x]; rw [and_iff_right h]

中文:
定理 Wbtw.swap_right_iff
  条件: (h : Wbtw R x y z)
  结论: Wbtw R x z y ↔ y = z
  证明: by
  rw [← wbtw_swap_right_iff R x]; rw [and_iff_right h]

Depends on / 依赖: and_iff_right, wbtw_swap_right_iff
-/
theorem Wbtw.swap_right_iff (h : Wbtw R x y z) : Wbtw R x z y ↔ y = z := by
  rw [← wbtw_swap_right_iff R x]; rw [and_iff_right h]

/--
theorem `Wbtw.rotate_iff` / 定理 `Wbtw.rotate_iff`

English:
theorem Wbtw.rotate_iff
  given: (h : Wbtw R x y z)
  statement: Wbtw R z x y ↔ x = y
  proof: by
  rw [← wbtw_rotate_iff R x]; rw [and_iff_right h]

中文:
定理 Wbtw.rotate_iff
  条件: (h : Wbtw R x y z)
  结论: Wbtw R z x y ↔ x = y
  证明: by
  rw [← wbtw_rotate_iff R x]; rw [and_iff_right h]

Depends on / 依赖: and_iff_right, wbtw_rotate_iff
-/
theorem Wbtw.rotate_iff (h : Wbtw R x y z) : Wbtw R z x y ↔ x = y := by
  rw [← wbtw_rotate_iff R x]; rw [and_iff_right h]

/--
theorem `Sbtw.not_swap_left` / 定理 `Sbtw.not_swap_left`

English:
theorem Sbtw.not_swap_left
  given: (h : Sbtw R x y z)
  statement: ¬Wbtw R y x z
  proof: fun hs =>
  h.left_ne (h.wbtw.swap_left_iff.1 hs)

中文:
定理 Sbtw.not_swap_left
  条件: (h : Sbtw R x y z)
  结论: ¬Wbtw R y x z
  证明: fun hs =>
  h.left_ne (h.wbtw.swap_left_iff.1 hs)
-/
theorem Sbtw.not_swap_left (h : Sbtw R x y z) : ¬Wbtw R y x z := fun hs =>
  h.left_ne (h.wbtw.swap_left_iff.1 hs)

/--
theorem `Sbtw.not_swap_right` / 定理 `Sbtw.not_swap_right`

English:
theorem Sbtw.not_swap_right
  given: (h : Sbtw R x y z)
  statement: ¬Wbtw R x z y
  proof: fun hs =>
  h.ne_right (h.wbtw.swap_right_iff.1 hs)

中文:
定理 Sbtw.not_swap_right
  条件: (h : Sbtw R x y z)
  结论: ¬Wbtw R x z y
  证明: fun hs =>
  h.ne_right (h.wbtw.swap_right_iff.1 hs)
-/
theorem Sbtw.not_swap_right (h : Sbtw R x y z) : ¬Wbtw R x z y := fun hs =>
  h.ne_right (h.wbtw.swap_right_iff.1 hs)

/--
theorem `Sbtw.not_rotate` / 定理 `Sbtw.not_rotate`

English:
theorem Sbtw.not_rotate
  given: (h : Sbtw R x y z)
  statement: ¬Wbtw R z x y
  proof: fun hs =>
  h.left_ne (h.wbtw.rotate_iff.1 hs)

中文:
定理 Sbtw.not_rotate
  条件: (h : Sbtw R x y z)
  结论: ¬Wbtw R z x y
  证明: fun hs =>
  h.left_ne (h.wbtw.rotate_iff.1 hs)
-/
theorem Sbtw.not_rotate (h : Sbtw R x y z) : ¬Wbtw R z x y := fun hs =>
  h.left_ne (h.wbtw.rotate_iff.1 hs)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `wbtw_lineMap_iff` / 定理 `wbtw_lineMap_iff`

English:
theorem wbtw_lineMap_iff
  proof: by
  by_cases hxy : x = y
  · rw [hxy, lineMap_same_apply]
    simp
  rw [or_iff_right hxy]; rw [Wbtw]; rw [affineSegment]; rw [(lineMap_injective R hxy).mem_set_image]

中文:
定理 wbtw_lineMap_iff
  证明: by
  by_cases hxy : x = y
  · rw [hxy, lineMap_same_apply]
    simp
  rw [or_iff_right hxy]; rw [Wbtw]; rw [affineSegment]; rw [(lineMap_injective R hxy).mem_set_image]

Depends on / 依赖: affineSegment, lineMap_injective, lineMap_same_apply, mem_set_image, or_iff_right
-/
theorem wbtw_lineMap_iff :
    Wbtw R x (lineMap x y r) y ↔ x = y ∨ r in Set.Icc (0 : R) 1 := by
  by_cases hxy : x = y
  · rw [hxy, lineMap_same_apply]
    simp
  rw [or_iff_right hxy]; rw [Wbtw]; rw [affineSegment]; rw [(lineMap_injective R hxy).mem_set_image]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `sbtw_lineMap_iff` / 定理 `sbtw_lineMap_iff`

English:
theorem sbtw_lineMap_iff
  proof: by
  rw [sbtw_iff_mem_image_Ioo_and_ne]; rw [and_comm]; rw [and_congr_right]
  intro hxy
  rw [(lineMap_injective R hxy).mem_set_image]

@[simp]

中文:
定理 sbtw_lineMap_iff
  证明: by
  rw [sbtw_iff_mem_image_Ioo_and_ne]; rw [and_comm]; rw [and_congr_right]
  intro hxy
  rw [(lineMap_injective R hxy).mem_set_image]

@[simp]

Depends on / 依赖: and_comm, and_congr_right, lineMap_injective, mem_set_image, sbtw_iff_mem_image_Ioo_and_ne
-/
theorem sbtw_lineMap_iff :
    Sbtw R x (lineMap x y r) y ↔ x != y ∧ r in Set.Ioo (0 : R) 1 := by
  rw [sbtw_iff_mem_image_Ioo_and_ne]; rw [and_comm]; rw [and_congr_right]
  intro hxy
  rw [(lineMap_injective R hxy).mem_set_image]

@[simp]
/--
theorem `wbtw_mul_sub_add_iff` / 定理 `wbtw_mul_sub_add_iff`

English:
theorem wbtw_mul_sub_add_iff
  given: {x y r : R}
  proof: wbtw_lineMap_iff

@[simp]

中文:
定理 wbtw_mul_sub_add_iff
  条件: {x y r : R}
  证明: wbtw_lineMap_iff

@[simp]

Depends on / 依赖: wbtw_lineMap_iff
-/
theorem wbtw_mul_sub_add_iff {x y r : R} :
    Wbtw R x (r * (y - x) + x) y ↔ x = y ∨ r in Set.Icc (0 : R) 1 :=
  wbtw_lineMap_iff

@[simp]
/--
theorem `sbtw_mul_sub_add_iff` / 定理 `sbtw_mul_sub_add_iff`

English:
theorem sbtw_mul_sub_add_iff
  given: {x y r : R}
  proof: sbtw_lineMap_iff

中文:
定理 sbtw_mul_sub_add_iff
  条件: {x y r : R}
  证明: sbtw_lineMap_iff

Depends on / 依赖: sbtw_lineMap_iff
-/
theorem sbtw_mul_sub_add_iff {x y r : R} :
    Sbtw R x (r * (y - x) + x) y ↔ x != y ∧ r in Set.Ioo (0 : R) 1 :=
  sbtw_lineMap_iff

/--
theorem `Wbtw.trans_sbtw_left` / 定理 `Wbtw.trans_sbtw_left`

English:
theorem Wbtw.trans_sbtw_left
  given: (h₁ : Wbtw R w y z) (h₂ : Sbtw R w x y)
  statement: Sbtw R w x z
  proof: by
  refine ⟨h₁.trans_left h₂.wbtw, h₂.ne_left, ?_⟩
  rintro rfl
  exact h₂.right_ne ((wbtw_swap_right_iff R w).1 ⟨h₁, h₂.wbtw⟩)

中文:
定理 Wbtw.trans_sbtw_left
  条件: (h₁ : Wbtw R w y z) (h₂ : Sbtw R w x y)
  结论: Sbtw R w x z
  证明: by
  refine ⟨h₁.trans_left h₂.wbtw, h₂.ne_left, ?_⟩
  rintro rfl
  exact h₂.right_ne ((wbtw_swap_right_iff R w).1 ⟨h₁, h₂.wbtw⟩)

Depends on / 依赖: ne_left, right_ne, trans_left, wbtw_swap_right_iff
-/
theorem Wbtw.trans_sbtw_left (h₁ : Wbtw R w y z) (h₂ : Sbtw R w x y) : Sbtw R w x z := by
  refine ⟨h₁.trans_left h₂.wbtw, h₂.ne_left, ?_⟩
  rintro rfl
  exact h₂.right_ne ((wbtw_swap_right_iff R w).1 ⟨h₁, h₂.wbtw⟩)

/--
theorem `Wbtw.trans_sbtw_right` / 定理 `Wbtw.trans_sbtw_right`

English:
theorem Wbtw.trans_sbtw_right
  given: (h₁ : Wbtw R w x z) (h₂ : Sbtw R x y z)
  statement: Sbtw R w y z
  proof: by
  rw [wbtw_comm] at *
  rw [sbtw_comm] at *
  exact h₁.trans_sbtw_left h₂

中文:
定理 Wbtw.trans_sbtw_right
  条件: (h₁ : Wbtw R w x z) (h₂ : Sbtw R x y z)
  结论: Sbtw R w y z
  证明: by
  rw [wbtw_comm] at *
  rw [sbtw_comm] at *
  exact h₁.trans_sbtw_left h₂

Depends on / 依赖: sbtw_comm, trans_sbtw_left, wbtw_comm
-/
theorem Wbtw.trans_sbtw_right (h₁ : Wbtw R w x z) (h₂ : Sbtw R x y z) : Sbtw R w y z := by
  rw [wbtw_comm] at *
  rw [sbtw_comm] at *
  exact h₁.trans_sbtw_left h₂

/--
theorem `Sbtw.trans_left` / 定理 `Sbtw.trans_left`

English:
theorem Sbtw.trans_left
  given: (h₁ : Sbtw R w y z) (h₂ : Sbtw R w x y)
  statement: Sbtw R w x z
  proof: h₁.wbtw.trans_sbtw_left h₂

中文:
定理 Sbtw.trans_left
  条件: (h₁ : Sbtw R w y z) (h₂ : Sbtw R w x y)
  结论: Sbtw R w x z
  证明: h₁.wbtw.trans_sbtw_left h₂

Depends on / 依赖: trans_sbtw_left, wbtw.trans_sbtw_left
-/
theorem Sbtw.trans_left (h₁ : Sbtw R w y z) (h₂ : Sbtw R w x y) : Sbtw R w x z :=
  h₁.wbtw.trans_sbtw_left h₂

/--
theorem `Sbtw.trans_right` / 定理 `Sbtw.trans_right`

English:
theorem Sbtw.trans_right
  given: (h₁ : Sbtw R w x z) (h₂ : Sbtw R x y z)
  statement: Sbtw R w y z
  proof: h₁.wbtw.trans_sbtw_right h₂

中文:
定理 Sbtw.trans_right
  条件: (h₁ : Sbtw R w x z) (h₂ : Sbtw R x y z)
  结论: Sbtw R w y z
  证明: h₁.wbtw.trans_sbtw_right h₂

Depends on / 依赖: trans_sbtw_right, wbtw.trans_sbtw_right
-/
theorem Sbtw.trans_right (h₁ : Sbtw R w x z) (h₂ : Sbtw R x y z) : Sbtw R w y z :=
  h₁.wbtw.trans_sbtw_right h₂

/--
theorem `Wbtw.trans_left_ne` / 定理 `Wbtw.trans_left_ne`

English:
theorem Wbtw.trans_left_ne
  given: (h₁ : Wbtw R w y z) (h₂ : Wbtw R w x y) (h : y != z)
  statement: x != z
  proof: by
  rintro rfl
  exact h (h₁.swap_right_iff.1 h₂)

中文:
定理 Wbtw.trans_left_ne
  条件: (h₁ : Wbtw R w y z) (h₂ : Wbtw R w x y) (h : y != z)
  结论: x != z
  证明: by
  rintro rfl
  exact h (h₁.swap_right_iff.1 h₂)

Depends on / 依赖: swap_right_iff
-/
theorem Wbtw.trans_left_ne (h₁ : Wbtw R w y z) (h₂ : Wbtw R w x y) (h : y != z) : x != z := by
  rintro rfl
  exact h (h₁.swap_right_iff.1 h₂)

/--
theorem `Wbtw.trans_right_ne` / 定理 `Wbtw.trans_right_ne`

English:
theorem Wbtw.trans_right_ne
  given: (h₁ : Wbtw R w x z) (h₂ : Wbtw R x y z) (h : w != x)
  statement: w != y
  proof: by
  rintro rfl
  exact h (h₁.swap_left_iff.1 h₂)

中文:
定理 Wbtw.trans_right_ne
  条件: (h₁ : Wbtw R w x z) (h₂ : Wbtw R x y z) (h : w != x)
  结论: w != y
  证明: by
  rintro rfl
  exact h (h₁.swap_left_iff.1 h₂)

Depends on / 依赖: swap_left_iff
-/
theorem Wbtw.trans_right_ne (h₁ : Wbtw R w x z) (h₂ : Wbtw R x y z) (h : w != x) : w != y := by
  rintro rfl
  exact h (h₁.swap_left_iff.1 h₂)

/--
theorem `Sbtw.trans_wbtw_left_ne` / 定理 `Sbtw.trans_wbtw_left_ne`

English:
theorem Sbtw.trans_wbtw_left_ne
  given: (h₁ : Sbtw R w y z) (h₂ : Wbtw R w x y)
  statement: x != z
  proof: h₁.wbtw.trans_left_ne h₂ h₁.ne_right

中文:
定理 Sbtw.trans_wbtw_left_ne
  条件: (h₁ : Sbtw R w y z) (h₂ : Wbtw R w x y)
  结论: x != z
  证明: h₁.wbtw.trans_left_ne h₂ h₁.ne_right

Depends on / 依赖: ne_right, trans_left_ne, wbtw.trans_left_ne
-/
theorem Sbtw.trans_wbtw_left_ne (h₁ : Sbtw R w y z) (h₂ : Wbtw R w x y) : x != z :=
  h₁.wbtw.trans_left_ne h₂ h₁.ne_right

/--
theorem `Sbtw.trans_wbtw_right_ne` / 定理 `Sbtw.trans_wbtw_right_ne`

English:
theorem Sbtw.trans_wbtw_right_ne
  given: (h₁ : Sbtw R w x z) (h₂ : Wbtw R x y z)
  statement: w != y
  proof: h₁.wbtw.trans_right_ne h₂ h₁.left_ne

中文:
定理 Sbtw.trans_wbtw_right_ne
  条件: (h₁ : Sbtw R w x z) (h₂ : Wbtw R x y z)
  结论: w != y
  证明: h₁.wbtw.trans_right_ne h₂ h₁.left_ne

Depends on / 依赖: left_ne, trans_right_ne, wbtw.trans_right_ne
-/
theorem Sbtw.trans_wbtw_right_ne (h₁ : Sbtw R w x z) (h₂ : Wbtw R x y z) : w != y :=
  h₁.wbtw.trans_right_ne h₂ h₁.left_ne

end IsTorsionFree

/--
theorem `Sbtw.affineCombination_of_mem_affineSpan_pair` / 定理 `Sbtw.affineCombination_of_mem_affineSpan_pair`

English:
theorem Sbtw.affineCombination_of_mem_affineSpan_pair
  statement: [IsDomain R] [IsTorsionFree R V]
  proof: by
  rw [affineCombination_mem_affineSpan_pair ha hw hw₁ hw₂] at h
  rcases h with ⟨r, hr⟩
  rw [hr i his]; rw [sbtw_mul_sub_add_iff] at hs
  change forall i in s, w i = (r • (w₂ - w₁) + w₁) i at hr
  rw [s.affineCombination_congr hr fun _ _ => rfl]
  rw [← s.weightedVSub_vadd_affineCombination]; rw

中文:
定理 Sbtw.affineCombination_of_mem_affineSpan_pair
  结论: [IsDomain R] [IsTorsionFree R V]
  证明: by
  rw [affineCombination_mem_affineSpan_pair ha hw hw₁ hw₂] at h
  rcases h with ⟨r, hr⟩
  rw [hr i his]; rw [sbtw_mul_sub_add_iff] at hs
  change forall i in s, w i = (r • (w₂ - w₁) + w₁) i at hr
  rw [s.affineCombination_congr hr fun _ _ => rfl]
  rw [← s.weightedVSub_vadd_affineCombination]; rw

Depends on / 依赖: affineCombination_congr, affineCombination_mem_affineSpan_pair, affineCombination_vsub, and_iff_left, lineMap_apply, s.affineCombination_congr, s.affineCombination_vsub, s.weightedVSub_const_smul, s.weightedVSub_vadd_affineCombination, sbtw_lineMap_iff, sbtw_mul_sub_add_iff, vsub_ne_zero, weightedVSub_const_smul, weightedVSub_vadd_affineCombination
-/
theorem Sbtw.affineCombination_of_mem_affineSpan_pair [IsDomain R] [IsTorsionFree R V]
    {ι : Type*} {p : ι -> P} (ha : AffineIndependent R p) {w w₁ w₂ : ι -> R} {s : Finset ι}
    (hw : ∑ i in s, w i = 1) (hw₁ : ∑ i in s, w₁ i = 1) (hw₂ : ∑ i in s, w₂ i = 1)
    (h : s.affineCombination R p w in
      line[R, s.affineCombination R p w₁, s.affineCombination R p w₂])
    {i : ι} (his : i in s) (hs : Sbtw R (w₁ i) (w i) (w₂ i)) :
    Sbtw R (s.affineCombination R p w₁) (s.affineCombination R p w)
      (s.affineCombination R p w₂) := by
  rw [affineCombination_mem_affineSpan_pair ha hw hw₁ hw₂] at h
  rcases h with ⟨r, hr⟩
  rw [hr i his]; rw [sbtw_mul_sub_add_iff] at hs
  change forall i in s, w i = (r • (w₂ - w₁) + w₁) i at hr
  rw [s.affineCombination_congr hr fun _ _ => rfl]
  rw [← s.weightedVSub_vadd_affineCombination]; rw [s.weightedVSub_const_smul]; rw [← s.affineCombination_vsub]; rw [← lineMap_apply]; rw [sbtw_lineMap_iff]; rw [and_iff_left hs.2]; rw [← @vsub_ne_zero V]; rw [s.affineCombination_vsub]
  intro hz
  have hw₁w₂ : (∑ i in s, (w₁ - w₂) i) = 0 := by
    simp_rw [Pi.sub_apply, Finset.sum_sub_distrib, hw₁, hw₂, sub_self]
  refine hs.1 ?_
  have ha' := ha s (w₁ - w₂) hw₁w₂ hz i his
  rwa [Pi.sub_apply, sub_eq_zero] at ha'

namespace Affine

namespace Simplex

/--
lemma `closedInterior_eq_affineSegment` / 引理 `closedInterior_eq_affineSegment`

English:
lemma closedInterior_eq_affineSegment
  given: (s : Simplex R P 1)
  proof: by
  ext p
  constructor
  · rintro ⟨w, hw, h01, rfl⟩
    have h : w = Finset.affineCombinationLineMapWeights 0 1 (w 1) := by
      rw [Fin.sum_univ_two] at hw
      ext i
      fin_cases i <;> simp [← hw]
    rw [h]; rw [Finset.univ.affineCombination_affineCombinationLineMapWeights _ (Finset.mem_un

中文:
引理 closedInterior_eq_affineSegment
  条件: (s : Simplex R P 1)
  证明: by
  ext p
  constructor
  · rintro ⟨w, hw, h01, rfl⟩
    have h : w = Finset.affineCombinationLineMapWeights 0 1 (w 1) := by
      rw [Fin.sum_univ_two] at hw
      ext i
      fin_cases i <;> simp [← hw]
    rw [h]; rw [Finset.univ.affineCombination_affineCombinationLineMapWeights _ (Finset.mem_un

Depends on / 依赖: Fin.sum_univ_two, Finset, Finset.affineCombinationLineMapWeights, Finset.mem_univ, Finset.univ.affineCombination_affineCombinationLineMapWeights, Set.mem_image_of_mem, affineCombinationLineMapWeights, affineCombination_affineCombinationLineMapWeights, affineCombination_mem_cl, fin_cases, mem_image_of_mem, mem_univ, sum_univ_two
-/
lemma closedInterior_eq_affineSegment (s : Simplex R P 1) :
    s.closedInterior = affineSegment R (s.points 0) (s.points 1) := by
  ext p
  constructor
  · rintro ⟨w, hw, h01, rfl⟩
    have h : w = Finset.affineCombinationLineMapWeights 0 1 (w 1) := by
      rw [Fin.sum_univ_two] at hw
      ext i
      fin_cases i <;> simp [← hw]
    rw [h]; rw [Finset.univ.affineCombination_affineCombinationLineMapWeights _ (Finset.mem_univ _)
      (Finset.mem_univ _)]
    exact Set.mem_image_of_mem _ (h01 _)
  · rintro ⟨r, ⟨h0, h1⟩, rfl⟩
    rw [← Finset.univ.affineCombination_affineCombinationLineMapWeights _ (Finset.mem_univ _)
      (Finset.mem_univ _)]; rw [affineCombination_mem_closedInterior_iff
        (Finset.sum_affineCombinationLineMapWeights _ (Finset.mem_univ _) (Finset.mem_univ _) _)]
    intro i
    fin_cases i <;> simp [h0, h1]

/--
lemma `mem_closedInterior_iff_wbtw` / 引理 `mem_closedInterior_iff_wbtw`

English:
lemma mem_closedInterior_iff_wbtw
  given: {s : Simplex R P 1} {p : P}
  proof: by
  rw [closedInterior_eq_affineSegment]; rw [Wbtw]

中文:
引理 mem_closedInterior_iff_wbtw
  条件: {s : Simplex R P 1} {p : P}
  证明: by
  rw [closedInterior_eq_affineSegment]; rw [Wbtw]

Depends on / 依赖: closedInterior_eq_affineSegment
-/
lemma mem_closedInterior_iff_wbtw {s : Simplex R P 1} {p : P} :
    p in s.closedInterior ↔ Wbtw R (s.points 0) p (s.points 1) := by
  rw [closedInterior_eq_affineSegment]; rw [Wbtw]

/--
lemma `closedInterior_face_eq_affineSegment` / 引理 `closedInterior_face_eq_affineSegment`

English:
lemma closedInterior_face_eq_affineSegment
  statement: {n : Nat} (s : Simplex R P n) {i j : Fin (n + 1)}
  proof: by
  have h' : affineSegment R (s.points i) (s.points j) =
      affineSegment R (s.points (min i j)) (s.points (max i j)) := by
    rcases h.lt_or_gt with hij | hji
    · simp [min_eq_left hij.le, max_eq_right hij.le]
    · nth_rw 2 [affineSegment_comm]
      simp [max_eq_left hji.le, min_eq_right 

中文:
引理 closedInterior_face_eq_affineSegment
  结论: {n : 自然数} (s : Simplex R P n) {i j : Fin (n + 1)}
  证明: by
  have h' : affineSegment R (s.points i) (s.points j) =
      affineSegment R (s.points (min i j)) (s.points (max i j)) := by
    rcases h.lt_or_gt with hij | hji
    · simp [min_eq_left hij.le, max_eq_right hij.le]
    · nth_rw 2 [affineSegment_comm]
      simp [max_eq_left hji.le, min_eq_right 

Depends on / 依赖: Finset, Finset.card_pair, Finset.min, Finset.orderEmbOfFin_zero, _pair, affineSegment, affineSegment_comm, card_pair, closedInterior_eq_affineSegment, convert, face_points, h.lt_or_gt, hij.le, hji.le, lt_or_gt, max_eq_left, max_eq_right, min_eq_left, min_eq_right, nth_rw
-/
lemma closedInterior_face_eq_affineSegment {n : Nat} (s : Simplex R P n) {i j : Fin (n + 1)}
    (h : i != j) :
    (s.face (Finset.card_pair h)).closedInterior = affineSegment R (s.points i) (s.points j) := by
  have h' : affineSegment R (s.points i) (s.points j) =
      affineSegment R (s.points (min i j)) (s.points (max i j)) := by
    rcases h.lt_or_gt with hij | hji
    · simp [min_eq_left hij.le, max_eq_right hij.le]
    · nth_rw 2 [affineSegment_comm]
      simp [max_eq_left hji.le, min_eq_right hji.le]
  rw [h']; rw [(s.face (Finset.card_pair h)).closedInterior_eq_affineSegment]; rw [face_points]; rw [face_points]
  congr 2
  · convert! Finset.orderEmbOfFin_zero _ _
    · exact (Finset.min'_pair i j).symm
    · lia
  · convert! Finset.orderEmbOfFin_last _ _
    · exact (Finset.max'_pair i j).symm
    · lia

/--
lemma `mem_closedInterior_face_iff_wbtw` / 引理 `mem_closedInterior_face_iff_wbtw`

English:
lemma mem_closedInterior_face_iff_wbtw
  statement: {n : Nat} (s : Simplex R P n) {p : P} {i j : Fin (n + 1)}
  proof: by
  rw [s.closedInterior_face_eq_affineSegment h]; rw [Wbtw]

中文:
引理 mem_closedInterior_face_iff_wbtw
  结论: {n : 自然数} (s : Simplex R P n) {p : P} {i j : Fin (n + 1)}
  证明: by
  rw [s.closedInterior_face_eq_affineSegment h]; rw [Wbtw]

Depends on / 依赖: closedInterior_face_eq_affineSegment, s.closedInterior_face_eq_affineSegment
-/
lemma mem_closedInterior_face_iff_wbtw {n : Nat} (s : Simplex R P n) {p : P} {i j : Fin (n + 1)}
    (h : i != j) :
    p in (s.face (Finset.card_pair h)).closedInterior ↔ Wbtw R (s.points i) p (s.points j) := by
  rw [s.closedInterior_face_eq_affineSegment h]; rw [Wbtw]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `interior_eq_image_Ioo` / 引理 `interior_eq_image_Ioo`

English:
lemma interior_eq_image_Ioo
  given: (s : Simplex R P 1)
  proof: by
  ext p
  constructor
  · rintro ⟨w, hw, h01, rfl⟩
    have h : w = Finset.affineCombinationLineMapWeights 0 1 (w 1) := by
      rw [Fin.sum_univ_two] at hw
      ext i
      fin_cases i <;> simp [← hw]
    rw [h]; rw [Finset.univ.affineCombination_affineCombinationLineMapWeights _ (Finset.mem_un

中文:
引理 interior_eq_image_Ioo
  条件: (s : Simplex R P 1)
  证明: by
  ext p
  constructor
  · rintro ⟨w, hw, h01, rfl⟩
    have h : w = Finset.affineCombinationLineMapWeights 0 1 (w 1) := by
      rw [Fin.sum_univ_two] at hw
      ext i
      fin_cases i <;> simp [← hw]
    rw [h]; rw [Finset.univ.affineCombination_affineCombinationLineMapWeights _ (Finset.mem_un

Depends on / 依赖: Fin.sum_univ_two, Finset, Finset.affineCombinationLineMapWeights, Finset.mem_univ, Finset.univ.affineCombination_affineCombinationLineMapWeights, Set.mem_image_of_mem, affineCombinationLineMapWeights, affineCombination_affineCombinationLineMapWeights, affineCombination_mem_in, fin_cases, mem_image_of_mem, mem_univ, sum_univ_two
-/
lemma interior_eq_image_Ioo (s : Simplex R P 1) :
    s.interior = AffineMap.lineMap (s.points 0) (s.points 1) '' Set.Ioo (0 : R) 1 := by
  ext p
  constructor
  · rintro ⟨w, hw, h01, rfl⟩
    have h : w = Finset.affineCombinationLineMapWeights 0 1 (w 1) := by
      rw [Fin.sum_univ_two] at hw
      ext i
      fin_cases i <;> simp [← hw]
    rw [h]; rw [Finset.univ.affineCombination_affineCombinationLineMapWeights _ (Finset.mem_univ _)
      (Finset.mem_univ _)]
    exact Set.mem_image_of_mem _ (h01 _)
  · rintro ⟨r, ⟨h0, h1⟩, rfl⟩
    rw [← Finset.univ.affineCombination_affineCombinationLineMapWeights _ (Finset.mem_univ _)
      (Finset.mem_univ _)]; rw [affineCombination_mem_interior_iff
        (Finset.sum_affineCombinationLineMapWeights _ (Finset.mem_univ _) (Finset.mem_univ _) _)]
    intro i
    fin_cases i <;> simp [h0, h1]

/--
lemma `mem_interior_iff_sbtw` / 引理 `mem_interior_iff_sbtw`

English:
lemma mem_interior_iff_sbtw
  given: [IsDomain R] [IsTorsionFree R V] {s : Simplex R P 1} {p : P}
  proof: by
  rw [interior_eq_image_Ioo]; rw [sbtw_iff_mem_image_Ioo_and_ne]
  simp [s.independent.injective.ne (by decide : (0 : Fin 2) != 1)]

中文:
引理 mem_interior_iff_sbtw
  条件: [IsDomain R] [IsTorsionFree R V] {s : Simplex R P 1} {p : P}
  证明: by
  rw [interior_eq_image_Ioo]; rw [sbtw_iff_mem_image_Ioo_and_ne]
  simp [s.independent.injective.ne (by decide : (0 : Fin 2) != 1)]

Depends on / 依赖: independent, injective, interior_eq_image_Ioo, s.independent.injective.ne, sbtw_iff_mem_image_Ioo_and_ne
-/
lemma mem_interior_iff_sbtw [IsDomain R] [IsTorsionFree R V] {s : Simplex R P 1} {p : P} :
    p in s.interior ↔ Sbtw R (s.points 0) p (s.points 1) := by
  rw [interior_eq_image_Ioo]; rw [sbtw_iff_mem_image_Ioo_and_ne]
  simp [s.independent.injective.ne (by decide : (0 : Fin 2) != 1)]

/--
lemma `mem_interior_face_iff_sbtw` / 引理 `mem_interior_face_iff_sbtw`

English:
lemma mem_interior_face_iff_sbtw
  statement: [IsDomain R] [IsTorsionFree R V] {n : Nat}
  proof: by
  have h' : Sbtw R (s.points i) p (s.points j) ↔
      Sbtw R (s.points (min i j)) p (s.points (max i j)) := by
    rcases h.lt_or_gt with hij | hji
    · simp [min_eq_left hij.le, max_eq_right hij.le]
    · nth_rw 2 [sbtw_comm]
      simp [max_eq_left hji.le, min_eq_right hji.le]
  rw [h']; rw [

中文:
引理 mem_interior_face_iff_sbtw
  结论: [IsDomain R] [IsTorsionFree R V] {n : 自然数}
  证明: by
  have h' : Sbtw R (s.points i) p (s.points j) ↔
      Sbtw R (s.points (min i j)) p (s.points (max i j)) := by
    rcases h.lt_or_gt with hij | hji
    · simp [min_eq_left hij.le, max_eq_right hij.le]
    · nth_rw 2 [sbtw_comm]
      simp [max_eq_left hji.le, min_eq_right hji.le]
  rw [h']; rw [

Depends on / 依赖: Finset, Finset.max, Finset.min, Finset.orderEmbOfFin_last, Finset.orderEmbOfFin_zero, _pair, convert, face_points, h.lt_or_gt, hij.le, hji.le, lt_or_gt, max_eq_left, max_eq_right, mem_interior_iff_sbtw, min_eq_left, min_eq_right, nth_rw, orderEmbOfFin_last, orderEmbOfFin_zero
-/
lemma mem_interior_face_iff_sbtw [IsDomain R] [IsTorsionFree R V] {n : Nat}
    (s : Simplex R P n) {p : P} {i j : Fin (n + 1)} (h : i != j) :
    p in (s.face (Finset.card_pair h)).interior ↔ Sbtw R (s.points i) p (s.points j) := by
  have h' : Sbtw R (s.points i) p (s.points j) ↔
      Sbtw R (s.points (min i j)) p (s.points (max i j)) := by
    rcases h.lt_or_gt with hij | hji
    · simp [min_eq_left hij.le, max_eq_right hij.le]
    · nth_rw 2 [sbtw_comm]
      simp [max_eq_left hji.le, min_eq_right hji.le]
  rw [h']; rw [mem_interior_iff_sbtw]; rw [face_points]; rw [face_points]
  congr! 4
  · convert! Finset.orderEmbOfFin_zero _ _
    · exact (Finset.min'_pair i j).symm
    · lia
  · convert! Finset.orderEmbOfFin_last _ _
    · exact (Finset.max'_pair i j).symm
    · lia

end Simplex

end Affine

end OrderedRing

section StrictOrderedCommRing

variable [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [AddTorsor V P]
variable {R}

/--
theorem `Wbtw.sameRay_vsub` / 定理 `Wbtw.sameRay_vsub`

English:
theorem Wbtw.sameRay_vsub
  given: {x y z : P} (h : Wbtw R x y z)
  statement: SameRay R (y -ᵥ x) (z -ᵥ y)
  proof: by
  simpa using sameRay_of_mem_segment ((mem_segment_iff_wbtw).2 (h.vsub_const x))

中文:
定理 Wbtw.sameRay_vsub
  条件: {x y z : P} (h : Wbtw R x y z)
  结论: SameRay R (y -ᵥ x) (z -ᵥ y)
  证明: by
  simpa using sameRay_of_mem_segment ((mem_segment_iff_wbtw).2 (h.vsub_const x))

Depends on / 依赖: h.vsub_const, mem_segment_iff_wbtw, sameRay_of_mem_segment, vsub_const
-/
theorem Wbtw.sameRay_vsub {x y z : P} (h : Wbtw R x y z) : SameRay R (y -ᵥ x) (z -ᵥ y) := by
  simpa using sameRay_of_mem_segment ((mem_segment_iff_wbtw).2 (h.vsub_const x))

/--
theorem `Wbtw.sameRay_vsub_left` / 定理 `Wbtw.sameRay_vsub_left`

English:
theorem Wbtw.sameRay_vsub_left
  given: {x y z : P} (h : Wbtw R x y z)
  statement: SameRay R (y -ᵥ x) (z -ᵥ x)
  proof: by
  rcases h with ⟨t, ⟨ht0, _⟩, rfl⟩
  simp [SameRay.sameRay_nonneg_smul_left (z -ᵥ x) ht0]

中文:
定理 Wbtw.sameRay_vsub_left
  条件: {x y z : P} (h : Wbtw R x y z)
  结论: SameRay R (y -ᵥ x) (z -ᵥ x)
  证明: by
  rcases h with ⟨t, ⟨ht0, _⟩, rfl⟩
  simp [SameRay.sameRay_nonneg_smul_left (z -ᵥ x) ht0]

Depends on / 依赖: SameRay, SameRay.sameRay_nonneg_smul_left, sameRay_nonneg_smul_left
-/
theorem Wbtw.sameRay_vsub_left {x y z : P} (h : Wbtw R x y z) : SameRay R (y -ᵥ x) (z -ᵥ x) := by
  rcases h with ⟨t, ⟨ht0, _⟩, rfl⟩
  simp [SameRay.sameRay_nonneg_smul_left (z -ᵥ x) ht0]

/--
theorem `Wbtw.sameRay_vsub_right` / 定理 `Wbtw.sameRay_vsub_right`

English:
theorem Wbtw.sameRay_vsub_right
  given: {x y z : P} (h : Wbtw R x y z)
  statement: SameRay R (z -ᵥ x) (z -ᵥ y)
  proof: by
  rcases h with ⟨t, ⟨_, ht1⟩, rfl⟩
  simp [SameRay.sameRay_nonneg_smul_right (z -ᵥ x) (sub_nonneg.2 ht1)]

中文:
定理 Wbtw.sameRay_vsub_right
  条件: {x y z : P} (h : Wbtw R x y z)
  结论: SameRay R (z -ᵥ x) (z -ᵥ y)
  证明: by
  rcases h with ⟨t, ⟨_, ht1⟩, rfl⟩
  simp [SameRay.sameRay_nonneg_smul_right (z -ᵥ x) (sub_nonneg.2 ht1)]

Depends on / 依赖: SameRay, SameRay.sameRay_nonneg_smul_right, sameRay_nonneg_smul_right, sub_nonneg
-/
theorem Wbtw.sameRay_vsub_right {x y z : P} (h : Wbtw R x y z) : SameRay R (z -ᵥ x) (z -ᵥ y) := by
  rcases h with ⟨t, ⟨_, ht1⟩, rfl⟩
  simp [SameRay.sameRay_nonneg_smul_right (z -ᵥ x) (sub_nonneg.2 ht1)]

end StrictOrderedCommRing

section LinearOrderedRing

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [AddTorsor V P]
variable {R}

/--
theorem `sbtw_of_sbtw_of_sbtw_of_mem_affineSpan_pair` / 定理 `sbtw_of_sbtw_of_sbtw_of_mem_affineSpan_pair`

English:
theorem sbtw_of_sbtw_of_sbtw_of_mem_affineSpan_pair
  statement: [IsTorsionFree R V]
  proof: by
  have h₁₃ : i₁ != i₃ := by
    rintro rfl
    simp at h₂
  have h₂₃ : i₂ != i₃ := by
    rintro rfl
    simp at h₁
  have h3 : forall i : Fin 3, i = i₁ ∨ i = i₂ ∨ i = i₃ := by lia
  have hu : (Finset.univ : Finset (Fin 3)) = {i₁, i₂, i₃} := by
    clear h₁ h₂ h₁' h₂'
    decide +revert
  have hp

中文:
定理 sbtw_of_sbtw_of_sbtw_of_mem_affineSpan_pair
  结论: [IsTorsionFree R V]
  证明: by
  have h₁₃ : i₁ != i₃ := by
    rintro rfl
    simp at h₂
  have h₂₃ : i₂ != i₃ := by
    rintro rfl
    simp at h₁
  have h3 : forall i : Fin 3, i = i₁ ∨ i = i₂ ∨ i = i₃ := by lia
  have hu : (Finset.univ : Finset (Fin 3)) = {i₁, i₂, i₃} := by
    clear h₁ h₂ h₁' h₂'
    decide +revert
  have hp

Depends on / 依赖: Finset, Finset.univ, Set.mem_range_self, Set.range, affineSpan, affineSpan_pair_le_of_mem_of_mem, mem_affineSpan, mem_range_self, points, revert, t.points
-/
theorem sbtw_of_sbtw_of_sbtw_of_mem_affineSpan_pair [IsTorsionFree R V]
    {t : Affine.Triangle R P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) {p₁ p₂ p : P}
    (h₁ : Sbtw R (t.points i₂) p₁ (t.points i₃)) (h₂ : Sbtw R (t.points i₁) p₂ (t.points i₃))
    (h₁' : p in line[R, t.points i₁, p₁]) (h₂' : p in line[R, t.points i₂, p₂]) :
    Sbtw R (t.points i₁) p p₁ := by
  have h₁₃ : i₁ != i₃ := by
    rintro rfl
    simp at h₂
  have h₂₃ : i₂ != i₃ := by
    rintro rfl
    simp at h₁
  have h3 : forall i : Fin 3, i = i₁ ∨ i = i₂ ∨ i = i₃ := by lia
  have hu : (Finset.univ : Finset (Fin 3)) = {i₁, i₂, i₃} := by
    clear h₁ h₂ h₁' h₂'
    decide +revert
  have hp : p in affineSpan R (Set.range t.points) := by
    have hle : line[R, t.points i₁, p₁] <= affineSpan R (Set.range t.points) := by
      refine affineSpan_pair_le_of_mem_of_mem (mem_affineSpan R (Set.mem_range_self _)) ?_
      have hle : line[R, t.points i₂, t.points i₃] <= affineSpan R (Set.range t.points) := by
        refine affineSpan_mono R ?_
        simp [Set.insert_subset_iff]
      rw [AffineSubspace.le_def'] at hle
      exact hle _ h₁.wbtw.mem_affineSpan
    rw [AffineSubspace.le_def'] at hle
    exact hle _ h₁'
  have h₁i := h₁.mem_image_Ioo
  have h₂i := h₂.mem_image_Ioo
  rw [Set.mem_image] at h₁i h₂i
  rcases h₁i with ⟨r₁, ⟨hr₁0, hr₁1⟩, rfl⟩
  rcases h₂i with ⟨r₂, ⟨hr₂0, hr₂1⟩, rfl⟩
  rcases eq_affineCombination_of_mem_affineSpan_of_fintype hp with ⟨w, hw, rfl⟩
  have h₁s :=
    sign_eq_of_affineCombination_mem_affineSpan_single_lineMap t.independent hw (Finset.mem_univ _)
      (Finset.mem_univ _) (Finset.mem_univ _) h₁₂ h₁₃ h₂₃ hr₁0 hr₁1 h₁'
  have h₂s :=
    sign_eq_of_affineCombination_mem_affineSpan_single_lineMap t.independent hw (Finset.mem_univ _)
      (Finset.mem_univ _) (Finset.mem_univ _) h₁₂.symm h₂₃ h₁₃ hr₂0 hr₂1 h₂'
  rw [← Finset.univ.affineCombination_piSingle R t.points
      (Finset.mem_univ i₁)]; rw [← Finset.univ.affineCombination_affineCombinationLineMapWeights t.points (Finset.mem_univ _)
      (Finset.mem_univ _)] at h₁' ⊢
  refine
    Sbtw.affineCombination_of_mem_affineSpan_pair t.independent hw (Fintype.sum_pi_single' _ _)
      (Finset.univ.sum_affineCombinationLineMapWeights (Finset.mem_univ _) (Finset.mem_univ _) _)
      h₁' (Finset.mem_univ i₁) ?_
  rw [Pi.single_eq_same]; rw [Finset.affineCombinationLineMapWeights_apply_of_ne h₁₂ h₁₃]; rw [sbtw_one_zero_iff]
  have hs : forall i : Fin 3, SignType.sign (w i) = SignType.sign (w i₃) := by
    intro i
    rcases h3 i with (rfl | rfl | rfl)
    · exact h₂s
    · exact h₁s
    · rfl
  have hss : SignType.sign (∑ i, w i) = 1 := by simp [hw]
  have hs' := sign_sum Finset.univ_nonempty (SignType.sign (w i₃)) fun i _ => hs i
  rw [hs'] at hss
  simp_rw [hss, sign_eq_one_iff] at hs
  refine ⟨hs i₁, ?_⟩
  rw [hu] at hw
  rw [Finset.sum_insert]; rw [Finset.sum_insert]; rw [Finset.sum_singleton] at hw
  · by_contra hle
    rw [not_lt] at hle
    exact (hle.trans_lt (lt_add_of_pos_right _ (Left.add_pos (hs i₂) (hs i₃)))).ne' hw
  · simpa using h₂₃
  · simpa [not_or] using ⟨h₁₂, h₁₃⟩

end LinearOrderedRing

section LinearOrderedField

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [AddTorsor V P] {x y z : P}
variable {R}

/--
lemma `wbtw_iff_of_le` / 引理 `wbtw_iff_of_le`

English:
lemma wbtw_iff_of_le
  given: {x y z : R} (hxz : x <= z)
  statement: Wbtw R x y z ↔ x <= y ∧ y <= z
  proof: by
  cases hxz.eq_or_lt with
  | inl hxz =>
    subst hxz
    rw [← le_antisymm_iff]; rw [wbtw_self_iff]; rw [eq_comm]
  | inr hxz =>
    have hxz' : 0 < z - x := sub_pos.mpr hxz
    let r := (y - x) / (z - x)
    have hy : y = r * (z - x) + x := by simp [r, hxz'.ne']
    simp [hy, wbtw_mul_sub_add_

中文:
引理 wbtw_iff_of_le
  条件: {x y z : R} (hxz : x <= z)
  结论: Wbtw R x y z ↔ x <= y ∧ y <= z
  证明: by
  cases hxz.eq_or_lt with
  | inl hxz =>
    subst hxz
    rw [← le_antisymm_iff]; rw [wbtw_self_iff]; rw [eq_comm]
  | inr hxz =>
    have hxz' : 0 < z - x := sub_pos.mpr hxz
    let r := (y - x) / (z - x)
    have hy : y = r * (z - x) + x := by simp [r, hxz'.ne']
    simp [hy, wbtw_mul_sub_add_

Depends on / 依赖: eq_comm, eq_or_lt, hxz.eq_or_lt, hxz.ne, le_antisymm_iff, le_sub_iff_add_le, mul_le_iff_le_one_left, mul_nonneg_iff_of_pos_right, sub_pos, sub_pos.mpr, wbtw_mul_sub_add_iff, wbtw_self_iff
-/
lemma wbtw_iff_of_le {x y z : R} (hxz : x <= z) : Wbtw R x y z ↔ x <= y ∧ y <= z := by
  cases hxz.eq_or_lt with
  | inl hxz =>
    subst hxz
    rw [← le_antisymm_iff]; rw [wbtw_self_iff]; rw [eq_comm]
  | inr hxz =>
    have hxz' : 0 < z - x := sub_pos.mpr hxz
    let r := (y - x) / (z - x)
    have hy : y = r * (z - x) + x := by simp [r, hxz'.ne']
    simp [hy, wbtw_mul_sub_add_iff, mul_nonneg_iff_of_pos_right hxz', ← le_sub_iff_add_le,
      mul_le_iff_le_one_left hxz', hxz.ne]

/--
lemma `Wbtw.of_le_of_le` / 引理 `Wbtw.of_le_of_le`

English:
lemma Wbtw.of_le_of_le
  given: {x y z : R} (hxy : x <= y) (hyz : y <= z)
  statement: Wbtw R x y z
  proof: (wbtw_iff_of_le (hxy.trans hyz)).mpr ⟨hxy, hyz⟩

中文:
引理 Wbtw.of_le_of_le
  条件: {x y z : R} (hxy : x <= y) (hyz : y <= z)
  结论: Wbtw R x y z
  证明: (wbtw_iff_of_le (hxy.trans hyz)).mpr ⟨hxy, hyz⟩

Depends on / 依赖: hxy.trans, wbtw_iff_of_le
-/
lemma Wbtw.of_le_of_le {x y z : R} (hxy : x <= y) (hyz : y <= z) : Wbtw R x y z :=
  (wbtw_iff_of_le (hxy.trans hyz)).mpr ⟨hxy, hyz⟩

/--
lemma `Sbtw.of_lt_of_lt` / 引理 `Sbtw.of_lt_of_lt`

English:
lemma Sbtw.of_lt_of_lt
  given: {x y z : R} (hxy : x < y) (hyz : y < z)
  statement: Sbtw R x y z
  proof: ⟨.of_le_of_le hxy.le hyz.le, hxy.ne', hyz.ne⟩

中文:
引理 Sbtw.of_lt_of_lt
  条件: {x y z : R} (hxy : x < y) (hyz : y < z)
  结论: Sbtw R x y z
  证明: ⟨.of_le_of_le hxy.le hyz.le, hxy.ne', hyz.ne⟩

Depends on / 依赖: hxy.le, hxy.ne, hyz.le, hyz.ne, of_le_of_le
-/
lemma Sbtw.of_lt_of_lt {x y z : R} (hxy : x < y) (hyz : y < z) : Sbtw R x y z :=
  ⟨.of_le_of_le hxy.le hyz.le, hxy.ne', hyz.ne⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `wbtw_iff_left_eq_or_right_mem_image_Ici` / 定理 `wbtw_iff_left_eq_or_right_mem_image_Ici`

English:
theorem wbtw_iff_left_eq_or_right_mem_image_Ici
  given: {x y z : P}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨r, ⟨hr0, hr1⟩, rfl⟩
    rcases hr0.lt_or_eq with (hr0' | rfl)
    · rw [Set.mem_image]
      refine .inr ⟨r⁻¹, (one_le_inv₀ hr0').2 hr1, ?_⟩
      simp only [lineMap_apply, smul_smul, vadd_vsub]
      rw [inv_mul_cancel₀ hr0'.ne']; rw [one_sm

中文:
定理 wbtw_iff_left_eq_or_right_mem_image_Ici
  条件: {x y z : P}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨r, ⟨hr0, hr1⟩, rfl⟩
    rcases hr0.lt_or_eq with (hr0' | rfl)
    · rw [Set.mem_image]
      refine .inr ⟨r⁻¹, (one_le_inv₀ hr0').2 hr1, ?_⟩
      simp only [lineMap_apply, smul_smul, vadd_vsub]
      rw [inv_mul_cancel₀ hr0'.ne']; rw [one_sm

Depends on / 依赖: Set.mem_Ici, Set.mem_image, hr0.lt_or_eq, inv_nonneg, lineMap_apply, lt_or_eq, mem_Ici, mem_image, one_smul, smul_smul, vadd_vsub, vsub_vadd, wbtw_self_left, zero_le_one, zero_le_one.trans
-/
theorem wbtw_iff_left_eq_or_right_mem_image_Ici {x y z : P} :
    Wbtw R x y z ↔ x = y ∨ z in lineMap x y '' Set.Ici (1 : R) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨r, ⟨hr0, hr1⟩, rfl⟩
    rcases hr0.lt_or_eq with (hr0' | rfl)
    · rw [Set.mem_image]
      refine .inr ⟨r⁻¹, (one_le_inv₀ hr0').2 hr1, ?_⟩
      simp only [lineMap_apply, smul_smul, vadd_vsub]
      rw [inv_mul_cancel₀ hr0'.ne']; rw [one_smul]; rw [vsub_vadd]
    · simp
  · rcases h with (rfl | ⟨r, ⟨hr, rfl⟩⟩)
    · exact wbtw_self_left _ _ _
    · rw [Set.mem_Ici] at hr
      refine ⟨r⁻¹, ⟨inv_nonneg.2 (zero_le_one.trans hr), inv_le_one_of_one_le₀ hr⟩, ?_⟩
      simp only [lineMap_apply, smul_smul, vadd_vsub]
      rw [inv_mul_cancel₀ (one_pos.trans_le hr).ne']; rw [one_smul]; rw [vsub_vadd]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Wbtw.right_mem_image_Ici_of_left_ne` / 定理 `Wbtw.right_mem_image_Ici_of_left_ne`

English:
theorem Wbtw.right_mem_image_Ici_of_left_ne
  given: {x y z : P} (h : Wbtw R x y z) (hne : x != y)
  proof: (wbtw_iff_left_eq_or_right_mem_image_Ici.1 h).resolve_left hne

中文:
定理 Wbtw.right_mem_image_Ici_of_left_ne
  条件: {x y z : P} (h : Wbtw R x y z) (hne : x != y)
  证明: (wbtw_iff_left_eq_or_right_mem_image_Ici.1 h).resolve_left hne

Depends on / 依赖: resolve_left, wbtw_iff_left_eq_or_right_mem_image_Ici
-/
theorem Wbtw.right_mem_image_Ici_of_left_ne {x y z : P} (h : Wbtw R x y z) (hne : x != y) :
    z in lineMap x y '' Set.Ici (1 : R) :=
  (wbtw_iff_left_eq_or_right_mem_image_Ici.1 h).resolve_left hne

/--
theorem `Wbtw.right_mem_affineSpan_of_left_ne` / 定理 `Wbtw.right_mem_affineSpan_of_left_ne`

English:
theorem Wbtw.right_mem_affineSpan_of_left_ne
  given: {x y z : P} (h : Wbtw R x y z) (hne : x != y)
  proof: by
  rcases h.right_mem_image_Ici_of_left_ne hne with ⟨r, ⟨-, rfl⟩⟩
  exact lineMap_mem_affineSpan_pair _ _ _

中文:
定理 Wbtw.right_mem_affineSpan_of_left_ne
  条件: {x y z : P} (h : Wbtw R x y z) (hne : x != y)
  证明: by
  rcases h.right_mem_image_Ici_of_left_ne hne with ⟨r, ⟨-, rfl⟩⟩
  exact lineMap_mem_affineSpan_pair _ _ _

Depends on / 依赖: h.right_mem_image_Ici_of_left_ne, lineMap_mem_affineSpan_pair, right_mem_image_Ici_of_left_ne
-/
theorem Wbtw.right_mem_affineSpan_of_left_ne {x y z : P} (h : Wbtw R x y z) (hne : x != y) :
    z in line[R, x, y] := by
  rcases h.right_mem_image_Ici_of_left_ne hne with ⟨r, ⟨-, rfl⟩⟩
  exact lineMap_mem_affineSpan_pair _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sbtw_iff_left_ne_and_right_mem_image_Ioi` / 定理 `sbtw_iff_left_ne_and_right_mem_image_Ioi`

English:
theorem sbtw_iff_left_ne_and_right_mem_image_Ioi
  given: {x y z : P}
  proof: by
  refine ⟨fun h => ⟨h.left_ne, ?_⟩, fun h => ?_⟩
  · obtain ⟨r, ⟨hr, rfl⟩⟩ := h.wbtw.right_mem_image_Ici_of_left_ne h.left_ne
    rw [Set.mem_Ici] at hr
    rcases hr.lt_or_eq with (hrlt | rfl)
    · exact Set.mem_image_of_mem _ hrlt
    · simp at h
  · rcases h with ⟨hne, r, hr, rfl⟩
    rw [Set

中文:
定理 sbtw_iff_left_ne_and_right_mem_image_Ioi
  条件: {x y z : P}
  证明: by
  refine ⟨fun h => ⟨h.left_ne, ?_⟩, fun h => ?_⟩
  · obtain ⟨r, ⟨hr, rfl⟩⟩ := h.wbtw.right_mem_image_Ici_of_left_ne h.left_ne
    rw [Set.mem_Ici] at hr
    rcases hr.lt_or_eq with (hrlt | rfl)
    · exact Set.mem_image_of_mem _ hrlt
    · simp at h
  · rcases h with ⟨hne, r, hr, rfl⟩
    rw [Set

Depends on / 依赖: Ioi_subset_Ici_self, Or.inr, Set.Ioi_subset_Ici_self, Set.mem_Ici, Set.mem_Ioi, Set.mem_image_of_mem, Set.mem_of_mem_of_subset, h.left_ne, h.wbtw.right_mem_image_Ici_of_left_ne, hne.symm, hr.lt_or_eq, left_ne, lineMap_apply, lt_or_eq, mem_Ici, mem_Ioi, mem_image_of_mem, mem_of_mem_of_subset, right_mem_image_Ici_of_left_ne, vsub_ne_zero
-/
theorem sbtw_iff_left_ne_and_right_mem_image_Ioi {x y z : P} :
    Sbtw R x y z ↔ x != y ∧ z in lineMap x y '' Set.Ioi (1 : R) := by
  refine ⟨fun h => ⟨h.left_ne, ?_⟩, fun h => ?_⟩
  · obtain ⟨r, ⟨hr, rfl⟩⟩ := h.wbtw.right_mem_image_Ici_of_left_ne h.left_ne
    rw [Set.mem_Ici] at hr
    rcases hr.lt_or_eq with (hrlt | rfl)
    · exact Set.mem_image_of_mem _ hrlt
    · simp at h
  · rcases h with ⟨hne, r, hr, rfl⟩
    rw [Set.mem_Ioi] at hr
    refine
      ⟨wbtw_iff_left_eq_or_right_mem_image_Ici.2
          (Or.inr (Set.mem_image_of_mem _ (Set.mem_of_mem_of_subset hr Set.Ioi_subset_Ici_self))),
        hne.symm, ?_⟩
    rw [lineMap_apply]; rw [← @vsub_ne_zero V]; rw [vsub_vadd_eq_vsub_sub]
    nth_rw 1 [← one_smul R (y -ᵥ x)]
    rw [← sub_smul]; rw [smul_ne_zero_iff]; rw [vsub_ne_zero]; rw [sub_ne_zero]
    exact ⟨hr.ne, hne.symm⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Sbtw.right_mem_image_Ioi` / 定理 `Sbtw.right_mem_image_Ioi`

English:
theorem Sbtw.right_mem_image_Ioi
  given: {x y z : P} (h : Sbtw R x y z)
  proof: (sbtw_iff_left_ne_and_right_mem_image_Ioi.1 h).2

中文:
定理 Sbtw.right_mem_image_Ioi
  条件: {x y z : P} (h : Sbtw R x y z)
  证明: (sbtw_iff_left_ne_and_right_mem_image_Ioi.1 h).2

Depends on / 依赖: sbtw_iff_left_ne_and_right_mem_image_Ioi
-/
theorem Sbtw.right_mem_image_Ioi {x y z : P} (h : Sbtw R x y z) :
    z in lineMap x y '' Set.Ioi (1 : R) :=
  (sbtw_iff_left_ne_and_right_mem_image_Ioi.1 h).2

/--
theorem `Sbtw.right_mem_affineSpan` / 定理 `Sbtw.right_mem_affineSpan`

English:
theorem Sbtw.right_mem_affineSpan
  given: {x y z : P} (h : Sbtw R x y z)
  statement: z in line[R, x, y]
  proof: h.wbtw.right_mem_affineSpan_of_left_ne h.left_ne

中文:
定理 Sbtw.right_mem_affineSpan
  条件: {x y z : P} (h : Sbtw R x y z)
  结论: z in line[R, x, y]
  证明: h.wbtw.right_mem_affineSpan_of_left_ne h.left_ne

Depends on / 依赖: h.left_ne, h.wbtw.right_mem_affineSpan_of_left_ne, left_ne, right_mem_affineSpan_of_left_ne
-/
theorem Sbtw.right_mem_affineSpan {x y z : P} (h : Sbtw R x y z) : z in line[R, x, y] :=
  h.wbtw.right_mem_affineSpan_of_left_ne h.left_ne

set_option backward.isDefEq.respectTransparency false in
/--
theorem `wbtw_iff_right_eq_or_left_mem_image_Ici` / 定理 `wbtw_iff_right_eq_or_left_mem_image_Ici`

English:
theorem wbtw_iff_right_eq_or_left_mem_image_Ici
  given: {x y z : P}
  proof: by
  rw [wbtw_comm]; rw [wbtw_iff_left_eq_or_right_mem_image_Ici]

中文:
定理 wbtw_iff_right_eq_or_left_mem_image_Ici
  条件: {x y z : P}
  证明: by
  rw [wbtw_comm]; rw [wbtw_iff_left_eq_or_right_mem_image_Ici]

Depends on / 依赖: wbtw_comm, wbtw_iff_left_eq_or_right_mem_image_Ici
-/
theorem wbtw_iff_right_eq_or_left_mem_image_Ici {x y z : P} :
    Wbtw R x y z ↔ z = y ∨ x in lineMap z y '' Set.Ici (1 : R) := by
  rw [wbtw_comm]; rw [wbtw_iff_left_eq_or_right_mem_image_Ici]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Wbtw.left_mem_image_Ici_of_right_ne` / 定理 `Wbtw.left_mem_image_Ici_of_right_ne`

English:
theorem Wbtw.left_mem_image_Ici_of_right_ne
  given: {x y z : P} (h : Wbtw R x y z) (hne : z != y)
  proof: h.symm.right_mem_image_Ici_of_left_ne hne

中文:
定理 Wbtw.left_mem_image_Ici_of_right_ne
  条件: {x y z : P} (h : Wbtw R x y z) (hne : z != y)
  证明: h.symm.right_mem_image_Ici_of_left_ne hne

Depends on / 依赖: h.symm.right_mem_image_Ici_of_left_ne, right_mem_image_Ici_of_left_ne
-/
theorem Wbtw.left_mem_image_Ici_of_right_ne {x y z : P} (h : Wbtw R x y z) (hne : z != y) :
    x in lineMap z y '' Set.Ici (1 : R) :=
  h.symm.right_mem_image_Ici_of_left_ne hne

/--
theorem `Wbtw.left_mem_affineSpan_of_right_ne` / 定理 `Wbtw.left_mem_affineSpan_of_right_ne`

English:
theorem Wbtw.left_mem_affineSpan_of_right_ne
  given: {x y z : P} (h : Wbtw R x y z) (hne : z != y)
  proof: h.symm.right_mem_affineSpan_of_left_ne hne

中文:
定理 Wbtw.left_mem_affineSpan_of_right_ne
  条件: {x y z : P} (h : Wbtw R x y z) (hne : z != y)
  证明: h.symm.right_mem_affineSpan_of_left_ne hne

Depends on / 依赖: h.symm.right_mem_affineSpan_of_left_ne, right_mem_affineSpan_of_left_ne
-/
theorem Wbtw.left_mem_affineSpan_of_right_ne {x y z : P} (h : Wbtw R x y z) (hne : z != y) :
    x in line[R, z, y] :=
  h.symm.right_mem_affineSpan_of_left_ne hne

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sbtw_iff_right_ne_and_left_mem_image_Ioi` / 定理 `sbtw_iff_right_ne_and_left_mem_image_Ioi`

English:
theorem sbtw_iff_right_ne_and_left_mem_image_Ioi
  given: {x y z : P}
  proof: by
  rw [sbtw_comm]; rw [sbtw_iff_left_ne_and_right_mem_image_Ioi]

中文:
定理 sbtw_iff_right_ne_and_left_mem_image_Ioi
  条件: {x y z : P}
  证明: by
  rw [sbtw_comm]; rw [sbtw_iff_left_ne_and_right_mem_image_Ioi]

Depends on / 依赖: sbtw_comm, sbtw_iff_left_ne_and_right_mem_image_Ioi
-/
theorem sbtw_iff_right_ne_and_left_mem_image_Ioi {x y z : P} :
    Sbtw R x y z ↔ z != y ∧ x in lineMap z y '' Set.Ioi (1 : R) := by
  rw [sbtw_comm]; rw [sbtw_iff_left_ne_and_right_mem_image_Ioi]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Sbtw.left_mem_image_Ioi` / 定理 `Sbtw.left_mem_image_Ioi`

English:
theorem Sbtw.left_mem_image_Ioi
  given: {x y z : P} (h : Sbtw R x y z)
  proof: h.symm.right_mem_image_Ioi

中文:
定理 Sbtw.left_mem_image_Ioi
  条件: {x y z : P} (h : Sbtw R x y z)
  证明: h.symm.right_mem_image_Ioi

Depends on / 依赖: h.symm.right_mem_image_Ioi, right_mem_image_Ioi
-/
theorem Sbtw.left_mem_image_Ioi {x y z : P} (h : Sbtw R x y z) :
    x in lineMap z y '' Set.Ioi (1 : R) :=
  h.symm.right_mem_image_Ioi

/--
theorem `Sbtw.left_mem_affineSpan` / 定理 `Sbtw.left_mem_affineSpan`

English:
theorem Sbtw.left_mem_affineSpan
  given: {x y z : P} (h : Sbtw R x y z)
  statement: x in line[R, z, y]
  proof: h.symm.right_mem_affineSpan

omit [IsStrictOrderedRing R] in

中文:
定理 Sbtw.left_mem_affineSpan
  条件: {x y z : P} (h : Sbtw R x y z)
  结论: x in line[R, z, y]
  证明: h.symm.right_mem_affineSpan

omit [IsStrictOrderedRing R] in

Depends on / 依赖: h.symm.right_mem_affineSpan, right_mem_affineSpan
-/
theorem Sbtw.left_mem_affineSpan {x y z : P} (h : Sbtw R x y z) : x in line[R, z, y] :=
  h.symm.right_mem_affineSpan

omit [IsStrictOrderedRing R] in
/--
lemma `AffineSubspace.right_mem_of_wbtw` / 引理 `AffineSubspace.right_mem_of_wbtw`

English:
lemma AffineSubspace.right_mem_of_wbtw
  statement: {s : AffineSubspace R P} (hxyz : Wbtw R x y z) (hx : x in s)
  proof: by
  obtain ⟨ε, -, rfl⟩ := hxyz
  have hε : ε != 0 := by rintro rfl; simp at hxy
  simpa [hε] using lineMap_mem ε⁻¹ hx hy

中文:
引理 AffineSubspace.right_mem_of_wbtw
  结论: {s : AffineSubspace R P} (hxyz : Wbtw R x y z) (hx : x in s)
  证明: by
  obtain ⟨ε, -, rfl⟩ := hxyz
  have hε : ε != 0 := by rintro rfl; simp at hxy
  simpa [hε] using lineMap_mem ε⁻¹ hx hy

Depends on / 依赖: lineMap_mem
-/
lemma AffineSubspace.right_mem_of_wbtw {s : AffineSubspace R P} (hxyz : Wbtw R x y z) (hx : x in s)
    (hy : y in s) (hxy : x != y) : z in s := by
  obtain ⟨ε, -, rfl⟩ := hxyz
  have hε : ε != 0 := by rintro rfl; simp at hxy
  simpa [hε] using lineMap_mem ε⁻¹ hx hy

/--
theorem `wbtw_smul_vadd_smul_vadd_of_nonneg_of_le` / 定理 `wbtw_smul_vadd_smul_vadd_of_nonneg_of_le`

English:
theorem wbtw_smul_vadd_smul_vadd_of_nonneg_of_le
  statement: (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 <= r₁)
  proof: by
  refine ⟨r₁ / r₂, ⟨div_nonneg hr₁ (hr₁.trans hr₂), div_le_one_of_le₀ hr₂ (hr₁.trans hr₂)⟩, ?_⟩
  by_cases h : r₁ = 0; · simp [h]
  simp [lineMap_apply, smul_smul, ((hr₁.lt_of_ne' h).trans_le hr₂).ne.symm]

中文:
定理 wbtw_smul_vadd_smul_vadd_of_nonneg_of_le
  结论: (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 <= r₁)
  证明: by
  refine ⟨r₁ / r₂, ⟨div_nonneg hr₁ (hr₁.trans hr₂), div_le_one_of_le₀ hr₂ (hr₁.trans hr₂)⟩, ?_⟩
  by_cases h : r₁ = 0; · simp [h]
  simp [lineMap_apply, smul_smul, ((hr₁.lt_of_ne' h).trans_le hr₂).ne.symm]

Depends on / 依赖: div_nonneg, lineMap_apply, lt_of_ne, ne.symm, smul_smul, trans_le
-/
theorem wbtw_smul_vadd_smul_vadd_of_nonneg_of_le (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 <= r₁)
    (hr₂ : r₁ <= r₂) : Wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x) := by
  refine ⟨r₁ / r₂, ⟨div_nonneg hr₁ (hr₁.trans hr₂), div_le_one_of_le₀ hr₂ (hr₁.trans hr₂)⟩, ?_⟩
  by_cases h : r₁ = 0; · simp [h]
  simp [lineMap_apply, smul_smul, ((hr₁.lt_of_ne' h).trans_le hr₂).ne.symm]

/--
theorem `wbtw_or_wbtw_smul_vadd_of_nonneg` / 定理 `wbtw_or_wbtw_smul_vadd_of_nonneg`

English:
theorem wbtw_or_wbtw_smul_vadd_of_nonneg
  given: (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 <= r₁) (hr₂ : 0 <= r₂)
  proof: by
  rcases le_total r₁ r₂ with (h | h)
  · exact Or.inl (wbtw_smul_vadd_smul_vadd_of_nonneg_of_le x v hr₁ h)
  · exact Or.inr (wbtw_smul_vadd_smul_vadd_of_nonneg_of_le x v hr₂ h)

中文:
定理 wbtw_or_wbtw_smul_vadd_of_nonneg
  条件: (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 <= r₁) (hr₂ : 0 <= r₂)
  证明: by
  rcases le_total r₁ r₂ with (h | h)
  · exact Or.inl (wbtw_smul_vadd_smul_vadd_of_nonneg_of_le x v hr₁ h)
  · exact Or.inr (wbtw_smul_vadd_smul_vadd_of_nonneg_of_le x v hr₂ h)

Depends on / 依赖: Or.inl, Or.inr, le_total, wbtw_smul_vadd_smul_vadd_of_nonneg_of_le
-/
theorem wbtw_or_wbtw_smul_vadd_of_nonneg (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 <= r₁) (hr₂ : 0 <= r₂) :
    Wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x) ∨ Wbtw R x (r₂ • v +ᵥ x) (r₁ • v +ᵥ x) := by
  rcases le_total r₁ r₂ with (h | h)
  · exact Or.inl (wbtw_smul_vadd_smul_vadd_of_nonneg_of_le x v hr₁ h)
  · exact Or.inr (wbtw_smul_vadd_smul_vadd_of_nonneg_of_le x v hr₂ h)

/--
theorem `wbtw_smul_vadd_smul_vadd_of_nonpos_of_le` / 定理 `wbtw_smul_vadd_smul_vadd_of_nonpos_of_le`

English:
theorem wbtw_smul_vadd_smul_vadd_of_nonpos_of_le
  statement: (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ <= 0)
  proof: by
  convert!
    wbtw_smul_vadd_smul_vadd_of_nonneg_of_le x (-v) (Left.nonneg_neg_iff.2 hr₁)
      (neg_le_neg_iff.2 hr₂) using
    1 <;>
    rw [neg_smul_neg]

中文:
定理 wbtw_smul_vadd_smul_vadd_of_nonpos_of_le
  结论: (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ <= 0)
  证明: by
  convert!
    wbtw_smul_vadd_smul_vadd_of_nonneg_of_le x (-v) (Left.nonneg_neg_iff.2 hr₁)
      (neg_le_neg_iff.2 hr₂) using
    1 <;>
    rw [neg_smul_neg]

Depends on / 依赖: Left.nonneg_neg_iff, convert, neg_le_neg_iff, neg_smul_neg, nonneg_neg_iff, wbtw_smul_vadd_smul_vadd_of_nonneg_of_le
-/
theorem wbtw_smul_vadd_smul_vadd_of_nonpos_of_le (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ <= 0)
    (hr₂ : r₂ <= r₁) : Wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x) := by
  convert!
    wbtw_smul_vadd_smul_vadd_of_nonneg_of_le x (-v) (Left.nonneg_neg_iff.2 hr₁)
      (neg_le_neg_iff.2 hr₂) using
    1 <;>
    rw [neg_smul_neg]

/--
theorem `wbtw_or_wbtw_smul_vadd_of_nonpos` / 定理 `wbtw_or_wbtw_smul_vadd_of_nonpos`

English:
theorem wbtw_or_wbtw_smul_vadd_of_nonpos
  given: (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ <= 0) (hr₂ : r₂ <= 0)
  proof: by
  rcases le_total r₁ r₂ with (h | h)
  · exact Or.inr (wbtw_smul_vadd_smul_vadd_of_nonpos_of_le x v hr₂ h)
  · exact Or.inl (wbtw_smul_vadd_smul_vadd_of_nonpos_of_le x v hr₁ h)

中文:
定理 wbtw_or_wbtw_smul_vadd_of_nonpos
  条件: (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ <= 0) (hr₂ : r₂ <= 0)
  证明: by
  rcases le_total r₁ r₂ with (h | h)
  · exact Or.inr (wbtw_smul_vadd_smul_vadd_of_nonpos_of_le x v hr₂ h)
  · exact Or.inl (wbtw_smul_vadd_smul_vadd_of_nonpos_of_le x v hr₁ h)

Depends on / 依赖: Or.inl, Or.inr, le_total, wbtw_smul_vadd_smul_vadd_of_nonpos_of_le
-/
theorem wbtw_or_wbtw_smul_vadd_of_nonpos (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ <= 0) (hr₂ : r₂ <= 0) :
    Wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x) ∨ Wbtw R x (r₂ • v +ᵥ x) (r₁ • v +ᵥ x) := by
  rcases le_total r₁ r₂ with (h | h)
  · exact Or.inr (wbtw_smul_vadd_smul_vadd_of_nonpos_of_le x v hr₂ h)
  · exact Or.inl (wbtw_smul_vadd_smul_vadd_of_nonpos_of_le x v hr₁ h)

/--
theorem `wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg` / 定理 `wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg`

English:
theorem wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg
  statement: (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ <= 0)
  proof: by
  convert!
    wbtw_smul_vadd_smul_vadd_of_nonneg_of_le (r₁ • v +ᵥ x) v (Left.nonneg_neg_iff.2 hr₁)
      (neg_le_sub_iff_le_add.2 ((le_add_iff_nonneg_left r₁).2 hr₂)) using
    1 <;>
    simp [sub_smul, ← add_vadd]

中文:
定理 wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg
  结论: (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ <= 0)
  证明: by
  convert!
    wbtw_smul_vadd_smul_vadd_of_nonneg_of_le (r₁ • v +ᵥ x) v (Left.nonneg_neg_iff.2 hr₁)
      (neg_le_sub_iff_le_add.2 ((le_add_iff_nonneg_left r₁).2 hr₂)) using
    1 <;>
    simp [sub_smul, ← add_vadd]

Depends on / 依赖: Left.nonneg_neg_iff, add_vadd, convert, le_add_iff_nonneg_left, neg_le_sub_iff_le_add, nonneg_neg_iff, sub_smul, wbtw_smul_vadd_smul_vadd_of_nonneg_of_le
-/
theorem wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ <= 0)
    (hr₂ : 0 <= r₂) : Wbtw R (r₁ • v +ᵥ x) x (r₂ • v +ᵥ x) := by
  convert!
    wbtw_smul_vadd_smul_vadd_of_nonneg_of_le (r₁ • v +ᵥ x) v (Left.nonneg_neg_iff.2 hr₁)
      (neg_le_sub_iff_le_add.2 ((le_add_iff_nonneg_left r₁).2 hr₂)) using
    1 <;>
    simp [sub_smul, ← add_vadd]

/--
theorem `wbtw_smul_vadd_smul_vadd_of_nonneg_of_nonpos` / 定理 `wbtw_smul_vadd_smul_vadd_of_nonneg_of_nonpos`

English:
theorem wbtw_smul_vadd_smul_vadd_of_nonneg_of_nonpos
  statement: (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 <= r₁)
  proof: by
  rw [wbtw_comm]
  exact wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg x v hr₂ hr₁

中文:
定理 wbtw_smul_vadd_smul_vadd_of_nonneg_of_nonpos
  结论: (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 <= r₁)
  证明: by
  rw [wbtw_comm]
  exact wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg x v hr₂ hr₁

Depends on / 依赖: wbtw_comm, wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg
-/
theorem wbtw_smul_vadd_smul_vadd_of_nonneg_of_nonpos (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 <= r₁)
    (hr₂ : r₂ <= 0) : Wbtw R (r₁ • v +ᵥ x) x (r₂ • v +ᵥ x) := by
  rw [wbtw_comm]
  exact wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg x v hr₂ hr₁

/--
theorem `Wbtw.trans_left_right` / 定理 `Wbtw.trans_left_right`

English:
theorem Wbtw.trans_left_right
  given: {w x y z : P} (h₁ : Wbtw R w y z) (h₂ : Wbtw R w x y)
  proof: by
  rcases h₁ with ⟨t₁, ht₁, rfl⟩
  rcases h₂ with ⟨t₂, ht₂, rfl⟩
  refine
    ⟨(t₁ - t₂ * t₁) / (1 - t₂ * t₁),
      ⟨div_nonneg (sub_nonneg.2 (mul_le_of_le_one_left ht₁.1 ht₂.2))
          (sub_nonneg.2 (mul_le_one₀ ht₂.2 ht₁.1 ht₁.2)), div_le_one_of_le₀
            (sub_le_sub_right ht₁.2 _) (su

中文:
定理 Wbtw.trans_left_right
  条件: {w x y z : P} (h₁ : Wbtw R w y z) (h₂ : Wbtw R w x y)
  证明: by
  rcases h₁ with ⟨t₁, ht₁, rfl⟩
  rcases h₂ with ⟨t₂, ht₂, rfl⟩
  refine
    ⟨(t₁ - t₂ * t₁) / (1 - t₂ * t₁),
      ⟨div_nonneg (sub_nonneg.2 (mul_le_of_le_one_left ht₁.1 ht₂.2))
          (sub_nonneg.2 (mul_le_one₀ ht₂.2 ht₁.1 ht₁.2)), div_le_one_of_le₀
            (sub_le_sub_right ht₁.2 _) (su

Depends on / 依赖: add_smul, add_vadd, div_mul_eq_mul_div, div_nonneg, div_sub_div_same, lineMap_apply, mul_le_of_le_one_left, nth_rw, smul_smul, smul_sub, sub_le_sub_right, sub_nonneg, sub_smul, vadd_right_cancel_iff, vadd_vsub, vsub_vadd_eq_vsub_sub
-/
theorem Wbtw.trans_left_right {w x y z : P} (h₁ : Wbtw R w y z) (h₂ : Wbtw R w x y) :
    Wbtw R x y z := by
  rcases h₁ with ⟨t₁, ht₁, rfl⟩
  rcases h₂ with ⟨t₂, ht₂, rfl⟩
  refine
    ⟨(t₁ - t₂ * t₁) / (1 - t₂ * t₁),
      ⟨div_nonneg (sub_nonneg.2 (mul_le_of_le_one_left ht₁.1 ht₂.2))
          (sub_nonneg.2 (mul_le_one₀ ht₂.2 ht₁.1 ht₁.2)), div_le_one_of_le₀
            (sub_le_sub_right ht₁.2 _) (sub_nonneg.2 (mul_le_one₀ ht₂.2 ht₁.1 ht₁.2))⟩,
      ?_⟩
  simp only [lineMap_apply, smul_smul, ← add_vadd, vsub_vadd_eq_vsub_sub, smul_sub, ← sub_smul,
    ← add_smul, vadd_vsub, vadd_right_cancel_iff, div_mul_eq_mul_div, div_sub_div_same]
  nth_rw 1 [← mul_one (t₁ - t₂ * t₁)]
  rw [← mul_sub]; rw [mul_div_assoc]
  by_cases h : 1 - t₂ * t₁ = 0
  · rw [sub_eq_zero, eq_comm] at h
    rw [h]
    suffices t₁ = 1 by simp [this]
    exact
      eq_of_le_of_not_lt ht₁.2 fun ht₁lt =>
        (mul_lt_one_of_nonneg_of_lt_one_right ht₂.2 ht₁.1 ht₁lt).ne h
  · rw [div_self h]
    ring_nf

/--
theorem `Wbtw.trans_right_left` / 定理 `Wbtw.trans_right_left`

English:
theorem Wbtw.trans_right_left
  given: {w x y z : P} (h₁ : Wbtw R w x z) (h₂ : Wbtw R x y z)
  proof: by
  rw [wbtw_comm] at *
  exact h₁.trans_left_right h₂

中文:
定理 Wbtw.trans_right_left
  条件: {w x y z : P} (h₁ : Wbtw R w x z) (h₂ : Wbtw R x y z)
  证明: by
  rw [wbtw_comm] at *
  exact h₁.trans_left_right h₂

Depends on / 依赖: trans_left_right, wbtw_comm
-/
theorem Wbtw.trans_right_left {w x y z : P} (h₁ : Wbtw R w x z) (h₂ : Wbtw R x y z) :
    Wbtw R w x y := by
  rw [wbtw_comm] at *
  exact h₁.trans_left_right h₂

/--
theorem `Sbtw.trans_left_right` / 定理 `Sbtw.trans_left_right`

English:
theorem Sbtw.trans_left_right
  given: {w x y z : P} (h₁ : Sbtw R w y z) (h₂ : Sbtw R w x y)
  proof: ⟨h₁.wbtw.trans_left_right h₂.wbtw, h₂.right_ne, h₁.ne_right⟩

中文:
定理 Sbtw.trans_left_right
  条件: {w x y z : P} (h₁ : Sbtw R w y z) (h₂ : Sbtw R w x y)
  证明: ⟨h₁.wbtw.trans_left_right h₂.wbtw, h₂.right_ne, h₁.ne_right⟩

Depends on / 依赖: ne_right, right_ne, trans_left_right, wbtw.trans_left_right
-/
theorem Sbtw.trans_left_right {w x y z : P} (h₁ : Sbtw R w y z) (h₂ : Sbtw R w x y) :
    Sbtw R x y z :=
  ⟨h₁.wbtw.trans_left_right h₂.wbtw, h₂.right_ne, h₁.ne_right⟩

/--
theorem `Sbtw.trans_right_left` / 定理 `Sbtw.trans_right_left`

English:
theorem Sbtw.trans_right_left
  given: {w x y z : P} (h₁ : Sbtw R w x z) (h₂ : Sbtw R x y z)
  proof: ⟨h₁.wbtw.trans_right_left h₂.wbtw, h₁.ne_left, h₂.left_ne⟩

中文:
定理 Sbtw.trans_right_left
  条件: {w x y z : P} (h₁ : Sbtw R w x z) (h₂ : Sbtw R x y z)
  证明: ⟨h₁.wbtw.trans_right_left h₂.wbtw, h₁.ne_left, h₂.left_ne⟩

Depends on / 依赖: left_ne, ne_left, trans_right_left, wbtw.trans_right_left
-/
theorem Sbtw.trans_right_left {w x y z : P} (h₁ : Sbtw R w x z) (h₂ : Sbtw R x y z) :
    Sbtw R w x y :=
  ⟨h₁.wbtw.trans_right_left h₂.wbtw, h₁.ne_left, h₂.left_ne⟩

/--
theorem `Wbtw.trans_expand_left` / 定理 `Wbtw.trans_expand_left`

English:
theorem Wbtw.trans_expand_left
  statement: {w x y z : P} (h₁ : Wbtw R w x y) (h₂ : Wbtw R x y z)
  proof: by
  rcases h₁ with ⟨t₁, ht₁, hx⟩
  rcases h₂ with ⟨t₂, ht₂, hy⟩
  refine ⟨t₁ * t₂ / (1 - t₁ + t₁ * t₂), ?_, ?_⟩
  · constructor
    · apply div_nonneg (mul_nonneg ht₁.1 ht₂.1)
      nlinarith [ht₁.1, ht₁.2, ht₂.1, ht₂.2]
    · apply div_le_one_of_le₀
      · grind
      · nlinarith [ht₁.1, ht₁.2, h

中文:
定理 Wbtw.trans_expand_left
  结论: {w x y z : P} (h₁ : Wbtw R w x y) (h₂ : Wbtw R x y z)
  证明: by
  rcases h₁ with ⟨t₁, ht₁, hx⟩
  rcases h₂ with ⟨t₂, ht₂, hy⟩
  refine ⟨t₁ * t₂ / (1 - t₁ + t₁ * t₂), ?_, ?_⟩
  · constructor
    · apply div_nonneg (mul_nonneg ht₁.1 ht₂.1)
      nlinarith [ht₁.1, ht₁.2, ht₂.1, ht₂.2]
    · apply div_le_one_of_le₀
      · grind
      · nlinarith [ht₁.1, ht₁.2, h

Depends on / 依赖: contrapose, div_nonneg, h_denom, h_ne, lineMap_apply, lineMap_apply_one, mul_nonneg
-/
theorem Wbtw.trans_expand_left {w x y z : P} (h₁ : Wbtw R w x y) (h₂ : Wbtw R x y z)
    (h_ne : x != y) : Wbtw R w x z := by
  rcases h₁ with ⟨t₁, ht₁, hx⟩
  rcases h₂ with ⟨t₂, ht₂, hy⟩
  refine ⟨t₁ * t₂ / (1 - t₁ + t₁ * t₂), ?_, ?_⟩
  · constructor
    · apply div_nonneg (mul_nonneg ht₁.1 ht₂.1)
      nlinarith [ht₁.1, ht₁.2, ht₂.1, ht₂.2]
    · apply div_le_one_of_le₀
      · grind
      · nlinarith [ht₁.1, ht₁.2, ht₂.1, ht₂.2]
  have h_denom : 1 - t₁ + t₁ * t₂ != 0 := by
    contrapose h_ne
    have h1 : t₁ = 1 := by nlinarith [ht₁.1, ht₁.2, ht₂.1, ht₂.2]
    rw [← hx]; rw [h1]; rw [lineMap_apply_one]
  rw [← hy]; rw [lineMap_apply]; rw [lineMap_apply]; rw [eq_comm]; rw [eq_vadd_iff_vsub_eq] at hx
  rw [lineMap_apply]; rw [eq_comm]; rw [eq_vadd_iff_vsub_eq]; rw [div_eq_mul_inv]; rw [mul_comm]; rw [mul_smul]; rw [eq_inv_smul_iff₀ h_denom]; rw [add_smul]; rw [sub_smul]; rw [one_smul]
  nth_rw 1 [hx]
  rw [← smul_sub]; rw [mul_smul]; rw [mul_smul]; rw [vsub_sub_vsub_cancel_right]; rw [vadd_vsub]; rw [← smul_assoc]; rw [← smul_assoc]; rw [← smul_assoc]; rw [← smul_add]; rw [vsub_add_vsub_cancel]

/--
theorem `Wbtw.trans_expand_right` / 定理 `Wbtw.trans_expand_right`

English:
theorem Wbtw.trans_expand_right
  statement: {w x y z : P} (h₁ : Wbtw R w x y) (h₂ : Wbtw R x y z)
  proof: Wbtw.trans_right (h₁.trans_expand_left h₂ h_ne) h₂

中文:
定理 Wbtw.trans_expand_right
  结论: {w x y z : P} (h₁ : Wbtw R w x y) (h₂ : Wbtw R x y z)
  证明: Wbtw.trans_right (h₁.trans_expand_left h₂ h_ne) h₂

Depends on / 依赖: Wbtw.trans_right, h_ne, trans_expand_left, trans_right
-/
theorem Wbtw.trans_expand_right {w x y z : P} (h₁ : Wbtw R w x y) (h₂ : Wbtw R x y z)
    (h_ne : x != y) : Wbtw R w y z := Wbtw.trans_right (h₁.trans_expand_left h₂ h_ne) h₂

/--
theorem `Sbtw.trans_expand_left` / 定理 `Sbtw.trans_expand_left`

English:
theorem Sbtw.trans_expand_left
  given: {w x y z : P} (h₁ : Sbtw R w x y) (h₂ : Sbtw R x y z)
  proof: ⟨Wbtw.trans_expand_left h₁.wbtw h₂.wbtw h₂.left_ne, h₁.left_ne.symm, h₂.left_ne_right⟩

中文:
定理 Sbtw.trans_expand_left
  条件: {w x y z : P} (h₁ : Sbtw R w x y) (h₂ : Sbtw R x y z)
  证明: ⟨Wbtw.trans_expand_left h₁.wbtw h₂.wbtw h₂.left_ne, h₁.left_ne.symm, h₂.left_ne_right⟩

Depends on / 依赖: Wbtw.trans_expand_left, left_ne, left_ne.symm, left_ne_right, trans_expand_left
-/
theorem Sbtw.trans_expand_left {w x y z : P} (h₁ : Sbtw R w x y) (h₂ : Sbtw R x y z) :
    Sbtw R w x z :=
  ⟨Wbtw.trans_expand_left h₁.wbtw h₂.wbtw h₂.left_ne, h₁.left_ne.symm, h₂.left_ne_right⟩

/--
theorem `Sbtw.trans_expand_right` / 定理 `Sbtw.trans_expand_right`

English:
theorem Sbtw.trans_expand_right
  given: {w x y z : P} (h₁ : Sbtw R w x y) (h₂ : Sbtw R x y z)
  proof: Sbtw.trans_right (h₁.trans_expand_left h₂) h₂

omit [IsStrictOrderedRing R] in

中文:
定理 Sbtw.trans_expand_right
  条件: {w x y z : P} (h₁ : Sbtw R w x y) (h₂ : Sbtw R x y z)
  证明: Sbtw.trans_right (h₁.trans_expand_left h₂) h₂

omit [IsStrictOrderedRing R] in

Depends on / 依赖: Sbtw.trans_right, trans_expand_left, trans_right
-/
theorem Sbtw.trans_expand_right {w x y z : P} (h₁ : Sbtw R w x y) (h₂ : Sbtw R x y z) :
    Sbtw R w y z := Sbtw.trans_right (h₁.trans_expand_left h₂) h₂

omit [IsStrictOrderedRing R] in
/--
theorem `Wbtw.collinear` / 定理 `Wbtw.collinear`

English:
theorem Wbtw.collinear
  given: {x y z : P} (h : Wbtw R x y z)
  statement: Collinear R ({x, y, z} : Set P)
  proof: by
  have : {y, x, z} = {x, y, z} := Set.insert_comm y x {z}
  simpa [this] using collinear_insert_of_mem_affineSpan_pair (mem_affineSpan h)

中文:
定理 Wbtw.collinear
  条件: {x y z : P} (h : Wbtw R x y z)
  结论: Collinear R ({x, y, z} : Set P)
  证明: by
  have : {y, x, z} = {x, y, z} := Set.insert_comm y x {z}
  simpa [this] using collinear_insert_of_mem_affineSpan_pair (mem_affineSpan h)

Depends on / 依赖: Set.insert_comm, collinear_insert_of_mem_affineSpan_pair, insert_comm, mem_affineSpan
-/
theorem Wbtw.collinear {x y z : P} (h : Wbtw R x y z) : Collinear R ({x, y, z} : Set P) := by
  have : {y, x, z} = {x, y, z} := Set.insert_comm y x {z}
  simpa [this] using collinear_insert_of_mem_affineSpan_pair (mem_affineSpan h)

/--
theorem `Collinear.wbtw_or_wbtw_or_wbtw` / 定理 `Collinear.wbtw_or_wbtw_or_wbtw`

English:
theorem Collinear.wbtw_or_wbtw_or_wbtw
  given: {x y z : P} (h : Collinear R ({x, y, z} : Set P))
  proof: by
  rw [collinear_iff_of_mem (Set.mem_insert _ _)] at h
  rcases h with ⟨v, h⟩
  simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  have hy := h y (Or.inr (Or.inl rfl))
  have hz := h z (Or.inr (Or.inr rfl))
  rcases hy with ⟨ty, rfl⟩
  rcases hz with ⟨tz, rfl⟩
  rcases lt_trichotomy ty 0 w

中文:
定理 Collinear.wbtw_or_wbtw_or_wbtw
  条件: {x y z : P} (h : Collinear R ({x, y, z} : Set P))
  证明: by
  rw [collinear_iff_of_mem (Set.mem_insert _ _)] at h
  rcases h with ⟨v, h⟩
  simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  have hy := h y (Or.inr (Or.inl rfl))
  have hz := h z (Or.inr (Or.inr rfl))
  rcases hy with ⟨ty, rfl⟩
  rcases hz with ⟨tz, rfl⟩
  rcases lt_trichotomy ty 0 w

Depends on / 依赖: Or.inl, Or.inr, Set.mem_insert, Set.mem_insert_iff, Set.mem_singleton_iff, collinear_iff_of_mem, hy0.le, hz0.le, lt_trichotomy, mem_insert, mem_insert_iff, mem_singleton_iff, or_assoc, simp_rw, wbtw_comm, wbtw_or_wbtw_smul_vadd_of_nonpos
-/
theorem Collinear.wbtw_or_wbtw_or_wbtw {x y z : P} (h : Collinear R ({x, y, z} : Set P)) :
    Wbtw R x y z ∨ Wbtw R y z x ∨ Wbtw R z x y := by
  rw [collinear_iff_of_mem (Set.mem_insert _ _)] at h
  rcases h with ⟨v, h⟩
  simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  have hy := h y (Or.inr (Or.inl rfl))
  have hz := h z (Or.inr (Or.inr rfl))
  rcases hy with ⟨ty, rfl⟩
  rcases hz with ⟨tz, rfl⟩
  rcases lt_trichotomy ty 0 with (hy0 | rfl | hy0)
  · rcases lt_trichotomy tz 0 with (hz0 | rfl | hz0)
    · rw [wbtw_comm (z := x)]
      rw [← or_assoc]
      exact Or.inl (wbtw_or_wbtw_smul_vadd_of_nonpos _ _ hy0.le hz0.le)
    · simp
    · exact Or.inr (Or.inr (wbtw_smul_vadd_smul_vadd_of_nonneg_of_nonpos _ _ hz0.le hy0.le))
  · simp
  · rcases lt_trichotomy tz 0 with (hz0 | rfl | hz0)
    · refine Or.inr (Or.inr (wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg _ _ hz0.le hy0.le))
    · simp
    · rw [wbtw_comm (z := x)]
      rw [← or_assoc]
      exact Or.inl (wbtw_or_wbtw_smul_vadd_of_nonneg _ _ hy0.le hz0.le)

/--
theorem `wbtw_iff_sameRay_vsub` / 定理 `wbtw_iff_sameRay_vsub`

English:
theorem wbtw_iff_sameRay_vsub
  given: {x y z : P}
  statement: Wbtw R x y z ↔ SameRay R (y -ᵥ x) (z -ᵥ y)
  proof: by
  simp [← wbtw_vsub_const_iff x, ← mem_segment_iff_wbtw, mem_segment_iff_sameRay]

中文:
定理 wbtw_iff_sameRay_vsub
  条件: {x y z : P}
  结论: Wbtw R x y z ↔ SameRay R (y -ᵥ x) (z -ᵥ y)
  证明: by
  simp [← wbtw_vsub_const_iff x, ← mem_segment_iff_wbtw, mem_segment_iff_sameRay]

Depends on / 依赖: mem_segment_iff_sameRay, mem_segment_iff_wbtw, wbtw_vsub_const_iff
-/
theorem wbtw_iff_sameRay_vsub {x y z : P} : Wbtw R x y z ↔ SameRay R (y -ᵥ x) (z -ᵥ y) := by
  simp [← wbtw_vsub_const_iff x, ← mem_segment_iff_wbtw, mem_segment_iff_sameRay]

/--
lemma `wbtw_total_of_sameRay_vsub_left` / 引理 `wbtw_total_of_sameRay_vsub_left`

English:
lemma wbtw_total_of_sameRay_vsub_left
  given: {x y z : P} (h : SameRay R (y -ᵥ x) (z -ᵥ x))
  proof: by
  rcases h with (h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩)
  · simp_all
  · simp_all
  wlog hr : r₂ <= r₁ generalizing r₁ r₂ y z
  · rw [or_comm]
    apply this r₂ r₁ hr₂ hr₁ h.symm (Std.le_of_not_ge hr)
  left
  refine ⟨r₂ / r₁, ⟨div_nonneg hr₂.le hr₁.le, div_le_one_of_le₀ hr hr₁.le⟩, ?_⟩
  have h' : y = r

中文:
引理 wbtw_total_of_sameRay_vsub_left
  条件: {x y z : P} (h : SameRay R (y -ᵥ x) (z -ᵥ x))
  证明: by
  rcases h with (h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩)
  · simp_all
  · simp_all
  wlog hr : r₂ <= r₁ generalizing r₁ r₂ y z
  · rw [or_comm]
    apply this r₂ r₁ hr₂ hr₁ h.symm (Std.le_of_not_ge hr)
  left
  refine ⟨r₂ / r₁, ⟨div_nonneg hr₂.le hr₁.le, div_le_one_of_le₀ hr hr₁.le⟩, ?_⟩
  have h' : y = r

Depends on / 依赖: Std.le_of_not_ge, add_zero, div_nonneg, eq_vadd_iff_vsub_eq, generalizing, h.symm, le_of_not_ge, lineMap_apply, or_comm, ring_nf, smul_smul, vadd_vsub_assoc, vsub_self
-/
lemma wbtw_total_of_sameRay_vsub_left {x y z : P} (h : SameRay R (y -ᵥ x) (z -ᵥ x)) :
    Wbtw R x y z ∨ Wbtw R x z y := by
  rcases h with (h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩)
  · simp_all
  · simp_all
  wlog hr : r₂ <= r₁ generalizing r₁ r₂ y z
  · rw [or_comm]
    apply this r₂ r₁ hr₂ hr₁ h.symm (Std.le_of_not_ge hr)
  left
  refine ⟨r₂ / r₁, ⟨div_nonneg hr₂.le hr₁.le, div_le_one_of_le₀ hr hr₁.le⟩, ?_⟩
  have h' : y = r₁⁻¹ • r₂ • (z -ᵥ x) +ᵥ x := by simp [← h, hr₁.ne']
  simp only [lineMap_apply, h', vadd_vsub_assoc, smul_smul, eq_vadd_iff_vsub_eq, vsub_self,
    add_zero]
  ring_nf

/--
theorem `AffineIndependent.not_wbtw_of_injective` / 定理 `AffineIndependent.not_wbtw_of_injective`

English:
theorem AffineIndependent.not_wbtw_of_injective
  statement: {ι} (i j k : ι)
  proof: by
  replace hT := hT.comp_embedding ⟨_, h⟩
  rw [affineIndependent_iff_not_collinear] at hT
  contrapose hT
  simp [Set.range_comp, Set.image_insert_eq, hT.symm.collinear]

中文:
定理 AffineIndependent.not_wbtw_of_injective
  结论: {ι} (i j k : ι)
  证明: by
  replace hT := hT.comp_embedding ⟨_, h⟩
  rw [affineIndependent_iff_not_collinear] at hT
  contrapose hT
  simp [Set.range_comp, Set.image_insert_eq, hT.symm.collinear]

Depends on / 依赖: Set.image_insert_eq, Set.range_comp, affineIndependent_iff_not_collinear, collinear, comp_embedding, contrapose, hT.comp_embedding, hT.symm.collinear, image_insert_eq, range_comp, replace
-/
theorem AffineIndependent.not_wbtw_of_injective {ι} (i j k : ι)
    (h : Function.Injective ![i, j, k]) {T : ι -> P} (hT : AffineIndependent R T) :
    ¬ Wbtw R (T i) (T j) (T k) := by
  replace hT := hT.comp_embedding ⟨_, h⟩
  rw [affineIndependent_iff_not_collinear] at hT
  contrapose hT
  simp [Set.range_comp, Set.image_insert_eq, hT.symm.collinear]

variable (R)

/--
theorem `wbtw_pointReflection` / 定理 `wbtw_pointReflection`

English:
theorem wbtw_pointReflection
  given: (x y : P)
  statement: Wbtw R y x (pointReflection R x y)
  proof: by
  refine ⟨2⁻¹, ⟨by simp, by norm_num⟩, ?_⟩
  rw [lineMap_apply]; rw [pointReflection_apply]; rw [vadd_vsub_assoc]; rw [← two_smul R (x -ᵥ y)]
  simp

中文:
定理 wbtw_pointReflection
  条件: (x y : P)
  结论: Wbtw R y x (pointReflection R x y)
  证明: by
  refine ⟨2⁻¹, ⟨by simp, by norm_num⟩, ?_⟩
  rw [lineMap_apply]; rw [pointReflection_apply]; rw [vadd_vsub_assoc]; rw [← two_smul R (x -ᵥ y)]
  simp

Depends on / 依赖: lineMap_apply, pointReflection_apply, two_smul, vadd_vsub_assoc
-/
theorem wbtw_pointReflection (x y : P) : Wbtw R y x (pointReflection R x y) := by
  refine ⟨2⁻¹, ⟨by simp, by norm_num⟩, ?_⟩
  rw [lineMap_apply]; rw [pointReflection_apply]; rw [vadd_vsub_assoc]; rw [← two_smul R (x -ᵥ y)]
  simp

/--
theorem `sbtw_pointReflection_of_ne` / 定理 `sbtw_pointReflection_of_ne`

English:
theorem sbtw_pointReflection_of_ne
  given: {x y : P} (h : x != y)
  statement: Sbtw R y x (pointReflection R x y)
  proof: by
  refine ⟨wbtw_pointReflection _ _ _, h, ?_⟩
  nth_rw 1 [← pointReflection_self R x]
  exact (pointReflection_involutive R x).injective.ne h

中文:
定理 sbtw_pointReflection_of_ne
  条件: {x y : P} (h : x != y)
  结论: Sbtw R y x (pointReflection R x y)
  证明: by
  refine ⟨wbtw_pointReflection _ _ _, h, ?_⟩
  nth_rw 1 [← pointReflection_self R x]
  exact (pointReflection_involutive R x).injective.ne h

Depends on / 依赖: injective, injective.ne, nth_rw, pointReflection_involutive, pointReflection_self, wbtw_pointReflection
-/
theorem sbtw_pointReflection_of_ne {x y : P} (h : x != y) : Sbtw R y x (pointReflection R x y) := by
  refine ⟨wbtw_pointReflection _ _ _, h, ?_⟩
  nth_rw 1 [← pointReflection_self R x]
  exact (pointReflection_involutive R x).injective.ne h

/--
theorem `wbtw_midpoint` / 定理 `wbtw_midpoint`

English:
theorem wbtw_midpoint
  given: (x y : P)
  statement: Wbtw R x (midpoint R x y) y
  proof: by
  convert! wbtw_pointReflection R (midpoint R x y) x
  rw [pointReflection_midpoint_left]

中文:
定理 wbtw_midpoint
  条件: (x y : P)
  结论: Wbtw R x (midpoint R x y) y
  证明: by
  convert! wbtw_pointReflection R (midpoint R x y) x
  rw [pointReflection_midpoint_left]

Depends on / 依赖: convert, midpoint, pointReflection_midpoint_left, wbtw_pointReflection
-/
theorem wbtw_midpoint (x y : P) : Wbtw R x (midpoint R x y) y := by
  convert! wbtw_pointReflection R (midpoint R x y) x
  rw [pointReflection_midpoint_left]

/--
theorem `sbtw_midpoint_of_ne` / 定理 `sbtw_midpoint_of_ne`

English:
theorem sbtw_midpoint_of_ne
  given: {x y : P} (h : x != y)
  statement: Sbtw R x (midpoint R x y) y
  proof: by
  have h : midpoint R x y != x := by simp [h]
  convert! sbtw_pointReflection_of_ne R h
  rw [pointReflection_midpoint_left]

中文:
定理 sbtw_midpoint_of_ne
  条件: {x y : P} (h : x != y)
  结论: Sbtw R x (midpoint R x y) y
  证明: by
  have h : midpoint R x y != x := by simp [h]
  convert! sbtw_pointReflection_of_ne R h
  rw [pointReflection_midpoint_left]

Depends on / 依赖: convert, midpoint, pointReflection_midpoint_left, sbtw_pointReflection_of_ne
-/
theorem sbtw_midpoint_of_ne {x y : P} (h : x != y) : Sbtw R x (midpoint R x y) y := by
  have h : midpoint R x y != x := by simp [h]
  convert! sbtw_pointReflection_of_ne R h
  rw [pointReflection_midpoint_left]

end LinearOrderedField
