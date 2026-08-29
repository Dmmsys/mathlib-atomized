/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison
-/
module

public import Mathlib.Algebra.Order.Interval.Set.Instances
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# The unit interval, as a topological space

Use `open unitInterval` to turn on the notation `I := Set.Icc (0 : ℝ) (1 : ℝ)`.

We provide basic instances, as well as a custom tactic for discharging
`0 ≤ ↑x`, `0 ≤ 1 - ↑x`, `↑x ≤ 1`, and `1 - ↑x ≤ 1` when `x : I`.

-/

@[expose] public section

noncomputable section

open Topology Filter Set Int Set.Icc

/-! ### The unit interval -/


/--
Definition of `unitInterval` / `unitInterval` 的定义

English:
abbreviation unitInterval
  signature: : Set Real
  body: Set.Icc 0 1

@[inherit_doc]
scoped[unitInterval] notation "I" => unitInterval

中文:
缩写 unit整数erval
  签名: : 集合 实数
  定义体: Set.Icc 0 1

@[inherit_doc]
scoped[unitInterval] notation "I" => unitInterval

Depends on / 依赖: Set.Icc
-/
abbrev unitInterval : Set Real :=
  Set.Icc 0 1

@[inherit_doc]
scoped[unitInterval] notation "I" => unitInterval

namespace unitInterval

/--
theorem `zero_mem` / 定理 `zero_mem`

English:
theorem zero_mem
  statement: (0 : Real) in I
  proof: ⟨le_rfl, zero_le_one⟩

中文:
定理 zero_mem
  结论: (0 : 实数) in I
  证明: ⟨le_rfl, zero_le_one⟩

Depends on / 依赖: le_rfl, zero_le_one
-/
theorem zero_mem : (0 : Real) in I :=
  ⟨le_rfl, zero_le_one⟩

/--
theorem `one_mem` / 定理 `one_mem`

English:
theorem one_mem
  statement: (1 : Real) in I
  proof: ⟨zero_le_one, le_rfl⟩

中文:
定理 one_mem
  结论: (1 : 实数) in I
  证明: ⟨zero_le_one, le_rfl⟩

Depends on / 依赖: le_rfl, zero_le_one
-/
theorem one_mem : (1 : Real) in I :=
  ⟨zero_le_one, le_rfl⟩

/--
theorem `mul_mem` / 定理 `mul_mem`

English:
theorem mul_mem
  given: {x y : Real} (hx : x in I) (hy : y in I)
  statement: x * y in I
  proof: ⟨mul_nonneg hx.1 hy.1, mul_le_one₀ hx.2 hy.1 hy.2⟩

中文:
定理 mul_mem
  条件: {x y : 实数} (hx : x in I) (hy : y in I)
  结论: x * y in I
  证明: ⟨mul_nonneg hx.1 hy.1, mul_le_one₀ hx.2 hy.1 hy.2⟩

Depends on / 依赖: mul_nonneg
-/
theorem mul_mem {x y : Real} (hx : x in I) (hy : y in I) : x * y in I :=
  ⟨mul_nonneg hx.1 hy.1, mul_le_one₀ hx.2 hy.1 hy.2⟩

/--
theorem `div_mem` / 定理 `div_mem`

English:
theorem div_mem
  given: {x y : Real} (hx : 0 <= x) (hy : 0 <= y) (hxy : x <= y)
  statement: x / y in I
  proof: ⟨div_nonneg hx hy, div_le_one_of_le₀ hxy hy⟩

中文:
定理 div_mem
  条件: {x y : 实数} (hx : 0 <= x) (hy : 0 <= y) (hxy : x <= y)
  结论: x / y in I
  证明: ⟨div_nonneg hx hy, div_le_one_of_le₀ hxy hy⟩

Depends on / 依赖: div_nonneg
-/
theorem div_mem {x y : Real} (hx : 0 <= x) (hy : 0 <= y) (hxy : x <= y) : x / y in I :=
  ⟨div_nonneg hx hy, div_le_one_of_le₀ hxy hy⟩

/--
theorem `fract_mem` / 定理 `fract_mem`

English:
theorem fract_mem
  given: (x : Real)
  statement: fract x in I
  proof: ⟨fract_nonneg _, (fract_lt_one _).le⟩

中文:
定理 fract_mem
  条件: (x : 实数)
  结论: fract x in I
  证明: ⟨fract_nonneg _, (fract_lt_one _).le⟩

Depends on / 依赖: fract_lt_one, fract_nonneg
-/
theorem fract_mem (x : Real) : fract x in I :=
  ⟨fract_nonneg _, (fract_lt_one _).le⟩

/--
lemma `univ_eq_Icc` / 引理 `univ_eq_Icc`

English:
lemma univ_eq_Icc
  statement: (univ : Set I) = Icc (0 : I) (1 : I)
  proof: Icc_bot_top.symm

中文:
引理 univ_eq_Icc
  结论: (univ : 集合 I) = 闭区间 (0 : I) (1 : I)
  证明: Icc_bot_top.symm

Depends on / 依赖: Icc_bot_top, Icc_bot_top.symm
-/
lemma univ_eq_Icc : (univ : Set I) = Icc (0 : I) (1 : I) := Icc_bot_top.symm

/--
theorem `coe_ne_zero` / 定理 `coe_ne_zero`

English:
theorem coe_ne_zero
  given: {x : I}
  statement: (x : Real) != 0 ↔ x != 0
  proof: coe_eq_zero.not

中文:
定理 coe_ne_zero
  条件: {x : I}
  结论: (x : 实数) != 0 ↔ x != 0
  证明: coe_eq_zero.not
-/
@[norm_cast] theorem coe_ne_zero {x : I} : (x : Real) != 0 ↔ x != 0 := coe_eq_zero.not

/--
theorem `coe_ne_one` / 定理 `coe_ne_one`

English:
theorem coe_ne_one
  given: {x : I}
  statement: (x : Real) != 1 ↔ x != 1
  proof: coe_eq_one.not

中文:
定理 coe_ne_one
  条件: {x : I}
  结论: (x : 实数) != 1 ↔ x != 1
  证明: coe_eq_one.not
-/
@[norm_cast] theorem coe_ne_one {x : I} : (x : Real) != 1 ↔ x != 1 := coe_eq_one.not

/--
theorem `coe_pos` / 定理 `coe_pos`

English:
theorem coe_pos
  given: {x : I}
  statement: (0 : Real) < x ↔ 0 < x
  proof: Iff.rfl

中文:
定理 coe_pos
  条件: {x : I}
  结论: (0 : 实数) < x ↔ 0 < x
  证明: Iff.rfl
-/
@[simp, norm_cast] theorem coe_pos {x : I} : (0 : Real) < x ↔ 0 < x := Iff.rfl

/--
theorem `coe_lt_one` / 定理 `coe_lt_one`

English:
theorem coe_lt_one
  given: {x : I}
  statement: (x : Real) < 1 ↔ x < 1
  proof: Iff.rfl

中文:
定理 coe_lt_one
  条件: {x : I}
  结论: (x : 实数) < 1 ↔ x < 1
  证明: Iff.rfl
-/
@[simp, norm_cast] theorem coe_lt_one {x : I} : (x : Real) < 1 ↔ x < 1 := Iff.rfl

/--
theorem `mul_le_left` / 定理 `mul_le_left`

English:
theorem mul_le_left
  given: {x y : I}
  statement: x * y <= x
  proof: Subtype.coe_le_coe.mp mul_le_of_le_one_right x.2.1 y.2.2

中文:
定理 mul_le_left
  条件: {x y : I}
  结论: x * y <= x
  证明: Subtype.coe_le_coe.mp mul_le_of_le_one_right x.2.1 y.2.2

Depends on / 依赖: Subtype, Subtype.coe_le_coe.mp, coe_le_coe, mul_le_of_le_one_right
-/
theorem mul_le_left {x y : I} : x * y <= x :=
Subtype.coe_le_coe.mp mul_le_of_le_one_right x.2.1 y.2.2

/--
theorem `mul_le_right` / 定理 `mul_le_right`

English:
theorem mul_le_right
  given: {x y : I}
  statement: x * y <= y
  proof: Subtype.coe_le_coe.mp mul_le_of_le_one_left y.2.1 x.2.2

中文:
定理 mul_le_right
  条件: {x y : I}
  结论: x * y <= y
  证明: Subtype.coe_le_coe.mp mul_le_of_le_one_left y.2.1 x.2.2

Depends on / 依赖: Subtype, Subtype.coe_le_coe.mp, coe_le_coe, mul_le_of_le_one_left
-/
theorem mul_le_right {x y : I} : x * y <= y :=
Subtype.coe_le_coe.mp mul_le_of_le_one_left y.2.1 x.2.2

/--
theorem `eq_closedBall` / 定理 `eq_closedBall`

English:
theorem eq_closedBall
  statement: I = Metric.closedBall 2⁻¹ 2⁻¹
  proof: by
  norm_num [unitInterval, Real.Icc_eq_closedBall]

中文:
定理 eq_closedBall
  结论: I = Metric.closedBall 2⁻¹ 2⁻¹
  证明: by
  norm_num [unitInterval, Real.Icc_eq_closedBall]

Depends on / 依赖: Icc_eq_closedBall, Real.Icc_eq_closedBall, unitInterval
-/
theorem eq_closedBall : I = Metric.closedBall 2⁻¹ 2⁻¹ := by
  norm_num [unitInterval, Real.Icc_eq_closedBall]

/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: : I -> I
  body: fun t => ⟨1 - t, Icc.mem_iff_one_sub_mem.mp t.prop⟩

@[inherit_doc]
scoped notation "σ" => unitInterval.symm

@[simp, grind =]

中文:
定义 symm
  签名: : I -> I
  定义体: fun t => ⟨1 - t, Icc.mem_iff_one_sub_mem.mp t.prop⟩

@[inherit_doc]
scoped notation "σ" => unitInterval.symm

@[simp, grind =]

Depends on / 依赖: Icc.mem_iff_one_sub_mem.mp, mem_iff_one_sub_mem, t.prop
-/
def symm : I -> I := fun t => ⟨1 - t, Icc.mem_iff_one_sub_mem.mp t.prop⟩

@[inherit_doc]
scoped notation "σ" => unitInterval.symm

@[simp, grind =]
/--
theorem `symm_zero` / 定理 `symm_zero`

English:
theorem symm_zero
  statement: σ 0 = 1
  proof: Subtype.ext by simp [symm]

@[simp, grind =]

中文:
定理 symm_zero
  结论: σ 0 = 1
  证明: Subtype.ext by simp [symm]

@[simp, grind =]

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem symm_zero : σ 0 = 1 :=
Subtype.ext by simp [symm]

@[simp, grind =]
/--
theorem `symm_one` / 定理 `symm_one`

English:
theorem symm_one
  statement: σ 1 = 0
  proof: Subtype.ext by simp [symm]

@[simp, grind =]

中文:
定理 symm_one
  结论: σ 1 = 0
  证明: Subtype.ext by simp [symm]

@[simp, grind =]

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem symm_one : σ 1 = 0 :=
Subtype.ext by simp [symm]

@[simp, grind =]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (x : I)
  statement: σ (σ x) = x
  proof: Subtype.ext by simp [symm]

中文:
定理 symm_symm
  条件: (x : I)
  结论: σ (σ x) = x
  证明: Subtype.ext by simp [symm]

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem symm_symm (x : I) : σ (σ x) = x :=
Subtype.ext by simp [symm]

/--
theorem `symm_involutive` / 定理 `symm_involutive`

English:
theorem symm_involutive
  statement: Function.Involutive (symm : I -> I)
  proof: symm_symm

中文:
定理 symm_involutive
  结论: 函数.对合 (symm : I -> I)
  证明: symm_symm

Depends on / 依赖: symm_symm
-/
theorem symm_involutive : Function.Involutive (symm : I -> I) := symm_symm

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (symm : I -> I)
  proof: symm_involutive.bijective

@[simp, grind =]

中文:
定理 symm_bijective
  结论: 函数.双射 (symm : I -> I)
  证明: symm_involutive.bijective

@[simp, grind =]

Depends on / 依赖: bijective, symm_involutive, symm_involutive.bijective
-/
theorem symm_bijective : Function.Bijective (symm : I -> I) := symm_involutive.bijective

@[simp, grind =]
/--
theorem `coe_symm_eq` / 定理 `coe_symm_eq`

English:
theorem coe_symm_eq
  given: (x : I)
  statement: (σ x : Real) = 1 - x
  proof: rfl

中文:
定理 coe_symm_eq
  条件: (x : I)
  结论: (σ x : 实数) = 1 - x
  证明: rfl
-/
theorem coe_symm_eq (x : I) : (σ x : Real) = 1 - x :=
  rfl

/--
lemma `image_coe_preimage_symm` / 引理 `image_coe_preimage_symm`

English:
lemma image_coe_preimage_symm
  given: {s : Set I}
  proof: by
  simp [symm_involutive, ← Function.Involutive.image_eq_preimage_symm, image_image]

@[simp]

中文:
引理 image_coe_preimage_symm
  条件: {s : 集合 I}
  证明: by
  simp [symm_involutive, ← Function.Involutive.image_eq_preimage_symm, image_image]

@[simp]

Depends on / 依赖: Function, Function.Involutive.image_eq_preimage_symm, Involutive, image_eq_preimage_symm, image_image, symm_involutive
-/
lemma image_coe_preimage_symm {s : Set I} :
    Subtype.val '' σ ⁻¹' s = (1 - ·) ⁻¹' Subtype.val '' s := by
  simp [symm_involutive, ← Function.Involutive.image_eq_preimage_symm, image_image]

@[simp]
/--
theorem `symm_projIcc` / 定理 `symm_projIcc`

English:
theorem symm_projIcc
  given: (x : Real)
  proof: by
  ext
  rcases le_total x 0 with h₀ | h₀
  · simp [projIcc_of_le_left, projIcc_of_right_le, h₀]
  · rcases le_total x 1 with h₁ | h₁
    · lift x to I using ⟨h₀, h₁⟩
      simp_rw [← coe_symm_eq, projIcc_val]
    · simp [projIcc_of_le_left, projIcc_of_right_le, h₁]

@[continuity, fun_prop]

中文:
定理 symm_projIcc
  条件: (x : 实数)
  证明: by
  ext
  rcases le_total x 0 with h₀ | h₀
  · simp [projIcc_of_le_left, projIcc_of_right_le, h₀]
  · rcases le_total x 1 with h₁ | h₁
    · lift x to I using ⟨h₀, h₁⟩
      simp_rw [← coe_symm_eq, projIcc_val]
    · simp [projIcc_of_le_left, projIcc_of_right_le, h₁]

@[continuity, fun_prop]

Depends on / 依赖: coe_symm_eq, le_total, projIcc_of_le_left, projIcc_of_right_le, projIcc_val, simp_rw
-/
theorem symm_projIcc (x : Real) :
    symm (projIcc 0 1 zero_le_one x) = projIcc 0 1 zero_le_one (1 - x) := by
  ext
  rcases le_total x 0 with h₀ | h₀
  · simp [projIcc_of_le_left, projIcc_of_right_le, h₀]
  · rcases le_total x 1 with h₁ | h₁
    · lift x to I using ⟨h₀, h₁⟩
      simp_rw [← coe_symm_eq, projIcc_val]
    · simp [projIcc_of_le_left, projIcc_of_right_le, h₁]

@[continuity, fun_prop]
/--
theorem `continuous_symm` / 定理 `continuous_symm`

English:
theorem continuous_symm
  statement: Continuous σ
  proof: Continuous.subtype_mk (by fun_prop) _

中文:
定理 continuous_symm
  结论: 连续 σ
  证明: Continuous.subtype_mk (by fun_prop) _

Depends on / 依赖: Continuous, Continuous.subtype_mk, fun_prop, subtype_mk
-/
theorem continuous_symm : Continuous σ :=
  Continuous.subtype_mk (by fun_prop) _

/-- `unitInterval.symm` as a `Homeomorph`. -/
@[simps]
/--
Definition of `symmHomeomorph` / `symmHomeomorph` 的定义

English:
definition symmHomeomorph
  signature: : I ≃ₜ I where
  body: symm
  invFun := symm
  left_inv := symm_symm
  right_inv := symm_symm

中文:
定义 symmHomeomorph
  签名: : I ≃ₜ I where
  定义体: symm
  invFun := symm
  left_inv := symm_symm
  right_inv := symm_symm
-/
def symmHomeomorph : I ≃ₜ I where
  toFun := symm
  invFun := symm
  left_inv := symm_symm
  right_inv := symm_symm

/--
theorem `strictAnti_symm` / 定理 `strictAnti_symm`

English:
theorem strictAnti_symm
  statement: StrictAnti σ
  proof: fun _ _ h => sub_lt_sub_left (α := Real) h _


@[simp]

中文:
定理 strictAnti_symm
  结论: 严格递减 σ
  证明: fun _ _ h => sub_lt_sub_left (α := Real) h _


@[simp]

Depends on / 依赖: sub_lt_sub_left
-/
theorem strictAnti_symm : StrictAnti σ := fun _ _ h => sub_lt_sub_left (α := Real) h _


@[simp]
/--
theorem `symm_inj` / 定理 `symm_inj`

English:
theorem symm_inj
  given: {i j : I}
  statement: σ i = σ j ↔ i = j
  proof: symm_bijective.injective.eq_iff

中文:
定理 symm_inj
  条件: {i j : I}
  结论: σ i = σ j ↔ i = j
  证明: symm_bijective.injective.eq_iff

Depends on / 依赖: eq_iff, injective, symm_bijective, symm_bijective.injective.eq_iff
-/
theorem symm_inj {i j : I} : σ i = σ j ↔ i = j := symm_bijective.injective.eq_iff

/--
theorem `half_le_symm_iff` / 定理 `half_le_symm_iff`

English:
theorem half_le_symm_iff
  given: (t : I)
  statement: 1 / 2 <= (σ t : Real) ↔ (t : Real) <= 1 / 2
  proof: by
  rw [coe_symm_eq]; rw [le_sub_iff_add_le]; rw [add_comm]; rw [← le_sub_iff_add_le]; rw [sub_half]

@[simp]

中文:
定理 half_le_symm_iff
  条件: (t : I)
  结论: 1 / 2 <= (σ t : 实数) ↔ (t : 实数) <= 1 / 2
  证明: by
  rw [coe_symm_eq]; rw [le_sub_iff_add_le]; rw [add_comm]; rw [← le_sub_iff_add_le]; rw [sub_half]

@[simp]

Depends on / 依赖: add_comm, coe_symm_eq, le_sub_iff_add_le, sub_half
-/
theorem half_le_symm_iff (t : I) : 1 / 2 <= (σ t : Real) ↔ (t : Real) <= 1 / 2 := by
  rw [coe_symm_eq]; rw [le_sub_iff_add_le]; rw [add_comm]; rw [← le_sub_iff_add_le]; rw [sub_half]

@[simp]
/--
lemma `symm_eq_one` / 引理 `symm_eq_one`

English:
lemma symm_eq_one
  given: {i : I}
  statement: σ i = 1 ↔ i = 0
  proof: by
  rw [← symm_zero]; rw [symm_inj]

@[simp]

中文:
引理 symm_eq_one
  条件: {i : I}
  结论: σ i = 1 ↔ i = 0
  证明: by
  rw [← symm_zero]; rw [symm_inj]

@[simp]

Depends on / 依赖: symm_inj, symm_zero
-/
lemma symm_eq_one {i : I} : σ i = 1 ↔ i = 0 := by
  rw [← symm_zero]; rw [symm_inj]

@[simp]
/--
lemma `symm_eq_zero` / 引理 `symm_eq_zero`

English:
lemma symm_eq_zero
  given: {i : I}
  statement: σ i = 0 ↔ i = 1
  proof: by
  rw [← symm_one]; rw [symm_inj]

@[simp]

中文:
引理 symm_eq_zero
  条件: {i : I}
  结论: σ i = 0 ↔ i = 1
  证明: by
  rw [← symm_one]; rw [symm_inj]

@[simp]

Depends on / 依赖: symm_inj, symm_one
-/
lemma symm_eq_zero {i : I} : σ i = 0 ↔ i = 1 := by
  rw [← symm_one]; rw [symm_inj]

@[simp]
/--
theorem `symm_le_symm` / 定理 `symm_le_symm`

English:
theorem symm_le_symm
  given: {i j : I}
  statement: σ i <= σ j ↔ j <= i
  proof: by
  simp only [symm, Subtype.mk_le_mk, sub_le_sub_iff, add_le_add_iff_left, Subtype.coe_le_coe]

中文:
定理 symm_le_symm
  条件: {i j : I}
  结论: σ i <= σ j ↔ j <= i
  证明: by
  simp only [symm, Subtype.mk_le_mk, sub_le_sub_iff, add_le_add_iff_left, Subtype.coe_le_coe]

Depends on / 依赖: Subtype, Subtype.coe_le_coe, Subtype.mk_le_mk, add_le_add_iff_left, coe_le_coe, mk_le_mk, sub_le_sub_iff
-/
theorem symm_le_symm {i j : I} : σ i <= σ j ↔ j <= i := by
  simp only [symm, Subtype.mk_le_mk, sub_le_sub_iff, add_le_add_iff_left, Subtype.coe_le_coe]

/--
theorem `le_symm_comm` / 定理 `le_symm_comm`

English:
theorem le_symm_comm
  given: {i j : I}
  statement: i <= σ j ↔ j <= σ i
  proof: by
  rw [← symm_le_symm]; rw [symm_symm]

中文:
定理 le_symm_comm
  条件: {i j : I}
  结论: i <= σ j ↔ j <= σ i
  证明: by
  rw [← symm_le_symm]; rw [symm_symm]

Depends on / 依赖: symm_le_symm, symm_symm
-/
theorem le_symm_comm {i j : I} : i <= σ j ↔ j <= σ i := by
  rw [← symm_le_symm]; rw [symm_symm]

/--
theorem `symm_le_comm` / 定理 `symm_le_comm`

English:
theorem symm_le_comm
  given: {i j : I}
  statement: σ i <= j ↔ σ j <= i
  proof: by
  rw [← symm_le_symm]; rw [symm_symm]

@[simp]

中文:
定理 symm_le_comm
  条件: {i j : I}
  结论: σ i <= j ↔ σ j <= i
  证明: by
  rw [← symm_le_symm]; rw [symm_symm]

@[simp]

Depends on / 依赖: symm_le_symm, symm_symm
-/
theorem symm_le_comm {i j : I} : σ i <= j ↔ σ j <= i := by
  rw [← symm_le_symm]; rw [symm_symm]

@[simp]
/--
theorem `symm_lt_symm` / 定理 `symm_lt_symm`

English:
theorem symm_lt_symm
  given: {i j : I}
  statement: σ i < σ j ↔ j < i
  proof: by
  simp only [symm, Subtype.mk_lt_mk, sub_lt_sub_iff_left, Subtype.coe_lt_coe]

中文:
定理 symm_lt_symm
  条件: {i j : I}
  结论: σ i < σ j ↔ j < i
  证明: by
  simp only [symm, Subtype.mk_lt_mk, sub_lt_sub_iff_left, Subtype.coe_lt_coe]

Depends on / 依赖: Subtype, Subtype.coe_lt_coe, Subtype.mk_lt_mk, coe_lt_coe, mk_lt_mk, sub_lt_sub_iff_left
-/
theorem symm_lt_symm {i j : I} : σ i < σ j ↔ j < i := by
  simp only [symm, Subtype.mk_lt_mk, sub_lt_sub_iff_left, Subtype.coe_lt_coe]

/--
theorem `lt_symm_comm` / 定理 `lt_symm_comm`

English:
theorem lt_symm_comm
  given: {i j : I}
  statement: i < σ j ↔ j < σ i
  proof: by
  rw [← symm_lt_symm]; rw [symm_symm]

中文:
定理 lt_symm_comm
  条件: {i j : I}
  结论: i < σ j ↔ j < σ i
  证明: by
  rw [← symm_lt_symm]; rw [symm_symm]

Depends on / 依赖: symm_lt_symm, symm_symm
-/
theorem lt_symm_comm {i j : I} : i < σ j ↔ j < σ i := by
  rw [← symm_lt_symm]; rw [symm_symm]

/--
theorem `symm_lt_comm` / 定理 `symm_lt_comm`

English:
theorem symm_lt_comm
  given: {i j : I}
  statement: σ i < j ↔ σ j < i
  proof: by
  rw [← symm_lt_symm]; rw [symm_symm]

中文:
定理 symm_lt_comm
  条件: {i j : I}
  结论: σ i < j ↔ σ j < i
  证明: by
  rw [← symm_lt_symm]; rw [symm_symm]

Depends on / 依赖: symm_lt_symm, symm_symm
-/
theorem symm_lt_comm {i j : I} : σ i < j ↔ σ j < i := by
  rw [← symm_lt_symm]; rw [symm_symm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConnectedSpace I
  body: Subtype.connectedSpace ⟨nonempty_Icc.mpr zero_le_one, isPreconnected_Icc⟩

中文:
实例 :
  签名: 连通空间 I
  定义体: Subtype.connectedSpace ⟨nonempty_Icc.mpr zero_le_one, isPreconnected_Icc⟩

Depends on / 依赖: Subtype, Subtype.connectedSpace, connectedSpace, isPreconnected_Icc, nonempty_Icc, nonempty_Icc.mpr, zero_le_one
-/
instance : ConnectedSpace I :=
  Subtype.connectedSpace ⟨nonempty_Icc.mpr zero_le_one, isPreconnected_Icc⟩

/-- Verify there is an instance for `CompactSpace I`. -/
example : CompactSpace I := by infer_instance

/--
theorem `nonneg` / 定理 `nonneg`

English:
theorem nonneg
  given: (x : I)
  statement: 0 <= (x : Real)
  proof: x.2.1

中文:
定理 nonneg
  条件: (x : I)
  结论: 0 <= (x : 实数)
  证明: x.2.1
-/
theorem nonneg (x : I) : 0 <= (x : Real) :=
  x.2.1

/--
theorem `one_minus_nonneg` / 定理 `one_minus_nonneg`

English:
theorem one_minus_nonneg
  given: (x : I)
  statement: 0 <= 1 - (x : Real)
  proof: by simpa using x.2.2

中文:
定理 one_minus_nonneg
  条件: (x : I)
  结论: 0 <= 1 - (x : 实数)
  证明: by simpa using x.2.2
-/
theorem one_minus_nonneg (x : I) : 0 <= 1 - (x : Real) := by simpa using x.2.2

/--
theorem `le_one` / 定理 `le_one`

English:
theorem le_one
  given: (x : I)
  statement: (x : Real) <= 1
  proof: x.2.2

中文:
定理 le_one
  条件: (x : I)
  结论: (x : 实数) <= 1
  证明: x.2.2
-/
theorem le_one (x : I) : (x : Real) <= 1 :=
  x.2.2

/--
theorem `one_minus_le_one` / 定理 `one_minus_le_one`

English:
theorem one_minus_le_one
  given: (x : I)
  statement: 1 - (x : Real) <= 1
  proof: by simpa using x.2.1

中文:
定理 one_minus_le_one
  条件: (x : I)
  结论: 1 - (x : 实数) <= 1
  证明: by simpa using x.2.1
-/
theorem one_minus_le_one (x : I) : 1 - (x : Real) <= 1 := by simpa using x.2.1

/--
theorem `add_pos` / 定理 `add_pos`

English:
theorem add_pos
  given: {t : I} {x : Real} (hx : 0 < x)
  statement: 0 < (x + t : Real)
  proof: add_pos_of_pos_of_nonneg hx nonneg _

中文:
定理 add_pos
  条件: {t : I} {x : 实数} (hx : 0 < x)
  结论: 0 < (x + t : 实数)
  证明: add_pos_of_pos_of_nonneg hx nonneg _

Depends on / 依赖: add_pos_of_pos_of_nonneg, nonneg
-/
theorem add_pos {t : I} {x : Real} (hx : 0 < x) : 0 < (x + t : Real) :=
add_pos_of_pos_of_nonneg hx nonneg _

/--
theorem `nonneg'` / 定理 `nonneg'`

English:
theorem nonneg'
  given: {t : I}
  statement: 0 <= t
  proof: t.2.1

中文:
定理 nonneg'
  条件: {t : I}
  结论: 0 <= t
  证明: t.2.1
-/
theorem nonneg' {t : I} : 0 <= t :=
  t.2.1

/--
theorem `le_one'` / 定理 `le_one'`

English:
theorem le_one'
  given: {t : I}
  statement: t <= 1
  proof: t.2.2

中文:
定理 le_one'
  条件: {t : I}
  结论: t <= 1
  证明: t.2.2
-/
theorem le_one' {t : I} : t <= 1 :=
  t.2.2

/--
lemma `pos_iff_ne_zero` / 引理 `pos_iff_ne_zero`

English:
lemma pos_iff_ne_zero
  given: {x : I}
  statement: 0 < x ↔ x != 0
  proof: bot_lt_iff_ne_bot

中文:
引理 pos_iff_ne_zero
  条件: {x : I}
  结论: 0 < x ↔ x != 0
  证明: bot_lt_iff_ne_bot
-/
protected lemma pos_iff_ne_zero {x : I} : 0 < x ↔ x != 0 := bot_lt_iff_ne_bot

/--
lemma `lt_one_iff_ne_one` / 引理 `lt_one_iff_ne_one`

English:
lemma lt_one_iff_ne_one
  given: {x : I}
  statement: x < 1 ↔ x != 1
  proof: lt_top_iff_ne_top

中文:
引理 lt_one_iff_ne_one
  条件: {x : I}
  结论: x < 1 ↔ x != 1
  证明: lt_top_iff_ne_top
-/
protected lemma lt_one_iff_ne_one {x : I} : x < 1 ↔ x != 1 := lt_top_iff_ne_top

/--
lemma `eq_one_or_eq_zero_of_le_mul` / 引理 `eq_one_or_eq_zero_of_le_mul`

English:
lemma eq_one_or_eq_zero_of_le_mul
  given: {i j : I} (h : i <= j * i)
  statement: i = 0 ∨ j = 1
  proof: by
  contrapose! h
  rw [← unitInterval.lt_one_iff_ne_one]; rw [← coe_lt_one]; rw [← unitInterval.pos_iff_ne_zero]; rw [← coe_pos] at h
  rw [← Subtype.coe_lt_coe]; rw [coe_mul]
  simpa using mul_lt_mul_of_pos_right h.right h.left

中文:
引理 eq_one_or_eq_zero_of_le_mul
  条件: {i j : I} (h : i <= j * i)
  结论: i = 0 ∨ j = 1
  证明: by
  contrapose! h
  rw [← unitInterval.lt_one_iff_ne_one]; rw [← coe_lt_one]; rw [← unitInterval.pos_iff_ne_zero]; rw [← coe_pos] at h
  rw [← Subtype.coe_lt_coe]; rw [coe_mul]
  simpa using mul_lt_mul_of_pos_right h.right h.left

Depends on / 依赖: Subtype, Subtype.coe_lt_coe, coe_lt_coe, coe_lt_one, coe_mul, coe_pos, contrapose, h.left, h.right, lt_one_iff_ne_one, mul_lt_mul_of_pos_right, pos_iff_ne_zero, unitInterval, unitInterval.lt_one_iff_ne_one, unitInterval.pos_iff_ne_zero
-/
lemma eq_one_or_eq_zero_of_le_mul {i j : I} (h : i <= j * i) : i = 0 ∨ j = 1 := by
  contrapose! h
  rw [← unitInterval.lt_one_iff_ne_one]; rw [← coe_lt_one]; rw [← unitInterval.pos_iff_ne_zero]; rw [← coe_pos] at h
  rw [← Subtype.coe_lt_coe]; rw [coe_mul]
  simpa using mul_lt_mul_of_pos_right h.right h.left

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nontrivial I
  body: ⟨⟨1, 0, (one_ne_zero <| congrArg Subtype.val ·)⟩⟩

中文:
实例 :
  签名: 非平凡 I
  定义体: ⟨⟨1, 0, (one_ne_zero <| congrArg Subtype.val ·)⟩⟩

Depends on / 依赖: Subtype, Subtype.val, one_ne_zero
-/
instance : Nontrivial I := ⟨⟨1, 0, (one_ne_zero <| congrArg Subtype.val ·)⟩⟩

/--
theorem `mul_pos_mem_iff` / 定理 `mul_pos_mem_iff`

English:
theorem mul_pos_mem_iff
  given: {a t : Real} (ha : 0 < a)
  statement: a * t in I ↔ t in Set.Icc (0 : Real) (1 / a)
  proof: by
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor
  · exact nonneg_of_mul_nonneg_right h₁ ha
  · rwa [le_div_iff₀ ha, mul_comm]
  · exact mul_nonneg ha.le h₁
  · rwa [le_div_iff₀ ha, mul_comm] at h₂

中文:
定理 mul_pos_mem_iff
  条件: {a t : 实数} (ha : 0 < a)
  结论: a * t in I ↔ t in 集合.闭区间 (0 : 实数) (1 / a)
  证明: by
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor
  · exact nonneg_of_mul_nonneg_right h₁ ha
  · rwa [le_div_iff₀ ha, mul_comm]
  · exact mul_nonneg ha.le h₁
  · rwa [le_div_iff₀ ha, mul_comm] at h₂

Depends on / 依赖: ha.le, mul_comm, mul_nonneg, nonneg_of_mul_nonneg_right
-/
theorem mul_pos_mem_iff {a t : Real} (ha : 0 < a) : a * t in I ↔ t in Set.Icc (0 : Real) (1 / a) := by
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor
  · exact nonneg_of_mul_nonneg_right h₁ ha
  · rwa [le_div_iff₀ ha, mul_comm]
  · exact mul_nonneg ha.le h₁
  · rwa [le_div_iff₀ ha, mul_comm] at h₂

/--
theorem `two_mul_sub_one_mem_iff` / 定理 `two_mul_sub_one_mem_iff`

English:
theorem two_mul_sub_one_mem_iff
  given: {t : Real}
  statement: 2 * t - 1 in I ↔ t in Set.Icc (1 / 2 : Real) 1
  proof: by
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

中文:
定理 two_mul_sub_one_mem_iff
  条件: {t : 实数}
  结论: 2 * t - 1 in I ↔ t in 集合.闭区间 (1 / 2 : 实数) 1
  证明: by
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
-/
theorem two_mul_sub_one_mem_iff {t : Real} : 2 * t - 1 in I ↔ t in Set.Icc (1 / 2 : Real) 1 := by
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/--
Definition of `submonoid` / `submonoid` 的定义

English:
definition submonoid
  signature: : Submonoid Real where
  body: unitInterval
  one_mem' := unitInterval.one_mem
  mul_mem' := unitInterval.mul_mem

中文:
定义 submonoid
  签名: : 子幺半群 实数 where
  定义体: unitInterval
  one_mem' := unitInterval.one_mem
  mul_mem' := unitInterval.mul_mem

Depends on / 依赖: unitInterval
-/
def submonoid : Submonoid Real where
  carrier := unitInterval
  one_mem' := unitInterval.one_mem
  mul_mem' := unitInterval.mul_mem

/--
theorem `coe_unitIntervalSubmonoid` / 定理 `coe_unitIntervalSubmonoid`

English:
theorem coe_unitIntervalSubmonoid
  statement: submonoid = unitInterval
  proof: rfl

中文:
定理 coe_unit整数ervalSubmonoid
  结论: submonoid = unit整数erval
  证明: rfl
-/
@[simp] theorem coe_unitIntervalSubmonoid : submonoid = unitInterval := rfl
/--
theorem `mem_unitIntervalSubmonoid` / 定理 `mem_unitIntervalSubmonoid`

English:
theorem mem_unitIntervalSubmonoid
  given: {x}
  statement: x in submonoid ↔ x in unitInterval
  proof: Iff.rfl

中文:
定理 mem_unit整数ervalSubmonoid
  条件: {x}
  结论: x in submonoid ↔ x in unit整数erval
  证明: Iff.rfl
-/
@[simp] theorem mem_unitIntervalSubmonoid {x} : x in submonoid ↔ x in unitInterval :=
  Iff.rfl

/--
theorem `prod_mem` / 定理 `prod_mem`

English:
theorem prod_mem
  statement: {ι : Type*} {t : Finset ι} {f : ι -> Real}
  proof: _root_.prod_mem (S := unitInterval.submonoid) h

中文:
定理 prod_mem
  结论: {ι : 类型} {t : 有限集 ι} {f : ι -> 实数}
  证明: _root_.prod_mem (S := unitInterval.submonoid) h
-/
protected theorem prod_mem {ι : Type*} {t : Finset ι} {f : ι -> Real}
    (h : forall c in t, f c in unitInterval) :
    ∏ c in t, f c in unitInterval := _root_.prod_mem (S := unitInterval.submonoid) h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrderedCommMonoidWithZero I
  body: x.2.1
  mul_lt_mul_of_pos_left i hi j k hjk := by
    simp only [← Subtype.coe_lt_coe, coe_mul]; gcongr

中文:
实例 :
  签名: 带零LinearOrderedComm幺半群 I
  定义体: x.2.1
  mul_lt_mul_of_pos_left i hi j k hjk := by
    simp only [← Subtype.coe_lt_coe, coe_mul]; gcongr
-/
instance : LinearOrderedCommMonoidWithZero I where
  isBot_zero x := x.2.1
  mul_lt_mul_of_pos_left i hi j k hjk := by
    simp only [← Subtype.coe_lt_coe, coe_mul]; gcongr

/--
lemma `subtype_Iic_eq_Icc` / 引理 `subtype_Iic_eq_Icc`

English:
lemma subtype_Iic_eq_Icc
  given: (x : I)
  statement: Subtype.val ⁻¹' (Iic ↑x) = Icc 0 x
  proof: by
  rw [preimage_subtype_val_Iic]
  exact Icc_bot.symm

中文:
引理 subtype_Iic_eq_Icc
  条件: (x : I)
  结论: 子类型.val ⁻¹' (左无界右闭区间 ↑x) = 闭区间 0 x
  证明: by
  rw [preimage_subtype_val_Iic]
  exact Icc_bot.symm

Depends on / 依赖: Icc_bot, Icc_bot.symm, preimage_subtype_val_Iic
-/
lemma subtype_Iic_eq_Icc (x : I) : Subtype.val ⁻¹' (Iic ↑x) = Icc 0 x := by
  rw [preimage_subtype_val_Iic]
  exact Icc_bot.symm

/--
lemma `subtype_Iio_eq_Ico` / 引理 `subtype_Iio_eq_Ico`

English:
lemma subtype_Iio_eq_Ico
  given: (x : I)
  statement: Subtype.val ⁻¹' (Iio ↑x) = Ico 0 x
  proof: by
  rw [preimage_subtype_val_Iio]
  exact Ico_bot.symm

中文:
引理 subtype_Iio_eq_Ico
  条件: (x : I)
  结论: 子类型.val ⁻¹' (左无界右开区间 ↑x) = 左闭右开区间 0 x
  证明: by
  rw [preimage_subtype_val_Iio]
  exact Ico_bot.symm

Depends on / 依赖: Ico_bot, Ico_bot.symm, preimage_subtype_val_Iio
-/
lemma subtype_Iio_eq_Ico (x : I) : Subtype.val ⁻¹' (Iio ↑x) = Ico 0 x := by
  rw [preimage_subtype_val_Iio]
  exact Ico_bot.symm

/--
lemma `subtype_Ici_eq_Icc` / 引理 `subtype_Ici_eq_Icc`

English:
lemma subtype_Ici_eq_Icc
  given: (x : I)
  statement: Subtype.val ⁻¹' (Ici ↑x) = Icc x 1
  proof: by
  rw [preimage_subtype_val_Ici]
  exact Icc_top.symm

中文:
引理 subtype_Ici_eq_Icc
  条件: (x : I)
  结论: 子类型.val ⁻¹' (左闭右无界区间 ↑x) = 闭区间 x 1
  证明: by
  rw [preimage_subtype_val_Ici]
  exact Icc_top.symm

Depends on / 依赖: Icc_top, Icc_top.symm, preimage_subtype_val_Ici
-/
lemma subtype_Ici_eq_Icc (x : I) : Subtype.val ⁻¹' (Ici ↑x) = Icc x 1 := by
  rw [preimage_subtype_val_Ici]
  exact Icc_top.symm

/--
lemma `subtype_Ioi_eq_Ioc` / 引理 `subtype_Ioi_eq_Ioc`

English:
lemma subtype_Ioi_eq_Ioc
  given: (x : I)
  statement: Subtype.val ⁻¹' (Ioi ↑x) = Ioc x 1
  proof: by
  rw [preimage_subtype_val_Ioi]
  exact Ioc_top.symm

中文:
引理 subtype_Ioi_eq_Ioc
  条件: (x : I)
  结论: 子类型.val ⁻¹' (左开右无界区间 ↑x) = 左开右闭区间 x 1
  证明: by
  rw [preimage_subtype_val_Ioi]
  exact Ioc_top.symm

Depends on / 依赖: Ioc_top, Ioc_top.symm, preimage_subtype_val_Ioi
-/
lemma subtype_Ioi_eq_Ioc (x : I) : Subtype.val ⁻¹' (Ioi ↑x) = Ioc x 1 := by
  rw [preimage_subtype_val_Ioi]
  exact Ioc_top.symm

end unitInterval

section partition

namespace Set.Icc

variable {α} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  {a b c d : α} (h : a <= b) {δ : α}

-- TODO: Set.projIci, Set.projIic
/--
lemma `_root_.Set.abs_projIcc_sub_projIcc` / 引理 `_root_.Set.abs_projIcc_sub_projIcc`

English:
lemma _root_.Set.abs_projIcc_sub_projIcc
  statement: (|projIcc a b h c - projIcc a b h d| : α) <= |c - d|
  proof: by
  wlog hdc : d <= c generalizing c d
  · rw [abs_sub_comm, abs_sub_comm c]; exact this (le_of_not_ge hdc)
  rw [abs_eq_self.2 (sub_nonneg.2 hdc)]; rw [abs_eq_self.2 (sub_nonneg.2 <| mod_cast monotone_projIcc h hdc)]
  rw [← sub_nonneg] at hdc
  refine (max_sub_max_le_max _ _ _ _).trans (max_le (b

中文:
引理 _root_.集合.abs_projIcc_sub_projIcc
  结论: (|projIcc a b h c - projIcc a b h d| : α) <= |c - d|
  证明: by
  wlog hdc : d <= c generalizing c d
  · rw [abs_sub_comm, abs_sub_comm c]; exact this (le_of_not_ge hdc)
  rw [abs_eq_self.2 (sub_nonneg.2 hdc)]; rw [abs_eq_self.2 (sub_nonneg.2 <| mod_cast monotone_projIcc h hdc)]
  rw [← sub_nonneg] at hdc
  refine (max_sub_max_le_max _ _ _ _).trans (max_le (b

Depends on / 依赖: abs_eq_self, abs_eq_self.mpr, abs_min_sub_min_le_max, abs_sub_comm, abs_zero, generalizing, le_abs_self, le_of_not_ge, max_le, max_sub_max_le_max, mod_cast, monotone_projIcc, sub_nonneg, sub_self
-/
lemma _root_.Set.abs_projIcc_sub_projIcc : (|projIcc a b h c - projIcc a b h d| : α) <= |c - d| := by
  wlog hdc : d <= c generalizing c d
  · rw [abs_sub_comm, abs_sub_comm c]; exact this (le_of_not_ge hdc)
  rw [abs_eq_self.2 (sub_nonneg.2 hdc)]; rw [abs_eq_self.2 (sub_nonneg.2 <| mod_cast monotone_projIcc h hdc)]
  rw [← sub_nonneg] at hdc
  refine (max_sub_max_le_max _ _ _ _).trans (max_le (by rwa [sub_self]) ?_)
  refine ((le_abs_self _).trans <| abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rwa [sub_self, abs_zero]
  · exact (abs_eq_self.mpr hdc).le

/--
Definition of `addNSMul` / `addNSMul` 的定义

English:
definition addNSMul
  signature: (δ : α) (n : Nat)
  body: projIcc a b h (a + n • δ)

omit [IsOrderedAddMonoid α] in

中文:
定义 addNSMul
  签名: (δ : α) (n : 自然数)
  定义体: projIcc a b h (a + n • δ)

omit [IsOrderedAddMonoid α] in

Depends on / 依赖: projIcc
-/
def addNSMul (δ : α) (n : Nat) : Icc a b := projIcc a b h (a + n • δ)

omit [IsOrderedAddMonoid α] in
/--
lemma `addNSMul_zero` / 引理 `addNSMul_zero`

English:
lemma addNSMul_zero
  statement: addNSMul h δ 0 = a
  proof: by
  rw [addNSMul]; rw [zero_smul]; rw [add_zero]; rw [projIcc_left]

中文:
引理 addNSMul_zero
  结论: addNSMul h δ 0 = a
  证明: by
  rw [addNSMul]; rw [zero_smul]; rw [add_zero]; rw [projIcc_left]

Depends on / 依赖: addNSMul, add_zero, projIcc_left, zero_smul
-/
lemma addNSMul_zero : addNSMul h δ 0 = a := by
  rw [addNSMul]; rw [zero_smul]; rw [add_zero]; rw [projIcc_left]

/--
lemma `addNSMul_eq_right` / 引理 `addNSMul_eq_right`

English:
lemma addNSMul_eq_right
  given: [Archimedean α] (hδ : 0 < δ)
  proof: by
  obtain ⟨m, hm⟩ := Archimedean.arch (b - a) hδ
  refine ⟨m, fun n hn => ?_⟩
  rw [addNSMul]; rw [coe_projIcc]; rw [add_comm]; rw [min_eq_left_iff.mpr]; rw [max_eq_right h]
  exact sub_le_iff_le_add.mp (hm.trans <| nsmul_le_nsmul_left hδ.le hn)

中文:
引理 addNSMul_eq_right
  条件: [阿基米德 α] (hδ : 0 < δ)
  证明: by
  obtain ⟨m, hm⟩ := Archimedean.arch (b - a) hδ
  refine ⟨m, fun n hn => ?_⟩
  rw [addNSMul]; rw [coe_projIcc]; rw [add_comm]; rw [min_eq_left_iff.mpr]; rw [max_eq_right h]
  exact sub_le_iff_le_add.mp (hm.trans <| nsmul_le_nsmul_left hδ.le hn)

Depends on / 依赖: Archimedean, Archimedean.arch, addNSMul, add_comm, coe_projIcc, hm.trans, max_eq_right, min_eq_left_iff, min_eq_left_iff.mpr, nsmul_le_nsmul_left, sub_le_iff_le_add, sub_le_iff_le_add.mp
-/
lemma addNSMul_eq_right [Archimedean α] (hδ : 0 < δ) :
    exists m, forall n >= m, addNSMul h δ n = b := by
  obtain ⟨m, hm⟩ := Archimedean.arch (b - a) hδ
  refine ⟨m, fun n hn => ?_⟩
  rw [addNSMul]; rw [coe_projIcc]; rw [add_comm]; rw [min_eq_left_iff.mpr]; rw [max_eq_right h]
  exact sub_le_iff_le_add.mp (hm.trans <| nsmul_le_nsmul_left hδ.le hn)

/--
lemma `monotone_addNSMul` / 引理 `monotone_addNSMul`

English:
lemma monotone_addNSMul
  given: (hδ : 0 <= δ)
  statement: Monotone (addNSMul h δ)
  proof: fun _ _ hnm => monotone_projIcc h (add_le_add_iff_left _).mpr (nsmul_le_nsmul_left hδ hnm)

中文:
引理 monotone_addNSMul
  条件: (hδ : 0 <= δ)
  结论: 递增 (addNSMul h δ)
  证明: fun _ _ hnm => monotone_projIcc h (add_le_add_iff_left _).mpr (nsmul_le_nsmul_left hδ hnm)

Depends on / 依赖: add_le_add_iff_left, monotone_projIcc, nsmul_le_nsmul_left
-/
lemma monotone_addNSMul (hδ : 0 <= δ) : Monotone (addNSMul h δ) :=
fun _ _ hnm => monotone_projIcc h (add_le_add_iff_left _).mpr (nsmul_le_nsmul_left hδ hnm)

/--
lemma `abs_sub_addNSMul_le` / 引理 `abs_sub_addNSMul_le`

English:
lemma abs_sub_addNSMul_le
  statement: (hδ : 0 <= δ) {t : Icc a b} (n : Nat)
  proof: calc
(|t - addNSMul h δ n| : α) = t - addNSMul h δ n := abs_eq_self.2 sub_nonneg.2 ht.1
    _ <= projIcc a b h (a + (n + 1) • δ) - addNSMul h δ n := by apply sub_le_sub_right; exact ht.2
    _ <= (|projIcc a b h (a + (n + 1) • δ) - addNSMul h δ n| : α) := le_abs_self _
    _ <= |a + (n + 1) • δ - (a

中文:
引理 abs_sub_addNSMul_le
  结论: (hδ : 0 <= δ) {t : 闭区间 a b} (n : 自然数)
  证明: calc
(|t - addNSMul h δ n| : α) = t - addNSMul h δ n := abs_eq_self.2 sub_nonneg.2 ht.1
    _ <= projIcc a b h (a + (n + 1) • δ) - addNSMul h δ n := by apply sub_le_sub_right; exact ht.2
    _ <= (|projIcc a b h (a + (n + 1) • δ) - addNSMul h δ n| : α) := le_abs_self _
    _ <= |a + (n + 1) • δ - (a

Depends on / 依赖: abs_eq_self, abs_eq_self.mpr, abs_projIcc_sub_projIcc, addNSMul, add_sub_add_comm, add_sub_cancel_right, le_abs_self, projIcc, sub_le_sub_right, sub_nonneg, sub_self, succ_nsmul, zero_add
-/
lemma abs_sub_addNSMul_le (hδ : 0 <= δ) {t : Icc a b} (n : Nat)
    (ht : t in Icc (addNSMul h δ n) (addNSMul h δ (n + 1))) :
    (|t - addNSMul h δ n| : α) <= δ :=
  calc
(|t - addNSMul h δ n| : α) = t - addNSMul h δ n := abs_eq_self.2 sub_nonneg.2 ht.1
    _ <= projIcc a b h (a + (n + 1) • δ) - addNSMul h δ n := by apply sub_le_sub_right; exact ht.2
    _ <= (|projIcc a b h (a + (n + 1) • δ) - addNSMul h δ n| : α) := le_abs_self _
    _ <= |a + (n + 1) • δ - (a + n • δ)| := abs_projIcc_sub_projIcc h
    _ <= δ := by
          rw [add_sub_add_comm]; rw [sub_self]; rw [zero_add]; rw [succ_nsmul']; rw [add_sub_cancel_right]
          exact (abs_eq_self.mpr hδ).le

/--
Definition of `convexComb` / `convexComb` 的定义

English:
definition convexComb
  signature: {a b : Real} (x y : Icc a b) (t : unitInterval)
  body: ⟨(1 - t) * x + t * y, by
    constructor
    · nlinarith [x.2.1, y.2.1, t.2.1, t.2.2]
    · nlinarith [x.2.2, y.2.2, t.2.1, t.2.2]⟩

@[simp, grind =]

中文:
定义 convexComb
  签名: {a b : 实数} (x y : 闭区间 a b) (t : unit整数erval)
  定义体: ⟨(1 - t) * x + t * y, by
    constructor
    · nlinarith [x.2.1, y.2.1, t.2.1, t.2.2]
    · nlinarith [x.2.2, y.2.2, t.2.1, t.2.2]⟩

@[simp, grind =]
-/
def convexComb {a b : Real} (x y : Icc a b) (t : unitInterval) : Icc a b :=
  ⟨(1 - t) * x + t * y, by
    constructor
    · nlinarith [x.2.1, y.2.1, t.2.1, t.2.2]
    · nlinarith [x.2.2, y.2.2, t.2.1, t.2.2]⟩

@[simp, grind =]
/--
theorem `coe_convexComb` / 定理 `coe_convexComb`

English:
theorem coe_convexComb
  given: {a b : Real} (x y : Icc a b) (t : unitInterval)
  proof: rfl

@[simp, grind =]

中文:
定理 coe_convexComb
  条件: {a b : 实数} (x y : 闭区间 a b) (t : unit整数erval)
  证明: rfl

@[simp, grind =]
-/
theorem coe_convexComb {a b : Real} (x y : Icc a b) (t : unitInterval) :
  (convexComb x y t : Real) = (1 - t) * x + t * y := rfl

@[simp, grind =]
/--
theorem `convexComb_zero` / 定理 `convexComb_zero`

English:
theorem convexComb_zero
  given: {a b : Real} (x y : Icc a b)
  statement: convexComb x y 0 = x
  proof: by
  simp [convexComb]

@[simp, grind =]

中文:
定理 convexComb_zero
  条件: {a b : 实数} (x y : 闭区间 a b)
  结论: convexComb x y 0 = x
  证明: by
  simp [convexComb]

@[simp, grind =]

Depends on / 依赖: convexComb
-/
theorem convexComb_zero {a b : Real} (x y : Icc a b) : convexComb x y 0 = x := by
  simp [convexComb]

@[simp, grind =]
/--
theorem `convexComb_one` / 定理 `convexComb_one`

English:
theorem convexComb_one
  given: {a b : Real} (x y : Icc a b)
  statement: convexComb x y 1 = y
  proof: by
  simp [convexComb]

@[simp, grind =]

中文:
定理 convexComb_one
  条件: {a b : 实数} (x y : 闭区间 a b)
  结论: convexComb x y 1 = y
  证明: by
  simp [convexComb]

@[simp, grind =]

Depends on / 依赖: convexComb
-/
theorem convexComb_one {a b : Real} (x y : Icc a b) : convexComb x y 1 = y := by
  simp [convexComb]

@[simp, grind =]
/--
theorem `convexComb_zero_one` / 定理 `convexComb_zero_one`

English:
theorem convexComb_zero_one
  given: (t : unitInterval)
  statement: convexComb 0 1 t = t
  proof: by
  simp [convexComb]

@[simp, grind =]

中文:
定理 convexComb_zero_one
  条件: (t : unit整数erval)
  结论: convexComb 0 1 t = t
  证明: by
  simp [convexComb]

@[simp, grind =]

Depends on / 依赖: convexComb
-/
theorem convexComb_zero_one (t : unitInterval) : convexComb 0 1 t = t := by
  simp [convexComb]

@[simp, grind =]
/--
theorem `convexComb_eq` / 定理 `convexComb_eq`

English:
theorem convexComb_eq
  given: {a b : Real} (x : Icc a b) (t : unitInterval)
  statement: convexComb x x t = x
  proof: by
  simp [convexComb, sub_mul]

@[simp, grind =]

中文:
定理 convexComb_eq
  条件: {a b : 实数} (x : 闭区间 a b) (t : unit整数erval)
  结论: convexComb x x t = x
  证明: by
  simp [convexComb, sub_mul]

@[simp, grind =]

Depends on / 依赖: convexComb, sub_mul
-/
theorem convexComb_eq {a b : Real} (x : Icc a b) (t : unitInterval) : convexComb x x t = x := by
  simp [convexComb, sub_mul]

@[simp, grind =]
/--
theorem `convexComb_symm` / 定理 `convexComb_symm`

English:
theorem convexComb_symm
  given: {a b : Real} (x y : Icc a b) (t : unitInterval)
  proof: by
  simp [convexComb]
  abel

@[grind .]

中文:
定理 convexComb_symm
  条件: {a b : 实数} (x y : 闭区间 a b) (t : unit整数erval)
  证明: by
  simp [convexComb]
  abel

@[grind .]

Depends on / 依赖: convexComb
-/
theorem convexComb_symm {a b : Real} (x y : Icc a b) (t : unitInterval) :
    convexComb x y (unitInterval.symm t) = convexComb y x t := by
  simp [convexComb]
  abel

@[grind .]
/--
theorem `le_convexComb` / 定理 `le_convexComb`

English:
theorem le_convexComb
  given: {a b : Real} {x y : Icc a b} (h : x <= y) (t : unitInterval)
  proof: by
  rw [← Subtype.coe_le_coe] at h ⊢
  simp
  nlinarith [t.2.1, t.2.2]

@[grind .]

中文:
定理 le_convexComb
  条件: {a b : 实数} {x y : 闭区间 a b} (h : x <= y) (t : unit整数erval)
  证明: by
  rw [← Subtype.coe_le_coe] at h ⊢
  simp
  nlinarith [t.2.1, t.2.2]

@[grind .]

Depends on / 依赖: Subtype, Subtype.coe_le_coe, coe_le_coe
-/
theorem le_convexComb {a b : Real} {x y : Icc a b} (h : x <= y) (t : unitInterval) :
    x <= convexComb x y t := by
  rw [← Subtype.coe_le_coe] at h ⊢
  simp
  nlinarith [t.2.1, t.2.2]

@[grind .]
/--
theorem `convexComb_le` / 定理 `convexComb_le`

English:
theorem convexComb_le
  given: {a b : Real} {x y : Icc a b} (h : x <= y) (t : unitInterval)
  proof: by
  rw [← Subtype.coe_le_coe] at h ⊢
  simp
  nlinarith [t.2.1, t.2.2]

@[continuity, fun_prop]

中文:
定理 convexComb_le
  条件: {a b : 实数} {x y : 闭区间 a b} (h : x <= y) (t : unit整数erval)
  证明: by
  rw [← Subtype.coe_le_coe] at h ⊢
  simp
  nlinarith [t.2.1, t.2.2]

@[continuity, fun_prop]

Depends on / 依赖: Subtype, Subtype.coe_le_coe, coe_le_coe
-/
theorem convexComb_le {a b : Real} {x y : Icc a b} (h : x <= y) (t : unitInterval) :
    convexComb x y t <= y := by
  rw [← Subtype.coe_le_coe] at h ⊢
  simp
  nlinarith [t.2.1, t.2.2]

@[continuity, fun_prop]
/--
theorem `continuous_convexComb` / 定理 `continuous_convexComb`

English:
theorem continuous_convexComb
  given: {a b : Real} (x y : Icc a b)
  statement: Continuous (convexComb x y)
  proof: by
  unfold Icc.convexComb
  fun_prop

@[continuity, fun_prop]

中文:
定理 continuous_convexComb
  条件: {a b : 实数} (x y : 闭区间 a b)
  结论: 连续 (convexComb x y)
  证明: by
  unfold Icc.convexComb
  fun_prop

@[continuity, fun_prop]

Depends on / 依赖: Icc.convexComb, convexComb, fun_prop
-/
theorem continuous_convexComb {a b : Real} (x y : Icc a b) : Continuous (convexComb x y) := by
  unfold Icc.convexComb
  fun_prop

@[continuity, fun_prop]
/--
theorem `continuous_convexComb_prod` / 定理 `continuous_convexComb_prod`

English:
theorem continuous_convexComb_prod
  given: {a b : Real}
  proof: by
  unfold Icc.convexComb
  fun_prop

中文:
定理 continuous_convexComb_prod
  条件: {a b : 实数}
  证明: by
  unfold Icc.convexComb
  fun_prop

Depends on / 依赖: Icc.convexComb, convexComb, fun_prop
-/
theorem continuous_convexComb_prod {a b : Real} :
    Continuous fun x : Icc a b × Icc a b × unitInterval => Icc.convexComb x.1 x.2.1 x.2.2 := by
  unfold Icc.convexComb
  fun_prop

/--
Definition of `convexComb_assoc_coeff₁` / `convexComb_assoc_coeff₁` 的定义

English:
abbreviation convexComb_assoc_coeff₁
  signature: (s t : unitInterval)
  body: ⟨s * (1 - t) / (1 - s * t),
    by
      apply div_nonneg
      · nlinarith [s.2.1, t.2.2]
      · nlinarith [s.2.2, t.2.2, t.2.1],
    by
      apply div_le_one_of_le₀
      · nlinarith [s.2.2]
      · nlinarith [s.2.2, t.2.2, t.2.1]⟩

中文:
缩写 convexComb_assoc_coeff₁
  签名: (s t : unit整数erval)
  定义体: ⟨s * (1 - t) / (1 - s * t),
    by
      apply div_nonneg
      · nlinarith [s.2.1, t.2.2]
      · nlinarith [s.2.2, t.2.2, t.2.1],
    by
      apply div_le_one_of_le₀
      · nlinarith [s.2.2]
      · nlinarith [s.2.2, t.2.2, t.2.1]⟩

Depends on / 依赖: div_nonneg
-/
abbrev convexComb_assoc_coeff₁ (s t : unitInterval) : unitInterval :=
  ⟨s * (1 - t) / (1 - s * t),
    by
      apply div_nonneg
      · nlinarith [s.2.1, t.2.2]
      · nlinarith [s.2.2, t.2.2, t.2.1],
    by
      apply div_le_one_of_le₀
      · nlinarith [s.2.2]
      · nlinarith [s.2.2, t.2.2, t.2.1]⟩

/--
Definition of `convexComb_assoc_coeff₂` / `convexComb_assoc_coeff₂` 的定义

English:
abbreviation convexComb_assoc_coeff₂
  signature: (s t : unitInterval)
  body: s * t

中文:
缩写 convexComb_assoc_coeff₂
  签名: (s t : unit整数erval)
  定义体: s * t
-/
abbrev convexComb_assoc_coeff₂ (s t : unitInterval) : unitInterval := s * t

/--
theorem `convexComb_assoc` / 定理 `convexComb_assoc`

English:
theorem convexComb_assoc
  given: {a b : Real} (x y z : Icc a b) (s t : unitInterval)
  proof: by
  simp only [convexComb, coe_mul, Subtype.mk.injEq]
  by_cases hs : (s : Real) = 1
  · simp only [hs]
    by_cases ht : (t : Real) = 1
    · simp [ht]
    · have : (1 - t : Real) != 0 := by grind
      field_simp
      simp
  · by_cases ht : (t : Real) = 1
    · simp [ht]
    · have : (1 - s * t 

中文:
定理 convexComb_assoc
  条件: {a b : 实数} (x y z : 闭区间 a b) (s t : unit整数erval)
  证明: by
  simp only [convexComb, coe_mul, Subtype.mk.injEq]
  by_cases hs : (s : Real) = 1
  · simp only [hs]
    by_cases ht : (t : Real) = 1
    · simp [ht]
    · have : (1 - t : Real) != 0 := by grind
      field_simp
      simp
  · by_cases ht : (t : Real) = 1
    · simp [ht]
    · have : (1 - s * t 

Depends on / 依赖: Subtype, Subtype.mk.injEq, coe_mul, convexComb, ring_nf
-/
theorem convexComb_assoc {a b : Real} (x y z : Icc a b) (s t : unitInterval) :
    convexComb x (convexComb y z t) s =
      convexComb (convexComb x y (convexComb_assoc_coeff₁ s t)) z
        (convexComb_assoc_coeff₂ s t) := by
  simp only [convexComb, coe_mul, Subtype.mk.injEq]
  by_cases hs : (s : Real) = 1
  · simp only [hs]
    by_cases ht : (t : Real) = 1
    · simp [ht]
    · have : (1 - t : Real) != 0 := by grind
      field_simp
      simp
  · by_cases ht : (t : Real) = 1
    · simp [ht]
    · have : (1 - s * t : Real) != 0 := by
        intro h
        have : 1 <= (t : Real) := by nlinarith [s.2.2, t.2.1]
        grind
      field_simp
      ring_nf

/--
Definition of `convexComb_assoc_coeff₁'` / `convexComb_assoc_coeff₁'` 的定义

English:
abbreviation convexComb_assoc_coeff₁'
  signature: (s t : unitInterval)
  body: unitInterval.symm (convexComb_assoc_coeff₂ (unitInterval.symm t) (unitInterval.symm s))

中文:
缩写 convexComb_assoc_coeff₁'
  签名: (s t : unit整数erval)
  定义体: unitInterval.symm (convexComb_assoc_coeff₂ (unitInterval.symm t) (unitInterval.symm s))

Depends on / 依赖: unitInterval, unitInterval.symm
-/
abbrev convexComb_assoc_coeff₁' (s t : unitInterval) : unitInterval :=
  unitInterval.symm (convexComb_assoc_coeff₂ (unitInterval.symm t) (unitInterval.symm s))

/--
Definition of `convexComb_assoc_coeff₂'` / `convexComb_assoc_coeff₂'` 的定义

English:
abbreviation convexComb_assoc_coeff₂'
  signature: (s t : unitInterval)
  body: unitInterval.symm (convexComb_assoc_coeff₁ (unitInterval.symm t) (unitInterval.symm s))

中文:
缩写 convexComb_assoc_coeff₂'
  签名: (s t : unit整数erval)
  定义体: unitInterval.symm (convexComb_assoc_coeff₁ (unitInterval.symm t) (unitInterval.symm s))

Depends on / 依赖: unitInterval, unitInterval.symm
-/
abbrev convexComb_assoc_coeff₂' (s t : unitInterval) : unitInterval :=
  unitInterval.symm (convexComb_assoc_coeff₁ (unitInterval.symm t) (unitInterval.symm s))

/--
theorem `convexComb_assoc'` / 定理 `convexComb_assoc'`

English:
theorem convexComb_assoc'
  given: {a b : Real} (x y z : Icc a b) (s t : unitInterval)
  proof: by
  rw [← convexComb_symm]; rw [← convexComb_symm y x]; rw [convexComb_assoc]; rw [← convexComb_symm x]; rw [← convexComb_symm z y]
  rw [convexComb_assoc_coeff₁']; rw [convexComb_assoc_coeff₂']; rw [unitInterval.symm_symm]

中文:
定理 convexComb_assoc'
  条件: {a b : 实数} (x y z : 闭区间 a b) (s t : unit整数erval)
  证明: by
  rw [← convexComb_symm]; rw [← convexComb_symm y x]; rw [convexComb_assoc]; rw [← convexComb_symm x]; rw [← convexComb_symm z y]
  rw [convexComb_assoc_coeff₁']; rw [convexComb_assoc_coeff₂']; rw [unitInterval.symm_symm]

Depends on / 依赖: convexComb_assoc, convexComb_symm, symm_symm, unitInterval, unitInterval.symm_symm
-/
theorem convexComb_assoc' {a b : Real} (x y z : Icc a b) (s t : unitInterval) :
    convexComb (convexComb x y s) z t =
      convexComb x (convexComb y z (convexComb_assoc_coeff₂' s t))
        (convexComb_assoc_coeff₁' s t) := by
  rw [← convexComb_symm]; rw [← convexComb_symm y x]; rw [convexComb_assoc]; rw [← convexComb_symm x]; rw [← convexComb_symm z y]
  rw [convexComb_assoc_coeff₁']; rw [convexComb_assoc_coeff₂']; rw [unitInterval.symm_symm]

set_option backward.privateInPublic true in
/--
theorem `eq_convexComb.zero_le` / 定理 `eq_convexComb.zero_le`

English:
theorem eq_convexComb.zero_le
  given: {a b : Real} {x y z : Icc a b} (hxy : x <= y) (hyz : y <= z)
  proof: by
  by_cases h : (z - x : Real) = 0
  · simp_all
  · replace hxy : (x : Real) <= (y : Real) := hxy
    replace hyz : (y : Real) <= (z : Real) := hyz
    apply div_nonneg <;> grind

中文:
定理 eq_convexComb.zero_le
  条件: {a b : 实数} {x y z : 闭区间 a b} (hxy : x <= y) (hyz : y <= z)
  证明: by
  by_cases h : (z - x : Real) = 0
  · simp_all
  · replace hxy : (x : Real) <= (y : Real) := hxy
    replace hyz : (y : Real) <= (z : Real) := hyz
    apply div_nonneg <;> grind
-/
private theorem eq_convexComb.zero_le {a b : Real} {x y z : Icc a b} (hxy : x <= y) (hyz : y <= z) :
    0 <= ((y - x) / (z - x) : Real) := by
  by_cases h : (z - x : Real) = 0
  · simp_all
  · replace hxy : (x : Real) <= (y : Real) := hxy
    replace hyz : (y : Real) <= (z : Real) := hyz
    apply div_nonneg <;> grind

set_option backward.privateInPublic true in
/--
theorem `eq_convexComb.le_one` / 定理 `eq_convexComb.le_one`

English:
theorem eq_convexComb.le_one
  given: {a b : Real} {x y z : Icc a b} (hxy : x <= y) (hyz : y <= z)
  proof: by
  by_cases h : (z - x : Real) = 0
  · simp_all
  · replace hxy : (x : Real) <= (y : Real) := hxy
    replace hyz : (y : Real) <= (z : Real) := hyz
    apply div_le_one_of_le₀ <;> grind

中文:
定理 eq_convexComb.le_one
  条件: {a b : 实数} {x y z : 闭区间 a b} (hxy : x <= y) (hyz : y <= z)
  证明: by
  by_cases h : (z - x : Real) = 0
  · simp_all
  · replace hxy : (x : Real) <= (y : Real) := hxy
    replace hyz : (y : Real) <= (z : Real) := hyz
    apply div_le_one_of_le₀ <;> grind
-/
private theorem eq_convexComb.le_one {a b : Real} {x y z : Icc a b} (hxy : x <= y) (hyz : y <= z) :
    ((y - x) / (z - x) : Real) <= 1 := by
  by_cases h : (z - x : Real) = 0
  · simp_all
  · replace hxy : (x : Real) <= (y : Real) := hxy
    replace hyz : (y : Real) <= (z : Real) := hyz
    apply div_le_one_of_le₀ <;> grind

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `eq_convexComb` / 定理 `eq_convexComb`

English:
theorem eq_convexComb
  given: {a b : Real} {x y z : Icc a b} (hxy : x <= y) (hyz : y <= z)
  proof: by
  ext
  simp only [coe_convexComb]
  by_cases h : (z - x : Real) = 0
  · simp_all only [div_zero, sub_zero, one_mul, zero_mul, add_zero]
    replace hxy : (x : Real) <= (y : Real) := hxy
    replace hyz : (y : Real) <= (z : Real) := hyz
    linarith
  · field_simp
    ring_nf

中文:
定理 eq_convexComb
  条件: {a b : 实数} {x y z : 闭区间 a b} (hxy : x <= y) (hyz : y <= z)
  证明: by
  ext
  simp only [coe_convexComb]
  by_cases h : (z - x : Real) = 0
  · simp_all only [div_zero, sub_zero, one_mul, zero_mul, add_zero]
    replace hxy : (x : Real) <= (y : Real) := hxy
    replace hyz : (y : Real) <= (z : Real) := hyz
    linarith
  · field_simp
    ring_nf

Depends on / 依赖: add_zero, coe_convexComb, div_zero, one_mul, replace, ring_nf, sub_zero, zero_mul
-/
theorem eq_convexComb {a b : Real} {x y z : Icc a b} (hxy : x <= y) (hyz : y <= z) :
    y = convexComb x z ⟨((y - x) / (z - x)),
          eq_convexComb.zero_le hxy hyz, eq_convexComb.le_one hxy hyz⟩ := by
  ext
  simp only [coe_convexComb]
  by_cases h : (z - x : Real) = 0
  · simp_all only [div_zero, sub_zero, one_mul, zero_mul, add_zero]
    replace hxy : (x : Real) <= (y : Real) := hxy
    replace hyz : (y : Real) <= (z : Real) := hyz
    linarith
  · field_simp
    ring_nf

end Set.Icc

open scoped unitInterval

/--
lemma `exists_monotone_Icc_subset_open_cover_Icc` / 引理 `exists_monotone_Icc_subset_open_cover_Icc`

English:
lemma exists_monotone_Icc_subset_open_cover_Icc
  statement: {ι} {a b : Real} (h : a <= b) {c : ι -> Set (Icc a b)}
  proof: by
  obtain ⟨δ, δ_pos, ball_subset⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc₁ hc₂
  have hδ := half_pos δ_pos
  refine ⟨addNSMul h (δ/2), addNSMul_zero h,
    monotone_addNSMul h hδ.le, addNSMul_eq_right h hδ, fun n => ?_⟩
  obtain ⟨i, hsub⟩ := ball_subset (addNSMul h (δ / 2) n) trivial


中文:
引理 存在_monotone_Icc_subset_open_cover_Icc
  结论: {ι} {a b : 实数} (h : a <= b) {c : ι -> 集合 (闭区间 a b)}
  证明: by
  obtain ⟨δ, δ_pos, ball_subset⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc₁ hc₂
  have hδ := half_pos δ_pos
  refine ⟨addNSMul h (δ/2), addNSMul_zero h,
    monotone_addNSMul h hδ.le, addNSMul_eq_right h hδ, fun n => ?_⟩
  obtain ⟨i, hsub⟩ := ball_subset (addNSMul h (δ / 2) n) trivial


Depends on / 依赖: abs_sub_addNSMul_le, addNSMul, addNSMul_eq_right, addNSMul_zero, ball_subset, half_lt_self, half_pos, isCompact_univ, lebesgue_number_lemma_of_metric, monotone_addNSMul, trans_lt
-/
lemma exists_monotone_Icc_subset_open_cover_Icc {ι} {a b : Real} (h : a <= b) {c : ι -> Set (Icc a b)}
    (hc₁ : forall i, IsOpen (c i)) (hc₂ : univ subseteq ⋃ i, c i) : exists t : Nat -> Icc a b, t 0 = a ∧
      Monotone t ∧ (exists m, forall n >= m, t n = b) ∧ forall n, exists i, Icc (t n) (t (n + 1)) subseteq c i := by
  obtain ⟨δ, δ_pos, ball_subset⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc₁ hc₂
  have hδ := half_pos δ_pos
  refine ⟨addNSMul h (δ/2), addNSMul_zero h,
    monotone_addNSMul h hδ.le, addNSMul_eq_right h hδ, fun n => ?_⟩
  obtain ⟨i, hsub⟩ := ball_subset (addNSMul h (δ / 2) n) trivial
  exact ⟨i, fun t ht => hsub ((abs_sub_addNSMul_le h hδ.le n ht).trans_lt <| half_lt_self δ_pos)⟩

/--
lemma `exists_monotone_Icc_subset_open_cover_unitInterval` / 引理 `exists_monotone_Icc_subset_open_cover_unitInterval`

English:
lemma exists_monotone_Icc_subset_open_cover_unitInterval
  statement: {ι} {c : ι -> Set I}
  proof: by
  simp_rw [← Subtype.coe_inj]
  exact exists_monotone_Icc_subset_open_cover_Icc zero_le_one hc₁ hc₂

中文:
引理 存在_monotone_Icc_subset_open_cover_unit整数erval
  结论: {ι} {c : ι -> 集合 I}
  证明: by
  simp_rw [← Subtype.coe_inj]
  exact exists_monotone_Icc_subset_open_cover_Icc zero_le_one hc₁ hc₂

Depends on / 依赖: Subtype, Subtype.coe_inj, coe_inj, exists_monotone_Icc_subset_open_cover_Icc, simp_rw, zero_le_one
-/
lemma exists_monotone_Icc_subset_open_cover_unitInterval {ι} {c : ι -> Set I}
    (hc₁ : forall i, IsOpen (c i)) (hc₂ : univ subseteq ⋃ i, c i) : exists t : Nat -> I, t 0 = 0 ∧
      Monotone t ∧ (exists n, forall m >= n, t m = 1) ∧ forall n, exists i, Icc (t n) (t (n + 1)) subseteq c i := by
  simp_rw [← Subtype.coe_inj]
  exact exists_monotone_Icc_subset_open_cover_Icc zero_le_one hc₁ hc₂

/--
lemma `exists_monotone_Icc_subset_open_cover_unitInterval_prod_self` / 引理 `exists_monotone_Icc_subset_open_cover_unitInterval_prod_self`

English:
lemma exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
  statement: {ι} {c : ι -> Set (I × I)}
  proof: by
  obtain ⟨δ, δ_pos, ball_subset⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc₁ hc₂
  have hδ := half_pos δ_pos
  simp_rw [Subtype.ext_iff]
  have h : (0 : Real) <= 1 := zero_le_one
  refine ⟨addNSMul h (δ/2), addNSMul_zero h,
    monotone_addNSMul h hδ.le, addNSMul_eq_right h hδ, fun n m 

中文:
引理 存在_monotone_Icc_subset_open_cover_unit整数erval_prod_self
  结论: {ι} {c : ι -> 集合 (I × I)}
  证明: by
  obtain ⟨δ, δ_pos, ball_subset⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc₁ hc₂
  have hδ := half_pos δ_pos
  simp_rw [Subtype.ext_iff]
  have h : (0 : Real) <= 1 := zero_le_one
  refine ⟨addNSMul h (δ/2), addNSMul_zero h,
    monotone_addNSMul h hδ.le, addNSMul_eq_right h hδ, fun n m 

Depends on / 依赖: Metric, Metric.mem_ball.mpr, Subtype, Subtype.ext_iff, abs_sub_addNSMul_le, addNSMul, addNSMul_eq_right, addNSMul_zero, ball_subset, ext_iff, half_pos, isCompact_univ, lebesgue_number_lemma_of_metric, max_le, mem_ball, monotone_addNSMul, simp_rw, zero_le_one
-/
lemma exists_monotone_Icc_subset_open_cover_unitInterval_prod_self {ι} {c : ι -> Set (I × I)}
    (hc₁ : forall i, IsOpen (c i)) (hc₂ : univ subseteq ⋃ i, c i) :
    exists t : Nat -> I, t 0 = 0 ∧ Monotone t ∧ (exists n, forall m >= n, t m = 1) ∧
      forall n m, exists i, Icc (t n) (t (n + 1)) ×ˢ Icc (t m) (t (m + 1)) subseteq c i := by
  obtain ⟨δ, δ_pos, ball_subset⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc₁ hc₂
  have hδ := half_pos δ_pos
  simp_rw [Subtype.ext_iff]
  have h : (0 : Real) <= 1 := zero_le_one
  refine ⟨addNSMul h (δ/2), addNSMul_zero h,
    monotone_addNSMul h hδ.le, addNSMul_eq_right h hδ, fun n m => ?_⟩
  obtain ⟨i, hsub⟩ := ball_subset (addNSMul h (δ / 2) n, addNSMul h (δ / 2) m) trivial
  exact ⟨i, fun t ht => hsub (Metric.mem_ball.mpr <| (max_le (abs_sub_addNSMul_le h hδ.le n ht.1) <|
    abs_sub_addNSMul_le h hδ.le m ht.2).trans_lt <| half_lt_self δ_pos)⟩

end partition

@[simp]
/--
theorem `projIcc_eq_zero` / 定理 `projIcc_eq_zero`

English:
theorem projIcc_eq_zero
  given: {x : Real}
  statement: projIcc (0 : Real) 1 zero_le_one x = 0 ↔ x <= 0
  proof: projIcc_eq_left zero_lt_one

@[simp]

中文:
定理 projIcc_eq_zero
  条件: {x : 实数}
  结论: projIcc (0 : 实数) 1 zero_le_one x = 0 ↔ x <= 0
  证明: projIcc_eq_left zero_lt_one

@[simp]

Depends on / 依赖: projIcc_eq_left, zero_lt_one
-/
theorem projIcc_eq_zero {x : Real} : projIcc (0 : Real) 1 zero_le_one x = 0 ↔ x <= 0 :=
  projIcc_eq_left zero_lt_one

@[simp]
/--
theorem `projIcc_eq_one` / 定理 `projIcc_eq_one`

English:
theorem projIcc_eq_one
  given: {x : Real}
  statement: projIcc (0 : Real) 1 zero_le_one x = 1 ↔ 1 <= x
  proof: projIcc_eq_right zero_lt_one

中文:
定理 projIcc_eq_one
  条件: {x : 实数}
  结论: projIcc (0 : 实数) 1 zero_le_one x = 1 ↔ 1 <= x
  证明: projIcc_eq_right zero_lt_one

Depends on / 依赖: projIcc_eq_right, zero_lt_one
-/
theorem projIcc_eq_one {x : Real} : projIcc (0 : Real) 1 zero_le_one x = 1 ↔ 1 <= x :=
  projIcc_eq_right zero_lt_one

namespace Mathlib.Tactic.Interactive

/--
`unit_interval` solves the goals `0 ≤ ↑x`, `0 ≤ 1 - ↑x`, `↑x ≤ 1`, and `1 - ↑x ≤ 1` for
any expression `x : I`.
-/
macro "unit_interval" : tactic =>
  `(tactic| (first
  | apply unitInterval.nonneg
  | apply unitInterval.one_minus_nonneg
  | apply unitInterval.le_one
  | apply unitInterval.one_minus_le_one))

example (x : unitInterval) : 0 <= (x : Real) := by unit_interval

end Mathlib.Tactic.Interactive

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]

set_option backward.isDefEq.respectTransparency false in
-- We only need the ordering on `𝕜` here to avoid talking about flipping the interval over.
-- At the end of the day I only care about `ℝ`, so I'm hesitant to put work into generalizing.
/--
theorem `affineHomeomorph_image_I` / 定理 `affineHomeomorph_image_I`

English:
theorem affineHomeomorph_image_I
  given: (a b : 𝕜) (h : 0 < a)
  proof: by simp [h]

中文:
定理 affineHomeomorph_image_I
  条件: (a b : 𝕜) (h : 0 < a)
  证明: by simp [h]
-/
theorem affineHomeomorph_image_I (a b : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne.symm '' Set.Icc 0 1 = Set.Icc b (a + b) := by simp [h]

/--
Definition of `iccHomeoI` / `iccHomeoI` 的定义

English:
definition iccHomeoI
  signature: (a b : 𝕜) (h : a < b)
  body: by
  let e := Homeomorph.image (affineHomeomorph (b - a) a (sub_pos.mpr h).ne.symm) (Set.Icc 0 1)
  refine (e.trans ?_).symm
  apply Homeomorph.setCongr
  rw [affineHomeomorph_image_I _ _ (sub_pos.2 h)]
  simp

@[simp]

中文:
定义 iccHomeoI
  签名: (a b : 𝕜) (h : a < b)
  定义体: by
  let e := Homeomorph.image (affineHomeomorph (b - a) a (sub_pos.mpr h).ne.symm) (Set.Icc 0 1)
  refine (e.trans ?_).symm
  apply Homeomorph.setCongr
  rw [affineHomeomorph_image_I _ _ (sub_pos.2 h)]
  simp

@[simp]

Depends on / 依赖: Homeomorph, Homeomorph.image, Homeomorph.setCongr, Set.Icc, affineHomeomorph, affineHomeomorph_image_I, e.trans, ne.symm, setCongr, sub_pos, sub_pos.mpr
-/
def iccHomeoI (a b : 𝕜) (h : a < b) : Set.Icc a b ≃ₜ Set.Icc (0 : 𝕜) (1 : 𝕜) := by
  let e := Homeomorph.image (affineHomeomorph (b - a) a (sub_pos.mpr h).ne.symm) (Set.Icc 0 1)
  refine (e.trans ?_).symm
  apply Homeomorph.setCongr
  rw [affineHomeomorph_image_I _ _ (sub_pos.2 h)]
  simp

@[simp]
/--
theorem `iccHomeoI_apply_coe` / 定理 `iccHomeoI_apply_coe`

English:
theorem iccHomeoI_apply_coe
  given: (a b : 𝕜) (h : a < b) (x : Set.Icc a b)
  proof: rfl

@[simp]

中文:
定理 iccHomeoI_apply_coe
  条件: (a b : 𝕜) (h : a < b) (x : 集合.闭区间 a b)
  证明: rfl

@[simp]
-/
theorem iccHomeoI_apply_coe (a b : 𝕜) (h : a < b) (x : Set.Icc a b) :
    ((iccHomeoI a b h) x : 𝕜) = (x - a) / (b - a) :=
  rfl

@[simp]
/--
theorem `iccHomeoI_symm_apply_coe` / 定理 `iccHomeoI_symm_apply_coe`

English:
theorem iccHomeoI_symm_apply_coe
  given: (a b : 𝕜) (h : a < b) (x : Set.Icc (0 : 𝕜) (1 : 𝕜))
  proof: rfl

中文:
定理 iccHomeoI_symm_apply_coe
  条件: (a b : 𝕜) (h : a < b) (x : 集合.闭区间 (0 : 𝕜) (1 : 𝕜))
  证明: rfl
-/
theorem iccHomeoI_symm_apply_coe (a b : 𝕜) (h : a < b) (x : Set.Icc (0 : 𝕜) (1 : 𝕜)) :
    ((iccHomeoI a b h).symm x : 𝕜) = (b - a) * x + a :=
  rfl

end

namespace unitInterval

open NNReal

/--
Definition of `toNNReal` / `toNNReal` 的定义

English:
definition toNNReal
  signature: : I -> Real>=0
  body: fun i => ⟨i.1, i.2.1⟩

中文:
定义 toNN实数
  签名: : I -> 实数>=0
  定义体: fun i => ⟨i.1, i.2.1⟩
-/
def toNNReal : I -> Real>=0 := fun i => ⟨i.1, i.2.1⟩

/--
lemma `toNNReal_zero` / 引理 `toNNReal_zero`

English:
lemma toNNReal_zero
  statement: toNNReal 0 = 0
  proof: rfl

中文:
引理 toNN实数_zero
  结论: toNN实数 0 = 0
  证明: rfl
-/
@[simp] lemma toNNReal_zero : toNNReal 0 = 0 := rfl

/--
lemma `toNNReal_one` / 引理 `toNNReal_one`

English:
lemma toNNReal_one
  statement: toNNReal 1 = 1
  proof: rfl

中文:
引理 toNN实数_one
  结论: toNN实数 1 = 1
  证明: rfl
-/
@[simp] lemma toNNReal_one : toNNReal 1 = 1 := rfl

/--
lemma `toNNReal_continuous` / 引理 `toNNReal_continuous`

English:
lemma toNNReal_continuous
  statement: Continuous toNNReal
  proof: by delta toNNReal; fun_prop

中文:
引理 toNN实数_continuous
  结论: 连续 toNN实数
  证明: by delta toNNReal; fun_prop
-/
@[fun_prop] lemma toNNReal_continuous : Continuous toNNReal := by delta toNNReal; fun_prop

/--
lemma `coe_toNNReal` / 引理 `coe_toNNReal`

English:
lemma coe_toNNReal
  given: (x : I)
  statement: ((toNNReal x) : Real) = x
  proof: rfl

中文:
引理 coe_toNN实数
  条件: (x : I)
  结论: ((toNN实数 x) : 实数) = x
  证明: rfl
-/
@[simp] lemma coe_toNNReal (x : I) : ((toNNReal x) : Real) = x := rfl

/--
lemma `toNNReal_add_toNNReal_symm` / 引理 `toNNReal_add_toNNReal_symm`

English:
lemma toNNReal_add_toNNReal_symm
  given: (x : I)
  statement: toNNReal x + toNNReal (σ x) = 1
  proof: by ext; simp

中文:
引理 toNN实数_add_toNN实数_symm
  条件: (x : I)
  结论: toNN实数 x + toNN实数 (σ x) = 1
  证明: by ext; simp
-/
@[simp] lemma toNNReal_add_toNNReal_symm (x : I) : toNNReal x + toNNReal (σ x) = 1 := by ext; simp
/--
lemma `toNNReal_symm_add_toNNReal` / 引理 `toNNReal_symm_add_toNNReal`

English:
lemma toNNReal_symm_add_toNNReal
  given: (x : I)
  statement: toNNReal (σ x) + toNNReal x = 1
  proof: by ext; simp

中文:
引理 toNN实数_symm_add_toNN实数
  条件: (x : I)
  结论: toNN实数 (σ x) + toNN实数 x = 1
  证明: by ext; simp
-/
@[simp] lemma toNNReal_symm_add_toNNReal (x : I) : toNNReal (σ x) + toNNReal x = 1 := by ext; simp

end unitInterval
