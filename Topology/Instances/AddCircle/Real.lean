/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Topology.Instances.ZMultiples

/-!
# The additive circle over `ℝ`

Results specific to the additive circle over `ℝ`.
-/

@[expose] public section


noncomputable section

open AddCommGroup Set Function AddSubgroup TopologicalSpace Topology

namespace AddCircle

variable (p : Real)

/--
Instance `pathConnectedSpace` / 实例 `pathConnectedSpace`

English:
instance pathConnectedSpace
  signature: : PathConnectedSpace AddCircle p
  body: inferInstanceAs PathConnectedSpace (Quotient _)

中文:
实例 pathConnectedSpace
  签名: : 道路连通空间 AddCircle p
  定义体: inferInstanceAs PathConnectedSpace (Quotient _)

Depends on / 依赖: PathConnectedSpace, Quotient
-/
instance pathConnectedSpace : PathConnectedSpace AddCircle p :=
inferInstanceAs PathConnectedSpace (Quotient _)

/--
Instance `compactSpace` / 实例 `compactSpace`

English:
instance compactSpace
  signature: [Fact (0 < p)]
  body: by
  rw [← isCompact_univ_iff]; rw [← coe_image_Icc_eq p 0]
  exact isCompact_Icc.image (AddCircle.continuous_mk' p)

中文:
实例 compactSpace
  签名: [Fact (0 < p)]
  定义体: by
  rw [← isCompact_univ_iff]; rw [← coe_image_Icc_eq p 0]
  exact isCompact_Icc.image (AddCircle.continuous_mk' p)

Depends on / 依赖: AddCircle, AddCircle.continuous_mk, coe_image_Icc_eq, continuous_mk, isCompact_Icc, isCompact_Icc.image, isCompact_univ_iff
-/
instance compactSpace [Fact (0 < p)] : CompactSpace AddCircle p := by
  rw [← isCompact_univ_iff]; rw [← coe_image_Icc_eq p 0]
  exact isCompact_Icc.image (AddCircle.continuous_mk' p)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ProperlyDiscontinuousVAdd (zmultiples p).op Real
  body: (zmultiples p).properlyDiscontinuousVAdd_opposite_of_tendsto_cofinite
    (AddSubgroup.tendsto_zmultiples_subtype_cofinite p)

中文:
实例 :
  签名: ProperlyDiscontinuousVAdd (zmultiples p).op 实数
  定义体: (zmultiples p).properlyDiscontinuousVAdd_opposite_of_tendsto_cofinite
    (AddSubgroup.tendsto_zmultiples_subtype_cofinite p)

Depends on / 依赖: AddSubgroup, AddSubgroup.tendsto_zmultiples_subtype_cofinite, properlyDiscontinuousVAdd_opposite_of_tendsto_cofinite, tendsto_zmultiples_subtype_cofinite, zmultiples
-/
instance : ProperlyDiscontinuousVAdd (zmultiples p).op Real :=
  (zmultiples p).properlyDiscontinuousVAdd_opposite_of_tendsto_cofinite
    (AddSubgroup.tendsto_zmultiples_subtype_cofinite p)

end AddCircle

section UnitAddCircle

/--
Definition of `UnitAddCircle` / `UnitAddCircle` 的定义

English:
abbreviation UnitAddCircle
  body: AddCircle (1 : Real)

中文:
缩写 UnitAddCircle
  定义体: AddCircle (1 : Real)

Depends on / 依赖: AddCircle
-/
abbrev UnitAddCircle :=
  AddCircle (1 : Real)

/--
Definition of `UnitAddTorus` / `UnitAddTorus` 的定义

English:
abbreviation UnitAddTorus
  signature: (d : Type*)
  body: d -> UnitAddCircle

中文:
缩写 UnitAddTorus
  签名: (d : 类型)
  定义体: d -> UnitAddCircle

Depends on / 依赖: UnitAddCircle
-/
abbrev UnitAddTorus (d : Type*) := d -> UnitAddCircle

end UnitAddCircle

namespace ZMod

variable {N : Nat} [NeZero N]

/--
Definition of `toAddCircle` / `toAddCircle` 的定义

English:
definition toAddCircle
  signature: : ZMod N ->+ UnitAddCircle
  body: lift N ⟨AddMonoidHom.mk' (fun j => ↑(j / N : Real)) (by simp [add_div]),
    by simp [div_self (NeZero.ne _)]⟩

中文:
定义 toAddCircle
  签名: : ZMod N ->+ UnitAddCircle
  定义体: lift N ⟨AddMonoidHom.mk' (fun j => ↑(j / N : Real)) (by simp [add_div]),
    by simp [div_self (NeZero.ne _)]⟩

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, NeZero, NeZero.ne, add_div, div_self
-/
noncomputable def toAddCircle : ZMod N ->+ UnitAddCircle :=
  lift N ⟨AddMonoidHom.mk' (fun j => ↑(j / N : Real)) (by simp [add_div]),
    by simp [div_self (NeZero.ne _)]⟩

/--
lemma `toAddCircle_intCast` / 引理 `toAddCircle_intCast`

English:
lemma toAddCircle_intCast
  given: (j : Int)
  proof: by
  simp [toAddCircle]

中文:
引理 toAddCircle_intCast
  条件: (j : 整数)
  证明: by
  simp [toAddCircle]

Depends on / 依赖: toAddCircle
-/
lemma toAddCircle_intCast (j : Int) :
    toAddCircle (j : ZMod N) = ↑(j / N : Real) := by
  simp [toAddCircle]

/--
lemma `toAddCircle_natCast` / 引理 `toAddCircle_natCast`

English:
lemma toAddCircle_natCast
  given: (j : Nat)
  proof: by
  simpa using toAddCircle_intCast (N := N) j

中文:
引理 toAddCircle_natCast
  条件: (j : 自然数)
  证明: by
  simpa using toAddCircle_intCast (N := N) j

Depends on / 依赖: toAddCircle_intCast
-/
lemma toAddCircle_natCast (j : Nat) :
    toAddCircle (j : ZMod N) = ↑(j / N : Real) := by
  simpa using toAddCircle_intCast (N := N) j

/--
lemma `toAddCircle_apply` / 引理 `toAddCircle_apply`

English:
lemma toAddCircle_apply
  given: (j : ZMod N)
  proof: by
  rw [← toAddCircle_natCast]; rw [natCast_zmod_val]

中文:
引理 toAddCircle_apply
  条件: (j : ZMod N)
  证明: by
  rw [← toAddCircle_natCast]; rw [natCast_zmod_val]

Depends on / 依赖: natCast_zmod_val, toAddCircle_natCast
-/
lemma toAddCircle_apply (j : ZMod N) :
    toAddCircle j = ↑(j.val / N : Real) := by
  rw [← toAddCircle_natCast]; rw [natCast_zmod_val]

variable (N) in
/--
lemma `toAddCircle_injective` / 引理 `toAddCircle_injective`

English:
lemma toAddCircle_injective
  statement: Function.Injective (toAddCircle : ZMod N -> _)
  proof: by
  intro x y hxy
  have : (0 : Real) < N := Nat.cast_pos.mpr (NeZero.pos _)
  rwa [toAddCircle_apply, toAddCircle_apply, AddCircle.coe_eq_coe_iff_of_mem_Ico,
    div_left_inj' this.ne', Nat.cast_inj, (val_injective N).eq_iff] at hxy <;>
  exact ⟨by positivity, by simpa only [zero_add, div_lt_one t

中文:
引理 toAddCircle_injective
  结论: 函数.单射 (toAddCircle : ZMod N -> _)
  证明: by
  intro x y hxy
  have : (0 : Real) < N := Nat.cast_pos.mpr (NeZero.pos _)
  rwa [toAddCircle_apply, toAddCircle_apply, AddCircle.coe_eq_coe_iff_of_mem_Ico,
    div_left_inj' this.ne', Nat.cast_inj, (val_injective N).eq_iff] at hxy <;>
  exact ⟨by positivity, by simpa only [zero_add, div_lt_one t

Depends on / 依赖: AddCircle, AddCircle.coe_eq_coe_iff_of_mem_Ico, Nat.cast_inj, Nat.cast_lt, Nat.cast_pos.mpr, NeZero, NeZero.pos, cast_inj, cast_lt, cast_pos, coe_eq_coe_iff_of_mem_Ico, div_left_inj, div_lt_one, eq_iff, this.ne, toAddCircle_apply, val_injective, val_lt, zero_add
-/
lemma toAddCircle_injective : Function.Injective (toAddCircle : ZMod N -> _) := by
  intro x y hxy
  have : (0 : Real) < N := Nat.cast_pos.mpr (NeZero.pos _)
  rwa [toAddCircle_apply, toAddCircle_apply, AddCircle.coe_eq_coe_iff_of_mem_Ico,
    div_left_inj' this.ne', Nat.cast_inj, (val_injective N).eq_iff] at hxy <;>
  exact ⟨by positivity, by simpa only [zero_add, div_lt_one this, Nat.cast_lt] using val_lt _⟩

/--
lemma `toAddCircle_inj` / 引理 `toAddCircle_inj`

English:
lemma toAddCircle_inj
  given: {j k : ZMod N}
  statement: toAddCircle j = toAddCircle k ↔ j = k
  proof: (toAddCircle_injective N).eq_iff

中文:
引理 toAddCircle_inj
  条件: {j k : ZMod N}
  结论: toAddCircle j = toAddCircle k ↔ j = k
  证明: (toAddCircle_injective N).eq_iff
-/
@[simp] lemma toAddCircle_inj {j k : ZMod N} : toAddCircle j = toAddCircle k ↔ j = k :=
  (toAddCircle_injective N).eq_iff

/--
lemma `toAddCircle_eq_zero` / 引理 `toAddCircle_eq_zero`

English:
lemma toAddCircle_eq_zero
  given: {j : ZMod N}
  statement: toAddCircle j = 0 ↔ j = 0
  proof: map_eq_zero_iff _ (toAddCircle_injective N)

中文:
引理 toAddCircle_eq_zero
  条件: {j : ZMod N}
  结论: toAddCircle j = 0 ↔ j = 0
  证明: map_eq_zero_iff _ (toAddCircle_injective N)
-/
@[simp] lemma toAddCircle_eq_zero {j : ZMod N} : toAddCircle j = 0 ↔ j = 0 :=
  map_eq_zero_iff _ (toAddCircle_injective N)

end ZMod
