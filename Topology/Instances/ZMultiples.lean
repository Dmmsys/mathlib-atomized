/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Metrizable.Basic

/-!
The subgroup "multiples of `a`" (`zmultiples a`) is a discrete subgroup of `ℝ`, i.e. its
intersection with compact sets is finite.
-/

public section


noncomputable section

open Filter Int Metric Set TopologicalSpace Bornology
open scoped Topology Uniformity Interval

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace Int

open Metric

/-- This is a special case of `NormedSpace.discreteTopology_zmultiples`. It exists only to simplify
dependencies. -/
instance {a : Real} : DiscreteTopology (AddSubgroup.zmultiples a) := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · rw [AddSubgroup.zmultiples_zero_eq_bot]
    exact Subsingleton.discreteTopology (α := (⊥ : Submodule Int Real))
  rw [discreteTopology_iff_isOpen_singleton_zero]; rw [isOpen_induced_iff]
  refine ⟨ball 0 |a|, isOpen_ball, ?_⟩
  ext ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  simp [ha, Real.dist_eq, abs_mul, (by norm_cast : |(k : Real)| < 1 ↔ |k| < 1)]

/--
theorem `tendsto_coe_cofinite` / 定理 `tendsto_coe_cofinite`

English:
theorem tendsto_coe_cofinite
  statement: Tendsto ((↑) : Int -> Real) cofinite (cocompact Real)
  proof: by
  apply (castAddHom Real).tendsto_coe_cofinite_of_discrete cast_injective
  rw [range_castAddHom]; rw [SetLike.isDiscrete_iff_discreteTopology]
  infer_instance

中文:
定理 tendsto_coe_cofinite
  结论: Tendsto ((↑) : 整数 -> 实数) cofinite (cocompact 实数)
  证明: by
  apply (castAddHom Real).tendsto_coe_cofinite_of_discrete cast_injective
  rw [range_castAddHom]; rw [SetLike.isDiscrete_iff_discreteTopology]
  infer_instance

Depends on / 依赖: SetLike, SetLike.isDiscrete_iff_discreteTopology, castAddHom, cast_injective, infer_instance, isDiscrete_iff_discreteTopology, range_castAddHom, tendsto_coe_cofinite_of_discrete
-/
theorem tendsto_coe_cofinite : Tendsto ((↑) : Int -> Real) cofinite (cocompact Real) := by
  apply (castAddHom Real).tendsto_coe_cofinite_of_discrete cast_injective
  rw [range_castAddHom]; rw [SetLike.isDiscrete_iff_discreteTopology]
  infer_instance

/--
theorem `tendsto_zmultiplesHom_cofinite` / 定理 `tendsto_zmultiplesHom_cofinite`

English:
theorem tendsto_zmultiplesHom_cofinite
  given: {a : Real} (ha : a != 0)
  proof: by
apply (zmultiplesHom Real a).tendsto_coe_cofinite_of_discrete smul_left_injective Int ha
  rw [AddSubgroup.range_zmultiplesHom]; rw [SetLike.isDiscrete_iff_discreteTopology]
  infer_instance

中文:
定理 tendsto_zmultiplesHom_cofinite
  条件: {a : 实数} (ha : a != 0)
  证明: by
apply (zmultiplesHom Real a).tendsto_coe_cofinite_of_discrete smul_left_injective Int ha
  rw [AddSubgroup.range_zmultiplesHom]; rw [SetLike.isDiscrete_iff_discreteTopology]
  infer_instance

Depends on / 依赖: AddSubgroup, AddSubgroup.range_zmultiplesHom, SetLike, SetLike.isDiscrete_iff_discreteTopology, infer_instance, isDiscrete_iff_discreteTopology, range_zmultiplesHom, smul_left_injective, tendsto_coe_cofinite_of_discrete, zmultiplesHom
-/
theorem tendsto_zmultiplesHom_cofinite {a : Real} (ha : a != 0) :
    Tendsto (zmultiplesHom Real a) cofinite (cocompact Real) := by
apply (zmultiplesHom Real a).tendsto_coe_cofinite_of_discrete smul_left_injective Int ha
  rw [AddSubgroup.range_zmultiplesHom]; rw [SetLike.isDiscrete_iff_discreteTopology]
  infer_instance

end Int

namespace AddSubgroup

/--
theorem `tendsto_zmultiples_subtype_cofinite` / 定理 `tendsto_zmultiples_subtype_cofinite`

English:
theorem tendsto_zmultiples_subtype_cofinite
  given: (a : Real)
  proof: by
  refine (zmultiples a).tendsto_coe_cofinite_of_discrete ?_
  rw [SetLike.isDiscrete_iff_discreteTopology]
  infer_instance

中文:
定理 tendsto_zmultiples_subtype_cofinite
  条件: (a : 实数)
  证明: by
  refine (zmultiples a).tendsto_coe_cofinite_of_discrete ?_
  rw [SetLike.isDiscrete_iff_discreteTopology]
  infer_instance

Depends on / 依赖: SetLike, SetLike.isDiscrete_iff_discreteTopology, infer_instance, isDiscrete_iff_discreteTopology, tendsto_coe_cofinite_of_discrete, zmultiples
-/
theorem tendsto_zmultiples_subtype_cofinite (a : Real) :
    Tendsto (zmultiples a).subtype cofinite (cocompact Real) := by
  refine (zmultiples a).tendsto_coe_cofinite_of_discrete ?_
  rw [SetLike.isDiscrete_iff_discreteTopology]
  infer_instance

end AddSubgroup
