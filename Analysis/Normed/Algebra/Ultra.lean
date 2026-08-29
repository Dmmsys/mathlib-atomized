/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.Analysis.Normed.Field.Ultra
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Normed algebra preserves ultrametricity

This file contains the proof that a normed division ring over an ultrametric field is ultrametric.
-/

public section

variable {K L : Type*} [NormedField K]

variable (L) in
/--
theorem `IsUltrametricDist.of_normedAlgebra'` / 定理 `IsUltrametricDist.of_normedAlgebra'`

English:
theorem IsUltrametricDist.of_normedAlgebra'
  statement: [SeminormedRing L] [NormOneClass L] [NormedAlgebra K L]
  proof: ⟨fun x y z => by
    simpa using h.dist_triangle_max (algebraMap K L x) (algebraMap K L y) (algebraMap K L z)⟩

中文:
定理 是UltrametricDist.of_normedAlgebra'
  结论: [Seminormed环 L] [NormOne类 L] [赋范代数 K L]
  证明: ⟨fun x y z => by
    simpa using h.dist_triangle_max (algebraMap K L x) (algebraMap K L y) (algebraMap K L z)⟩

Depends on / 依赖: algebraMap, dist_triangle_max, h.dist_triangle_max
-/
theorem IsUltrametricDist.of_normedAlgebra' [SeminormedRing L] [NormOneClass L] [NormedAlgebra K L]
    [h : IsUltrametricDist L] : IsUltrametricDist K :=
  ⟨fun x y z => by
    simpa using h.dist_triangle_max (algebraMap K L x) (algebraMap K L y) (algebraMap K L z)⟩

variable (K) in
/--
theorem `IsUltrametricDist.of_normedAlgebra` / 定理 `IsUltrametricDist.of_normedAlgebra`

English:
theorem IsUltrametricDist.of_normedAlgebra
  statement: [NormedDivisionRing L] [NormedAlgebra K L]
  proof: by
  rw [isUltrametricDist_iff_forall_norm_natCast_le_one] at h ⊢
  exact fun n => (algebraMap.coe_natCast (R := K) (A := L) n) ▸ norm_algebraMap' L (n : K) ▸ h n

中文:
定理 是UltrametricDist.of_normedAlgebra
  结论: [NormedDivision环 L] [赋范代数 K L]
  证明: by
  rw [isUltrametricDist_iff_forall_norm_natCast_le_one] at h ⊢
  exact fun n => (algebraMap.coe_natCast (R := K) (A := L) n) ▸ norm_algebraMap' L (n : K) ▸ h n

Depends on / 依赖: algebraMap, algebraMap.coe_natCast, coe_natCast, isUltrametricDist_iff_forall_norm_natCast_le_one, norm_algebraMap
-/
theorem IsUltrametricDist.of_normedAlgebra [NormedDivisionRing L] [NormedAlgebra K L]
    [h : IsUltrametricDist K] : IsUltrametricDist L := by
  rw [isUltrametricDist_iff_forall_norm_natCast_le_one] at h ⊢
  exact fun n => (algebraMap.coe_natCast (R := K) (A := L) n) ▸ norm_algebraMap' L (n : K) ▸ h n

variable (K L) in
/--
theorem `IsUltrametricDist.normedAlgebra_iff` / 定理 `IsUltrametricDist.normedAlgebra_iff`

English:
theorem IsUltrametricDist.normedAlgebra_iff
  given: [NormedDivisionRing L] [NormedAlgebra K L]
  proof: ⟨fun _ => IsUltrametricDist.of_normedAlgebra' L, fun _ => IsUltrametricDist.of_normedAlgebra K⟩

中文:
定理 是UltrametricDist.normedAlgebra_iff
  条件: [NormedDivision环 L] [赋范代数 K L]
  证明: ⟨fun _ => IsUltrametricDist.of_normedAlgebra' L, fun _ => IsUltrametricDist.of_normedAlgebra K⟩

Depends on / 依赖: IsUltrametricDist, IsUltrametricDist.of_normedAlgebra, of_normedAlgebra
-/
theorem IsUltrametricDist.normedAlgebra_iff [NormedDivisionRing L] [NormedAlgebra K L] :
    IsUltrametricDist L ↔ IsUltrametricDist K :=
  ⟨fun _ => IsUltrametricDist.of_normedAlgebra' L, fun _ => IsUltrametricDist.of_normedAlgebra K⟩
