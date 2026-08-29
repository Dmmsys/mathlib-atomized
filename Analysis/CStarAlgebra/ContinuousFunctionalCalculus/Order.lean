/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-! # Facts about star-ordered rings that depend on the continuous functional calculus

This file contains various basic facts about star-ordered rings (i.e. mainly C⋆-algebras)
that depend on the continuous functional calculus.

We also put an order instance on `A⁺¹ := Unitization ℂ A` when `A` is a C⋆-algebra via
the spectral order.

## Main theorems

* `IsSelfAdjoint.le_algebraMap_norm_self` and `IsSelfAdjoint.le_algebraMap_norm_self`,
  which respectively show that `a ≤ algebraMap ℝ A ‖a‖` and `-(algebraMap ℝ A ‖a‖) ≤ a` in a
  C⋆-algebra.
* `mul_star_le_algebraMap_norm_sq` and `star_mul_le_algebraMap_norm_sq`, which give similar
  statements for `a * star a` and `star a * a`.
* `CStarAlgebra.norm_le_norm_of_nonneg_of_le`: in a non-unital C⋆-algebra, if `0 ≤ a ≤ b`, then
  `‖a‖ ≤ ‖b‖`.
* `CStarAlgebra.conjugate_le_norm_smul`: in a non-unital C⋆-algebra, we have that
  `star a * b * a ≤ ‖b‖ • (star a * a)` (and a primed version for the `a * b * star a` case).
* `CStarAlgebra.inv_le_inv_iff`: in a unital C⋆-algebra, `b⁻¹ ≤ a⁻¹` iff `a ≤ b`.

## Tags

continuous functional calculus, normal, selfadjoint
-/

public section

open scoped NNReal CStarAlgebra

local notation "σₙ" => quasispectrum

/--
theorem `cfc_tsub` / 定理 `cfc_tsub`

English:
theorem cfc_tsub
  statement: {A : Type*} [TopologicalSpace A] [Ring A] [PartialOrder A] [StarRing A]
  proof: by
  have ha' := SpectrumRestricts.nnreal_of_nonneg ha
  have : (spectrum Real a).EqOn (fun x => ((f x.toNNReal - g x.toNNReal : Real>=0) : Real))
      (fun x => f x.toNNReal - g x.toNNReal) :=
fun x hx => NNReal.coe_sub hfg _ ha'.apply_mem hx
  rw [cfc_nnreal_eq_real ..]; rw [cfc_nnreal_eq_real ..

中文:
定理 cfc_tsub
  结论: {A : 类型} [拓扑空间 A] [环 A] [偏序 A] [对合环 A]
  证明: by
  have ha' := SpectrumRestricts.nnreal_of_nonneg ha
  have : (spectrum Real a).EqOn (fun x => ((f x.toNNReal - g x.toNNReal : Real>=0) : Real))
      (fun x => f x.toNNReal - g x.toNNReal) :=
fun x hx => NNReal.coe_sub hfg _ ha'.apply_mem hx
  rw [cfc_nnreal_eq_real ..]; rw [cfc_nnreal_eq_real ..

Depends on / 依赖: ContinuousOn, NNReal, NNReal.coe_sub, SpectrumRestricts, SpectrumRestricts.nnreal_of_nonneg, apply_mem, cfc_cont_tac, cfc_nnreal_eq_rea, cfc_nnreal_eq_real, cfc_tac, coe_sub, nnreal_of_nonneg, spectrum, toNNReal, x.toNNReal
-/
theorem cfc_tsub {A : Type*} [TopologicalSpace A] [Ring A] [PartialOrder A] [StarRing A]
    [StarOrderedRing A] [Algebra Real A] [IsTopologicalRing A] [T2Space A]
    [ContinuousFunctionalCalculus Real A IsSelfAdjoint]
    [NonnegSpectrumClass Real A] (f g : Real>=0 -> Real>=0)
    (a : A) (hfg : forall x in spectrum Real>=0 a, g x <= f x) (ha : 0 <= a := by cfc_tac)
    (hf : ContinuousOn f (spectrum Real>=0 a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum Real>=0 a) := by cfc_cont_tac) :
    cfc (fun x => f x - g x) a = cfc f a - cfc g a := by
  have ha' := SpectrumRestricts.nnreal_of_nonneg ha
  have : (spectrum Real a).EqOn (fun x => ((f x.toNNReal - g x.toNNReal : Real>=0) : Real))
      (fun x => f x.toNNReal - g x.toNNReal) :=
fun x hx => NNReal.coe_sub hfg _ ha'.apply_mem hx
  rw [cfc_nnreal_eq_real ..]; rw [cfc_nnreal_eq_real ..]; rw [cfc_nnreal_eq_real ..]; rw [cfc_congr this]
  refine cfc_sub _ _ a ?_ ?_
  all_goals
exact continuous_subtype_val.comp_continuousOn
ContinuousOn.comp ‹_› continuous_real_toNNReal.continuousOn ha'.image ▸ Set.mapsTo_image ..

/--
theorem `cfcₙ_tsub` / 定理 `cfcₙ_tsub`

English:
theorem cfcₙ_tsub
  statement: {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [PartialOrder A] [StarRing A]
  proof: by
  have ha' := QuasispectrumRestricts.nnreal_of_nonneg ha
  have : (σₙ Real a).EqOn (fun x => ((f x.toNNReal - g x.toNNReal : Real>=0) : Real))
      (fun x => f x.toNNReal - g x.toNNReal) :=
fun x hx => NNReal.coe_sub hfg _ ha'.apply_mem hx
  rw [cfcₙ_nnreal_eq_real ..]; rw [cfcₙ_nnreal_eq_real .

中文:
定理 cfcₙ_tsub
  结论: {A : 类型} [拓扑空间 A] [非幺环 A] [偏序 A] [对合环 A]
  证明: by
  have ha' := QuasispectrumRestricts.nnreal_of_nonneg ha
  have : (σₙ Real a).EqOn (fun x => ((f x.toNNReal - g x.toNNReal : Real>=0) : Real))
      (fun x => f x.toNNReal - g x.toNNReal) :=
fun x hx => NNReal.coe_sub hfg _ ha'.apply_mem hx
  rw [cfcₙ_nnreal_eq_real ..]; rw [cfcₙ_nnreal_eq_real .

Depends on / 依赖: ContinuousOn, NNReal, NNReal.coe_sub, QuasispectrumRestricts, QuasispectrumRestricts.nnreal_of_nonneg, apply_mem, cfc_cont_tac, cfc_tac, cfc_zero_tac, coe_sub, nnreal_of_nonneg, toNNReal, x.toNNReal
-/
theorem cfcₙ_tsub {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [PartialOrder A] [StarRing A]
    [StarOrderedRing A] [Module Real A] [IsScalarTower Real A A] [SMulCommClass Real A A]
    [IsTopologicalRing A] [T2Space A] [NonUnitalContinuousFunctionalCalculus Real A IsSelfAdjoint]
    [NonnegSpectrumClass Real A] (f g : Real>=0 -> Real>=0)
    (a : A) (hfg : forall x in σₙ Real>=0 a, g x <= f x) (ha : 0 <= a := by cfc_tac)
    (hf : ContinuousOn f (σₙ Real>=0 a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ Real>=0 a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    cfcₙ (fun x => f x - g x) a = cfcₙ f a - cfcₙ g a := by
  have ha' := QuasispectrumRestricts.nnreal_of_nonneg ha
  have : (σₙ Real a).EqOn (fun x => ((f x.toNNReal - g x.toNNReal : Real>=0) : Real))
      (fun x => f x.toNNReal - g x.toNNReal) :=
fun x hx => NNReal.coe_sub hfg _ ha'.apply_mem hx
  rw [cfcₙ_nnreal_eq_real ..]; rw [cfcₙ_nnreal_eq_real ..]; rw [cfcₙ_nnreal_eq_real ..]; rw [cfcₙ_congr this]
  refine cfcₙ_sub _ _ a ?_ (by simpa) ?_
  all_goals
exact continuous_subtype_val.comp_continuousOn
ContinuousOn.comp ‹_› continuous_real_toNNReal.continuousOn ha'.image ▸ Set.mapsTo_image ..

namespace Unitization

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: : PartialOrder A⁺¹
  body: CStarAlgebra.spectralOrder _

中文:
实例 instPartialOrder
  签名: : 偏序 A⁺¹
  定义体: CStarAlgebra.spectralOrder _

Depends on / 依赖: CStarAlgebra, CStarAlgebra.spectralOrder, spectralOrder
-/
noncomputable instance instPartialOrder : PartialOrder A⁺¹ :=
    CStarAlgebra.spectralOrder _

/--
Instance `instStarOrderedRing` / 实例 `instStarOrderedRing`

English:
instance instStarOrderedRing
  signature: : StarOrderedRing A⁺¹
  body: CStarAlgebra.spectralOrderedRing _

中文:
实例 instStarOrderedRing
  签名: : StarOrdered环 A⁺¹
  定义体: CStarAlgebra.spectralOrderedRing _

Depends on / 依赖: CStarAlgebra, CStarAlgebra.spectralOrderedRing, spectralOrderedRing
-/
instance instStarOrderedRing : StarOrderedRing A⁺¹ :=
    CStarAlgebra.spectralOrderedRing _

/--
lemma `inr_le_iff` / 引理 `inr_le_iff`

English:
lemma inr_le_iff
  statement: (a b : A) (ha : IsSelfAdjoint a := by cfc_tac)
  proof: by
  -- TODO: prove the more general result for star monomorphisms and use it here.
  rw [← sub_nonneg]; rw [← sub_nonneg (a := b)]; rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := Real) _]; rw [← inr_sub Complex b a]; rw [← Unitization.quasispectrum_eq_spectrum_inr' Real Complex]
.symm exact S

中文:
引理 inr_le_iff
  结论: (a b : A) (ha : IsSelfAdjoint a := by cfc_tac)
  证明: by
  -- TODO: prove the more general result for star monomorphisms and use it here.
  rw [← sub_nonneg]; rw [← sub_nonneg (a := b)]; rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := Real) _]; rw [← inr_sub Complex b a]; rw [← Unitization.quasispectrum_eq_spectrum_inr' Real Complex]
.symm exact S

Depends on / 依赖: IsSelfAdjoint, cfc_tac
-/
lemma inr_le_iff (a b : A) (ha : IsSelfAdjoint a := by cfc_tac)
    (hb : IsSelfAdjoint b := by cfc_tac) :
    (a : A⁺¹) <= (b : A⁺¹) ↔ a <= b := by
  -- TODO: prove the more general result for star monomorphisms and use it here.
  rw [← sub_nonneg]; rw [← sub_nonneg (a := b)]; rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := Real) _]; rw [← inr_sub Complex b a]; rw [← Unitization.quasispectrum_eq_spectrum_inr' Real Complex]
.symm exact StarOrderedRing.nonneg_iff_quasispectrum_nonneg _

@[simp, norm_cast]
/--
lemma `inr_nonneg_iff` / 引理 `inr_nonneg_iff`

English:
lemma inr_nonneg_iff
  given: {a : A}
  statement: 0 <= (a : A⁺¹) ↔ 0 <= a
  proof: by
  by_cases ha : IsSelfAdjoint a
  · exact inr_zero Complex (A := A) ▸ inr_le_iff 0 a
  · refine ⟨?_, ?_⟩
    all_goals refine fun h => (ha ?_).elim
.mp .of_nonneg h · exact isSelfAdjoint_inr (R := Complex)
    · exact .of_nonneg h

中文:
引理 inr_nonneg_iff
  条件: {a : A}
  结论: 0 <= (a : A⁺¹) ↔ 0 <= a
  证明: by
  by_cases ha : IsSelfAdjoint a
  · exact inr_zero Complex (A := A) ▸ inr_le_iff 0 a
  · refine ⟨?_, ?_⟩
    all_goals refine fun h => (ha ?_).elim
.mp .of_nonneg h · exact isSelfAdjoint_inr (R := Complex)
    · exact .of_nonneg h

Depends on / 依赖: IsSelfAdjoint, all_goals, inr_le_iff, inr_zero, isSelfAdjoint_inr, of_nonneg
-/
lemma inr_nonneg_iff {a : A} : 0 <= (a : A⁺¹) ↔ 0 <= a := by
  by_cases ha : IsSelfAdjoint a
  · exact inr_zero Complex (A := A) ▸ inr_le_iff 0 a
  · refine ⟨?_, ?_⟩
    all_goals refine fun h => (ha ?_).elim
.mp .of_nonneg h · exact isSelfAdjoint_inr (R := Complex)
    · exact .of_nonneg h

/--
lemma `convexOn_of_convexOn_inr_comp` / 引理 `convexOn_of_convexOn_inr_comp`

English:
lemma convexOn_of_convexOn_inr_comp
  statement: {f : A -> A} {s : Set A}
  proof: by
  refine ⟨hf₂.1, ?_⟩
  intro x hx y hy a b ha hb hab
  rw [← Unitization.inr_le_iff _ _]
  simpa using hf₂.2 hx hy ha hb hab

中文:
引理 convexOn_of_convexOn_inr_comp
  结论: {f : A -> A} {s : 集合 A}
  证明: by
  refine ⟨hf₂.1, ?_⟩
  intro x hx y hy a b ha hb hab
  rw [← Unitization.inr_le_iff _ _]
  simpa using hf₂.2 hx hy ha hb hab

Depends on / 依赖: ConvexOn, Unitization, Unitization.inr_le_iff, inr_le_iff
-/
lemma convexOn_of_convexOn_inr_comp {f : A -> A} {s : Set A}
    (hf : forall x, IsSelfAdjoint (f x))
    (hf₂ : ConvexOn Real s (Unitization.inr (R := Complex) ∘ f)) : ConvexOn Real s f := by
  refine ⟨hf₂.1, ?_⟩
  intro x hx y hy a b ha hb hab
  rw [← Unitization.inr_le_iff _ _]
  simpa using hf₂.2 hx hy ha hb hab

/--
lemma `concaveOn_of_concaveOn_inr_comp` / 引理 `concaveOn_of_concaveOn_inr_comp`

English:
lemma concaveOn_of_concaveOn_inr_comp
  statement: {f : A -> A} {s : Set A}
  proof: by
  refine ⟨hf₂.1, ?_⟩
  intro x hx y hy a b ha hb hab
  rw [← Unitization.inr_le_iff _ _]
  simpa using hf₂.2 hx hy ha hb hab

alias ⟨LE.le.of_inr, LE.le.inr⟩ := inr_nonneg_iff

中文:
引理 concaveOn_of_concaveOn_inr_comp
  结论: {f : A -> A} {s : 集合 A}
  证明: by
  refine ⟨hf₂.1, ?_⟩
  intro x hx y hy a b ha hb hab
  rw [← Unitization.inr_le_iff _ _]
  simpa using hf₂.2 hx hy ha hb hab

alias ⟨LE.le.of_inr, LE.le.inr⟩ := inr_nonneg_iff

Depends on / 依赖: ConcaveOn, Unitization, Unitization.inr_le_iff, inr_le_iff
-/
lemma concaveOn_of_concaveOn_inr_comp {f : A -> A} {s : Set A}
    (hf : forall x, IsSelfAdjoint (f x))
    (hf₂ : ConcaveOn Real s (Unitization.inr (R := Complex) ∘ f)) : ConcaveOn Real s f := by
  refine ⟨hf₂.1, ?_⟩
  intro x hx y hy a b ha hb hab
  rw [← Unitization.inr_le_iff _ _]
  simpa using hf₂.2 hx hy ha hb hab

alias ⟨LE.le.of_inr, LE.le.inr⟩ := inr_nonneg_iff

/--
lemma `nnreal_cfcₙ_eq_cfc_inr` / 引理 `nnreal_cfcₙ_eq_cfc_inr`

English:
lemma nnreal_cfcₙ_eq_cfc_inr
  statement: (a : A) (f : Real>=0 -> Real>=0)
  proof: cfcₙ_eq_cfc_inr inr_nonneg_iff ..

中文:
引理 nnreal_cfcₙ_eq_cfc_inr
  结论: (a : A) (f : 实数>=0 -> 实数>=0)
  证明: cfcₙ_eq_cfc_inr inr_nonneg_iff ..

Depends on / 依赖: cfc_zero_tac, inr_nonneg_iff
-/
lemma nnreal_cfcₙ_eq_cfc_inr (a : A) (f : Real>=0 -> Real>=0)
    (hf₀ : f 0 = 0 := by cfc_zero_tac) : cfcₙ f a = cfc f (a : A⁺¹) :=
  cfcₙ_eq_cfc_inr inr_nonneg_iff ..

/--
lemma `sqrt_inr` / 引理 `sqrt_inr`

English:
lemma sqrt_inr
  given: {a : A}
  statement: CFC.sqrt (a : A⁺¹) = (↑(CFC.sqrt a) : A⁺¹)
  proof: by
  by_cases ha : 0 <= a <;> have ha' := by rwa [← Unitization.inr_nonneg_iff] at ha
  · rw [CFC.sqrt_eq_iff .., ← inr_mul, CFC.sqrt_mul_sqrt_self a]
  · rw [CFC.sqrt, CFC.sqrt, cfcₙ_apply_of_not_predicate _ ha,
      cfcₙ_apply_of_not_predicate _ ha', inr_zero]

中文:
引理 sqrt_inr
  条件: {a : A}
  结论: CFC.sqrt (a : A⁺¹) = (↑(CFC.sqrt a) : A⁺¹)
  证明: by
  by_cases ha : 0 <= a <;> have ha' := by rwa [← Unitization.inr_nonneg_iff] at ha
  · rw [CFC.sqrt_eq_iff .., ← inr_mul, CFC.sqrt_mul_sqrt_self a]
  · rw [CFC.sqrt, CFC.sqrt, cfcₙ_apply_of_not_predicate _ ha,
      cfcₙ_apply_of_not_predicate _ ha', inr_zero]

Depends on / 依赖: CFC.sqrt, CFC.sqrt_eq_iff, CFC.sqrt_mul_sqrt_self, Unitization, Unitization.inr_nonneg_iff, inr_mul, inr_nonneg_iff, inr_zero, sqrt_eq_iff, sqrt_mul_sqrt_self
-/
lemma sqrt_inr {a : A} : CFC.sqrt (a : A⁺¹) = (↑(CFC.sqrt a) : A⁺¹) := by
  by_cases ha : 0 <= a <;> have ha' := by rwa [← Unitization.inr_nonneg_iff] at ha
  · rw [CFC.sqrt_eq_iff .., ← inr_mul, CFC.sqrt_mul_sqrt_self a]
  · rw [CFC.sqrt, CFC.sqrt, cfcₙ_apply_of_not_predicate _ ha,
      cfcₙ_apply_of_not_predicate _ ha', inr_zero]

end Unitization

/--
lemma `cfc_nnreal_le_iff` / 引理 `cfc_nnreal_le_iff`

English:
lemma cfc_nnreal_le_iff
  statement: {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A]
  proof: by
have hf' := hf.ofReal_map_toNNReal ha_spec.image ▸ Set.mapsTo_image ..
have hg' := hg.ofReal_map_toNNReal ha_spec.image ▸ Set.mapsTo_image ..
  rw [cfc_nnreal_eq_real ..]; rw [cfc_nnreal_eq_real ..]; rw [cfc_le_iff ..]
  simp [NNReal.coe_le_coe, ← ha_spec.image]

中文:
引理 cfc_nnreal_le_iff
  结论: {A : 类型} [拓扑空间 A] [环 A] [对合环 A] [偏序 A]
  证明: by
have hf' := hf.ofReal_map_toNNReal ha_spec.image ▸ Set.mapsTo_image ..
have hg' := hg.ofReal_map_toNNReal ha_spec.image ▸ Set.mapsTo_image ..
  rw [cfc_nnreal_eq_real ..]; rw [cfc_nnreal_eq_real ..]; rw [cfc_le_iff ..]
  simp [NNReal.coe_le_coe, ← ha_spec.image]

Depends on / 依赖: ContinuousOn, NNReal, NNReal.coe_le_coe, Set.mapsTo_image, cfc_cont_tac, cfc_le_iff, cfc_nnreal_eq_real, cfc_tac, coe_le_coe, ha_spec, ha_spec.image, hf.ofReal_map_toNNReal, hg.ofReal_map_toNNReal, mapsTo_image, ofReal_map_toNNReal, spectrum
-/
lemma cfc_nnreal_le_iff {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A]
    [StarOrderedRing A] [Algebra Real A] [IsTopologicalRing A] [NonnegSpectrumClass Real A]
    [T2Space A] [ContinuousFunctionalCalculus Real A IsSelfAdjoint]
    (f : Real>=0 -> Real>=0) (g : Real>=0 -> Real>=0) (a : A)
    (ha_spec : SpectrumRestricts a ContinuousMap.realToNNReal)
    (hf : ContinuousOn f (spectrum Real>=0 a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum Real>=0 a) := by cfc_cont_tac)
    (ha : 0 <= a := by cfc_tac) :
    cfc f a <= cfc g a ↔ forall x in spectrum Real>=0 a, f x <= g x := by
have hf' := hf.ofReal_map_toNNReal ha_spec.image ▸ Set.mapsTo_image ..
have hg' := hg.ofReal_map_toNNReal ha_spec.image ▸ Set.mapsTo_image ..
  rw [cfc_nnreal_eq_real ..]; rw [cfc_nnreal_eq_real ..]; rw [cfc_le_iff ..]
  simp [NNReal.coe_le_coe, ← ha_spec.image]

open ContinuousFunctionalCalculus in
/--
lemma `CFC.exists_pos_algebraMap_le_iff` / 引理 `CFC.exists_pos_algebraMap_le_iff`

English:
lemma CFC.exists_pos_algebraMap_le_iff
  statement: {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A]
  proof: by
  have h_cpct : IsCompact (spectrum Real a) := isCompact_iff_compactSpace.mpr inferInstance
  simp_rw [algebraMap_le_iff_le_spectrum (a := a)]
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨r, hr, hr_le⟩
    exact (hr.trans_le <| hr_le · ·)
  · obtain ⟨r, hr, hr_min⟩ := h_cpct.exists_isMinOn
      (Conti

中文:
引理 CFC.存在_pos_algebraMap_le_iff
  结论: {A : 类型} [拓扑空间 A] [环 A] [对合环 A]
  证明: by
  have h_cpct : IsCompact (spectrum Real a) := isCompact_iff_compactSpace.mpr inferInstance
  simp_rw [algebraMap_le_iff_le_spectrum (a := a)]
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨r, hr, hr_le⟩
    exact (hr.trans_le <| hr_le · ·)
  · obtain ⟨r, hr, hr_min⟩ := h_cpct.exists_isMinOn
      (Conti

Depends on / 依赖: ContinuousFunctionalCalculus, ContinuousFunctionalCalculus.spectrum_nonempty, IsCompact, algebraMap, algebraMap_le_iff_le_spectrum, cfc_tac, continuousOn_id, exists_isMinOn, h_cpct, h_cpct.exists_isMinOn, hr.trans_le, hr_le, hr_min, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mpr, simp_rw, spectrum, spectrum_nonempty, trans_le
-/
lemma CFC.exists_pos_algebraMap_le_iff {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A]
    [PartialOrder A] [StarOrderedRing A] [Algebra Real A] [NonnegSpectrumClass Real A] [Nontrivial A]
    [ContinuousFunctionalCalculus Real A IsSelfAdjoint]
    {a : A} (ha : IsSelfAdjoint a := by cfc_tac) :
    (exists r > 0, algebraMap Real A r <= a) ↔ (forall x in spectrum Real a, 0 < x) := by
  have h_cpct : IsCompact (spectrum Real a) := isCompact_iff_compactSpace.mpr inferInstance
  simp_rw [algebraMap_le_iff_le_spectrum (a := a)]
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨r, hr, hr_le⟩
    exact (hr.trans_le <| hr_le · ·)
  · obtain ⟨r, hr, hr_min⟩ := h_cpct.exists_isMinOn
      (ContinuousFunctionalCalculus.spectrum_nonempty a ha) continuousOn_id
    exact ⟨r, h _ hr, hr_min⟩

section CStar_unital

variable {A : Type*} [CStarAlgebra A]

section StarOrderedRing

variable [PartialOrder A] [StarOrderedRing A]

/--
lemma `IsSelfAdjoint.le_algebraMap_norm_self` / 引理 `IsSelfAdjoint.le_algebraMap_norm_self`

English:
lemma IsSelfAdjoint.le_algebraMap_norm_self
  given: {a : A} (ha : IsSelfAdjoint a := by cfc_tac)
  proof: by
  by_cases! nontriv : Nontrivial A
  · refine le_algebraMap_of_spectrum_le fun r hr => ?_
    calc r <= ‖r‖ := Real.le_norm_self r
      _ <= ‖a‖ := spectrum.norm_le_norm_of_mem hr
  · simp

中文:
引理 IsSelfAdjoint.le_algebraMap_norm_self
  条件: {a : A} (ha : IsSelfAdjoint a := by cfc_tac)
  证明: by
  by_cases! nontriv : Nontrivial A
  · refine le_algebraMap_of_spectrum_le fun r hr => ?_
    calc r <= ‖r‖ := Real.le_norm_self r
      _ <= ‖a‖ := spectrum.norm_le_norm_of_mem hr
  · simp

Depends on / 依赖: Nontrivial, Real.le_norm_self, algebraMap, cfc_tac, le_algebraMap_of_spectrum_le, le_norm_self, nontriv, norm_le_norm_of_mem, spectrum, spectrum.norm_le_norm_of_mem
-/
lemma IsSelfAdjoint.le_algebraMap_norm_self {a : A} (ha : IsSelfAdjoint a := by cfc_tac) :
    a <= algebraMap Real A ‖a‖ := by
  by_cases! nontriv : Nontrivial A
  · refine le_algebraMap_of_spectrum_le fun r hr => ?_
    calc r <= ‖r‖ := Real.le_norm_self r
      _ <= ‖a‖ := spectrum.norm_le_norm_of_mem hr
  · simp

/--
lemma `IsSelfAdjoint.neg_algebraMap_norm_le_self` / 引理 `IsSelfAdjoint.neg_algebraMap_norm_le_self`

English:
lemma IsSelfAdjoint.neg_algebraMap_norm_le_self
  given: {a : A} (ha : IsSelfAdjoint a := by cfc_tac)
  proof: by
  rw [neg_le]; rw [← norm_neg]
  exact ha.neg.le_algebraMap_norm_self

中文:
引理 IsSelfAdjoint.neg_algebraMap_norm_le_self
  条件: {a : A} (ha : IsSelfAdjoint a := by cfc_tac)
  证明: by
  rw [neg_le]; rw [← norm_neg]
  exact ha.neg.le_algebraMap_norm_self

Depends on / 依赖: algebraMap, cfc_tac, ha.neg.le_algebraMap_norm_self, le_algebraMap_norm_self, neg_le, norm_neg
-/
lemma IsSelfAdjoint.neg_algebraMap_norm_le_self {a : A} (ha : IsSelfAdjoint a := by cfc_tac) :
    -(algebraMap Real A ‖a‖) <= a := by
  rw [neg_le]; rw [← norm_neg]
  exact ha.neg.le_algebraMap_norm_self

/--
lemma `CStarAlgebra.mul_star_le_algebraMap_norm_sq` / 引理 `CStarAlgebra.mul_star_le_algebraMap_norm_sq`

English:
lemma CStarAlgebra.mul_star_le_algebraMap_norm_sq
  given: {a : A}
  proof: by
  have : a * star a <= algebraMap Real A ‖a * star a‖ := IsSelfAdjoint.le_algebraMap_norm_self
  rwa [CStarRing.norm_self_mul_star, ← pow_two] at this

中文:
引理 CStar代数.mul_star_le_algebraMap_norm_sq
  条件: {a : A}
  证明: by
  have : a * star a <= algebraMap Real A ‖a * star a‖ := IsSelfAdjoint.le_algebraMap_norm_self
  rwa [CStarRing.norm_self_mul_star, ← pow_two] at this

Depends on / 依赖: CStarRing, CStarRing.norm_self_mul_star, IsSelfAdjoint, IsSelfAdjoint.le_algebraMap_norm_self, algebraMap, le_algebraMap_norm_self, norm_self_mul_star, pow_two
-/
lemma CStarAlgebra.mul_star_le_algebraMap_norm_sq {a : A} :
    a * star a <= algebraMap Real A (‖a‖ ^ 2) := by
  have : a * star a <= algebraMap Real A ‖a * star a‖ := IsSelfAdjoint.le_algebraMap_norm_self
  rwa [CStarRing.norm_self_mul_star, ← pow_two] at this

/--
lemma `CStarAlgebra.star_mul_le_algebraMap_norm_sq` / 引理 `CStarAlgebra.star_mul_le_algebraMap_norm_sq`

English:
lemma CStarAlgebra.star_mul_le_algebraMap_norm_sq
  given: {a : A}
  proof: by
  have : star a * a <= algebraMap Real A ‖star a * a‖ := IsSelfAdjoint.le_algebraMap_norm_self
  rwa [CStarRing.norm_star_mul_self, ← pow_two] at this

中文:
引理 CStar代数.star_mul_le_algebraMap_norm_sq
  条件: {a : A}
  证明: by
  have : star a * a <= algebraMap Real A ‖star a * a‖ := IsSelfAdjoint.le_algebraMap_norm_self
  rwa [CStarRing.norm_star_mul_self, ← pow_two] at this

Depends on / 依赖: CStarRing, CStarRing.norm_star_mul_self, IsSelfAdjoint, IsSelfAdjoint.le_algebraMap_norm_self, algebraMap, le_algebraMap_norm_self, norm_star_mul_self, pow_two
-/
lemma CStarAlgebra.star_mul_le_algebraMap_norm_sq {a : A} :
    star a * a <= algebraMap Real A (‖a‖ ^ 2) := by
  have : star a * a <= algebraMap Real A ‖star a * a‖ := IsSelfAdjoint.le_algebraMap_norm_self
  rwa [CStarRing.norm_star_mul_self, ← pow_two] at this

end StarOrderedRing

/--
lemma `IsSelfAdjoint.toReal_spectralRadius_eq_norm` / 引理 `IsSelfAdjoint.toReal_spectralRadius_eq_norm`

English:
lemma IsSelfAdjoint.toReal_spectralRadius_eq_norm
  given: {a : A} (ha : IsSelfAdjoint a)
  proof: by
  simp [ha.spectrumRestricts.spectralRadius_eq, ha.spectralRadius_eq_nnnorm]

中文:
引理 IsSelfAdjoint.to实数_spectralRadius_eq_norm
  条件: {a : A} (ha : IsSelfAdjoint a)
  证明: by
  simp [ha.spectrumRestricts.spectralRadius_eq, ha.spectralRadius_eq_nnnorm]

Depends on / 依赖: ha.spectralRadius_eq_nnnorm, ha.spectrumRestricts.spectralRadius_eq, spectralRadius_eq, spectralRadius_eq_nnnorm, spectrumRestricts
-/
lemma IsSelfAdjoint.toReal_spectralRadius_eq_norm {a : A} (ha : IsSelfAdjoint a) :
    (spectralRadius Real a).toReal = ‖a‖ := by
  simp [ha.spectrumRestricts.spectralRadius_eq, ha.spectralRadius_eq_nnnorm]

namespace CStarAlgebra

/--
lemma `norm_or_neg_norm_mem_spectrum` / 引理 `norm_or_neg_norm_mem_spectrum`

English:
lemma norm_or_neg_norm_mem_spectrum
  statement: [Nontrivial A] {a : A}
  proof: by
  have ha' : SpectrumRestricts a Complex.reCLM := ha.spectrumRestricts
  rw [← ha.toReal_spectralRadius_eq_norm]
  exact Real.spectralRadius_mem_spectrum_or (ha'.image ▸ (spectrum.nonempty a).image _)

中文:
引理 norm_or_neg_norm_mem_spectrum
  结论: [非平凡 A] {a : A}
  证明: by
  have ha' : SpectrumRestricts a Complex.reCLM := ha.spectrumRestricts
  rw [← ha.toReal_spectralRadius_eq_norm]
  exact Real.spectralRadius_mem_spectrum_or (ha'.image ▸ (spectrum.nonempty a).image _)

Depends on / 依赖: Complex.reCLM, Real.spectralRadius_mem_spectrum_or, SpectrumRestricts, cfc_tac, ha.spectrumRestricts, ha.toReal_spectralRadius_eq_norm, nonempty, spectralRadius_mem_spectrum_or, spectrum, spectrum.nonempty, spectrumRestricts, toReal_spectralRadius_eq_norm
-/
lemma norm_or_neg_norm_mem_spectrum [Nontrivial A] {a : A}
    (ha : IsSelfAdjoint a := by cfc_tac) : ‖a‖ in spectrum Real a ∨ -‖a‖ in spectrum Real a := by
  have ha' : SpectrumRestricts a Complex.reCLM := ha.spectrumRestricts
  rw [← ha.toReal_spectralRadius_eq_norm]
  exact Real.spectralRadius_mem_spectrum_or (ha'.image ▸ (spectrum.nonempty a).image _)

variable [PartialOrder A] [StarOrderedRing A]

/--
lemma `nnnorm_mem_spectrum_of_nonneg` / 引理 `nnnorm_mem_spectrum_of_nonneg`

English:
lemma nnnorm_mem_spectrum_of_nonneg
  given: [Nontrivial A] {a : A} (ha : 0 <= a := by cfc_tac)
  proof: by
  have : IsSelfAdjoint a := .of_nonneg ha
  convert! NNReal.spectralRadius_mem_spectrum (a := a) ?_ (.nnreal_of_nonneg ha)
  · simp [this.spectrumRestricts.spectralRadius_eq, this.spectralRadius_eq_nnnorm]
  · exact this.spectrumRestricts.image ▸ (spectrum.nonempty a).image _

中文:
引理 nnnorm_mem_spectrum_of_nonneg
  条件: [非平凡 A] {a : A} (ha : 0 <= a := by cfc_tac)
  证明: by
  have : IsSelfAdjoint a := .of_nonneg ha
  convert! NNReal.spectralRadius_mem_spectrum (a := a) ?_ (.nnreal_of_nonneg ha)
  · simp [this.spectrumRestricts.spectralRadius_eq, this.spectralRadius_eq_nnnorm]
  · exact this.spectrumRestricts.image ▸ (spectrum.nonempty a).image _

Depends on / 依赖: IsSelfAdjoint, NNReal, NNReal.spectralRadius_mem_spectrum, cfc_tac, convert, nnreal_of_nonneg, nonempty, of_nonneg, spectralRadius_eq, spectralRadius_eq_nnnorm, spectralRadius_mem_spectrum, spectrum, spectrum.nonempty, spectrumRestricts, this.spectralRadius_eq_nnnorm, this.spectrumRestricts.image, this.spectrumRestricts.spectralRadius_eq
-/
lemma nnnorm_mem_spectrum_of_nonneg [Nontrivial A] {a : A} (ha : 0 <= a := by cfc_tac) :
    ‖a‖₊ in spectrum Real>=0 a := by
  have : IsSelfAdjoint a := .of_nonneg ha
  convert! NNReal.spectralRadius_mem_spectrum (a := a) ?_ (.nnreal_of_nonneg ha)
  · simp [this.spectrumRestricts.spectralRadius_eq, this.spectralRadius_eq_nnnorm]
  · exact this.spectrumRestricts.image ▸ (spectrum.nonempty a).image _

/--
lemma `norm_mem_spectrum_of_nonneg` / 引理 `norm_mem_spectrum_of_nonneg`

English:
lemma norm_mem_spectrum_of_nonneg
  given: [Nontrivial A] {a : A} (ha : 0 <= a := by cfc_tac)
  proof: by
simpa using spectrum.algebraMap_mem Real nnnorm_mem_spectrum_of_nonneg ha

中文:
引理 norm_mem_spectrum_of_nonneg
  条件: [非平凡 A] {a : A} (ha : 0 <= a := by cfc_tac)
  证明: by
simpa using spectrum.algebraMap_mem Real nnnorm_mem_spectrum_of_nonneg ha

Depends on / 依赖: algebraMap_mem, cfc_tac, nnnorm_mem_spectrum_of_nonneg, spectrum, spectrum.algebraMap_mem
-/
lemma norm_mem_spectrum_of_nonneg [Nontrivial A] {a : A} (ha : 0 <= a := by cfc_tac) :
    ‖a‖ in spectrum Real a := by
simpa using spectrum.algebraMap_mem Real nnnorm_mem_spectrum_of_nonneg ha

/--
lemma `norm_le_iff_le_algebraMap` / 引理 `norm_le_iff_le_algebraMap`

English:
lemma norm_le_iff_le_algebraMap
  given: (a : A) {r : Real} (hr : 0 <= r) (ha : 0 <= a := by cfc_tac)
  proof: by
  rw [le_algebraMap_iff_spectrum_le]
  obtain (h | _) := subsingleton_or_nontrivial A
  · simp [Subsingleton.elim a 0, hr]
.trans h, .trans (spectrum.norm_le_norm_of_mem hx) · exact ⟨fun h x hx => Real.le_norm_self x
fun h => h ‖a‖ norm_mem_spectrum_of_nonneg⟩

中文:
引理 norm_le_iff_le_algebraMap
  条件: (a : A) {r : 实数} (hr : 0 <= r) (ha : 0 <= a := by cfc_tac)
  证明: by
  rw [le_algebraMap_iff_spectrum_le]
  obtain (h | _) := subsingleton_or_nontrivial A
  · simp [Subsingleton.elim a 0, hr]
.trans h, .trans (spectrum.norm_le_norm_of_mem hx) · exact ⟨fun h x hx => Real.le_norm_self x
fun h => h ‖a‖ norm_mem_spectrum_of_nonneg⟩

Depends on / 依赖: Real.le_norm_self, Subsingleton, Subsingleton.elim, algebraMap, cfc_tac, le_algebraMap_iff_spectrum_le, le_norm_self, norm_le_norm_of_mem, norm_mem_spectrum_of_nonneg, spectrum, spectrum.norm_le_norm_of_mem, subsingleton_or_nontrivial
-/
lemma norm_le_iff_le_algebraMap (a : A) {r : Real} (hr : 0 <= r) (ha : 0 <= a := by cfc_tac) :
    ‖a‖ <= r ↔ a <= algebraMap Real A r := by
  rw [le_algebraMap_iff_spectrum_le]
  obtain (h | _) := subsingleton_or_nontrivial A
  · simp [Subsingleton.elim a 0, hr]
.trans h, .trans (spectrum.norm_le_norm_of_mem hx) · exact ⟨fun h x hx => Real.le_norm_self x
fun h => h ‖a‖ norm_mem_spectrum_of_nonneg⟩

/--
lemma `nnnorm_le_iff_of_nonneg` / 引理 `nnnorm_le_iff_of_nonneg`

English:
lemma nnnorm_le_iff_of_nonneg
  given: (a : A) (r : Real>=0) (ha : 0 <= a := by cfc_tac)
  proof: by
  rw [← NNReal.coe_le_coe]
  exact norm_le_iff_le_algebraMap a r.2

中文:
引理 nnnorm_le_iff_of_nonneg
  条件: (a : A) (r : 实数>=0) (ha : 0 <= a := by cfc_tac)
  证明: by
  rw [← NNReal.coe_le_coe]
  exact norm_le_iff_le_algebraMap a r.2

Depends on / 依赖: NNReal, NNReal.coe_le_coe, algebraMap, cfc_tac, coe_le_coe, norm_le_iff_le_algebraMap
-/
lemma nnnorm_le_iff_of_nonneg (a : A) (r : Real>=0) (ha : 0 <= a := by cfc_tac) :
    ‖a‖₊ <= r ↔ a <= algebraMap Real>=0 A r := by
  rw [← NNReal.coe_le_coe]
  exact norm_le_iff_le_algebraMap a r.2

/--
lemma `norm_le_one_iff_of_nonneg` / 引理 `norm_le_one_iff_of_nonneg`

English:
lemma norm_le_one_iff_of_nonneg
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  proof: by
  simpa using norm_le_iff_le_algebraMap a zero_le_one

中文:
引理 norm_le_one_iff_of_nonneg
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  证明: by
  simpa using norm_le_iff_le_algebraMap a zero_le_one

Depends on / 依赖: cfc_tac, norm_le_iff_le_algebraMap, zero_le_one
-/
lemma norm_le_one_iff_of_nonneg (a : A) (ha : 0 <= a := by cfc_tac) :
    ‖a‖ <= 1 ↔ a <= 1 := by
  simpa using norm_le_iff_le_algebraMap a zero_le_one

/--
lemma `nnnorm_le_one_iff_of_nonneg` / 引理 `nnnorm_le_one_iff_of_nonneg`

English:
lemma nnnorm_le_one_iff_of_nonneg
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  proof: by
  rw [← NNReal.coe_le_coe]
  exact norm_le_one_iff_of_nonneg a

中文:
引理 nnnorm_le_one_iff_of_nonneg
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  证明: by
  rw [← NNReal.coe_le_coe]
  exact norm_le_one_iff_of_nonneg a

Depends on / 依赖: NNReal, NNReal.coe_le_coe, cfc_tac, coe_le_coe, norm_le_one_iff_of_nonneg
-/
lemma nnnorm_le_one_iff_of_nonneg (a : A) (ha : 0 <= a := by cfc_tac) :
    ‖a‖₊ <= 1 ↔ a <= 1 := by
  rw [← NNReal.coe_le_coe]
  exact norm_le_one_iff_of_nonneg a

/--
lemma `norm_le_natCast_iff_of_nonneg` / 引理 `norm_le_natCast_iff_of_nonneg`

English:
lemma norm_le_natCast_iff_of_nonneg
  given: (a : A) (n : Nat) (ha : 0 <= a := by cfc_tac)
  proof: by
  simpa using norm_le_iff_le_algebraMap a n.cast_nonneg

中文:
引理 norm_le_natCast_iff_of_nonneg
  条件: (a : A) (n : 自然数) (ha : 0 <= a := by cfc_tac)
  证明: by
  simpa using norm_le_iff_le_algebraMap a n.cast_nonneg

Depends on / 依赖: cast_nonneg, cfc_tac, n.cast_nonneg, norm_le_iff_le_algebraMap
-/
lemma norm_le_natCast_iff_of_nonneg (a : A) (n : Nat) (ha : 0 <= a := by cfc_tac) :
    ‖a‖ <= n ↔ a <= n := by
  simpa using norm_le_iff_le_algebraMap a n.cast_nonneg

/--
lemma `nnnorm_le_natCast_iff_of_nonneg` / 引理 `nnnorm_le_natCast_iff_of_nonneg`

English:
lemma nnnorm_le_natCast_iff_of_nonneg
  given: (a : A) (n : Nat) (ha : 0 <= a := by cfc_tac)
  proof: by
  simpa using nnnorm_le_iff_of_nonneg a n

中文:
引理 nnnorm_le_natCast_iff_of_nonneg
  条件: (a : A) (n : 自然数) (ha : 0 <= a := by cfc_tac)
  证明: by
  simpa using nnnorm_le_iff_of_nonneg a n

Depends on / 依赖: cfc_tac, nnnorm_le_iff_of_nonneg
-/
lemma nnnorm_le_natCast_iff_of_nonneg (a : A) (n : Nat) (ha : 0 <= a := by cfc_tac) :
    ‖a‖₊ <= n ↔ a <= n := by
  simpa using nnnorm_le_iff_of_nonneg a n


section Icc

open Set

/--
lemma `mem_Icc_algebraMap_iff_norm_le` / 引理 `mem_Icc_algebraMap_iff_norm_le`

English:
lemma mem_Icc_algebraMap_iff_norm_le
  given: {x : A} {r : Real} (hr : 0 <= r)
  proof: by
  rw [mem_Icc]; rw [and_congr_right_iff]; rw [iff_comm]
  exact (norm_le_iff_le_algebraMap _ hr ·)

中文:
引理 mem_Icc_algebraMap_iff_norm_le
  条件: {x : A} {r : 实数} (hr : 0 <= r)
  证明: by
  rw [mem_Icc]; rw [and_congr_right_iff]; rw [iff_comm]
  exact (norm_le_iff_le_algebraMap _ hr ·)

Depends on / 依赖: and_congr_right_iff, iff_comm, mem_Icc, norm_le_iff_le_algebraMap
-/
lemma mem_Icc_algebraMap_iff_norm_le {x : A} {r : Real} (hr : 0 <= r) :
    x in Icc 0 (algebraMap Real A r) ↔ 0 <= x ∧ ‖x‖ <= r := by
  rw [mem_Icc]; rw [and_congr_right_iff]; rw [iff_comm]
  exact (norm_le_iff_le_algebraMap _ hr ·)

/--
lemma `mem_Icc_algebraMap_iff_nnnorm_le` / 引理 `mem_Icc_algebraMap_iff_nnnorm_le`

English:
lemma mem_Icc_algebraMap_iff_nnnorm_le
  given: {x : A} {r : Real>=0}
  proof: mem_Icc_algebraMap_iff_norm_le (hr := r.2)

中文:
引理 mem_Icc_algebraMap_iff_nnnorm_le
  条件: {x : A} {r : 实数>=0}
  证明: mem_Icc_algebraMap_iff_norm_le (hr := r.2)

Depends on / 依赖: mem_Icc_algebraMap_iff_norm_le
-/
lemma mem_Icc_algebraMap_iff_nnnorm_le {x : A} {r : Real>=0} :
    x in Icc 0 (algebraMap Real>=0 A r) ↔ 0 <= x ∧ ‖x‖₊ <= r :=
  mem_Icc_algebraMap_iff_norm_le (hr := r.2)

/--
lemma `mem_Icc_iff_norm_le_one` / 引理 `mem_Icc_iff_norm_le_one`

English:
lemma mem_Icc_iff_norm_le_one
  given: {x : A}
  proof: by
  simpa only [map_one] using mem_Icc_algebraMap_iff_norm_le zero_le_one (A := A)

中文:
引理 mem_Icc_iff_norm_le_one
  条件: {x : A}
  证明: by
  simpa only [map_one] using mem_Icc_algebraMap_iff_norm_le zero_le_one (A := A)

Depends on / 依赖: map_one, mem_Icc_algebraMap_iff_norm_le, zero_le_one
-/
lemma mem_Icc_iff_norm_le_one {x : A} :
    x in Icc 0 1 ↔ 0 <= x ∧ ‖x‖ <= 1 := by
  simpa only [map_one] using mem_Icc_algebraMap_iff_norm_le zero_le_one (A := A)

/--
lemma `mem_Icc_iff_nnnorm_le_one` / 引理 `mem_Icc_iff_nnnorm_le_one`

English:
lemma mem_Icc_iff_nnnorm_le_one
  given: {x : A}
  proof: mem_Icc_iff_norm_le_one

中文:
引理 mem_Icc_iff_nnnorm_le_one
  条件: {x : A}
  证明: mem_Icc_iff_norm_le_one

Depends on / 依赖: mem_Icc_iff_norm_le_one
-/
lemma mem_Icc_iff_nnnorm_le_one {x : A} :
    x in Icc 0 1 ↔ 0 <= x ∧ ‖x‖₊ <= 1 :=
  mem_Icc_iff_norm_le_one

end Icc

end CStarAlgebra

section Inv

open CFC

variable [PartialOrder A] [StarOrderedRing A]

/--
lemma `CFC.conjugate_rpow_neg_one_half` / 引理 `CFC.conjugate_rpow_neg_one_half`

English:
lemma CFC.conjugate_rpow_neg_one_half
  given: (a : A) (ha : IsStrictlyPositive a := by cfc_tac)
  proof: by
  lift a to Aˣ using ha.isUnit
  nth_rw 2 [← rpow_one (a : A)]
  simp only [← rpow_add a.isUnit]
  norm_num
  exact rpow_zero _

中文:
引理 CFC.conjugate_rpow_neg_one_half
  条件: (a : A) (ha : IsStrictlyPositive a := by cfc_tac)
  证明: by
  lift a to Aˣ using ha.isUnit
  nth_rw 2 [← rpow_one (a : A)]
  simp only [← rpow_add a.isUnit]
  norm_num
  exact rpow_zero _

Depends on / 依赖: a.isUnit, cfc_tac, ha.isUnit, isUnit, nth_rw, rpow_add, rpow_one, rpow_zero
-/
lemma CFC.conjugate_rpow_neg_one_half (a : A) (ha : IsStrictlyPositive a := by cfc_tac) :
    a ^ (-(1 / 2) : Real) * a * a ^ (-(1 / 2) : Real) = 1 := by
  lift a to Aˣ using ha.isUnit
  nth_rw 2 [← rpow_one (a : A)]
  simp only [← rpow_add a.isUnit]
  norm_num
  exact rpow_zero _

/--
lemma `CStarAlgebra.isUnit_of_le` / 引理 `CStarAlgebra.isUnit_of_le`

English:
lemma CStarAlgebra.isUnit_of_le
  statement: (a : A) {b : A} (hab : a <= b)
  proof: by
  nontriviality A
  rw [← spectrum.zero_notMem_iff Real]
  obtain ⟨r, hr, hr_le⟩ : exists r > 0, (algebraMap Real A) r <= a :=
    (exists_pos_algebraMap_le_iff h.isSelfAdjoint).2 fun x hx => h.spectrum_pos hx
exact fun h0 => not_le_of_gt hr (algebraMap_le_iff_le_spectrum <| .of_nonneg <|
    h.n

中文:
引理 CStar代数.isUnit_of_le
  结论: (a : A) {b : A} (hab : a <= b)
  证明: by
  nontriviality A
  rw [← spectrum.zero_notMem_iff Real]
  obtain ⟨r, hr, hr_le⟩ : exists r > 0, (algebraMap Real A) r <= a :=
    (exists_pos_algebraMap_le_iff h.isSelfAdjoint).2 fun x hx => h.spectrum_pos hx
exact fun h0 => not_le_of_gt hr (algebraMap_le_iff_le_spectrum <| .of_nonneg <|
    h.n

Depends on / 依赖: IsUnit, algebraMap, algebraMap_le_iff_le_spectrum, cfc_tac, exists_pos_algebraMap_le_iff, h.isSelfAdjoint, h.nonneg.trans, h.spectrum_pos, hr_le, hr_le.trans, isSelfAdjoint, nonneg, nontriviality, not_le_of_gt, of_nonneg, spectrum, spectrum.zero_notMem_iff, spectrum_pos, zero_notMem_iff
-/
lemma CStarAlgebra.isUnit_of_le (a : A) {b : A} (hab : a <= b)
    (h : IsStrictlyPositive a := by cfc_tac) : IsUnit b := by
  nontriviality A
  rw [← spectrum.zero_notMem_iff Real]
  obtain ⟨r, hr, hr_le⟩ : exists r > 0, (algebraMap Real A) r <= a :=
    (exists_pos_algebraMap_le_iff h.isSelfAdjoint).2 fun x hx => h.spectrum_pos hx
exact fun h0 => not_le_of_gt hr (algebraMap_le_iff_le_spectrum <| .of_nonneg <|
    h.nonneg.trans hab).1 (hr_le.trans hab) 0 h0

/--
lemma `le_iff_norm_sqrt_mul_rpow` / 引理 `le_iff_norm_sqrt_mul_rpow`

English:
lemma le_iff_norm_sqrt_mul_rpow
  statement: (a b : A) (ha : 0 <= a := by cfc_tac)
  proof: by
  lift b to Aˣ using hb.isUnit
  have hbab : 0 <= (b : A) ^ (-(1 / 2) : Real) * a * (b : A) ^ (-(1 / 2) : Real) :=
    conjugate_nonneg_of_nonneg ha rpow_nonneg
  conv_rhs =>
    rw [← sq_le_one_iff₀ (norm_nonneg _)]; rw [sq]; rw [← CStarRing.norm_star_mul_self]; rw [star_mul]; rw [IsSelfAdjoint.

中文:
引理 le_iff_norm_sqrt_mul_rpow
  结论: (a b : A) (ha : 0 <= a := by cfc_tac)
  证明: by
  lift b to Aˣ using hb.isUnit
  have hbab : 0 <= (b : A) ^ (-(1 / 2) : Real) * a * (b : A) ^ (-(1 / 2) : Real) :=
    conjugate_nonneg_of_nonneg ha rpow_nonneg
  conv_rhs =>
    rw [← sq_le_one_iff₀ (norm_nonneg _)]; rw [sq]; rw [← CStarRing.norm_star_mul_self]; rw [star_mul]; rw [IsSelfAdjoint.

Depends on / 依赖: CStarRing, CStarRing.norm_star_mul_self, IsSelfAdjoint, IsSelfAdjoint.of_nonneg, IsStrictlyPositive, cfc_tac, conjugate_nonneg_of_nonneg, conv_rhs, hb.isUnit, isUnit, mul_assoc, norm_nonneg, norm_star_mul_self, of_nonneg, rpow_nonneg, sqrt_nonneg, star_mul
-/
lemma le_iff_norm_sqrt_mul_rpow (a b : A) (ha : 0 <= a := by cfc_tac)
    (hb : IsStrictlyPositive b := by cfc_tac) :
    a <= b ↔ ‖sqrt a * (b : A) ^ (-(1 / 2) : Real)‖ <= 1 := by
  lift b to Aˣ using hb.isUnit
  have hbab : 0 <= (b : A) ^ (-(1 / 2) : Real) * a * (b : A) ^ (-(1 / 2) : Real) :=
    conjugate_nonneg_of_nonneg ha rpow_nonneg
  conv_rhs =>
    rw [← sq_le_one_iff₀ (norm_nonneg _)]; rw [sq]; rw [← CStarRing.norm_star_mul_self]; rw [star_mul]; rw [IsSelfAdjoint.of_nonneg (sqrt_nonneg a)]; rw [IsSelfAdjoint.of_nonneg rpow_nonneg]; rw [← mul_assoc]; rw [mul_assoc _ _ (sqrt a)]; rw [sqrt_mul_sqrt_self a]; rw [CStarAlgebra.norm_le_one_iff_of_nonneg _ hbab]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · calc
      _ <= ↑b ^ (-(1 / 2) : Real) * (b : A) * ↑b ^ (-(1 / 2) : Real) :=
.conjugate_le_conjugate h IsSelfAdjoint.of_nonneg rpow_nonneg
      _ = 1 := conjugate_rpow_neg_one_half (b : A)
  · calc
      a = (sqrt ↑b * ↑b ^ (-(1 / 2) : Real)) * a * (↑b ^ (-(1 / 2) : Real) * sqrt ↑b) := by
        simp only [CFC.sqrt_eq_rpow .., ← CFC.rpow_add b.isUnit]
        norm_num
        simp [CFC.rpow_zero (b : A)]
      _ = sqrt ↑b * (↑b ^ (-(1 / 2) : Real) * a * ↑b ^ (-(1 / 2) : Real)) * sqrt ↑b := by
        simp only [mul_assoc]
.trans by _ <= b := conjugate_le_conjugate_of_nonneg h (sqrt_nonneg _)
        simp [CFC.sqrt_mul_sqrt_self (b : A)]

/--
lemma `le_iff_norm_sqrt_mul_sqrt_inv` / 引理 `le_iff_norm_sqrt_mul_sqrt_inv`

English:
lemma le_iff_norm_sqrt_mul_sqrt_inv
  given: {a : A} {b : Aˣ} (ha : 0 <= a) (hb : 0 <= (b : A))
  proof: by
  rw [CFC.sqrt_eq_rpow (a := (↑b⁻¹ : A))]; rw [← CFC.rpow_neg_one_eq_inv b]; rw [CFC.rpow_rpow (b : A) _ _ (by simp)]; rw [le_iff_norm_sqrt_mul_rpow a (hb := b.isUnit.isStrictlyPositive hb)]
  simp

中文:
引理 le_iff_norm_sqrt_mul_sqrt_inv
  条件: {a : A} {b : Aˣ} (ha : 0 <= a) (hb : 0 <= (b : A))
  证明: by
  rw [CFC.sqrt_eq_rpow (a := (↑b⁻¹ : A))]; rw [← CFC.rpow_neg_one_eq_inv b]; rw [CFC.rpow_rpow (b : A) _ _ (by simp)]; rw [le_iff_norm_sqrt_mul_rpow a (hb := b.isUnit.isStrictlyPositive hb)]
  simp

Depends on / 依赖: CFC.rpow_neg_one_eq_inv, CFC.rpow_rpow, CFC.sqrt_eq_rpow, b.isUnit.isStrictlyPositive, isStrictlyPositive, isUnit, le_iff_norm_sqrt_mul_rpow, rpow_neg_one_eq_inv, rpow_rpow, sqrt_eq_rpow
-/
lemma le_iff_norm_sqrt_mul_sqrt_inv {a : A} {b : Aˣ} (ha : 0 <= a) (hb : 0 <= (b : A)) :
    a <= b ↔ ‖sqrt a * sqrt (↑b⁻¹ : A)‖ <= 1 := by
  rw [CFC.sqrt_eq_rpow (a := (↑b⁻¹ : A))]; rw [← CFC.rpow_neg_one_eq_inv b]; rw [CFC.rpow_rpow (b : A) _ _ (by simp)]; rw [le_iff_norm_sqrt_mul_rpow a (hb := b.isUnit.isStrictlyPositive hb)]
  simp

namespace CStarAlgebra

/--
lemma `inv_le_inv` / 引理 `inv_le_inv`

English:
lemma inv_le_inv
  statement: {a b : Aˣ} (ha : 0 <= (a : A))
  proof: by
  have hb := ha.trans hab
  have hb_inv : (0 : A) <= b⁻¹ := inv_nonneg_of_nonneg b hb
  have ha_inv : (0 : A) <= a⁻¹ := inv_nonneg_of_nonneg a ha
  rw [le_iff_norm_sqrt_mul_sqrt_inv ha hb]; rw [← sq_le_one_iff₀ (norm_nonneg _)]; rw [sq]; rw [← CStarRing.norm_star_mul_self] at hab
  rw [le_iff_nor

中文:
引理 inv_le_inv
  结论: {a b : Aˣ} (ha : 0 <= (a : A))
  证明: by
  have hb := ha.trans hab
  have hb_inv : (0 : A) <= b⁻¹ := inv_nonneg_of_nonneg b hb
  have ha_inv : (0 : A) <= a⁻¹ := inv_nonneg_of_nonneg a ha
  rw [le_iff_norm_sqrt_mul_sqrt_inv ha hb]; rw [← sq_le_one_iff₀ (norm_nonneg _)]; rw [sq]; rw [← CStarRing.norm_star_mul_self] at hab
  rw [le_iff_nor
-/
protected lemma inv_le_inv {a b : Aˣ} (ha : 0 <= (a : A))
    (hab : (a : A) <= b) : (↑b⁻¹ : A) <= a⁻¹ := by
  have hb := ha.trans hab
  have hb_inv : (0 : A) <= b⁻¹ := inv_nonneg_of_nonneg b hb
  have ha_inv : (0 : A) <= a⁻¹ := inv_nonneg_of_nonneg a ha
  rw [le_iff_norm_sqrt_mul_sqrt_inv ha hb]; rw [← sq_le_one_iff₀ (norm_nonneg _)]; rw [sq]; rw [← CStarRing.norm_star_mul_self] at hab
  rw [le_iff_norm_sqrt_mul_sqrt_inv hb_inv ha_inv]; rw [inv_inv]; rw [← sq_le_one_iff₀ (norm_nonneg _)]; rw [sq]; rw [← CStarRing.norm_self_mul_star]
  rwa [star_mul, IsSelfAdjoint.of_nonneg (sqrt_nonneg _),
    IsSelfAdjoint.of_nonneg (sqrt_nonneg _)] at hab ⊢

/--
lemma `inv_le_inv_iff` / 引理 `inv_le_inv_iff`

English:
lemma inv_le_inv_iff
  given: {a b : Aˣ} (ha : 0 <= (a : A)) (hb : 0 <= (b : A))
  proof: ⟨CStarAlgebra.inv_le_inv (inv_nonneg_of_nonneg a ha), CStarAlgebra.inv_le_inv hb⟩

中文:
引理 inv_le_inv_iff
  条件: {a b : Aˣ} (ha : 0 <= (a : A)) (hb : 0 <= (b : A))
  证明: ⟨CStarAlgebra.inv_le_inv (inv_nonneg_of_nonneg a ha), CStarAlgebra.inv_le_inv hb⟩
-/
protected lemma inv_le_inv_iff {a b : Aˣ} (ha : 0 <= (a : A)) (hb : 0 <= (b : A)) :
    (↑a⁻¹ : A) <= b⁻¹ ↔ (b : A) <= a :=
  ⟨CStarAlgebra.inv_le_inv (inv_nonneg_of_nonneg a ha), CStarAlgebra.inv_le_inv hb⟩

/--
lemma `inv_le_iff` / 引理 `inv_le_iff`

English:
lemma inv_le_iff
  given: {a b : Aˣ} (ha : 0 <= (a : A)) (hb : 0 <= (↑b : A))
  proof: by
  simpa using CStarAlgebra.inv_le_inv_iff ha (inv_nonneg_of_nonneg b hb)

中文:
引理 inv_le_iff
  条件: {a b : Aˣ} (ha : 0 <= (a : A)) (hb : 0 <= (↑b : A))
  证明: by
  simpa using CStarAlgebra.inv_le_inv_iff ha (inv_nonneg_of_nonneg b hb)

Depends on / 依赖: CStarAlgebra, CStarAlgebra.inv_le_inv_iff, inv_le_inv_iff, inv_nonneg_of_nonneg
-/
lemma inv_le_iff {a b : Aˣ} (ha : 0 <= (a : A)) (hb : 0 <= (↑b : A)) :
    (↑a⁻¹ : A) <= b ↔ (↑b⁻¹ : A) <= a := by
  simpa using CStarAlgebra.inv_le_inv_iff ha (inv_nonneg_of_nonneg b hb)

/--
lemma `le_inv_iff` / 引理 `le_inv_iff`

English:
lemma le_inv_iff
  given: {a b : Aˣ} (ha : 0 <= (a : A)) (hb : 0 <= (↑b : A))
  proof: by
  simpa using CStarAlgebra.inv_le_inv_iff (inv_nonneg_of_nonneg a ha) hb

中文:
引理 le_inv_iff
  条件: {a b : Aˣ} (ha : 0 <= (a : A)) (hb : 0 <= (↑b : A))
  证明: by
  simpa using CStarAlgebra.inv_le_inv_iff (inv_nonneg_of_nonneg a ha) hb

Depends on / 依赖: CStarAlgebra, CStarAlgebra.inv_le_inv_iff, inv_le_inv_iff, inv_nonneg_of_nonneg
-/
lemma le_inv_iff {a b : Aˣ} (ha : 0 <= (a : A)) (hb : 0 <= (↑b : A)) :
    a <= (↑b⁻¹ : A) ↔ b <= (↑a⁻¹ : A) := by
  simpa using CStarAlgebra.inv_le_inv_iff (inv_nonneg_of_nonneg a ha) hb

/--
lemma `one_le_inv_iff_le_one` / 引理 `one_le_inv_iff_le_one`

English:
lemma one_le_inv_iff_le_one
  given: {a : Aˣ} (ha : 0 <= (a : A))
  proof: by
  simpa using! CStarAlgebra.le_inv_iff (a := 1) (by simp) ha

中文:
引理 one_le_inv_iff_le_one
  条件: {a : Aˣ} (ha : 0 <= (a : A))
  证明: by
  simpa using! CStarAlgebra.le_inv_iff (a := 1) (by simp) ha

Depends on / 依赖: CStarAlgebra, CStarAlgebra.le_inv_iff, le_inv_iff
-/
lemma one_le_inv_iff_le_one {a : Aˣ} (ha : 0 <= (a : A)) :
    1 <= (↑a⁻¹ : A) ↔ a <= 1 := by
  simpa using! CStarAlgebra.le_inv_iff (a := 1) (by simp) ha

/--
lemma `inv_le_one_iff_one_le` / 引理 `inv_le_one_iff_one_le`

English:
lemma inv_le_one_iff_one_le
  given: {a : Aˣ} (ha : 0 <= (a : A))
  proof: by
  simpa using! CStarAlgebra.inv_le_iff ha (b := 1) (by simp)

中文:
引理 inv_le_one_iff_one_le
  条件: {a : Aˣ} (ha : 0 <= (a : A))
  证明: by
  simpa using! CStarAlgebra.inv_le_iff ha (b := 1) (by simp)

Depends on / 依赖: CStarAlgebra, CStarAlgebra.inv_le_iff, inv_le_iff
-/
lemma inv_le_one_iff_one_le {a : Aˣ} (ha : 0 <= (a : A)) :
    (↑a⁻¹ : A) <= 1 ↔ 1 <= a := by
  simpa using! CStarAlgebra.inv_le_iff ha (b := 1) (by simp)

/--
lemma `inv_le_one` / 引理 `inv_le_one`

English:
lemma inv_le_one
  given: {a : Aˣ} (ha : 1 <= a)
  statement: (↑a⁻¹ : A) <= 1
  proof: .mpr ha CStarAlgebra.inv_le_one_iff_one_le (zero_le_one.trans ha)

中文:
引理 inv_le_one
  条件: {a : Aˣ} (ha : 1 <= a)
  结论: (↑a⁻¹ : A) <= 1
  证明: .mpr ha CStarAlgebra.inv_le_one_iff_one_le (zero_le_one.trans ha)

Depends on / 依赖: CStarAlgebra, CStarAlgebra.inv_le_one_iff_one_le, inv_le_one_iff_one_le, zero_le_one, zero_le_one.trans
-/
lemma inv_le_one {a : Aˣ} (ha : 1 <= a) : (↑a⁻¹ : A) <= 1 :=
.mpr ha CStarAlgebra.inv_le_one_iff_one_le (zero_le_one.trans ha)

/--
lemma `le_one_of_one_le_inv` / 引理 `le_one_of_one_le_inv`

English:
lemma le_one_of_one_le_inv
  given: {a : Aˣ} (ha : 1 <= (↑a⁻¹ : A))
  statement: (a : A) <= 1
  proof: by
  simpa using CStarAlgebra.inv_le_one ha

中文:
引理 le_one_of_one_le_inv
  条件: {a : Aˣ} (ha : 1 <= (↑a⁻¹ : A))
  结论: (a : A) <= 1
  证明: by
  simpa using CStarAlgebra.inv_le_one ha

Depends on / 依赖: CStarAlgebra, CStarAlgebra.inv_le_one, inv_le_one
-/
lemma le_one_of_one_le_inv {a : Aˣ} (ha : 1 <= (↑a⁻¹ : A)) : (a : A) <= 1 := by
  simpa using CStarAlgebra.inv_le_one ha

/--
lemma `rpow_neg_one_le_rpow_neg_one` / 引理 `rpow_neg_one_le_rpow_neg_one`

English:
lemma rpow_neg_one_le_rpow_neg_one
  statement: {a b : A} (hab : a <= b)
  proof: by
  lift b to Aˣ using isUnit_of_le a hab
  lift a to Aˣ using ha.isUnit
  rw [rpow_neg_one_eq_inv a]; rw [rpow_neg_one_eq_inv b (ha.nonneg.trans hab)]
  exact CStarAlgebra.inv_le_inv ha.nonneg hab

中文:
引理 rpow_neg_one_le_rpow_neg_one
  结论: {a b : A} (hab : a <= b)
  证明: by
  lift b to Aˣ using isUnit_of_le a hab
  lift a to Aˣ using ha.isUnit
  rw [rpow_neg_one_eq_inv a]; rw [rpow_neg_one_eq_inv b (ha.nonneg.trans hab)]
  exact CStarAlgebra.inv_le_inv ha.nonneg hab

Depends on / 依赖: CStarAlgebra, CStarAlgebra.inv_le_inv, cfc_tac, ha.isUnit, ha.nonneg, ha.nonneg.trans, inv_le_inv, isUnit, isUnit_of_le, nonneg, rpow_neg_one_eq_inv
-/
lemma rpow_neg_one_le_rpow_neg_one {a b : A} (hab : a <= b)
    (ha : IsStrictlyPositive a := by cfc_tac) :
    b ^ (-1 : Real) <= a ^ (-1 : Real) := by
  lift b to Aˣ using isUnit_of_le a hab
  lift a to Aˣ using ha.isUnit
  rw [rpow_neg_one_eq_inv a]; rw [rpow_neg_one_eq_inv b (ha.nonneg.trans hab)]
  exact CStarAlgebra.inv_le_inv ha.nonneg hab

/--
lemma `rpow_neg_one_le_one` / 引理 `rpow_neg_one_le_one`

English:
lemma rpow_neg_one_le_one
  given: {a : A} (ha : 1 <= a)
  statement: a ^ (-1 : Real) <= 1
  proof: by
  lift a to Aˣ using isUnit_of_le 1 ha
  rw [rpow_neg_one_eq_inv a (zero_le_one.trans ha)]
  exact inv_le_one ha

中文:
引理 rpow_neg_one_le_one
  条件: {a : A} (ha : 1 <= a)
  结论: a ^ (-1 : 实数) <= 1
  证明: by
  lift a to Aˣ using isUnit_of_le 1 ha
  rw [rpow_neg_one_eq_inv a (zero_le_one.trans ha)]
  exact inv_le_one ha

Depends on / 依赖: inv_le_one, isUnit_of_le, rpow_neg_one_eq_inv, zero_le_one, zero_le_one.trans
-/
lemma rpow_neg_one_le_one {a : A} (ha : 1 <= a) : a ^ (-1 : Real) <= 1 := by
  lift a to Aˣ using isUnit_of_le 1 ha
  rw [rpow_neg_one_eq_inv a (zero_le_one.trans ha)]
  exact inv_le_one ha

/--
lemma `_root_.IsStrictlyPositive.of_le` / 引理 `_root_.IsStrictlyPositive.of_le`

English:
lemma _root_.IsStrictlyPositive.of_le
  statement: {a b : A} (ha : IsStrictlyPositive a)
  proof: ⟨ha.nonneg.trans hab, CStarAlgebra.isUnit_of_le a hab⟩

中文:
引理 _root_.IsStrictlyPositive.of_le
  结论: {a b : A} (ha : IsStrictlyPositive a)
  证明: ⟨ha.nonneg.trans hab, CStarAlgebra.isUnit_of_le a hab⟩
-/
protected lemma _root_.IsStrictlyPositive.of_le {a b : A} (ha : IsStrictlyPositive a)
    (hab : a <= b) : IsStrictlyPositive b :=
  ⟨ha.nonneg.trans hab, CStarAlgebra.isUnit_of_le a hab⟩

/--
theorem `_root_.IsStrictlyPositive.add_nonneg` / 定理 `_root_.IsStrictlyPositive.add_nonneg`

English:
theorem _root_.IsStrictlyPositive.add_nonneg
  statement: {a b : A}
  proof: IsStrictlyPositive.of_le ha ((le_add_iff_nonneg_right a).mpr hb)

中文:
定理 _root_.IsStrictlyPositive.add_nonneg
  结论: {a b : A}
  证明: IsStrictlyPositive.of_le ha ((le_add_iff_nonneg_right a).mpr hb)

Depends on / 依赖: IsStrictlyPositive, IsStrictlyPositive.of_le, le_add_iff_nonneg_right, of_le
-/
theorem _root_.IsStrictlyPositive.add_nonneg {a b : A}
    (ha : IsStrictlyPositive a) (hb : 0 <= b) : IsStrictlyPositive (a + b) :=
  IsStrictlyPositive.of_le ha ((le_add_iff_nonneg_right a).mpr hb)

/--
theorem `_root_.IsStrictlyPositive.nonneg_add` / 定理 `_root_.IsStrictlyPositive.nonneg_add`

English:
theorem _root_.IsStrictlyPositive.nonneg_add
  statement: {a b : A}
  proof: add_comm a b ▸ hb.add_nonneg ha

@[grind ←, aesop 90% apply]

中文:
定理 _root_.IsStrictlyPositive.nonneg_add
  结论: {a b : A}
  证明: add_comm a b ▸ hb.add_nonneg ha

@[grind ←, aesop 90% apply]

Depends on / 依赖: add_comm, add_nonneg, hb.add_nonneg
-/
theorem _root_.IsStrictlyPositive.nonneg_add {a b : A}
    (ha : 0 <= a) (hb : IsStrictlyPositive b) : IsStrictlyPositive (a + b) :=
  add_comm a b ▸ hb.add_nonneg ha

@[grind ←, aesop 90% apply]
/--
lemma `_root_.isStrictlyPositive_add` / 引理 `_root_.isStrictlyPositive_add`

English:
lemma _root_.isStrictlyPositive_add
  statement: {a b : A}
  proof: by
  grind [IsStrictlyPositive.add_nonneg, IsStrictlyPositive.nonneg_add]

中文:
引理 _root_.isStrictlyPositive_add
  结论: {a b : A}
  证明: by
  grind [IsStrictlyPositive.add_nonneg, IsStrictlyPositive.nonneg_add]

Depends on / 依赖: IsStrictlyPositive, IsStrictlyPositive.add_nonneg, IsStrictlyPositive.nonneg_add, add_nonneg, nonneg_add
-/
lemma _root_.isStrictlyPositive_add {a b : A}
    (h : IsStrictlyPositive a ∧ 0 <= b ∨ 0 <= a ∧ IsStrictlyPositive b) :
    IsStrictlyPositive (a + b) := by
  grind [IsStrictlyPositive.add_nonneg, IsStrictlyPositive.nonneg_add]

/--
lemma `antitoneOn_ringInverse` / 引理 `antitoneOn_ringInverse`

English:
lemma antitoneOn_ringInverse
  statement: AntitoneOn Ring.inverse {a : A | IsStrictlyPositive a}
  proof: by
  intro a (apos : IsStrictlyPositive a) b (bpos : IsStrictlyPositive b) hab
  rw [Ring.inverse_of_isUnit (by grind)]; rw [Ring.inverse_of_isUnit (by grind)]
  exact CStarAlgebra.inv_le_inv (Units.isStrictlyPositive_iff.mp apos) hab

中文:
引理 antitoneOn_ringInverse
  结论: AntitoneOn 环.inverse {a : A | IsStrictlyPositive a}
  证明: by
  intro a (apos : IsStrictlyPositive a) b (bpos : IsStrictlyPositive b) hab
  rw [Ring.inverse_of_isUnit (by grind)]; rw [Ring.inverse_of_isUnit (by grind)]
  exact CStarAlgebra.inv_le_inv (Units.isStrictlyPositive_iff.mp apos) hab

Depends on / 依赖: CStarAlgebra, CStarAlgebra.inv_le_inv, IsStrictlyPositive, Ring.inverse_of_isUnit, Units.isStrictlyPositive_iff.mp, inv_le_inv, inverse_of_isUnit, isStrictlyPositive_iff
-/
lemma antitoneOn_ringInverse : AntitoneOn Ring.inverse {a : A | IsStrictlyPositive a} := by
  intro a (apos : IsStrictlyPositive a) b (bpos : IsStrictlyPositive b) hab
  rw [Ring.inverse_of_isUnit (by grind)]; rw [Ring.inverse_of_isUnit (by grind)]
  exact CStarAlgebra.inv_le_inv (Units.isStrictlyPositive_iff.mp apos) hab

open Ring in
@[gcongr]
/--
lemma `ringInverse_le_ringInverse` / 引理 `ringInverse_le_ringInverse`

English:
lemma ringInverse_le_ringInverse
  given: {a b : A} (hab : a <= b) (ha : IsStrictlyPositive a := by cfc_tac)
  proof: antitoneOn_ringInverse ha (IsStrictlyPositive.of_le ha hab) hab

中文:
引理 ringInverse_le_ringInverse
  条件: {a b : A} (hab : a <= b) (ha : IsStrictlyPositive a := by cfc_tac)
  证明: antitoneOn_ringInverse ha (IsStrictlyPositive.of_le ha hab) hab

Depends on / 依赖: IsStrictlyPositive, IsStrictlyPositive.of_le, antitoneOn_ringInverse, cfc_tac, of_le
-/
lemma ringInverse_le_ringInverse {a b : A} (hab : a <= b) (ha : IsStrictlyPositive a := by cfc_tac) :
    b⁻¹ʳ <= a⁻¹ʳ :=
  antitoneOn_ringInverse ha (IsStrictlyPositive.of_le ha hab) hab

end CStarAlgebra

end Inv

end CStar_unital

section CStar_nonunital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace CStarAlgebra

open ComplexOrder in
/--
Instance `instNonnegSpectrumClassComplexNonUnital` / 实例 `instNonnegSpectrumClassComplexNonUnital`

English:
instance instNonnegSpectrumClassComplexNonUnital
  signature: : NonnegSpectrumClass Complex A where
  body: by
    rw [Unitization.quasispectrum_eq_spectrum_inr' Complex Complex a] at hx
    exact spectrum_nonneg_of_nonneg (Unitization.inr_nonneg_iff.mpr ha) hx

中文:
实例 instNonnegSpectrumClassComplexNonUnital
  签名: : NonnegSpectrum类 复形 A where
  定义体: by
    rw [Unitization.quasispectrum_eq_spectrum_inr' Complex Complex a] at hx
    exact spectrum_nonneg_of_nonneg (Unitization.inr_nonneg_iff.mpr ha) hx

Depends on / 依赖: Unitization, Unitization.inr_nonneg_iff.mpr, Unitization.quasispectrum_eq_spectrum_inr, inr_nonneg_iff, quasispectrum_eq_spectrum_inr, spectrum_nonneg_of_nonneg
-/
instance instNonnegSpectrumClassComplexNonUnital : NonnegSpectrumClass Complex A where
  quasispectrum_nonneg_of_nonneg a ha x hx := by
    rw [Unitization.quasispectrum_eq_spectrum_inr' Complex Complex a] at hx
    exact spectrum_nonneg_of_nonneg (Unitization.inr_nonneg_iff.mpr ha) hx

/--
lemma `norm_le_norm_of_nonneg_of_le` / 引理 `norm_le_norm_of_nonneg_of_le`

English:
lemma norm_le_norm_of_nonneg_of_le
  given: {a b : A} (ha : 0 <= a := by cfc_tac) (hab : a <= b)
  proof: by
  suffices forall a b : A⁺¹, 0 <= a -> a <= b -> ‖a‖ <= ‖b‖ by
    have hb := ha.trans hab
    simpa only [ge_iff_le, Unitization.norm_inr] using
      this a b (by simpa) (by rwa [Unitization.inr_le_iff a b])
  intro a b ha hab
  have hb : 0 <= b := ha.trans hab
exact (norm_le_iff_le_algebraMap 

中文:
引理 norm_le_norm_of_nonneg_of_le
  条件: {a b : A} (ha : 0 <= a := by cfc_tac) (hab : a <= b)
  证明: by
  suffices forall a b : A⁺¹, 0 <= a -> a <= b -> ‖a‖ <= ‖b‖ by
    have hb := ha.trans hab
    simpa only [ge_iff_le, Unitization.norm_inr] using
      this a b (by simpa) (by rwa [Unitization.inr_le_iff a b])
  intro a b ha hab
  have hb : 0 <= b := ha.trans hab
exact (norm_le_iff_le_algebraMap 

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.le_algebraMap_norm_self, Unitization, Unitization.inr_le_iff, Unitization.norm_inr, cfc_tac, ge_iff_le, ha.trans, hab.trans, inr_le_iff, le_algebraMap_norm_self, norm_inr, norm_le_iff_le_algebraMap, norm_nonneg, of_nonneg
-/
lemma norm_le_norm_of_nonneg_of_le {a b : A} (ha : 0 <= a := by cfc_tac) (hab : a <= b) :
    ‖a‖ <= ‖b‖ := by
  suffices forall a b : A⁺¹, 0 <= a -> a <= b -> ‖a‖ <= ‖b‖ by
    have hb := ha.trans hab
    simpa only [ge_iff_le, Unitization.norm_inr] using
      this a b (by simpa) (by rwa [Unitization.inr_le_iff a b])
  intro a b ha hab
  have hb : 0 <= b := ha.trans hab
exact (norm_le_iff_le_algebraMap a (norm_nonneg _) ha).2 hab.trans
    IsSelfAdjoint.le_algebraMap_norm_self (.of_nonneg hb)

/--
theorem `nnnorm_le_nnnorm_of_nonneg_of_le` / 定理 `nnnorm_le_nnnorm_of_nonneg_of_le`

English:
theorem nnnorm_le_nnnorm_of_nonneg_of_le
  given: {a : A} {b : A} (ha : 0 <= a := by cfc_tac) (hab : a <= b)
  proof: norm_le_norm_of_nonneg_of_le ha hab

中文:
定理 nnnorm_le_nnnorm_of_nonneg_of_le
  条件: {a : A} {b : A} (ha : 0 <= a := by cfc_tac) (hab : a <= b)
  证明: norm_le_norm_of_nonneg_of_le ha hab

Depends on / 依赖: cfc_tac, norm_le_norm_of_nonneg_of_le
-/
theorem nnnorm_le_nnnorm_of_nonneg_of_le {a : A} {b : A} (ha : 0 <= a := by cfc_tac) (hab : a <= b) :
    ‖a‖₊ <= ‖b‖₊ :=
  norm_le_norm_of_nonneg_of_le ha hab

/--
lemma `star_left_conjugate_le_norm_smul` / 引理 `star_left_conjugate_le_norm_smul`

English:
lemma star_left_conjugate_le_norm_smul
  given: {a b : A} (hb : IsSelfAdjoint b := by cfc_tac)
  proof: by
  suffices forall a b : A⁺¹, IsSelfAdjoint b -> star a * b * a <= ‖b‖ • (star a * a) by
    rw [← Unitization.inr_le_iff _ _ (by aesop) ((IsSelfAdjoint.all _).smul (.star_mul_self a))]
simpa [Unitization.norm_inr] using this a b hb.inr Complex
  intro a b hb
  calc
    star a * b * a <= star a * 

中文:
引理 star_left_conjugate_le_norm_smul
  条件: {a b : A} (hb : IsSelfAdjoint b := by cfc_tac)
  证明: by
  suffices forall a b : A⁺¹, IsSelfAdjoint b -> star a * b * a <= ‖b‖ • (star a * a) by
    rw [← Unitization.inr_le_iff _ _ (by aesop) ((IsSelfAdjoint.all _).smul (.star_mul_self a))]
simpa [Unitization.norm_inr] using this a b hb.inr Complex
  intro a b hb
  calc
    star a * b * a <= star a * 

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, IsSelfAdjoint, IsSelfAdjoint.all, Unitization, Unitization.inr_le_iff, Unitization.norm_inr, algebraMap, algebraMap_eq_smul_one, cfc_tac, hb.inr, hb.le_algebraMap_norm_self, inr_le_iff, le_algebraMap_norm_self, norm_inr, star_left_conjugate_le_conjugate, star_mul_self
-/
lemma star_left_conjugate_le_norm_smul {a b : A} (hb : IsSelfAdjoint b := by cfc_tac) :
    star a * b * a <= ‖b‖ • (star a * a) := by
  suffices forall a b : A⁺¹, IsSelfAdjoint b -> star a * b * a <= ‖b‖ • (star a * a) by
    rw [← Unitization.inr_le_iff _ _ (by aesop) ((IsSelfAdjoint.all _).smul (.star_mul_self a))]
simpa [Unitization.norm_inr] using this a b hb.inr Complex
  intro a b hb
  calc
    star a * b * a <= star a * (algebraMap Real A⁺¹ ‖b‖) * a :=
      star_left_conjugate_le_conjugate hb.le_algebraMap_norm_self _
    _ = ‖b‖ • (star a * a) := by simp [Algebra.algebraMap_eq_smul_one]

/--
lemma `star_right_conjugate_le_norm_smul` / 引理 `star_right_conjugate_le_norm_smul`

English:
lemma star_right_conjugate_le_norm_smul
  given: {a b : A} (hb : IsSelfAdjoint b := by cfc_tac)
  proof: by
  simpa using star_left_conjugate_le_norm_smul (a := star a)

中文:
引理 star_right_conjugate_le_norm_smul
  条件: {a b : A} (hb : IsSelfAdjoint b := by cfc_tac)
  证明: by
  simpa using star_left_conjugate_le_norm_smul (a := star a)

Depends on / 依赖: cfc_tac, star_left_conjugate_le_norm_smul
-/
lemma star_right_conjugate_le_norm_smul {a b : A} (hb : IsSelfAdjoint b := by cfc_tac) :
    a * b * star a <= ‖b‖ • (a * star a) := by
  simpa using star_left_conjugate_le_norm_smul (a := star a)

/--
lemma `isClosed_nonneg` / 引理 `isClosed_nonneg`

English:
lemma isClosed_nonneg
  statement: IsClosed {a : A | 0 <= a}
  proof: by
  suffices IsClosed {a : A⁺¹ | 0 <= a} by
    rw [Unitization.isometry_inr (𝕜 := Complex) |>.isClosedEmbedding.isClosed_iff_image_isClosed]
convert! this.inter (Unitization.isometry_inr (𝕜 := Complex)).isClosedEmbedding.isClosed_range
    ext a
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set

中文:
引理 isClosed_nonneg
  结论: 是闭集 {a : A | 0 <= a}
  证明: by
  suffices IsClosed {a : A⁺¹ | 0 <= a} by
    rw [Unitization.isometry_inr (𝕜 := Complex) |>.isClosedEmbedding.isClosed_iff_image_isClosed]
convert! this.inter (Unitization.isometry_inr (𝕜 := Complex)).isClosedEmbedding.isClosed_range
    ext a
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set

Depends on / 依赖: IsClosed, Set.mem_image, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_range, SpectrumRestricts, SpectrumRestricts.nnrea, Unitization, Unitization.isometry_inr, and_congr_left, and_congr_right, convert, exists_and_left, isClosedEmbedding, isClosedEmbedding.isClosed_iff_image_isClosed, isClosedEmbedding.isClosed_range, isClosed_iff_image_isClosed, isClosed_range, isometry_inr, mem_image
-/
lemma isClosed_nonneg : IsClosed {a : A | 0 <= a} := by
  suffices IsClosed {a : A⁺¹ | 0 <= a} by
    rw [Unitization.isometry_inr (𝕜 := Complex) |>.isClosedEmbedding.isClosed_iff_image_isClosed]
convert! this.inter (Unitization.isometry_inr (𝕜 := Complex)).isClosedEmbedding.isClosed_range
    ext a
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_range,
      ← exists_and_left]
    congr! 2 with x
    exact and_congr_left fun h => by simp [← h]
  simp only [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts,
    and_congr_right (SpectrumRestricts.nnreal_iff_nnnorm · le_rfl), Set.ofPred_and]
.inter isClosed_le ?_ ?_ refine isClosed_eq ?_ ?_
  all_goals fun_prop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderClosedTopology A
  body: isClosed_le_of_isClosed_nonneg isClosed_nonneg

中文:
实例 :
  签名: OrderClosed拓扑 A
  定义体: isClosed_le_of_isClosed_nonneg isClosed_nonneg

Depends on / 依赖: isClosed_le_of_isClosed_nonneg, isClosed_nonneg
-/
instance : OrderClosedTopology A where
  isClosed_le' := isClosed_le_of_isClosed_nonneg isClosed_nonneg

open Unitization in
/--
lemma `convexOn_cfcₙ_of_convexOn_cfc` / 引理 `convexOn_cfcₙ_of_convexOn_cfc`

English:
lemma convexOn_cfcₙ_of_convexOn_cfc
  statement: {f : Real -> Real} {s : Set A}
  proof: by
  let inrl : A ->ₗ[Real] A⁺¹ := inrHom Real Complex A
  by_cases hf₀ : f 0 = 0
  case neg =>
    have : (cfcₙ f : A -> A) = fun _ => 0 := by
      ext x
      simp [cfcₙ_apply_of_not_map_zero _ hf₀]
    rw [this]
    refine convexOn_const _ ?_
    have : Convex Real (inrl ⁻¹' inrl '' s) := Convex

中文:
引理 convexOn_cfcₙ_of_convexOn_cfc
  结论: {f : 实数 -> 实数} {s : 集合 A}
  证明: by
  let inrl : A ->ₗ[Real] A⁺¹ := inrHom Real Complex A
  by_cases hf₀ : f 0 = 0
  case neg =>
    have : (cfcₙ f : A -> A) = fun _ => 0 := by
      ext x
      simp [cfcₙ_apply_of_not_map_zero _ hf₀]
    rw [this]
    refine convexOn_const _ ?_
    have : Convex Real (inrl ⁻¹' inrl '' s) := Convex

Depends on / 依赖: Convex, Convex.linear_preimage, ConvexOn, IsSelfAdjoint, IsSelfAdjoint.cfc, Set.preimage_image_eq, convexOn_const, convexOn_of_convexOn_inr_comp, inrHom, inrHom_injective, linear_preimage, preimage_image_eq
-/
lemma convexOn_cfcₙ_of_convexOn_cfc {f : Real -> Real} {s : Set A}
    (hf : ConvexOn Real (inr (R := Complex) '' s) (cfc f)) : ConvexOn Real s (cfcₙ f) := by
  let inrl : A ->ₗ[Real] A⁺¹ := inrHom Real Complex A
  by_cases hf₀ : f 0 = 0
  case neg =>
    have : (cfcₙ f : A -> A) = fun _ => 0 := by
      ext x
      simp [cfcₙ_apply_of_not_map_zero _ hf₀]
    rw [this]
    refine convexOn_const _ ?_
    have : Convex Real (inrl ⁻¹' inrl '' s) := Convex.linear_preimage hf.1 _
    rwa [Set.preimage_image_eq _ inrHom_injective] at this
  refine convexOn_of_convexOn_inr_comp (fun _ => IsSelfAdjoint.cfcₙ) ?_
  have h₁ : inr (R := Complex) ∘ (cfcₙ f) = fun x : A => ((cfcₙ f x : A) : A⁺¹) := rfl
  have h₂ : (fun x : A => ((cfcₙ f x : A) : A⁺¹))
      = fun x : A => cfc f (x : A⁺¹) := by ext1; rw [real_cfcₙ_eq_cfc_inr ..]
  rw [h₁]; rw [h₂]
  have h₃ : ConvexOn Real (inrl ⁻¹' inrl '' s) ((cfc f) ∘ inrl) :=
    ConvexOn.comp_linearMap (g := inrl) hf
  rwa [Set.preimage_image_eq _ inrHom_injective] at h₃

open Unitization in
/--
lemma `concaveOn_cfcₙ_of_concaveOn_cfc` / 引理 `concaveOn_cfcₙ_of_concaveOn_cfc`

English:
lemma concaveOn_cfcₙ_of_concaveOn_cfc
  statement: {f : Real -> Real} {s : Set A}
  proof: by
  have : ConcaveOn Real s (- -cfcₙ f) := by
    rw [← cfcₙ_neg' f]
    refine (convexOn_cfcₙ_of_convexOn_cfc ?_).neg
    rw [cfc_neg']
    exact hf.neg
  simpa using this

中文:
引理 concaveOn_cfcₙ_of_concaveOn_cfc
  结论: {f : 实数 -> 实数} {s : 集合 A}
  证明: by
  have : ConcaveOn Real s (- -cfcₙ f) := by
    rw [← cfcₙ_neg' f]
    refine (convexOn_cfcₙ_of_convexOn_cfc ?_).neg
    rw [cfc_neg']
    exact hf.neg
  simpa using this

Depends on / 依赖: ConcaveOn, cfc_neg, hf.neg
-/
lemma concaveOn_cfcₙ_of_concaveOn_cfc {f : Real -> Real} {s : Set A}
    (hf : ConcaveOn Real (inr (R := Complex) '' s) (cfc f)) : ConcaveOn Real s (cfcₙ f) := by
  have : ConcaveOn Real s (- -cfcₙ f) := by
    rw [← cfcₙ_neg' f]
    refine (convexOn_cfcₙ_of_convexOn_cfc ?_).neg
    rw [cfc_neg']
    exact hf.neg
  simpa using this

section Icc

open Unitization Set Metric

/--
lemma `inr_mem_Icc_iff_norm_le` / 引理 `inr_mem_Icc_iff_norm_le`

English:
lemma inr_mem_Icc_iff_norm_le
  given: {x : A}
  proof: by
  simp only [mem_Icc, inr_nonneg_iff, and_congr_right_iff]
  rw [← norm_inr (𝕜 := Complex)]; rw [← inr_nonneg_iff]; rw [iff_comm]
  exact (norm_le_one_iff_of_nonneg _ ·)

中文:
引理 inr_mem_Icc_iff_norm_le
  条件: {x : A}
  证明: by
  simp only [mem_Icc, inr_nonneg_iff, and_congr_right_iff]
  rw [← norm_inr (𝕜 := Complex)]; rw [← inr_nonneg_iff]; rw [iff_comm]
  exact (norm_le_one_iff_of_nonneg _ ·)

Depends on / 依赖: and_congr_right_iff, iff_comm, inr_nonneg_iff, mem_Icc, norm_inr, norm_le_one_iff_of_nonneg
-/
lemma inr_mem_Icc_iff_norm_le {x : A} :
    (x : A⁺¹) in Icc 0 1 ↔ 0 <= x ∧ ‖x‖ <= 1 := by
  simp only [mem_Icc, inr_nonneg_iff, and_congr_right_iff]
  rw [← norm_inr (𝕜 := Complex)]; rw [← inr_nonneg_iff]; rw [iff_comm]
  exact (norm_le_one_iff_of_nonneg _ ·)

/--
lemma `inr_mem_Icc_iff_nnnorm_le` / 引理 `inr_mem_Icc_iff_nnnorm_le`

English:
lemma inr_mem_Icc_iff_nnnorm_le
  given: {x : A}
  proof: inr_mem_Icc_iff_norm_le

中文:
引理 inr_mem_Icc_iff_nnnorm_le
  条件: {x : A}
  证明: inr_mem_Icc_iff_norm_le

Depends on / 依赖: inr_mem_Icc_iff_norm_le
-/
lemma inr_mem_Icc_iff_nnnorm_le {x : A} :
    (x : A⁺¹) in Icc 0 1 ↔ 0 <= x ∧ ‖x‖₊ <= 1 :=
  inr_mem_Icc_iff_norm_le

/--
lemma `preimage_inr_Icc_zero_one` / 引理 `preimage_inr_Icc_zero_one`

English:
lemma preimage_inr_Icc_zero_one
  proof: by
  ext
  simp [-mem_Icc, inr_mem_Icc_iff_norm_le]

中文:
引理 preimage_inr_Icc_zero_one
  证明: by
  ext
  simp [-mem_Icc, inr_mem_Icc_iff_norm_le]

Depends on / 依赖: inr_mem_Icc_iff_norm_le, mem_Icc
-/
lemma preimage_inr_Icc_zero_one :
    ((↑) : A -> A⁺¹) ⁻¹' Icc 0 1 = {x : A | 0 <= x} inter closedBall 0 1 := by
  ext
  simp [-mem_Icc, inr_mem_Icc_iff_norm_le]

/--
lemma `inr_map_Ici_zero` / 引理 `inr_map_Ici_zero`

English:
lemma inr_map_Ici_zero
  statement: inr '' (Ici (0 : A)) subseteq Ici (0 : A⁺¹)
  proof: by
  rintro - ⟨a, ha, rfl⟩
  exact Unitization.inr_nonneg_iff.mpr ha

中文:
引理 inr_map_Ici_zero
  结论: inr '' (左闭右无界区间 (0 : A)) subseteq 左闭右无界区间 (0 : A⁺¹)
  证明: by
  rintro - ⟨a, ha, rfl⟩
  exact Unitization.inr_nonneg_iff.mpr ha

Depends on / 依赖: Unitization, Unitization.inr_nonneg_iff.mpr, inr_nonneg_iff
-/
lemma inr_map_Ici_zero : inr '' (Ici (0 : A)) subseteq Ici (0 : A⁺¹) := by
  rintro - ⟨a, ha, rfl⟩
  exact Unitization.inr_nonneg_iff.mpr ha

end Icc

end CStarAlgebra

open CStarAlgebra Unitization CFC in
/--
lemma `IsStarProjection.mul_right_and_mul_left_of_nonneg_of_le` / 引理 `IsStarProjection.mul_right_and_mul_left_of_nonneg_of_le`

English:
lemma IsStarProjection.mul_right_and_mul_left_of_nonneg_of_le
  statement: {a e : A}
  proof: by
  suffices a * e = a from
    ⟨this, by simpa [ha.star_eq, he.isSelfAdjoint.star_eq] using congr(star $this)⟩
  suffices forall a e : A⁺¹, IsStarProjection e -> 0 <= a -> a <= e -> a * e = a from
    mod_cast this a e he.inr ha.inr (inr_le_iff a e |>.mpr hae)
  intro a e he ha hae
  suffices sqrt

中文:
引理 是StarProjection.mul_right_and_mul_left_of_nonneg_of_le
  结论: {a e : A}
  证明: by
  suffices a * e = a from
    ⟨this, by simpa [ha.star_eq, he.isSelfAdjoint.star_eq] using congr(star $this)⟩
  suffices forall a e : A⁺¹, IsStarProjection e -> 0 <= a -> a <= e -> a * e = a from
    mod_cast this a e he.inr ha.inr (inr_le_iff a e |>.mpr hae)
  intro a e he ha hae
  suffices sqrt

Depends on / 依赖: IsStarProjection, eq_comm, ha.inr, ha.star_eq, he.inr, he.isSelfAdjoint.star_eq, inr_le_iff, isSelfAdjoint, mod_cast, mul_assoc, mul_sub, norm_eq_zero, norm_star_mul_mul_self_of_nonn, sq_eq_zero_iff, sqrt_mul_sqrt_self, star_eq, sub_eq_zero
-/
lemma IsStarProjection.mul_right_and_mul_left_of_nonneg_of_le {a e : A}
    (he : IsStarProjection e) (ha : 0 <= a) (hae : a <= e) : a * e = a ∧ e * a = a := by
  suffices a * e = a from
    ⟨this, by simpa [ha.star_eq, he.isSelfAdjoint.star_eq] using congr(star $this)⟩
  suffices forall a e : A⁺¹, IsStarProjection e -> 0 <= a -> a <= e -> a * e = a from
    mod_cast this a e he.inr ha.inr (inr_le_iff a e |>.mpr hae)
  intro a e he ha hae
  suffices sqrt a * (1 - e : A⁺¹) = 0 by
    simpa [← mul_assoc, sqrt_mul_sqrt_self a, mul_sub, sub_eq_zero, eq_comm (a := a)]
      using congr(sqrt a * $this)
  rw [← norm_eq_zero]; rw [← sq_eq_zero_iff]; rw [← norm_star_mul_mul_self_of_nonneg]; rw [norm_eq_zero]
refine le_antisymm ?_ star_left_conjugate_nonneg ha _
  grw [star_left_conjugate_le_conjugate hae (1 - e), mul_assoc, he.mul_one_sub_self, mul_zero]

/--
lemma `IsStarProjection.conjugate_of_nonneg_of_le` / 引理 `IsStarProjection.conjugate_of_nonneg_of_le`

English:
lemma IsStarProjection.conjugate_of_nonneg_of_le
  statement: {a e : A} (he : IsStarProjection e)
  proof: by
  grind [he.mul_right_and_mul_left_of_nonneg_of_le ha hae]

中文:
引理 是StarProjection.conjugate_of_nonneg_of_le
  结论: {a e : A} (he : 是StarProjection e)
  证明: by
  grind [he.mul_right_and_mul_left_of_nonneg_of_le ha hae]

Depends on / 依赖: he.mul_right_and_mul_left_of_nonneg_of_le, mul_right_and_mul_left_of_nonneg_of_le
-/
lemma IsStarProjection.conjugate_of_nonneg_of_le {a e : A} (he : IsStarProjection e)
    (ha : 0 <= a) (hae : a <= e) : e * a * e = a := by
  grind [he.mul_right_and_mul_left_of_nonneg_of_le ha hae]

end CStar_nonunital

section Pow

namespace CStarAlgebra

variable {A : Type*} {B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/--
lemma `pow_nonneg` / 引理 `pow_nonneg`

English:
lemma pow_nonneg
  given: {a : A} (ha : 0 <= a := by cfc_tac) (n : Nat)
  statement: 0 <= a ^ n
  proof: by
  rw [← cfc_pow_id (R := Real>=0) a]
  exact cfc_nonneg_of_predicate

中文:
引理 pow_nonneg
  条件: {a : A} (ha : 0 <= a := by cfc_tac) (n : 自然数)
  结论: 0 <= a ^ n
  证明: by
  rw [← cfc_pow_id (R := Real>=0) a]
  exact cfc_nonneg_of_predicate

Depends on / 依赖: cfc_nonneg_of_predicate, cfc_pow_id, cfc_tac
-/
lemma pow_nonneg {a : A} (ha : 0 <= a := by cfc_tac) (n : Nat) : 0 <= a ^ n := by
  rw [← cfc_pow_id (R := Real>=0) a]
  exact cfc_nonneg_of_predicate

/--
lemma `pow_monotone` / 引理 `pow_monotone`

English:
lemma pow_monotone
  given: {a : A} (ha : 1 <= a)
  statement: Monotone (a ^ · : Nat -> A)
  proof: by
  have ha' : 0 <= a := zero_le_one.trans ha
  intro n m hnm
  simp only
  rw [← cfc_pow_id (R := Real) a]; rw [← cfc_pow_id (R := Real) a]; rw [cfc_le_iff ..]
  rw [CFC.one_le_iff (R := Real) a] at ha
  peel ha with x hx _
  exact pow_le_pow_right₀ (ha x hx) hnm

中文:
引理 pow_monotone
  条件: {a : A} (ha : 1 <= a)
  结论: 递增 (a ^ · : 自然数 -> A)
  证明: by
  have ha' : 0 <= a := zero_le_one.trans ha
  intro n m hnm
  simp only
  rw [← cfc_pow_id (R := Real) a]; rw [← cfc_pow_id (R := Real) a]; rw [cfc_le_iff ..]
  rw [CFC.one_le_iff (R := Real) a] at ha
  peel ha with x hx _
  exact pow_le_pow_right₀ (ha x hx) hnm

Depends on / 依赖: CFC.one_le_iff, cfc_le_iff, cfc_pow_id, one_le_iff, zero_le_one, zero_le_one.trans
-/
lemma pow_monotone {a : A} (ha : 1 <= a) : Monotone (a ^ · : Nat -> A) := by
  have ha' : 0 <= a := zero_le_one.trans ha
  intro n m hnm
  simp only
  rw [← cfc_pow_id (R := Real) a]; rw [← cfc_pow_id (R := Real) a]; rw [cfc_le_iff ..]
  rw [CFC.one_le_iff (R := Real) a] at ha
  peel ha with x hx _
  exact pow_le_pow_right₀ (ha x hx) hnm

/--
lemma `pow_antitone` / 引理 `pow_antitone`

English:
lemma pow_antitone
  given: {a : A} (ha₀ : 0 <= a := by cfc_tac) (ha₁ : a <= 1)
  proof: by
  intro n m hnm
  simp only
  rw [← cfc_pow_id (R := Real) a]; rw [← cfc_pow_id (R := Real) a]; rw [cfc_le_iff ..]
  rw [CFC.le_one_iff (R := Real) a] at ha₁
  peel ha₁ with x hx _
  exact pow_le_pow_of_le_one (spectrum_nonneg_of_nonneg ha₀ hx) (ha₁ x hx) hnm

中文:
引理 pow_antitone
  条件: {a : A} (ha₀ : 0 <= a := by cfc_tac) (ha₁ : a <= 1)
  证明: by
  intro n m hnm
  simp only
  rw [← cfc_pow_id (R := Real) a]; rw [← cfc_pow_id (R := Real) a]; rw [cfc_le_iff ..]
  rw [CFC.le_one_iff (R := Real) a] at ha₁
  peel ha₁ with x hx _
  exact pow_le_pow_of_le_one (spectrum_nonneg_of_nonneg ha₀ hx) (ha₁ x hx) hnm

Depends on / 依赖: Antitone, CFC.le_one_iff, cfc_le_iff, cfc_pow_id, cfc_tac, le_one_iff, pow_le_pow_of_le_one, spectrum_nonneg_of_nonneg
-/
lemma pow_antitone {a : A} (ha₀ : 0 <= a := by cfc_tac) (ha₁ : a <= 1) :
    Antitone (a ^ · : Nat -> A) := by
  intro n m hnm
  simp only
  rw [← cfc_pow_id (R := Real) a]; rw [← cfc_pow_id (R := Real) a]; rw [cfc_le_iff ..]
  rw [CFC.le_one_iff (R := Real) a] at ha₁
  peel ha₁ with x hx _
  exact pow_le_pow_of_le_one (spectrum_nonneg_of_nonneg ha₀ hx) (ha₁ x hx) hnm

end CStarAlgebra

end Pow
