/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Inverse function theorem - the easy half

In this file we prove that `g' (f x) = (f' x)⁻¹` provided that `f` is strictly differentiable at
`x`, `f' x ≠ 0`, and `g` is a local left inverse of `f` that is continuous at `f x`. This is the
easy half of the inverse function theorem: the harder half states that `g` exists.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative, inverse function
-/

public section


universe u v

open scoped Topology
open Filter Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : 𝕜 -> F}
variable {f' : F}
variable {s : Set 𝕜} {x : 𝕜} {c : F}

/--
theorem `HasStrictDerivAt.hasStrictFDerivAt_equiv` / 定理 `HasStrictDerivAt.hasStrictFDerivAt_equiv`

English:
theorem HasStrictDerivAt.hasStrictFDerivAt_equiv
  statement: {f : 𝕜 -> 𝕜} {f' x : 𝕜}
  proof: hf

中文:
定理 HasStrictDerivAt.hasStrictFDerivAt_equiv
  结论: {f : 𝕜 -> 𝕜} {f' x : 𝕜}
  证明: hf
-/
theorem HasStrictDerivAt.hasStrictFDerivAt_equiv {f : 𝕜 -> 𝕜} {f' x : 𝕜}
    (hf : HasStrictDerivAt f f' x) (hf' : f' != 0) :
    HasStrictFDerivAt f (ContinuousLinearEquiv.unitsEquivAut 𝕜 (Units.mk0 f' hf') : 𝕜 ->L[𝕜] 𝕜) x :=
  hf

/--
theorem `HasDerivAt.hasFDerivAt_equiv` / 定理 `HasDerivAt.hasFDerivAt_equiv`

English:
theorem HasDerivAt.hasFDerivAt_equiv
  statement: {f : 𝕜 -> 𝕜} {f' x : 𝕜} (hf : HasDerivAt f f' x)
  proof: hf

中文:
定理 HasDerivAt.hasFDerivAt_equiv
  结论: {f : 𝕜 -> 𝕜} {f' x : 𝕜} (hf : HasDerivAt f f' x)
  证明: hf
-/
theorem HasDerivAt.hasFDerivAt_equiv {f : 𝕜 -> 𝕜} {f' x : 𝕜} (hf : HasDerivAt f f' x)
    (hf' : f' != 0) :
    HasFDerivAt f (ContinuousLinearEquiv.unitsEquivAut 𝕜 (Units.mk0 f' hf') : 𝕜 ->L[𝕜] 𝕜) x :=
  hf

/--
theorem `HasStrictDerivAt.of_local_left_inverse` / 定理 `HasStrictDerivAt.of_local_left_inverse`

English:
theorem HasStrictDerivAt.of_local_left_inverse
  statement: {f g : 𝕜 -> 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a)
  proof: (hf.hasStrictFDerivAt_equiv hf').of_local_left_inverse hg hfg

中文:
定理 HasStrictDerivAt.of_local_left_inverse
  结论: {f g : 𝕜 -> 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a)
  证明: (hf.hasStrictFDerivAt_equiv hf').of_local_left_inverse hg hfg

Depends on / 依赖: hasStrictFDerivAt_equiv, hf.hasStrictFDerivAt_equiv, of_local_left_inverse
-/
theorem HasStrictDerivAt.of_local_left_inverse {f g : 𝕜 -> 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a)
    (hf : HasStrictDerivAt f f' (g a)) (hf' : f' != 0) (hfg : forallᶠ y in 𝓝 a, f (g y) = y) :
    HasStrictDerivAt g f'⁻¹ a :=
  (hf.hasStrictFDerivAt_equiv hf').of_local_left_inverse hg hfg

/--
theorem `OpenPartialHomeomorph.hasStrictDerivAt_symm` / 定理 `OpenPartialHomeomorph.hasStrictDerivAt_symm`

English:
theorem OpenPartialHomeomorph.hasStrictDerivAt_symm
  statement: (f : OpenPartialHomeomorph 𝕜 𝕜) {a f' : 𝕜}
  proof: htff'.of_local_left_inverse (f.symm.continuousAt ha) hf' (f.eventually_right_inverse ha)

中文:
定理 OpenPartialHomeomorph.hasStrictDerivAt_symm
  结论: (f : OpenPartialHomeomorph 𝕜 𝕜) {a f' : 𝕜}
  证明: htff'.of_local_left_inverse (f.symm.continuousAt ha) hf' (f.eventually_right_inverse ha)

Depends on / 依赖: continuousAt, eventually_right_inverse, f.eventually_right_inverse, f.symm.continuousAt, of_local_left_inverse
-/
theorem OpenPartialHomeomorph.hasStrictDerivAt_symm (f : OpenPartialHomeomorph 𝕜 𝕜) {a f' : 𝕜}
    (ha : a in f.target) (hf' : f' != 0) (htff' : HasStrictDerivAt f f' (f.symm a)) :
    HasStrictDerivAt f.symm f'⁻¹ a :=
  htff'.of_local_left_inverse (f.symm.continuousAt ha) hf' (f.eventually_right_inverse ha)

/--
theorem `HasDerivAt.of_comp_left` / 定理 `HasDerivAt.of_comp_left`

English:
theorem HasDerivAt.of_comp_left
  statement: {f g h : 𝕜 -> 𝕜} {f' h' a : 𝕜} (hst : ContinuousAt g a)
  proof: by
  convert! hf.hasFDerivAt.of_comp_of_leftInverse hst hh hcomp (f'symm := .toSpanSingleton 𝕜 f'⁻¹)
.hasDerivAt using 1 (fun _ => by simp [hf'])
  simp [div_eq_mul_inv]

中文:
定理 HasDerivAt.of_comp_left
  结论: {f g h : 𝕜 -> 𝕜} {f' h' a : 𝕜} (hst : ContinuousAt g a)
  证明: by
  convert! hf.hasFDerivAt.of_comp_of_leftInverse hst hh hcomp (f'symm := .toSpanSingleton 𝕜 f'⁻¹)
.hasDerivAt using 1 (fun _ => by simp [hf'])
  simp [div_eq_mul_inv]

Depends on / 依赖: convert, div_eq_mul_inv, hasDerivAt, hasFDerivAt, hf.hasFDerivAt.of_comp_of_leftInverse, of_comp_of_leftInverse, toSpanSingleton
-/
theorem HasDerivAt.of_comp_left {f g h : 𝕜 -> 𝕜} {f' h' a : 𝕜} (hst : ContinuousAt g a)
    (hf : HasDerivAt f f' (g a)) (hh : HasDerivAt h h' a) (hf' : f' != 0)
    (hcomp : f ∘ g =ᶠ[𝓝 a] h) : HasDerivAt g (h' / f') a := by
  convert! hf.hasFDerivAt.of_comp_of_leftInverse hst hh hcomp (f'symm := .toSpanSingleton 𝕜 f'⁻¹)
.hasDerivAt using 1 (fun _ => by simp [hf'])
  simp [div_eq_mul_inv]

/--
theorem `HasDerivAt.of_local_left_inverse` / 定理 `HasDerivAt.of_local_left_inverse`

English:
theorem HasDerivAt.of_local_left_inverse
  statement: {f g : 𝕜 -> 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a)
  proof: (hf.hasFDerivAt_equiv hf').of_local_left_inverse hg hfg

中文:
定理 HasDerivAt.of_local_left_inverse
  结论: {f g : 𝕜 -> 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a)
  证明: (hf.hasFDerivAt_equiv hf').of_local_left_inverse hg hfg

Depends on / 依赖: hasFDerivAt_equiv, hf.hasFDerivAt_equiv, of_local_left_inverse
-/
theorem HasDerivAt.of_local_left_inverse {f g : 𝕜 -> 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a)
    (hf : HasDerivAt f f' (g a)) (hf' : f' != 0) (hfg : forallᶠ y in 𝓝 a, f (g y) = y) :
    HasDerivAt g f'⁻¹ a :=
  (hf.hasFDerivAt_equiv hf').of_local_left_inverse hg hfg

/--
theorem `OpenPartialHomeomorph.hasDerivAt_symm` / 定理 `OpenPartialHomeomorph.hasDerivAt_symm`

English:
theorem OpenPartialHomeomorph.hasDerivAt_symm
  statement: (f : OpenPartialHomeomorph 𝕜 𝕜) {a f' : 𝕜}
  proof: htff'.of_local_left_inverse (f.symm.continuousAt ha) hf' (f.eventually_right_inverse ha)

中文:
定理 OpenPartialHomeomorph.hasDerivAt_symm
  结论: (f : OpenPartialHomeomorph 𝕜 𝕜) {a f' : 𝕜}
  证明: htff'.of_local_left_inverse (f.symm.continuousAt ha) hf' (f.eventually_right_inverse ha)

Depends on / 依赖: continuousAt, eventually_right_inverse, f.eventually_right_inverse, f.symm.continuousAt, of_local_left_inverse
-/
theorem OpenPartialHomeomorph.hasDerivAt_symm (f : OpenPartialHomeomorph 𝕜 𝕜) {a f' : 𝕜}
    (ha : a in f.target) (hf' : f' != 0) (htff' : HasDerivAt f f' (f.symm a)) :
    HasDerivAt f.symm f'⁻¹ a :=
  htff'.of_local_left_inverse (f.symm.continuousAt ha) hf' (f.eventually_right_inverse ha)

/--
theorem `HasDerivWithinAt.tendsto_nhdsWithin_nhdsNE` / 定理 `HasDerivWithinAt.tendsto_nhdsWithin_nhdsNE`

English:
theorem HasDerivWithinAt.tendsto_nhdsWithin_nhdsNE
  given: (h : HasDerivWithinAt f f' s x) (hf' : f' != 0)
  proof: h.hasFDerivWithinAt.tendsto_nhdsWithin_nhdsNE ⟨‖f'‖₊⁻¹, AntilipschitzWith.of_le_mul_dist
    fun _ _ => by simp [dist_eq_norm_sub, ← sub_smul, norm_smul]; field_simp; rfl⟩

中文:
定理 HasDerivWithinAt.tendsto_nhdsWithin_nhdsNE
  条件: (h : HasDerivWithinAt f f' s x) (hf' : f' != 0)
  证明: h.hasFDerivWithinAt.tendsto_nhdsWithin_nhdsNE ⟨‖f'‖₊⁻¹, AntilipschitzWith.of_le_mul_dist
    fun _ _ => by simp [dist_eq_norm_sub, ← sub_smul, norm_smul]; field_simp; rfl⟩

Depends on / 依赖: AntilipschitzWith, AntilipschitzWith.of_le_mul_dist, dist_eq_norm_sub, h.hasFDerivWithinAt.tendsto_nhdsWithin_nhdsNE, hasFDerivWithinAt, norm_smul, of_le_mul_dist, sub_smul, tendsto_nhdsWithin_nhdsNE
-/
theorem HasDerivWithinAt.tendsto_nhdsWithin_nhdsNE (h : HasDerivWithinAt f f' s x) (hf' : f' != 0) :
    Tendsto f (𝓝[s \ {x}] x) (𝓝[!=] f x) :=
  h.hasFDerivWithinAt.tendsto_nhdsWithin_nhdsNE ⟨‖f'‖₊⁻¹, AntilipschitzWith.of_le_mul_dist
    fun _ _ => by simp [dist_eq_norm_sub, ← sub_smul, norm_smul]; field_simp; rfl⟩

/--
theorem `HasDerivWithinAt.eventually_ne` / 定理 `HasDerivWithinAt.eventually_ne`

English:
theorem HasDerivWithinAt.eventually_ne
  given: (h : HasDerivWithinAt f f' s x) (hf' : f' != 0)
  proof: h.hasFDerivWithinAt.eventually_ne ⟨‖f'‖₊⁻¹, AntilipschitzWith.of_le_mul_dist
    fun _ _ => by simp [dist_eq_norm_sub, ← sub_smul, norm_smul]; field_simp; rfl⟩

中文:
定理 HasDerivWithinAt.eventually_ne
  条件: (h : HasDerivWithinAt f f' s x) (hf' : f' != 0)
  证明: h.hasFDerivWithinAt.eventually_ne ⟨‖f'‖₊⁻¹, AntilipschitzWith.of_le_mul_dist
    fun _ _ => by simp [dist_eq_norm_sub, ← sub_smul, norm_smul]; field_simp; rfl⟩

Depends on / 依赖: AntilipschitzWith, AntilipschitzWith.of_le_mul_dist, dist_eq_norm_sub, eventually_ne, h.hasFDerivWithinAt.eventually_ne, hasFDerivWithinAt, norm_smul, of_le_mul_dist, sub_smul
-/
theorem HasDerivWithinAt.eventually_ne (h : HasDerivWithinAt f f' s x) (hf' : f' != 0) :
    forallᶠ z in 𝓝[s \ {x}] x, f z != c :=
  h.hasFDerivWithinAt.eventually_ne ⟨‖f'‖₊⁻¹, AntilipschitzWith.of_le_mul_dist
    fun _ _ => by simp [dist_eq_norm_sub, ← sub_smul, norm_smul]; field_simp; rfl⟩

/--
theorem `HasDerivWithinAt.eventually_notMem` / 定理 `HasDerivWithinAt.eventually_notMem`

English:
theorem HasDerivWithinAt.eventually_notMem
  statement: (h : HasDerivWithinAt f f' s x) (hf' : f' != 0)
  proof: h.hasFDerivWithinAt.eventually_notMem ⟨‖f'‖₊⁻¹, AntilipschitzWith.of_le_mul_dist
    fun _ _ => by simp [dist_eq_norm_sub, ← sub_smul, norm_smul]; field_simp; rfl⟩ t ht

中文:
定理 HasDerivWithinAt.eventually_notMem
  结论: (h : HasDerivWithinAt f f' s x) (hf' : f' != 0)
  证明: h.hasFDerivWithinAt.eventually_notMem ⟨‖f'‖₊⁻¹, AntilipschitzWith.of_le_mul_dist
    fun _ _ => by simp [dist_eq_norm_sub, ← sub_smul, norm_smul]; field_simp; rfl⟩ t ht

Depends on / 依赖: AntilipschitzWith, AntilipschitzWith.of_le_mul_dist, dist_eq_norm_sub, eventually_notMem, h.hasFDerivWithinAt.eventually_notMem, hasFDerivWithinAt, norm_smul, of_le_mul_dist, sub_smul
-/
theorem HasDerivWithinAt.eventually_notMem (h : HasDerivWithinAt f f' s x) (hf' : f' != 0)
    (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t)) : forallᶠ z in 𝓝[s \ {x}] x, f z ∉ t :=
  h.hasFDerivWithinAt.eventually_notMem ⟨‖f'‖₊⁻¹, AntilipschitzWith.of_le_mul_dist
    fun _ _ => by simp [dist_eq_norm_sub, ← sub_smul, norm_smul]; field_simp; rfl⟩ t ht

/--
theorem `HasDerivAt.tendsto_nhdsNE` / 定理 `HasDerivAt.tendsto_nhdsNE`

English:
theorem HasDerivAt.tendsto_nhdsNE
  given: (h : HasDerivAt f f' x) (hf' : f' != 0)
  proof: by
  simpa only [compl_eq_univ_sdiff] using (hasDerivWithinAt_univ.2 h).tendsto_nhdsWithin_nhdsNE hf'

中文:
定理 HasDerivAt.tendsto_nhdsNE
  条件: (h : HasDerivAt f f' x) (hf' : f' != 0)
  证明: by
  simpa only [compl_eq_univ_sdiff] using (hasDerivWithinAt_univ.2 h).tendsto_nhdsWithin_nhdsNE hf'

Depends on / 依赖: compl_eq_univ_sdiff, hasDerivWithinAt_univ, tendsto_nhdsWithin_nhdsNE
-/
theorem HasDerivAt.tendsto_nhdsNE (h : HasDerivAt f f' x) (hf' : f' != 0) :
    Tendsto f (𝓝[!=] x) (𝓝[!=] f x) := by
  simpa only [compl_eq_univ_sdiff] using (hasDerivWithinAt_univ.2 h).tendsto_nhdsWithin_nhdsNE hf'

/--
theorem `HasDerivAt.eventually_ne` / 定理 `HasDerivAt.eventually_ne`

English:
theorem HasDerivAt.eventually_ne
  given: (h : HasDerivAt f f' x) (hf' : f' != 0)
  proof: by
  simpa only [compl_eq_univ_sdiff] using (hasDerivWithinAt_univ.2 h).eventually_ne hf'

中文:
定理 HasDerivAt.eventually_ne
  条件: (h : HasDerivAt f f' x) (hf' : f' != 0)
  证明: by
  simpa only [compl_eq_univ_sdiff] using (hasDerivWithinAt_univ.2 h).eventually_ne hf'

Depends on / 依赖: compl_eq_univ_sdiff, eventually_ne, hasDerivWithinAt_univ
-/
theorem HasDerivAt.eventually_ne (h : HasDerivAt f f' x) (hf' : f' != 0) :
    forallᶠ z in 𝓝[!=] x, f z != c := by
  simpa only [compl_eq_univ_sdiff] using (hasDerivWithinAt_univ.2 h).eventually_ne hf'

/--
theorem `HasDerivAt.eventually_notMem` / 定理 `HasDerivAt.eventually_notMem`

English:
theorem HasDerivAt.eventually_notMem
  statement: (h : HasDerivAt f f' x) (hf' : f' != 0)
  proof: by
  simpa only [compl_eq_univ_sdiff] using (hasDerivWithinAt_univ.2 h).eventually_notMem hf' t ht

中文:
定理 HasDerivAt.eventually_notMem
  结论: (h : HasDerivAt f f' x) (hf' : f' != 0)
  证明: by
  simpa only [compl_eq_univ_sdiff] using (hasDerivWithinAt_univ.2 h).eventually_notMem hf' t ht

Depends on / 依赖: compl_eq_univ_sdiff, eventually_notMem, hasDerivWithinAt_univ
-/
theorem HasDerivAt.eventually_notMem (h : HasDerivAt f f' x) (hf' : f' != 0)
    (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t)) : forallᶠ z in 𝓝[!=] x, f z ∉ t := by
  simpa only [compl_eq_univ_sdiff] using (hasDerivWithinAt_univ.2 h).eventually_notMem hf' t ht

/--
theorem `derivWithin_zero_of_frequently_const` / 定理 `derivWithin_zero_of_frequently_const`

English:
theorem derivWithin_zero_of_frequently_const
  given: {c} (h : existsᶠ y in 𝓝[s \ {x}] x, f y = c)
  proof: by
  by_cases hf : DifferentiableWithinAt 𝕜 f s x
  · contrapose! h
    exact hf.hasDerivWithinAt.eventually_ne h
  · exact derivWithin_zero_of_not_differentiableWithinAt hf

中文:
定理 derivWithin_zero_of_frequently_const
  条件: {c} (h : 存在ᶠ y in 𝓝[s \ {x}] x, f y = c)
  证明: by
  by_cases hf : DifferentiableWithinAt 𝕜 f s x
  · contrapose! h
    exact hf.hasDerivWithinAt.eventually_ne h
  · exact derivWithin_zero_of_not_differentiableWithinAt hf

Depends on / 依赖: DifferentiableWithinAt, contrapose, derivWithin_zero_of_not_differentiableWithinAt, eventually_ne, hasDerivWithinAt, hf.hasDerivWithinAt.eventually_ne
-/
theorem derivWithin_zero_of_frequently_const {c} (h : existsᶠ y in 𝓝[s \ {x}] x, f y = c) :
    derivWithin f s x = 0 := by
  by_cases hf : DifferentiableWithinAt 𝕜 f s x
  · contrapose! h
    exact hf.hasDerivWithinAt.eventually_ne h
  · exact derivWithin_zero_of_not_differentiableWithinAt hf

/--
theorem `derivWithin_zero_of_frequently_mem` / 定理 `derivWithin_zero_of_frequently_mem`

English:
theorem derivWithin_zero_of_frequently_mem
  statement: (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t))
  proof: by
  by_cases hf : DifferentiableWithinAt 𝕜 f s x
  · contrapose! h
    exact hf.hasDerivWithinAt.eventually_notMem h t ht
  · exact derivWithin_zero_of_not_differentiableWithinAt hf

中文:
定理 derivWithin_zero_of_frequently_mem
  结论: (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t))
  证明: by
  by_cases hf : DifferentiableWithinAt 𝕜 f s x
  · contrapose! h
    exact hf.hasDerivWithinAt.eventually_notMem h t ht
  · exact derivWithin_zero_of_not_differentiableWithinAt hf

Depends on / 依赖: DifferentiableWithinAt, contrapose, derivWithin_zero_of_not_differentiableWithinAt, eventually_notMem, hasDerivWithinAt, hf.hasDerivWithinAt.eventually_notMem
-/
theorem derivWithin_zero_of_frequently_mem (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t))
    (h : existsᶠ y in 𝓝[s \ {x}] x, f y in t) : derivWithin f s x = 0 := by
  by_cases hf : DifferentiableWithinAt 𝕜 f s x
  · contrapose! h
    exact hf.hasDerivWithinAt.eventually_notMem h t ht
  · exact derivWithin_zero_of_not_differentiableWithinAt hf

/--
theorem `deriv_zero_of_frequently_const` / 定理 `deriv_zero_of_frequently_const`

English:
theorem deriv_zero_of_frequently_const
  given: {c} (h : existsᶠ y in 𝓝[!=] x, f y = c)
  statement: deriv f x = 0
  proof: by
  rw [← derivWithin_univ]; rw [derivWithin_zero_of_frequently_const]
  rwa [← compl_eq_univ_sdiff]

中文:
定理 deriv_zero_of_frequently_const
  条件: {c} (h : 存在ᶠ y in 𝓝[!=] x, f y = c)
  结论: deriv f x = 0
  证明: by
  rw [← derivWithin_univ]; rw [derivWithin_zero_of_frequently_const]
  rwa [← compl_eq_univ_sdiff]

Depends on / 依赖: compl_eq_univ_sdiff, derivWithin_univ, derivWithin_zero_of_frequently_const
-/
theorem deriv_zero_of_frequently_const {c} (h : existsᶠ y in 𝓝[!=] x, f y = c) : deriv f x = 0 := by
  rw [← derivWithin_univ]; rw [derivWithin_zero_of_frequently_const]
  rwa [← compl_eq_univ_sdiff]

/--
theorem `deriv_zero_of_frequently_mem` / 定理 `deriv_zero_of_frequently_mem`

English:
theorem deriv_zero_of_frequently_mem
  statement: (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t))
  proof: by
  rw [← derivWithin_univ]; rw [derivWithin_zero_of_frequently_mem t ht]
  rwa [← compl_eq_univ_sdiff]

中文:
定理 deriv_zero_of_frequently_mem
  结论: (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t))
  证明: by
  rw [← derivWithin_univ]; rw [derivWithin_zero_of_frequently_mem t ht]
  rwa [← compl_eq_univ_sdiff]

Depends on / 依赖: compl_eq_univ_sdiff, derivWithin_univ, derivWithin_zero_of_frequently_mem
-/
theorem deriv_zero_of_frequently_mem (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t))
    (h : existsᶠ y in 𝓝[!=] x, f y in t) : deriv f x = 0 := by
  rw [← derivWithin_univ]; rw [derivWithin_zero_of_frequently_mem t ht]
  rwa [← compl_eq_univ_sdiff]

/--
theorem `not_differentiableWithinAt_of_local_left_inverse_hasDerivWithinAt_zero` / 定理 `not_differentiableWithinAt_of_local_left_inverse_hasDerivWithinAt_zero`

English:
theorem not_differentiableWithinAt_of_local_left_inverse_hasDerivWithinAt_zero
  statement: {f g : 𝕜 -> 𝕜} {a : 𝕜}
  proof: by
  intro hg
  have := (hf.comp a hg.hasDerivWithinAt hst).congr_of_eventuallyEq_of_mem hfg.symm ha
  simpa using hsu.eq_deriv _ this (hasDerivWithinAt_id _ _)

中文:
定理 not_differentiableWithinAt_of_local_left_inverse_hasDerivWithinAt_zero
  结论: {f g : 𝕜 -> 𝕜} {a : 𝕜}
  证明: by
  intro hg
  have := (hf.comp a hg.hasDerivWithinAt hst).congr_of_eventuallyEq_of_mem hfg.symm ha
  simpa using hsu.eq_deriv _ this (hasDerivWithinAt_id _ _)

Depends on / 依赖: congr_of_eventuallyEq_of_mem, eq_deriv, hasDerivWithinAt, hasDerivWithinAt_id, hf.comp, hfg.symm, hg.hasDerivWithinAt, hsu.eq_deriv
-/
theorem not_differentiableWithinAt_of_local_left_inverse_hasDerivWithinAt_zero {f g : 𝕜 -> 𝕜} {a : 𝕜}
    {s t : Set 𝕜} (ha : a in s) (hsu : UniqueDiffWithinAt 𝕜 s a) (hf : HasDerivWithinAt f 0 t (g a))
    (hst : MapsTo g s t) (hfg : f ∘ g =ᶠ[𝓝[s] a] id) : ¬DifferentiableWithinAt 𝕜 g s a := by
  intro hg
  have := (hf.comp a hg.hasDerivWithinAt hst).congr_of_eventuallyEq_of_mem hfg.symm ha
  simpa using hsu.eq_deriv _ this (hasDerivWithinAt_id _ _)

/--
theorem `not_differentiableAt_of_local_left_inverse_hasDerivAt_zero` / 定理 `not_differentiableAt_of_local_left_inverse_hasDerivAt_zero`

English:
theorem not_differentiableAt_of_local_left_inverse_hasDerivAt_zero
  statement: {f g : 𝕜 -> 𝕜} {a : 𝕜}
  proof: by
  intro hg
  have := (hf.comp a hg.hasDerivAt).congr_of_eventuallyEq hfg.symm
  simpa using this.unique (hasDerivAt_id a)

中文:
定理 not_differentiableAt_of_local_left_inverse_hasDerivAt_zero
  结论: {f g : 𝕜 -> 𝕜} {a : 𝕜}
  证明: by
  intro hg
  have := (hf.comp a hg.hasDerivAt).congr_of_eventuallyEq hfg.symm
  simpa using this.unique (hasDerivAt_id a)

Depends on / 依赖: congr_of_eventuallyEq, hasDerivAt, hasDerivAt_id, hf.comp, hfg.symm, hg.hasDerivAt, this.unique, unique
-/
theorem not_differentiableAt_of_local_left_inverse_hasDerivAt_zero {f g : 𝕜 -> 𝕜} {a : 𝕜}
    (hf : HasDerivAt f 0 (g a)) (hfg : f ∘ g =ᶠ[𝓝 a] id) : ¬DifferentiableAt 𝕜 g a := by
  intro hg
  have := (hf.comp a hg.hasDerivAt).congr_of_eventuallyEq hfg.symm
  simpa using this.unique (hasDerivAt_id a)
