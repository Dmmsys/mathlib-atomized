/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Local extrema of differentiable functions

## Main definitions

In a real normed space `E` we define `posTangentConeAt (s : Set E) (x : E)`.
This would be the same as `tangentConeAt ℝ≥0 s x` if we had a theory of normed semifields.
This set is used in the proof of Fermat's Theorem (see below), and can be used to formalize
[Lagrange multipliers](https://en.wikipedia.org/wiki/Lagrange_multiplier) and/or
[Karush–Kuhn–Tucker conditions](https://en.wikipedia.org/wiki/Karush–Kuhn–Tucker_conditions).

## Main statements

For each theorem name listed below,
we also prove similar theorems for `min`, `extr` (if applicable),
and `fderiv`/`deriv` instead of `HasFDerivAt`/`HasDerivAt`.

* `IsLocalMaxOn.hasFDerivWithinAt_nonpos` : `f' y ≤ 0` whenever `a` is a local maximum
  of `f` on `s`, `f` has derivative `f'` at `a` within `s`, and `y` belongs to the positive tangent
  cone of `s` at `a`.

* `IsLocalMaxOn.hasFDerivWithinAt_eq_zero` : In the settings of the previous theorem, if both
  `y` and `-y` belong to the positive tangent cone, then `f' y = 0`.

* `IsLocalMax.hasFDerivAt_eq_zero` :
  [Fermat's Theorem](https://en.wikipedia.org/wiki/Fermat's_theorem_(stationary_points)),
  the derivative of a differentiable function at a local extremum point equals zero.

## Implementation notes

For each mathematical fact we prove several versions of its formalization:

* for maxima and minima;
* using `HasFDeriv*`/`HasDeriv*` or `fderiv*`/`deriv*`.

For the `fderiv*`/`deriv*` versions we omit the differentiability condition whenever it is possible
due to the fact that `fderiv` and `deriv` are defined to be zero for non-differentiable functions.

## References

* [Fermat's Theorem](https://en.wikipedia.org/wiki/Fermat's_theorem_(stationary_points));
* [Tangent cone](https://en.wikipedia.org/wiki/Tangent_cone);

## Tags

local extremum, tangent cone, Fermat's Theorem
-/

public section


universe u v

open Filter Set

open scoped Topology Convex NNReal

section Module

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
  {f : E -> Real} {f' : StrongDual Real E} {s : Set E} {a x y : E}


/--
theorem `posTangentConeAt_mono` / 定理 `posTangentConeAt_mono`

English:
theorem posTangentConeAt_mono
  statement: Monotone fun s => posTangentConeAt s a
  proof: by
  intro s t hst
  exact tangentConeAt_mono hst

中文:
定理 posTangentConeAt_mono
  结论: 递增 fun s => posTangentConeAt s a
  证明: by
  intro s t hst
  exact tangentConeAt_mono hst

Depends on / 依赖: tangentConeAt_mono
-/
theorem posTangentConeAt_mono : Monotone fun s => posTangentConeAt s a := by
  intro s t hst
  exact tangentConeAt_mono hst

/--
theorem `mem_posTangentConeAt_of_frequently_mem` / 定理 `mem_posTangentConeAt_of_frequently_mem`

English:
theorem mem_posTangentConeAt_of_frequently_mem
  given: (h : existsᶠ t : Real in 𝓝[>] 0, x + t • y in s)
  proof: by
  rw [← NNReal.coe_zero]; rw [← NNReal.map_coe_nhdsGT]; rw [frequently_map]; rw [frequently_iff_neBot] at h
  apply mem_tangentConeAt_of_add_smul_mem (l := 𝓝[>] (0 : Real>=0) ⊓ 𝓟 {t | x + (t : Real) • y in s})
· exact tendsto_id'.mpr inf_le_left.trans nhdsGT_le_nhdsNE _
  · simp [eventually_inf_p

中文:
定理 mem_posTangentConeAt_of_frequently_mem
  条件: (h : 存在ᶠ t : 实数 in 𝓝[>] 0, x + t • y in s)
  证明: by
  rw [← NNReal.coe_zero]; rw [← NNReal.map_coe_nhdsGT]; rw [frequently_map]; rw [frequently_iff_neBot] at h
  apply mem_tangentConeAt_of_add_smul_mem (l := 𝓝[>] (0 : Real>=0) ⊓ 𝓟 {t | x + (t : Real) • y in s})
· exact tendsto_id'.mpr inf_le_left.trans nhdsGT_le_nhdsNE _
  · simp [eventually_inf_p

Depends on / 依赖: NNReal, NNReal.coe_zero, NNReal.map_coe_nhdsGT, NNReal.smul_def, coe_zero, eventually_inf_principal, frequently_iff_neBot, frequently_map, inf_le_left, inf_le_left.trans, map_coe_nhdsGT, mem_tangentConeAt_of_add_smul_mem, nhdsGT_le_nhdsNE, smul_def, tendsto_id
-/
theorem mem_posTangentConeAt_of_frequently_mem (h : existsᶠ t : Real in 𝓝[>] 0, x + t • y in s) :
    y in posTangentConeAt s x := by
  rw [← NNReal.coe_zero]; rw [← NNReal.map_coe_nhdsGT]; rw [frequently_map]; rw [frequently_iff_neBot] at h
  apply mem_tangentConeAt_of_add_smul_mem (l := 𝓝[>] (0 : Real>=0) ⊓ 𝓟 {t | x + (t : Real) • y in s})
· exact tendsto_id'.mpr inf_le_left.trans nhdsGT_le_nhdsNE _
  · simp [eventually_inf_principal, NNReal.smul_def]

/--
theorem `sub_mem_posTangentConeAt_of_segment_subset` / 定理 `sub_mem_posTangentConeAt_of_segment_subset`

English:
theorem sub_mem_posTangentConeAt_of_segment_subset
  given: (h : segment Real x y subseteq s)
  proof: sub_mem_posTangentConeAt_of_openSegment_subset (openSegment_subset_segment ..).trans h

中文:
定理 sub_mem_posTangentConeAt_of_segment_subset
  条件: (h : segment 实数 x y subseteq s)
  证明: sub_mem_posTangentConeAt_of_openSegment_subset (openSegment_subset_segment ..).trans h

Depends on / 依赖: openSegment_subset_segment, sub_mem_posTangentConeAt_of_openSegment_subset
-/
theorem sub_mem_posTangentConeAt_of_segment_subset (h : segment Real x y subseteq s) :
    y - x in posTangentConeAt s x :=
sub_mem_posTangentConeAt_of_openSegment_subset (openSegment_subset_segment ..).trans h

/--
theorem `mem_posTangentConeAt_of_segment_subset` / 定理 `mem_posTangentConeAt_of_segment_subset`

English:
theorem mem_posTangentConeAt_of_segment_subset
  given: (h : [x -[Real] x + y] subseteq s)
  proof: by
  simpa using sub_mem_posTangentConeAt_of_segment_subset h

中文:
定理 mem_posTangentConeAt_of_segment_subset
  条件: (h : [x -[实数] x + y] subseteq s)
  证明: by
  simpa using sub_mem_posTangentConeAt_of_segment_subset h

Depends on / 依赖: sub_mem_posTangentConeAt_of_segment_subset
-/
theorem mem_posTangentConeAt_of_segment_subset (h : [x -[Real] x + y] subseteq s) :
    y in posTangentConeAt s x := by
  simpa using sub_mem_posTangentConeAt_of_segment_subset h

/--
theorem `posTangentConeAt_univ` / 定理 `posTangentConeAt_univ`

English:
theorem posTangentConeAt_univ
  statement: posTangentConeAt univ a = univ
  proof: tangentConeAt_univ

中文:
定理 posTangentConeAt_univ
  结论: posTangentConeAt univ a = univ
  证明: tangentConeAt_univ

Depends on / 依赖: tangentConeAt_univ
-/
theorem posTangentConeAt_univ : posTangentConeAt univ a = univ := tangentConeAt_univ

/-!
### Fermat's Theorem (vector space)
-/

/--
theorem `IsLocalMaxOn.hasFDerivWithinAt_nonpos` / 定理 `IsLocalMaxOn.hasFDerivWithinAt_nonpos`

English:
theorem IsLocalMaxOn.hasFDerivWithinAt_nonpos
  statement: (h : IsLocalMaxOn f s a)
  proof: by
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hd, hcd⟩
  suffices forallᶠ n in l, c n • (f (a + d n) - f a) <= 0 from
    le_of_tendsto (hf.lim hd₀ hd hcd) this
  replace hd : Tendsto (fun n => a + d n) l (𝓝[s] (a + 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.

中文:
定理 IsLocalMaxOn.hasFDerivWithinAt_nonpos
  结论: (h : IsLocalMaxOn f s a)
  证明: by
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hd, hcd⟩
  suffices forallᶠ n in l, c n • (f (a + d n) - f a) <= 0 from
    le_of_tendsto (hf.lim hd₀ hd hcd) this
  replace hd : Tendsto (fun n => a + d n) l (𝓝[s] (a + 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.

Depends on / 依赖: Tendsto, add_zero, coe_nonneg, eventually, exists_fun_of_mem_tangentConeAt, hd.eventually, hf.lim, le_of_tendsto, mul_nonpos_of_nonneg_of_nonpos, replace, sub_nonpos, tendsto_const_nhds, tendsto_const_nhds.add, tendsto_nhdsWithin_iff
-/
theorem IsLocalMaxOn.hasFDerivWithinAt_nonpos (h : IsLocalMaxOn f s a)
    (hf : HasFDerivWithinAt f f' s a) (hy : y in posTangentConeAt s a) : f' y <= 0 := by
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hd, hcd⟩
  suffices forallᶠ n in l, c n • (f (a + d n) - f a) <= 0 from
    le_of_tendsto (hf.lim hd₀ hd hcd) this
  replace hd : Tendsto (fun n => a + d n) l (𝓝[s] (a + 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.add hd₀, hd⟩
  rw [add_zero] at hd
.mono fun n hn => ?_ refine hd.eventually h
  exact mul_nonpos_of_nonneg_of_nonpos (c n).coe_nonneg (sub_nonpos.2 hn)

/--
theorem `IsLocalMaxOn.fderivWithin_nonpos` / 定理 `IsLocalMaxOn.fderivWithin_nonpos`

English:
theorem IsLocalMaxOn.fderivWithin_nonpos
  statement: (h : IsLocalMaxOn f s a)
  proof: by
  classical
  exact
    if hf : DifferentiableWithinAt Real f s a then h.hasFDerivWithinAt_nonpos hf.hasFDerivWithinAt hy
    else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

中文:
定理 IsLocalMaxOn.fderivWithin_nonpos
  结论: (h : IsLocalMaxOn f s a)
  证明: by
  classical
  exact
    if hf : DifferentiableWithinAt Real f s a then h.hasFDerivWithinAt_nonpos hf.hasFDerivWithinAt hy
    else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

Depends on / 依赖: DifferentiableWithinAt, classical, fderivWithin_zero_of_not_differentiableWithinAt, h.hasFDerivWithinAt_nonpos, hasFDerivWithinAt, hasFDerivWithinAt_nonpos, hf.hasFDerivWithinAt
-/
theorem IsLocalMaxOn.fderivWithin_nonpos (h : IsLocalMaxOn f s a)
    (hy : y in posTangentConeAt s a) : (fderivWithin Real f s a : E -> Real) y <= 0 := by
  classical
  exact
    if hf : DifferentiableWithinAt Real f s a then h.hasFDerivWithinAt_nonpos hf.hasFDerivWithinAt hy
    else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

/--
theorem `IsLocalMaxOn.hasFDerivWithinAt_eq_zero` / 定理 `IsLocalMaxOn.hasFDerivWithinAt_eq_zero`

English:
theorem IsLocalMaxOn.hasFDerivWithinAt_eq_zero
  statement: (h : IsLocalMaxOn f s a)
  proof: le_antisymm (h.hasFDerivWithinAt_nonpos hf hy) by simpa using h.hasFDerivWithinAt_nonpos hf hy'

中文:
定理 IsLocalMaxOn.hasFDerivWithinAt_eq_zero
  结论: (h : IsLocalMaxOn f s a)
  证明: le_antisymm (h.hasFDerivWithinAt_nonpos hf hy) by simpa using h.hasFDerivWithinAt_nonpos hf hy'

Depends on / 依赖: h.hasFDerivWithinAt_nonpos, hasFDerivWithinAt_nonpos, le_antisymm
-/
theorem IsLocalMaxOn.hasFDerivWithinAt_eq_zero (h : IsLocalMaxOn f s a)
    (hf : HasFDerivWithinAt f f' s a) (hy : y in posTangentConeAt s a)
    (hy' : -y in posTangentConeAt s a) : f' y = 0 :=
le_antisymm (h.hasFDerivWithinAt_nonpos hf hy) by simpa using h.hasFDerivWithinAt_nonpos hf hy'

/--
theorem `IsLocalMaxOn.fderivWithin_eq_zero` / 定理 `IsLocalMaxOn.fderivWithin_eq_zero`

English:
theorem IsLocalMaxOn.fderivWithin_eq_zero
  statement: (h : IsLocalMaxOn f s a)
  proof: by
  classical
  exact if hf : DifferentiableWithinAt Real f s a then
    h.hasFDerivWithinAt_eq_zero hf.hasFDerivWithinAt hy hy'
  else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

中文:
定理 IsLocalMaxOn.fderivWithin_eq_zero
  结论: (h : IsLocalMaxOn f s a)
  证明: by
  classical
  exact if hf : DifferentiableWithinAt Real f s a then
    h.hasFDerivWithinAt_eq_zero hf.hasFDerivWithinAt hy hy'
  else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

Depends on / 依赖: DifferentiableWithinAt, classical, fderivWithin_zero_of_not_differentiableWithinAt, h.hasFDerivWithinAt_eq_zero, hasFDerivWithinAt, hasFDerivWithinAt_eq_zero, hf.hasFDerivWithinAt
-/
theorem IsLocalMaxOn.fderivWithin_eq_zero (h : IsLocalMaxOn f s a)
    (hy : y in posTangentConeAt s a) (hy' : -y in posTangentConeAt s a) :
    (fderivWithin Real f s a : E -> Real) y = 0 := by
  classical
  exact if hf : DifferentiableWithinAt Real f s a then
    h.hasFDerivWithinAt_eq_zero hf.hasFDerivWithinAt hy hy'
  else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

/--
theorem `IsLocalMinOn.hasFDerivWithinAt_nonneg` / 定理 `IsLocalMinOn.hasFDerivWithinAt_nonneg`

English:
theorem IsLocalMinOn.hasFDerivWithinAt_nonneg
  statement: (h : IsLocalMinOn f s a)
  proof: by
  simpa using h.neg.hasFDerivWithinAt_nonpos hf.neg hy

中文:
定理 IsLocalMinOn.hasFDerivWithinAt_nonneg
  结论: (h : IsLocalMinOn f s a)
  证明: by
  simpa using h.neg.hasFDerivWithinAt_nonpos hf.neg hy

Depends on / 依赖: h.neg.hasFDerivWithinAt_nonpos, hasFDerivWithinAt_nonpos, hf.neg
-/
theorem IsLocalMinOn.hasFDerivWithinAt_nonneg (h : IsLocalMinOn f s a)
    (hf : HasFDerivWithinAt f f' s a) (hy : y in posTangentConeAt s a) : 0 <= f' y := by
  simpa using h.neg.hasFDerivWithinAt_nonpos hf.neg hy

/--
theorem `IsLocalMinOn.fderivWithin_nonneg` / 定理 `IsLocalMinOn.fderivWithin_nonneg`

English:
theorem IsLocalMinOn.fderivWithin_nonneg
  statement: (h : IsLocalMinOn f s a)
  proof: by
  classical
  exact
    if hf : DifferentiableWithinAt Real f s a then h.hasFDerivWithinAt_nonneg hf.hasFDerivWithinAt hy
    else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

中文:
定理 IsLocalMinOn.fderivWithin_nonneg
  结论: (h : IsLocalMinOn f s a)
  证明: by
  classical
  exact
    if hf : DifferentiableWithinAt Real f s a then h.hasFDerivWithinAt_nonneg hf.hasFDerivWithinAt hy
    else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

Depends on / 依赖: DifferentiableWithinAt, classical, fderivWithin_zero_of_not_differentiableWithinAt, h.hasFDerivWithinAt_nonneg, hasFDerivWithinAt, hasFDerivWithinAt_nonneg, hf.hasFDerivWithinAt
-/
theorem IsLocalMinOn.fderivWithin_nonneg (h : IsLocalMinOn f s a)
    (hy : y in posTangentConeAt s a) : (0 : Real) <= (fderivWithin Real f s a : E -> Real) y := by
  classical
  exact
    if hf : DifferentiableWithinAt Real f s a then h.hasFDerivWithinAt_nonneg hf.hasFDerivWithinAt hy
    else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

/--
theorem `IsLocalMinOn.hasFDerivWithinAt_eq_zero` / 定理 `IsLocalMinOn.hasFDerivWithinAt_eq_zero`

English:
theorem IsLocalMinOn.hasFDerivWithinAt_eq_zero
  statement: (h : IsLocalMinOn f s a)
  proof: by
  simpa using h.neg.hasFDerivWithinAt_eq_zero hf.neg hy hy'

中文:
定理 IsLocalMinOn.hasFDerivWithinAt_eq_zero
  结论: (h : IsLocalMinOn f s a)
  证明: by
  simpa using h.neg.hasFDerivWithinAt_eq_zero hf.neg hy hy'

Depends on / 依赖: h.neg.hasFDerivWithinAt_eq_zero, hasFDerivWithinAt_eq_zero, hf.neg
-/
theorem IsLocalMinOn.hasFDerivWithinAt_eq_zero (h : IsLocalMinOn f s a)
    (hf : HasFDerivWithinAt f f' s a) (hy : y in posTangentConeAt s a)
    (hy' : -y in posTangentConeAt s a) : f' y = 0 := by
  simpa using h.neg.hasFDerivWithinAt_eq_zero hf.neg hy hy'

/--
theorem `IsLocalMinOn.fderivWithin_eq_zero` / 定理 `IsLocalMinOn.fderivWithin_eq_zero`

English:
theorem IsLocalMinOn.fderivWithin_eq_zero
  statement: (h : IsLocalMinOn f s a)
  proof: by
  classical
  exact if hf : DifferentiableWithinAt Real f s a then
    h.hasFDerivWithinAt_eq_zero hf.hasFDerivWithinAt hy hy'
  else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

中文:
定理 IsLocalMinOn.fderivWithin_eq_zero
  结论: (h : IsLocalMinOn f s a)
  证明: by
  classical
  exact if hf : DifferentiableWithinAt Real f s a then
    h.hasFDerivWithinAt_eq_zero hf.hasFDerivWithinAt hy hy'
  else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

Depends on / 依赖: DifferentiableWithinAt, classical, fderivWithin_zero_of_not_differentiableWithinAt, h.hasFDerivWithinAt_eq_zero, hasFDerivWithinAt, hasFDerivWithinAt_eq_zero, hf.hasFDerivWithinAt
-/
theorem IsLocalMinOn.fderivWithin_eq_zero (h : IsLocalMinOn f s a)
    (hy : y in posTangentConeAt s a) (hy' : -y in posTangentConeAt s a) :
    (fderivWithin Real f s a : E -> Real) y = 0 := by
  classical
  exact if hf : DifferentiableWithinAt Real f s a then
    h.hasFDerivWithinAt_eq_zero hf.hasFDerivWithinAt hy hy'
  else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

/--
theorem `IsLocalMin.hasFDerivAt_eq_zero` / 定理 `IsLocalMin.hasFDerivAt_eq_zero`

English:
theorem IsLocalMin.hasFDerivAt_eq_zero
  given: (h : IsLocalMin f a) (hf : HasFDerivAt f f' a)
  statement: f' = 0
  proof: by
  ext y
  apply (h.on univ).hasFDerivWithinAt_eq_zero hf.hasFDerivWithinAt <;>
      rw [posTangentConeAt_univ] <;>
    apply mem_univ

中文:
定理 IsLocalMin.hasFDerivAt_eq_zero
  条件: (h : IsLocalMin f a) (hf : 在点处Fréchet可导 f f' a)
  结论: f' = 0
  证明: by
  ext y
  apply (h.on univ).hasFDerivWithinAt_eq_zero hf.hasFDerivWithinAt <;>
      rw [posTangentConeAt_univ] <;>
    apply mem_univ

Depends on / 依赖: CStarAlgebra, CStarAlgebra.toNonUnitalCStarAlgebra, h.on, hasFDerivWithinAt, hasFDerivWithinAt_eq_zero, hf.hasFDerivWithinAt, mem_univ, posTangentConeAt_univ, toNonUnitalCStarAlgebra
-/
theorem IsLocalMin.hasFDerivAt_eq_zero (h : IsLocalMin f a) (hf : HasFDerivAt f f' a) : f' = 0 := by
  ext y
  apply (h.on univ).hasFDerivWithinAt_eq_zero hf.hasFDerivWithinAt <;>
      rw [posTangentConeAt_univ] <;>
    apply mem_univ

/--
theorem `IsLocalMin.fderiv_eq_zero` / 定理 `IsLocalMin.fderiv_eq_zero`

English:
theorem IsLocalMin.fderiv_eq_zero
  given: (h : IsLocalMin f a)
  statement: fderiv Real f a = 0
  proof: by
  classical
  exact if hf : DifferentiableAt Real f a then h.hasFDerivAt_eq_zero hf.hasFDerivAt
  else fderiv_zero_of_not_differentiableAt hf

中文:
定理 IsLocalMin.fderiv_eq_zero
  条件: (h : IsLocalMin f a)
  结论: fderiv 实数 f a = 0
  证明: by
  classical
  exact if hf : DifferentiableAt Real f a then h.hasFDerivAt_eq_zero hf.hasFDerivAt
  else fderiv_zero_of_not_differentiableAt hf

Depends on / 依赖: CommCStarAlgebra, CommCStarAlgebra.toNonUnitalCommCStarAlgebra, DifferentiableAt, classical, fderiv_zero_of_not_differentiableAt, h.hasFDerivAt_eq_zero, hasFDerivAt, hasFDerivAt_eq_zero, hf.hasFDerivAt, toNonUnitalCommCStarAlgebra
-/
theorem IsLocalMin.fderiv_eq_zero (h : IsLocalMin f a) : fderiv Real f a = 0 := by
  classical
  exact if hf : DifferentiableAt Real f a then h.hasFDerivAt_eq_zero hf.hasFDerivAt
  else fderiv_zero_of_not_differentiableAt hf

/--
theorem `IsLocalMax.hasFDerivAt_eq_zero` / 定理 `IsLocalMax.hasFDerivAt_eq_zero`

English:
theorem IsLocalMax.hasFDerivAt_eq_zero
  given: (h : IsLocalMax f a) (hf : HasFDerivAt f f' a)
  statement: f' = 0
  proof: neg_eq_zero.1 h.neg.hasFDerivAt_eq_zero hf.neg

中文:
定理 IsLocalMax.hasFDerivAt_eq_zero
  条件: (h : IsLocalMax f a) (hf : 在点处Fréchet可导 f f' a)
  结论: f' = 0
  证明: neg_eq_zero.1 h.neg.hasFDerivAt_eq_zero hf.neg

Depends on / 依赖: h.neg.hasFDerivAt_eq_zero, hasFDerivAt_eq_zero, hf.neg, neg_eq_zero
-/
theorem IsLocalMax.hasFDerivAt_eq_zero (h : IsLocalMax f a) (hf : HasFDerivAt f f' a) : f' = 0 :=
neg_eq_zero.1 h.neg.hasFDerivAt_eq_zero hf.neg

/--
theorem `IsLocalMax.fderiv_eq_zero` / 定理 `IsLocalMax.fderiv_eq_zero`

English:
theorem IsLocalMax.fderiv_eq_zero
  given: (h : IsLocalMax f a)
  statement: fderiv Real f a = 0
  proof: by
  classical
  exact if hf : DifferentiableAt Real f a then h.hasFDerivAt_eq_zero hf.hasFDerivAt
  else fderiv_zero_of_not_differentiableAt hf

中文:
定理 IsLocalMax.fderiv_eq_zero
  条件: (h : IsLocalMax f a)
  结论: fderiv 实数 f a = 0
  证明: by
  classical
  exact if hf : DifferentiableAt Real f a then h.hasFDerivAt_eq_zero hf.hasFDerivAt
  else fderiv_zero_of_not_differentiableAt hf

Depends on / 依赖: DifferentiableAt, classical, fderiv_zero_of_not_differentiableAt, h.hasFDerivAt_eq_zero, hasFDerivAt, hasFDerivAt_eq_zero, hf.hasFDerivAt
-/
theorem IsLocalMax.fderiv_eq_zero (h : IsLocalMax f a) : fderiv Real f a = 0 := by
  classical
  exact if hf : DifferentiableAt Real f a then h.hasFDerivAt_eq_zero hf.hasFDerivAt
  else fderiv_zero_of_not_differentiableAt hf

/--
theorem `IsLocalExtr.hasFDerivAt_eq_zero` / 定理 `IsLocalExtr.hasFDerivAt_eq_zero`

English:
theorem IsLocalExtr.hasFDerivAt_eq_zero
  given: (h : IsLocalExtr f a)
  statement: HasFDerivAt f f' a -> f' = 0
  proof: h.elim IsLocalMin.hasFDerivAt_eq_zero IsLocalMax.hasFDerivAt_eq_zero

中文:
定理 IsLocalExtr.hasFDerivAt_eq_zero
  条件: (h : IsLocalExtr f a)
  结论: 在点处Fréchet可导 f f' a -> f' = 0
  证明: h.elim IsLocalMin.hasFDerivAt_eq_zero IsLocalMax.hasFDerivAt_eq_zero

Depends on / 依赖: IsLocalMax, IsLocalMax.hasFDerivAt_eq_zero, IsLocalMin, IsLocalMin.hasFDerivAt_eq_zero, h.elim, hasFDerivAt_eq_zero
-/
theorem IsLocalExtr.hasFDerivAt_eq_zero (h : IsLocalExtr f a) : HasFDerivAt f f' a -> f' = 0 :=
  h.elim IsLocalMin.hasFDerivAt_eq_zero IsLocalMax.hasFDerivAt_eq_zero

/--
theorem `IsLocalExtr.fderiv_eq_zero` / 定理 `IsLocalExtr.fderiv_eq_zero`

English:
theorem IsLocalExtr.fderiv_eq_zero
  given: (h : IsLocalExtr f a)
  statement: fderiv Real f a = 0
  proof: h.elim IsLocalMin.fderiv_eq_zero IsLocalMax.fderiv_eq_zero

中文:
定理 IsLocalExtr.fderiv_eq_zero
  条件: (h : IsLocalExtr f a)
  结论: fderiv 实数 f a = 0
  证明: h.elim IsLocalMin.fderiv_eq_zero IsLocalMax.fderiv_eq_zero

Depends on / 依赖: IsLocalMax, IsLocalMax.fderiv_eq_zero, IsLocalMin, IsLocalMin.fderiv_eq_zero, fderiv_eq_zero, h.elim
-/
theorem IsLocalExtr.fderiv_eq_zero (h : IsLocalExtr f a) : fderiv Real f a = 0 :=
  h.elim IsLocalMin.fderiv_eq_zero IsLocalMax.fderiv_eq_zero

end Module

/-!
### Fermat's Theorem
-/

section Real

variable {f : Real -> Real} {f' : Real} {s : Set Real} {a b : Real}

/--
lemma `one_mem_posTangentConeAt_iff_mem_closure` / 引理 `one_mem_posTangentConeAt_iff_mem_closure`

English:
lemma one_mem_posTangentConeAt_iff_mem_closure
  proof: by
  constructor
  · intro h
    rcases exists_fun_of_mem_tangentConeAt h with ⟨ι, l, hl, c, d, hd₀, hd, hcd⟩
    have : Tendsto (a + d ·) l (𝓝 a) := by
      simpa only [add_zero] using tendsto_const_nhds.add hd₀
    apply mem_closure_of_tendsto this
    filter_upwards [hcd.eventually_const_lt one_

中文:
引理 one_mem_posTangentConeAt_iff_mem_closure
  证明: by
  constructor
  · intro h
    rcases exists_fun_of_mem_tangentConeAt h with ⟨ι, l, hl, c, d, hd₀, hd, hcd⟩
    have : Tendsto (a + d ·) l (𝓝 a) := by
      simpa only [add_zero] using tendsto_const_nhds.add hd₀
    apply mem_closure_of_tendsto this
    filter_upwards [hcd.eventually_const_lt one_

Depends on / 依赖: Tendsto, add_zero, eventually_const_lt, exists_fun_of_mem_tangentConeAt, filter_upwards, frequently_map, hcd.eventually_const_lt, map_add_left_nhds_zero, mem_closure_iff_frequently, mem_closure_of_tendsto, mem_posTangentConeAt_of_frequently_mem, one_pos, pos_of_mul_pos_right, tendsto_const_nhds, tendsto_const_nhds.add
-/
lemma one_mem_posTangentConeAt_iff_mem_closure :
    1 in posTangentConeAt s a ↔ a in closure (Ioi a inter s) := by
  constructor
  · intro h
    rcases exists_fun_of_mem_tangentConeAt h with ⟨ι, l, hl, c, d, hd₀, hd, hcd⟩
    have : Tendsto (a + d ·) l (𝓝 a) := by
      simpa only [add_zero] using tendsto_const_nhds.add hd₀
    apply mem_closure_of_tendsto this
    filter_upwards [hcd.eventually_const_lt one_pos, hd] with n hcdn hdn
    refine ⟨?_, hdn⟩
    simpa using pos_of_mul_pos_right hcdn
  · intro h
    apply mem_posTangentConeAt_of_frequently_mem
    rw [mem_closure_iff_frequently]; rw [← map_add_left_nhds_zero]; rw [frequently_map] at h
    simpa [nhdsWithin, frequently_inf_principal] using h

/--
lemma `one_mem_posTangentConeAt_iff_frequently` / 引理 `one_mem_posTangentConeAt_iff_frequently`

English:
lemma one_mem_posTangentConeAt_iff_frequently
  proof: by
  rw [one_mem_posTangentConeAt_iff_mem_closure]; rw [mem_closure_iff_frequently]; rw [frequently_nhdsWithin_iff]; rw [inter_comm]
  simp_rw [mem_inter_iff]

中文:
引理 one_mem_posTangentConeAt_iff_frequently
  证明: by
  rw [one_mem_posTangentConeAt_iff_mem_closure]; rw [mem_closure_iff_frequently]; rw [frequently_nhdsWithin_iff]; rw [inter_comm]
  simp_rw [mem_inter_iff]

Depends on / 依赖: frequently_nhdsWithin_iff, inter_comm, mem_closure_iff_frequently, mem_inter_iff, one_mem_posTangentConeAt_iff_mem_closure, simp_rw
-/
lemma one_mem_posTangentConeAt_iff_frequently :
    1 in posTangentConeAt s a ↔ existsᶠ x in 𝓝[>] a, x in s := by
  rw [one_mem_posTangentConeAt_iff_mem_closure]; rw [mem_closure_iff_frequently]; rw [frequently_nhdsWithin_iff]; rw [inter_comm]
  simp_rw [mem_inter_iff]

/--
theorem `IsLocalMin.hasDerivAt_eq_zero` / 定理 `IsLocalMin.hasDerivAt_eq_zero`

English:
theorem IsLocalMin.hasDerivAt_eq_zero
  given: (h : IsLocalMin f a) (hf : HasDerivAt f f' a)
  statement: f' = 0
  proof: by
  simpa using DFunLike.congr_fun (h.hasFDerivAt_eq_zero (hasDerivAt_iff_hasFDerivAt.1 hf)) 1

中文:
定理 IsLocalMin.hasDerivAt_eq_zero
  条件: (h : IsLocalMin f a) (hf : 在点处可导 f f' a)
  结论: f' = 0
  证明: by
  simpa using DFunLike.congr_fun (h.hasFDerivAt_eq_zero (hasDerivAt_iff_hasFDerivAt.1 hf)) 1

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, h.hasFDerivAt_eq_zero, hasDerivAt_iff_hasFDerivAt, hasFDerivAt_eq_zero
-/
theorem IsLocalMin.hasDerivAt_eq_zero (h : IsLocalMin f a) (hf : HasDerivAt f f' a) : f' = 0 := by
  simpa using DFunLike.congr_fun (h.hasFDerivAt_eq_zero (hasDerivAt_iff_hasFDerivAt.1 hf)) 1

/--
theorem `IsLocalMin.deriv_eq_zero` / 定理 `IsLocalMin.deriv_eq_zero`

English:
theorem IsLocalMin.deriv_eq_zero
  given: (h : IsLocalMin f a)
  statement: deriv f a = 0
  proof: by
  classical
  exact if hf : DifferentiableAt Real f a then h.hasDerivAt_eq_zero hf.hasDerivAt
  else deriv_zero_of_not_differentiableAt hf

中文:
定理 IsLocalMin.deriv_eq_zero
  条件: (h : IsLocalMin f a)
  结论: deriv f a = 0
  证明: by
  classical
  exact if hf : DifferentiableAt Real f a then h.hasDerivAt_eq_zero hf.hasDerivAt
  else deriv_zero_of_not_differentiableAt hf

Depends on / 依赖: DifferentiableAt, classical, deriv_zero_of_not_differentiableAt, h.hasDerivAt_eq_zero, hasDerivAt, hasDerivAt_eq_zero, hf.hasDerivAt
-/
theorem IsLocalMin.deriv_eq_zero (h : IsLocalMin f a) : deriv f a = 0 := by
  classical
  exact if hf : DifferentiableAt Real f a then h.hasDerivAt_eq_zero hf.hasDerivAt
  else deriv_zero_of_not_differentiableAt hf

/--
theorem `IsLocalMax.hasDerivAt_eq_zero` / 定理 `IsLocalMax.hasDerivAt_eq_zero`

English:
theorem IsLocalMax.hasDerivAt_eq_zero
  given: (h : IsLocalMax f a) (hf : HasDerivAt f f' a)
  statement: f' = 0
  proof: neg_eq_zero.1 h.neg.hasDerivAt_eq_zero hf.neg

中文:
定理 IsLocalMax.hasDerivAt_eq_zero
  条件: (h : IsLocalMax f a) (hf : 在点处可导 f f' a)
  结论: f' = 0
  证明: neg_eq_zero.1 h.neg.hasDerivAt_eq_zero hf.neg

Depends on / 依赖: h.neg.hasDerivAt_eq_zero, hasDerivAt_eq_zero, hf.neg, neg_eq_zero
-/
theorem IsLocalMax.hasDerivAt_eq_zero (h : IsLocalMax f a) (hf : HasDerivAt f f' a) : f' = 0 :=
neg_eq_zero.1 h.neg.hasDerivAt_eq_zero hf.neg

/--
theorem `IsLocalMax.deriv_eq_zero` / 定理 `IsLocalMax.deriv_eq_zero`

English:
theorem IsLocalMax.deriv_eq_zero
  given: (h : IsLocalMax f a)
  statement: deriv f a = 0
  proof: by
  classical
  exact if hf : DifferentiableAt Real f a then h.hasDerivAt_eq_zero hf.hasDerivAt
  else deriv_zero_of_not_differentiableAt hf

中文:
定理 IsLocalMax.deriv_eq_zero
  条件: (h : IsLocalMax f a)
  结论: deriv f a = 0
  证明: by
  classical
  exact if hf : DifferentiableAt Real f a then h.hasDerivAt_eq_zero hf.hasDerivAt
  else deriv_zero_of_not_differentiableAt hf

Depends on / 依赖: DifferentiableAt, classical, deriv_zero_of_not_differentiableAt, h.hasDerivAt_eq_zero, hasDerivAt, hasDerivAt_eq_zero, hf.hasDerivAt
-/
theorem IsLocalMax.deriv_eq_zero (h : IsLocalMax f a) : deriv f a = 0 := by
  classical
  exact if hf : DifferentiableAt Real f a then h.hasDerivAt_eq_zero hf.hasDerivAt
  else deriv_zero_of_not_differentiableAt hf

/--
theorem `IsLocalExtr.hasDerivAt_eq_zero` / 定理 `IsLocalExtr.hasDerivAt_eq_zero`

English:
theorem IsLocalExtr.hasDerivAt_eq_zero
  given: (h : IsLocalExtr f a)
  statement: HasDerivAt f f' a -> f' = 0
  proof: h.elim IsLocalMin.hasDerivAt_eq_zero IsLocalMax.hasDerivAt_eq_zero

中文:
定理 IsLocalExtr.hasDerivAt_eq_zero
  条件: (h : IsLocalExtr f a)
  结论: 在点处可导 f f' a -> f' = 0
  证明: h.elim IsLocalMin.hasDerivAt_eq_zero IsLocalMax.hasDerivAt_eq_zero

Depends on / 依赖: IsLocalMax, IsLocalMax.hasDerivAt_eq_zero, IsLocalMin, IsLocalMin.hasDerivAt_eq_zero, h.elim, hasDerivAt_eq_zero
-/
theorem IsLocalExtr.hasDerivAt_eq_zero (h : IsLocalExtr f a) : HasDerivAt f f' a -> f' = 0 :=
  h.elim IsLocalMin.hasDerivAt_eq_zero IsLocalMax.hasDerivAt_eq_zero

/--
theorem `IsLocalExtr.deriv_eq_zero` / 定理 `IsLocalExtr.deriv_eq_zero`

English:
theorem IsLocalExtr.deriv_eq_zero
  given: (h : IsLocalExtr f a)
  statement: deriv f a = 0
  proof: h.elim IsLocalMin.deriv_eq_zero IsLocalMax.deriv_eq_zero

中文:
定理 IsLocalExtr.deriv_eq_zero
  条件: (h : IsLocalExtr f a)
  结论: deriv f a = 0
  证明: h.elim IsLocalMin.deriv_eq_zero IsLocalMax.deriv_eq_zero

Depends on / 依赖: IsLocalMax, IsLocalMax.deriv_eq_zero, IsLocalMin, IsLocalMin.deriv_eq_zero, deriv_eq_zero, h.elim
-/
theorem IsLocalExtr.deriv_eq_zero (h : IsLocalExtr f a) : deriv f a = 0 :=
  h.elim IsLocalMin.deriv_eq_zero IsLocalMax.deriv_eq_zero

end Real
