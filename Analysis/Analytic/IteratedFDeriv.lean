/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Data.Fintype.Perm

/-!
# The iterated derivative of an analytic function

If a function is analytic, written as `f (x + y) = ∑ pₙ (y, ..., y)` then its `n`-th iterated
derivative at `x` is given by `(v₁, ..., vₙ) ↦ ∑ pₙ (v_{σ (1)}, ..., v_{σ (n)})` where the sum
is over all permutations of `{1, ..., n}`. In particular, it is symmetric.

This generalizes the result of `HasFPowerSeriesOnBall.factorial_smul` giving
`D^n f (v, ..., v) = n! * pₙ (v, ..., v)`.

## Main result

* `HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum` shows that
  `iteratedFDeriv 𝕜 n f x v = ∑ σ : Perm (Fin n), p n (fun i ↦ v (σ i))`,
  when `f` has `p` as power series within the set `s` on the ball `B (x, r)`.
* `ContDiffAt.iteratedFDeriv_comp_perm` proves the symmetry of the iterated derivative of an
  analytic function, in the form `iteratedFDeriv 𝕜 n f x (v ∘ σ) = iteratedFDeriv 𝕜 n f x v`
  for any permutation `σ` of `Fin n`.

Versions within sets are also given.

## Implementation

To prove the formula for the iterated derivative, we decompose an analytic function as
the sum of `fun y ↦ pₙ (y, ..., y)` and the rest. For the former, its iterated derivative follows
from the formula for iterated derivatives of multilinear maps
(see `ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal`). For the latter, we show by
induction on `n` that if the `n`-th term in a power series is zero, then the `n`-th iterated
derivative vanishes (see `HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_zero`).

All these results are proved assuming additionally that the function is analytic on the relevant
set (which does not follow from the fact that the function has a power series, if the target space
is not complete). This makes it possible to avoid all completeness assumptions in the final
statements. When needed, we give versions of some statements assuming completeness and dropping
analyticity, for ease of use.
-/

@[expose] public section

open scoped ENNReal Topology ContDiff
open Equiv Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : E -> F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} {r : Real>=0∞}

/--
Definition of `FormalMultilinearSeries.iteratedFDerivSeries` / `FormalMultilinearSeries.iteratedFDerivSeries` 的定义

English:
definition FormalMultilinearSeries.iteratedFDerivSeries
  body: match k with
  | 0 => (continuousMultilinearCurryFin0 𝕜 E F).symm
.toContinuousLinearEquiv.toContinuousLinearMap.compFormalMultilinearSeries p
  | (k + 1) => (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) => E) F).symm
.toContinuousLinearEquiv.toContinuousLinearMap.compFormalMultilinear

中文:
定义 FormalMultilinearSeries.iteratedFDerivSeries
  定义体: match k with
  | 0 => (continuousMultilinearCurryFin0 𝕜 E F).symm
.toContinuousLinearEquiv.toContinuousLinearMap.compFormalMultilinearSeries p
  | (k + 1) => (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) => E) F).symm
.toContinuousLinearEquiv.toContinuousLinearMap.compFormalMultilinear

Depends on / 依赖: compFormalMultilinearSeries, continuousMultilinearCurryFin0, continuousMultilinearCurryLeftEquiv, derivSeries, iteratedFDerivSeries, p.iteratedFDerivSeries, toContinuousLinearEquiv, toContinuousLinearEquiv.toContinuousLinearMap.compFormalMultilinearSeries, toContinuousLinearMap
-/
noncomputable def FormalMultilinearSeries.iteratedFDerivSeries
    (p : FormalMultilinearSeries 𝕜 E F) (k : Nat) :
    FormalMultilinearSeries 𝕜 E (E [×k]->L[𝕜] F) :=
  match k with
  | 0 => (continuousMultilinearCurryFin0 𝕜 E F).symm
.toContinuousLinearEquiv.toContinuousLinearMap.compFormalMultilinearSeries p
  | (k + 1) => (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) => E) F).symm
.toContinuousLinearEquiv.toContinuousLinearMap.compFormalMultilinearSeries
      (p.iteratedFDerivSeries k).derivSeries

/--
theorem `HasFPowerSeriesWithinOnBall.iteratedFDerivWithin` / 定理 `HasFPowerSeriesWithinOnBall.iteratedFDerivWithin`

English:
theorem HasFPowerSeriesWithinOnBall.iteratedFDerivWithin
  proof: by
  induction k with
  | zero =>
    exact (continuousMultilinearCurryFin0 𝕜 E F).symm
.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall h
  | succ k ih =>
    rw [iteratedFDerivWithin_succ_eq_comp_left]
    apply (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k 

中文:
定理 HasFPowerSeriesWithinOnBall.iteratedFDerivWithin
  证明: by
  induction k with
  | zero =>
    exact (continuousMultilinearCurryFin0 𝕜 E F).symm
.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall h
  | succ k ih =>
    rw [iteratedFDerivWithin_succ_eq_comp_left]
    apply (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k 
-/
protected theorem HasFPowerSeriesWithinOnBall.iteratedFDerivWithin
    (h : HasFPowerSeriesWithinOnBall f p s x r) (h' : AnalyticOn 𝕜 f s)
    (k : Nat) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) :
    HasFPowerSeriesWithinOnBall (iteratedFDerivWithin 𝕜 k f s)
      (p.iteratedFDerivSeries k) s x r := by
  induction k with
  | zero =>
    exact (continuousMultilinearCurryFin0 𝕜 E F).symm
.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall h
  | succ k ih =>
    rw [iteratedFDerivWithin_succ_eq_comp_left]
    apply (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) => E) F).symm
.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall
        (ih.fderivWithin_of_mem_of_analyticOn (h'.iteratedFDerivWithin hs _) hs hx)

/--
lemma `FormalMultilinearSeries.iteratedFDerivSeries_eq_zero` / 引理 `FormalMultilinearSeries.iteratedFDerivSeries_eq_zero`

English:
lemma FormalMultilinearSeries.iteratedFDerivSeries_eq_zero
  statement: {k n : Nat}
  proof: by
  induction k generalizing n with
  | zero =>
    ext
    have : p n = 0 := p.congr_zero rfl h
    simp [FormalMultilinearSeries.iteratedFDerivSeries, this]
  | succ k ih =>
    ext
    simp only [iteratedFDerivSeries, Nat.succ_eq_add_one,
      ContinuousLinearMap.compFormalMultilinearSeries_app

中文:
引理 FormalMultilinearSeries.iteratedFDerivSeries_eq_zero
  结论: {k n : 自然数}
  证明: by
  induction k generalizing n with
  | zero =>
    ext
    have : p n = 0 := p.congr_zero rfl h
    simp [FormalMultilinearSeries.iteratedFDerivSeries, this]
  | succ k ih =>
    ext
    simp only [iteratedFDerivSeries, Nat.succ_eq_add_one,
      ContinuousLinearMap.compFormalMultilinearSeries_app

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe, ContinuousLinearMap, ContinuousLinearMap.compContinuousMultilinearMap_coe, ContinuousLinearMap.compFormalMultilinearSeries_apply, FormalMultilinearSeries, FormalMultilinearSeries.iteratedFDerivSeries, Function, Function.comp_apply, LinearIsometryEquiv, LinearIsometryEquiv.coe_toContinuousLinearEquiv, Nat.succ_eq_add_one, _root_, _root_.zero_apply, coe_coe, coe_toContinuousLinearEquiv, compContinuousMultilinearMap_coe, compFormalMultilinearSeries_apply, comp_apply, congr_zero
-/
lemma FormalMultilinearSeries.iteratedFDerivSeries_eq_zero {k n : Nat}
    (h : p (n + k) = 0) : p.iteratedFDerivSeries k n = 0 := by
  induction k generalizing n with
  | zero =>
    ext
    have : p n = 0 := p.congr_zero rfl h
    simp [FormalMultilinearSeries.iteratedFDerivSeries, this]
  | succ k ih =>
    ext
    simp only [iteratedFDerivSeries, Nat.succ_eq_add_one,
      ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, Function.comp_apply,
      continuousMultilinearCurryLeftEquiv_symm_apply, _root_.zero_apply,
      derivSeries_eq_zero _ (ih (p.congr_zero (Nat.succ_add_eq_add_succ _ _).symm h))]

/--
lemma `HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_zero` / 引理 `HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_zero`

English:
lemma HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_zero
  proof: by
  have : iteratedFDerivWithin 𝕜 n f s x = p.iteratedFDerivSeries n 0 (fun _ => 0) :=
    ((h.iteratedFDerivWithin h' n hu hx).coeff_zero _).symm
  rw [this]; rw [p.iteratedFDerivSeries_eq_zero (p.congr_zero (Nat.zero_add n).symm hn)]; rw [zero_apply]

中文:
引理 HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_zero
  证明: by
  have : iteratedFDerivWithin 𝕜 n f s x = p.iteratedFDerivSeries n 0 (fun _ => 0) :=
    ((h.iteratedFDerivWithin h' n hu hx).coeff_zero _).symm
  rw [this]; rw [p.iteratedFDerivSeries_eq_zero (p.congr_zero (Nat.zero_add n).symm hn)]; rw [zero_apply]

Depends on / 依赖: Nat.zero_add, coeff_zero, congr_zero, h.iteratedFDerivWithin, iteratedFDerivSeries, iteratedFDerivSeries_eq_zero, iteratedFDerivWithin, p.congr_zero, p.iteratedFDerivSeries, p.iteratedFDerivSeries_eq_zero, zero_add, zero_apply
-/
lemma HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_zero
    (h : HasFPowerSeriesWithinOnBall f p s x r) (h' : AnalyticOn 𝕜 f s)
    (hu : UniqueDiffOn 𝕜 s) (hx : x in s) {n : Nat} (hn : p n = 0) :
    iteratedFDerivWithin 𝕜 n f s x = 0 := by
  have : iteratedFDerivWithin 𝕜 n f s x = p.iteratedFDerivSeries n 0 (fun _ => 0) :=
    ((h.iteratedFDerivWithin h' n hu hx).coeff_zero _).symm
  rw [this]; rw [p.iteratedFDerivSeries_eq_zero (p.congr_zero (Nat.zero_add n).symm hn)]; rw [zero_apply]

/--
lemma `ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal` / 引理 `ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal`

English:
lemma ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal
  proof: by
  rw [← sum_comp (Equiv.inv (Perm (Fin n)))]
  let g : E ->L[𝕜] (Fin n -> E) := ContinuousLinearMap.pi (fun i => ContinuousLinearMap.id 𝕜 E)
  change iteratedFDeriv 𝕜 n (f ∘ g) x v = _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ f.contDiff _ le_rfl]; rw [f.iteratedFDeriv_eq]
  simp only

中文:
引理 ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal
  证明: by
  rw [← sum_comp (Equiv.inv (Perm (Fin n)))]
  let g : E ->L[𝕜] (Fin n -> E) := ContinuousLinearMap.pi (fun i => ContinuousLinearMap.id 𝕜 E)
  change iteratedFDeriv 𝕜 n (f ∘ g) x v = _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ f.contDiff _ le_rfl]; rw [f.iteratedFDeriv_eq]
  simp only

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, ContinuousLinearMap.iteratedFDeriv_comp_right, ContinuousLinearMap.pi, ContinuousMultilinearMap, ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousMultilinearMap.iteratedFDeriv, ContinuousMultilinearMap.iteratedFDerivComponent_apply, Equiv.inv, Pi.compRightL_apply, Set.mem_range, compContinuousLinearMap_apply, compRightL_apply, contDiff, f.contDiff, f.iteratedFDeriv_eq, iteratedFDeriv, iteratedFDerivComponent_apply, iteratedFDeriv_comp_right, iteratedFDeriv_eq
-/
lemma ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal
    {n : Nat} (f : E [×n]->L[𝕜] F) (x : E) (v : Fin n -> E) :
    iteratedFDeriv 𝕜 n (fun x => f (fun _ => x)) x v = ∑ σ : Perm (Fin n), f (fun i => v (σ i)) := by
  rw [← sum_comp (Equiv.inv (Perm (Fin n)))]
  let g : E ->L[𝕜] (Fin n -> E) := ContinuousLinearMap.pi (fun i => ContinuousLinearMap.id 𝕜 E)
  change iteratedFDeriv 𝕜 n (f ∘ g) x v = _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ f.contDiff _ le_rfl]; rw [f.iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.iteratedFDeriv,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply, Set.mem_range, Pi.compRightL_apply]
  rw [← sum_comp (Equiv.embeddingEquivOfFinite (Fin n))]
  congr with σ
  congr with i
  obtain ⟨y, rfl⟩ := σ.equivOfFiniteSelfEmbedding.surjective i
  simp [Function.Embedding.equivOfFiniteSelfEmbedding, g]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset` / 引理 `HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset`

English:
lemma HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset
  proof: by
  have I : insert x s inter Metric.eball x r = s := by
    rw [Set.insert_eq_of_mem hx]
    exact Set.inter_eq_left.2 h's
  have fcont : ContDiffOn 𝕜 (↑n) f s := by
    apply AnalyticOn.contDiffOn _ hs
    simpa [I] using h'
  let g : E -> F := fun z => p n (fun _ => z - x)
  have gcont : ContDif

中文:
引理 HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset
  证明: by
  have I : insert x s inter Metric.eball x r = s := by
    rw [Set.insert_eq_of_mem hx]
    exact Set.inter_eq_left.2 h's
  have fcont : ContDiffOn 𝕜 (↑n) f s := by
    apply AnalyticOn.contDiffOn _ hs
    simpa [I] using h'
  let g : E -> F := fun z => p n (fun _ => z - x)
  have gcont : ContDif
-/
private lemma HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset
    (h : HasFPowerSeriesWithinOnBall f p s x r) (h' : AnalyticOn 𝕜 f s)
    (hs : UniqueDiffOn 𝕜 s) (hx : x in s)
    {n : Nat} (v : Fin n -> E) (h's : s subseteq Metric.eball x r) :
    iteratedFDerivWithin 𝕜 n f s x v = ∑ σ : Perm (Fin n), p n (fun i => v (σ i)) := by
  have I : insert x s inter Metric.eball x r = s := by
    rw [Set.insert_eq_of_mem hx]
    exact Set.inter_eq_left.2 h's
  have fcont : ContDiffOn 𝕜 (↑n) f s := by
    apply AnalyticOn.contDiffOn _ hs
    simpa [I] using h'
  let g : E -> F := fun z => p n (fun _ => z - x)
  have gcont : ContDiff 𝕜 ω g := by
    apply (p n).contDiff.comp
    exact contDiff_pi.2 (fun i => contDiff_id.sub contDiff_const)
  let q : FormalMultilinearSeries 𝕜 E F := fun k => if h : n = k then (h ▸ p n) else 0
  have A : HasFiniteFPowerSeriesOnBall g q x (n + 1) r := by
    apply HasFiniteFPowerSeriesOnBall.mk' _ h.r_pos
    · intro y hy
      rw [Finset.sum_eq_single_of_mem n]
      · simp [q, g]
      · simp
      · intro i hi h'i
        simp [q, h'i.symm]
    · intro m hm
      have : n != m := by lia
      simp [q, this]
  have B : HasFPowerSeriesWithinOnBall g q s x r :=
    A.toHasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall
  have J1 : iteratedFDerivWithin 𝕜 n f s x =
      iteratedFDerivWithin 𝕜 n g s x + iteratedFDerivWithin 𝕜 n (f - g) s x := by
    have : f = g + (f - g) := by abel
    nth_rewrite 1 [this]
    rw [iteratedFDerivWithin_add_apply (gcont.of_le le_top).contDiffWithinAt
      (by exact (fcont _ hx).sub (gcont.of_le le_top).contDiffWithinAt) hs hx]
  have J2 : iteratedFDerivWithin 𝕜 n (f - g) s x = 0 := by
    apply (h.sub B).iteratedFDerivWithin_eq_zero (h'.sub ?_) hs hx
    · simp [q]
    · apply gcont.contDiffOn.analyticOn
  have J3 : iteratedFDerivWithin 𝕜 n g s x = iteratedFDeriv 𝕜 n g x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hs (gcont.of_le le_top).contDiffAt hx
  simp only [J1, J3, J2, add_zero]
  let g' : E -> F := fun z => p n (fun _ => z)
  have : g = fun z => g' (z - x) := rfl
  rw [this]; rw [iteratedFDeriv_comp_sub]
  exact (p n).iteratedFDeriv_comp_diagonal _ v

/--
theorem `HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum` / 定理 `HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum`

English:
theorem HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum
  proof: by
  have : iteratedFDerivWithin 𝕜 n f s x
      = iteratedFDerivWithin 𝕜 n f (s inter Metric.eball x r) x :=
    (iteratedFDerivWithin_inter_open Metric.isOpen_eball (Metric.mem_eball_self h.r_pos)).symm
  rw [this]
  apply HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset
  · exact

中文:
定理 HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum
  证明: by
  have : iteratedFDerivWithin 𝕜 n f s x
      = iteratedFDerivWithin 𝕜 n f (s inter Metric.eball x r) x :=
    (iteratedFDerivWithin_inter_open Metric.isOpen_eball (Metric.mem_eball_self h.r_pos)).symm
  rw [this]
  apply HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset
  · exact

Depends on / 依赖: HasFPowerSeriesWithinOnBall, HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset, Metric, Metric.eball, Metric.isOpen_eball, Metric.mem_eball_self, h.mono, h.r_pos, hs.inter, inter_subset_left, inter_subset_right, isOpen_eball, iteratedFDerivWithin, iteratedFDerivWithin_eq_sum_of_subset, iteratedFDerivWithin_inter_open, mem_eball_self, r_pos
-/
theorem HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum
    (h : HasFPowerSeriesWithinOnBall f p s x r) (h' : AnalyticOn 𝕜 f s)
    (hs : UniqueDiffOn 𝕜 s) (hx : x in s) {n : Nat} (v : Fin n -> E) :
    iteratedFDerivWithin 𝕜 n f s x v = ∑ σ : Perm (Fin n), p n (fun i => v (σ i)) := by
  have : iteratedFDerivWithin 𝕜 n f s x
      = iteratedFDerivWithin 𝕜 n f (s inter Metric.eball x r) x :=
    (iteratedFDerivWithin_inter_open Metric.isOpen_eball (Metric.mem_eball_self h.r_pos)).symm
  rw [this]
  apply HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset
  · exact h.mono inter_subset_left
  · exact h'.mono inter_subset_left
  · exact hs.inter Metric.isOpen_eball
  · exact ⟨hx, Metric.mem_eball_self h.r_pos⟩
  · exact inter_subset_right

/--
theorem `HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum` / 定理 `HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum`

English:
theorem HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum
  proof: by
  simp only [← iteratedFDerivWithin_univ, ← hasFPowerSeriesWithinOnBall_univ] at h ⊢
  exact h.iteratedFDerivWithin_eq_sum h' uniqueDiffOn_univ (mem_univ x) v

中文:
定理 HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum
  证明: by
  simp only [← iteratedFDerivWithin_univ, ← hasFPowerSeriesWithinOnBall_univ] at h ⊢
  exact h.iteratedFDerivWithin_eq_sum h' uniqueDiffOn_univ (mem_univ x) v

Depends on / 依赖: h.iteratedFDerivWithin_eq_sum, hasFPowerSeriesWithinOnBall_univ, iteratedFDerivWithin_eq_sum, iteratedFDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
theorem HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum
    (h : HasFPowerSeriesOnBall f p x r) (h' : AnalyticOn 𝕜 f univ) {n : Nat} (v : Fin n -> E) :
    iteratedFDeriv 𝕜 n f x v = ∑ σ : Perm (Fin n), p n (fun i => v (σ i)) := by
  simp only [← iteratedFDerivWithin_univ, ← hasFPowerSeriesWithinOnBall_univ] at h ⊢
  exact h.iteratedFDerivWithin_eq_sum h' uniqueDiffOn_univ (mem_univ x) v

/--
theorem `HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_completeSpace` / 定理 `HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_completeSpace`

English:
theorem HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_completeSpace
  statement: [CompleteSpace F]
  proof: by
  have : iteratedFDerivWithin 𝕜 n f s x
      = iteratedFDerivWithin 𝕜 n f (s inter Metric.eball x r) x :=
    (iteratedFDerivWithin_inter_open Metric.isOpen_eball (Metric.mem_eball_self h.r_pos)).symm
  rw [this]
  apply HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset
  · exact

中文:
定理 HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_completeSpace
  结论: [CompleteSpace F]
  证明: by
  have : iteratedFDerivWithin 𝕜 n f s x
      = iteratedFDerivWithin 𝕜 n f (s inter Metric.eball x r) x :=
    (iteratedFDerivWithin_inter_open Metric.isOpen_eball (Metric.mem_eball_self h.r_pos)).symm
  rw [this]
  apply HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset
  · exact

Depends on / 依赖: HasFPowerSeriesWithinOnBall, HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset, Metric, Metric.eball, Metric.isOpen_eball, Metric.mem_eball_self, analyticOn, h.analyticOn.mono, h.mono, h.r_pos, hs.inter, insert_eq_of_mem, inter_subset_left, inter_subset_right, isOpen_eball, iteratedFDerivWithin, iteratedFDerivWithin_eq_sum_of_subset, iteratedFDerivWithin_inter_open, mem_eball_self, r_pos
-/
theorem HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_completeSpace [CompleteSpace F]
    (h : HasFPowerSeriesWithinOnBall f p s x r)
    (hs : UniqueDiffOn 𝕜 s) (hx : x in s) {n : Nat} (v : Fin n -> E) :
    iteratedFDerivWithin 𝕜 n f s x v = ∑ σ : Perm (Fin n), p n (fun i => v (σ i)) := by
  have : iteratedFDerivWithin 𝕜 n f s x
      = iteratedFDerivWithin 𝕜 n f (s inter Metric.eball x r) x :=
    (iteratedFDerivWithin_inter_open Metric.isOpen_eball (Metric.mem_eball_self h.r_pos)).symm
  rw [this]
  apply HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset
  · exact h.mono inter_subset_left
  · apply h.analyticOn.mono
    rw [insert_eq_of_mem hx]
  · exact hs.inter Metric.isOpen_eball
  · exact ⟨hx, Metric.mem_eball_self h.r_pos⟩
  · exact inter_subset_right

/--
theorem `HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace` / 定理 `HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace`

English:
theorem HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace
  statement: [CompleteSpace F]
  proof: by
  simp only [← iteratedFDerivWithin_univ, ← hasFPowerSeriesWithinOnBall_univ] at h ⊢
  exact h.iteratedFDerivWithin_eq_sum_of_completeSpace uniqueDiffOn_univ (mem_univ _) v

中文:
定理 HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace
  结论: [CompleteSpace F]
  证明: by
  simp only [← iteratedFDerivWithin_univ, ← hasFPowerSeriesWithinOnBall_univ] at h ⊢
  exact h.iteratedFDerivWithin_eq_sum_of_completeSpace uniqueDiffOn_univ (mem_univ _) v

Depends on / 依赖: h.iteratedFDerivWithin_eq_sum_of_completeSpace, hasFPowerSeriesWithinOnBall_univ, iteratedFDerivWithin_eq_sum_of_completeSpace, iteratedFDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
theorem HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace [CompleteSpace F]
    (h : HasFPowerSeriesOnBall f p x r) {n : Nat} (v : Fin n -> E) :
    iteratedFDeriv 𝕜 n f x v = ∑ σ : Perm (Fin n), p n (fun i => v (σ i)) := by
  simp only [← iteratedFDerivWithin_univ, ← hasFPowerSeriesWithinOnBall_univ] at h ⊢
  exact h.iteratedFDerivWithin_eq_sum_of_completeSpace uniqueDiffOn_univ (mem_univ _) v

/--
theorem `AnalyticOn.iteratedFDerivWithin_comp_perm` / 定理 `AnalyticOn.iteratedFDerivWithin_comp_perm`

English:
theorem AnalyticOn.iteratedFDerivWithin_comp_perm
  proof: by
  rcases h x hx with ⟨p, r, hp⟩
  rw [hp.iteratedFDerivWithin_eq_sum h hs hx]; rw [hp.iteratedFDerivWithin_eq_sum h hs hx]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft σ)]
  simp only [coe_mulLeft, Perm.coe_mul, Function.comp_apply]

中文:
定理 AnalyticOn.iteratedFDerivWithin_comp_perm
  证明: by
  rcases h x hx with ⟨p, r, hp⟩
  rw [hp.iteratedFDerivWithin_eq_sum h hs hx]; rw [hp.iteratedFDerivWithin_eq_sum h hs hx]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft σ)]
  simp only [coe_mulLeft, Perm.coe_mul, Function.comp_apply]

Depends on / 依赖: Equiv.mulLeft, Equiv.sum_comp, Function, Function.comp_apply, Perm.coe_mul, coe_mul, coe_mulLeft, comp_apply, conv_rhs, hp.iteratedFDerivWithin_eq_sum, iteratedFDerivWithin_eq_sum, mulLeft, sum_comp
-/
theorem AnalyticOn.iteratedFDerivWithin_comp_perm
    (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) {n : Nat} (v : Fin n -> E)
    (σ : Perm (Fin n)) :
    iteratedFDerivWithin 𝕜 n f s x (v ∘ σ) = iteratedFDerivWithin 𝕜 n f s x v := by
  rcases h x hx with ⟨p, r, hp⟩
  rw [hp.iteratedFDerivWithin_eq_sum h hs hx]; rw [hp.iteratedFDerivWithin_eq_sum h hs hx]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft σ)]
  simp only [coe_mulLeft, Perm.coe_mul, Function.comp_apply]

/--
theorem `AnalyticOn.domDomCongr_iteratedFDerivWithin` / 定理 `AnalyticOn.domDomCongr_iteratedFDerivWithin`

English:
theorem AnalyticOn.domDomCongr_iteratedFDerivWithin
  proof: by
  ext
  exact h.iteratedFDerivWithin_comp_perm hs hx _ _

中文:
定理 AnalyticOn.domDomCongr_iteratedFDerivWithin
  证明: by
  ext
  exact h.iteratedFDerivWithin_comp_perm hs hx _ _

Depends on / 依赖: h.iteratedFDerivWithin_comp_perm, iteratedFDerivWithin_comp_perm
-/
theorem AnalyticOn.domDomCongr_iteratedFDerivWithin
    (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) {n : Nat} (σ : Perm (Fin n)) :
    (iteratedFDerivWithin 𝕜 n f s x).domDomCongr σ = iteratedFDerivWithin 𝕜 n f s x := by
  ext
  exact h.iteratedFDerivWithin_comp_perm hs hx _ _

/--
theorem `ContDiffWithinAt.iteratedFDerivWithin_comp_perm` / 定理 `ContDiffWithinAt.iteratedFDerivWithin_comp_perm`

English:
theorem ContDiffWithinAt.iteratedFDerivWithin_comp_perm
  proof: by
  rcases h.contDiffOn' le_rfl (by simp) with ⟨u, u_open, xu, hu⟩
  rw [insert_eq_of_mem hx] at hu
  have : iteratedFDerivWithin 𝕜 n f (s inter u) x = iteratedFDerivWithin 𝕜 n f s x :=
    iteratedFDerivWithin_inter_open u_open xu
  rw [← this]
  exact AnalyticOn.iteratedFDerivWithin_comp_perm hu.

中文:
定理 ContDiffWithinAt.iteratedFDerivWithin_comp_perm
  证明: by
  rcases h.contDiffOn' le_rfl (by simp) with ⟨u, u_open, xu, hu⟩
  rw [insert_eq_of_mem hx] at hu
  have : iteratedFDerivWithin 𝕜 n f (s inter u) x = iteratedFDerivWithin 𝕜 n f s x :=
    iteratedFDerivWithin_inter_open u_open xu
  rw [← this]
  exact AnalyticOn.iteratedFDerivWithin_comp_perm hu.

Depends on / 依赖: AnalyticOn, AnalyticOn.iteratedFDerivWithin_comp_perm, analyticOn, contDiffOn, h.contDiffOn, hs.inter, hu.analyticOn, insert_eq_of_mem, iteratedFDerivWithin, iteratedFDerivWithin_comp_perm, iteratedFDerivWithin_inter_open, le_rfl, u_open
-/
theorem ContDiffWithinAt.iteratedFDerivWithin_comp_perm
    (h : ContDiffWithinAt 𝕜 ω f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) {n : Nat} (v : Fin n -> E)
    (σ : Perm (Fin n)) :
    iteratedFDerivWithin 𝕜 n f s x (v ∘ σ) = iteratedFDerivWithin 𝕜 n f s x v := by
  rcases h.contDiffOn' le_rfl (by simp) with ⟨u, u_open, xu, hu⟩
  rw [insert_eq_of_mem hx] at hu
  have : iteratedFDerivWithin 𝕜 n f (s inter u) x = iteratedFDerivWithin 𝕜 n f s x :=
    iteratedFDerivWithin_inter_open u_open xu
  rw [← this]
  exact AnalyticOn.iteratedFDerivWithin_comp_perm hu.analyticOn (hs.inter u_open) ⟨hx, xu⟩ _ _

/--
theorem `ContDiffWithinAt.domDomCongr_iteratedFDerivWithin` / 定理 `ContDiffWithinAt.domDomCongr_iteratedFDerivWithin`

English:
theorem ContDiffWithinAt.domDomCongr_iteratedFDerivWithin
  proof: by
  ext
  exact h.iteratedFDerivWithin_comp_perm hs hx _ _

中文:
定理 ContDiffWithinAt.domDomCongr_iteratedFDerivWithin
  证明: by
  ext
  exact h.iteratedFDerivWithin_comp_perm hs hx _ _

Depends on / 依赖: h.iteratedFDerivWithin_comp_perm, iteratedFDerivWithin_comp_perm
-/
theorem ContDiffWithinAt.domDomCongr_iteratedFDerivWithin
    (h : ContDiffWithinAt 𝕜 ω f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) {n : Nat}
    (σ : Perm (Fin n)) :
    (iteratedFDerivWithin 𝕜 n f s x).domDomCongr σ = iteratedFDerivWithin 𝕜 n f s x := by
  ext
  exact h.iteratedFDerivWithin_comp_perm hs hx _ _

/--
theorem `AnalyticOn.iteratedFDeriv_comp_perm` / 定理 `AnalyticOn.iteratedFDeriv_comp_perm`

English:
theorem AnalyticOn.iteratedFDeriv_comp_perm
  proof: by
  rw [← iteratedFDerivWithin_univ]
  exact h.iteratedFDerivWithin_comp_perm uniqueDiffOn_univ (mem_univ x) _ _

中文:
定理 AnalyticOn.iteratedFDeriv_comp_perm
  证明: by
  rw [← iteratedFDerivWithin_univ]
  exact h.iteratedFDerivWithin_comp_perm uniqueDiffOn_univ (mem_univ x) _ _

Depends on / 依赖: h.iteratedFDerivWithin_comp_perm, iteratedFDerivWithin_comp_perm, iteratedFDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
theorem AnalyticOn.iteratedFDeriv_comp_perm
    (h : AnalyticOn 𝕜 f univ) {n : Nat} (v : Fin n -> E) (σ : Perm (Fin n)) :
    iteratedFDeriv 𝕜 n f x (v ∘ σ) = iteratedFDeriv 𝕜 n f x v := by
  rw [← iteratedFDerivWithin_univ]
  exact h.iteratedFDerivWithin_comp_perm uniqueDiffOn_univ (mem_univ x) _ _

/--
theorem `AnalyticOn.domDomCongr_iteratedFDeriv` / 定理 `AnalyticOn.domDomCongr_iteratedFDeriv`

English:
theorem AnalyticOn.domDomCongr_iteratedFDeriv
  given: (h : AnalyticOn 𝕜 f univ) {n : Nat} (σ : Perm (Fin n))
  proof: by
  rw [← iteratedFDerivWithin_univ]
  exact h.domDomCongr_iteratedFDerivWithin uniqueDiffOn_univ (mem_univ x) _

中文:
定理 AnalyticOn.domDomCongr_iteratedFDeriv
  条件: (h : AnalyticOn 𝕜 f univ) {n : 自然数} (σ : Perm (Fin n))
  证明: by
  rw [← iteratedFDerivWithin_univ]
  exact h.domDomCongr_iteratedFDerivWithin uniqueDiffOn_univ (mem_univ x) _

Depends on / 依赖: domDomCongr_iteratedFDerivWithin, h.domDomCongr_iteratedFDerivWithin, iteratedFDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
theorem AnalyticOn.domDomCongr_iteratedFDeriv (h : AnalyticOn 𝕜 f univ) {n : Nat} (σ : Perm (Fin n)) :
    (iteratedFDeriv 𝕜 n f x).domDomCongr σ = iteratedFDeriv 𝕜 n f x := by
  rw [← iteratedFDerivWithin_univ]
  exact h.domDomCongr_iteratedFDerivWithin uniqueDiffOn_univ (mem_univ x) _

/--
theorem `ContDiffAt.iteratedFDeriv_comp_perm` / 定理 `ContDiffAt.iteratedFDeriv_comp_perm`

English:
theorem ContDiffAt.iteratedFDeriv_comp_perm
  proof: by
  rw [← iteratedFDerivWithin_univ]
  exact h.iteratedFDerivWithin_comp_perm uniqueDiffOn_univ (mem_univ x) _ _

中文:
定理 ContDiffAt.iteratedFDeriv_comp_perm
  证明: by
  rw [← iteratedFDerivWithin_univ]
  exact h.iteratedFDerivWithin_comp_perm uniqueDiffOn_univ (mem_univ x) _ _

Depends on / 依赖: h.iteratedFDerivWithin_comp_perm, iteratedFDerivWithin_comp_perm, iteratedFDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
theorem ContDiffAt.iteratedFDeriv_comp_perm
    (h : ContDiffAt 𝕜 ω f x) {n : Nat} (v : Fin n -> E) (σ : Perm (Fin n)) :
    iteratedFDeriv 𝕜 n f x (v ∘ σ) = iteratedFDeriv 𝕜 n f x v := by
  rw [← iteratedFDerivWithin_univ]
  exact h.iteratedFDerivWithin_comp_perm uniqueDiffOn_univ (mem_univ x) _ _

/--
theorem `ContDiffAt.domDomCongr_iteratedFDeriv` / 定理 `ContDiffAt.domDomCongr_iteratedFDeriv`

English:
theorem ContDiffAt.domDomCongr_iteratedFDeriv
  given: (h : ContDiffAt 𝕜 ω f x) {n : Nat} (σ : Perm (Fin n))
  proof: by
  rw [← iteratedFDerivWithin_univ]
  exact h.domDomCongr_iteratedFDerivWithin uniqueDiffOn_univ (mem_univ x) _

中文:
定理 ContDiffAt.domDomCongr_iteratedFDeriv
  条件: (h : ContDiffAt 𝕜 ω f x) {n : 自然数} (σ : Perm (Fin n))
  证明: by
  rw [← iteratedFDerivWithin_univ]
  exact h.domDomCongr_iteratedFDerivWithin uniqueDiffOn_univ (mem_univ x) _

Depends on / 依赖: domDomCongr_iteratedFDerivWithin, h.domDomCongr_iteratedFDerivWithin, iteratedFDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
theorem ContDiffAt.domDomCongr_iteratedFDeriv (h : ContDiffAt 𝕜 ω f x) {n : Nat} (σ : Perm (Fin n)) :
    (iteratedFDeriv 𝕜 n f x).domDomCongr σ = iteratedFDeriv 𝕜 n f x := by
  rw [← iteratedFDerivWithin_univ]
  exact h.domDomCongr_iteratedFDerivWithin uniqueDiffOn_univ (mem_univ x) _
