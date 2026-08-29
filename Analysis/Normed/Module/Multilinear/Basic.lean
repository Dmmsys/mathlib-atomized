/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Sophie Morel, Yury Kudryashov
-/
module

public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Operator norm on the space of continuous multilinear maps

When `f` is a continuous multilinear map in finitely many variables, we define its norm `‖f‖` as the
smallest number such that `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖` for all `m`.

We show that it is indeed a norm, and prove its basic properties.

## Main results

Let `f` be a multilinear map in finitely many variables.
* `exists_bound_of_continuous` asserts that, if `f` is continuous, then there exists `C > 0`
  with `‖f m‖ ≤ C * ∏ i, ‖m i‖` for all `m`.
* `continuous_of_bound`, conversely, asserts that this bound implies continuity.
* `mkContinuous` constructs the associated continuous multilinear map.

Let `f` be a continuous multilinear map in finitely many variables.
* `‖f‖` is its norm, i.e., the smallest number such that `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖` for
  all `m`.
* `le_opNorm f m` asserts the fundamental inequality `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖`.
* `norm_image_sub_le f m₁ m₂` gives a control of the difference `f m₁ - f m₂` in terms of
  `‖f‖` and `‖m₁ - m₂‖`.

## Implementation notes

We mostly follow the API (and the proofs) of `OperatorNorm.lean`, with the additional complexity
that we should deal with multilinear maps in several variables.

From the mathematical point of view, all the results follow from the results on operator norm in
one variable, by applying them to one variable after the other through currying. However, this
is only well defined when there is an order on the variables (for instance on `Fin n`) although
the final result is independent of the order. While everything could be done following this
approach, it turns out that direct proofs are easier and more efficient.
-/

@[expose] public section

suppress_compilation

noncomputable section

open scoped NNReal Topology Uniformity
open Finset Metric Function Filter

/-!
### Type variables

We use the following type variables in this file:

* `𝕜` : a `NontriviallyNormedField`;
* `ι`, `ι'` : finite index types with decidable equality;
* `E`, `E₁` : families of normed vector spaces over `𝕜` indexed by `i : ι`;
* `E'` : a family of normed vector spaces over `𝕜` indexed by `i' : ι'`;
* `Ei` : a family of normed vector spaces over `𝕜` indexed by `i : Fin (Nat.succ n)`;
* `G`, `G'` : normed vector spaces over `𝕜`.
-/

universe u v v' wE wE₁ wE' wG wG'

section continuous_eval

variable {𝕜 ι : Type*} {E : ι -> Type*} {F : Type*}
    [NormedField 𝕜] [Finite ι] [forall i, SeminormedAddCommGroup (E i)] [forall i, NormedSpace 𝕜 (E i)]
    [TopologicalSpace F] [AddCommGroup F] [IsTopologicalAddGroup F] [Module 𝕜 F]

/--
Instance `ContinuousMultilinearMap.instContinuousEval` / 实例 `ContinuousMultilinearMap.instContinuousEval`

English:
instance ContinuousMultilinearMap.instContinuousEval
  signature: :
  body: by
    cases nonempty_fintype ι
    let _ := IsTopologicalAddGroup.rightUniformSpace F
    have := isUniformAddGroup_of_addCommGroup (G := F)
    refine (UniformOnFun.continuousOn_eval₂ fun m => ?_).comp_continuous
      (isEmbedding_toUniformOnFun.continuous.prodMap continuous_id) fun (f, x) => f.cont.continuousAt
    exact ⟨ball m 1, NormedSpace.isVonNBounded_of_isBounded _ isBounded_ball,
      ball_mem_nhds _ one_pos⟩

中文:
实例 连续多重线性映射.instContinuousEval
  签名: :
  定义体: by
    cases nonempty_fintype ι
    let _ := IsTopologicalAddGroup.rightUniformSpace F
    have := isUniformAddGroup_of_addCommGroup (G := F)
    refine (UniformOnFun.continuousOn_eval₂ fun m => ?_).comp_continuous
      (isEmbedding_toUniformOnFun.continuous.prodMap continuous_id) fun (f, x) => f.cont.continuousAt
    exact ⟨ball m 1, NormedSpace.isVonNBounded_of_isBounded _ isBounded_ball,
      ball_mem_nhds _ one_pos⟩

Depends on / 依赖: IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, NormedSpace, NormedSpace.isVonNBounded_of_isBounded, UniformOnFun, UniformOnFun.continuousOn_eval, ball_mem_nhds, comp_continuous, continuous, continuousAt, continuous_id, f.cont.continuousAt, isBounded_ball, isEmbedding_toUniformOnFun, isEmbedding_toUniformOnFun.continuous.prodMap, isUniformAddGroup_of_addCommGroup, isVonNBounded_of_isBounded, nonempty_fintype, one_pos, prodMap
-/
instance ContinuousMultilinearMap.instContinuousEval :
    ContinuousEval (ContinuousMultilinearMap 𝕜 E F) (Π i, E i) F where
  continuous_eval := by
    cases nonempty_fintype ι
    let _ := IsTopologicalAddGroup.rightUniformSpace F
    have := isUniformAddGroup_of_addCommGroup (G := F)
    refine (UniformOnFun.continuousOn_eval₂ fun m => ?_).comp_continuous
      (isEmbedding_toUniformOnFun.continuous.prodMap continuous_id) fun (f, x) => f.cont.continuousAt
    exact ⟨ball m 1, NormedSpace.isVonNBounded_of_isBounded _ isBounded_ball,
      ball_mem_nhds _ one_pos⟩

namespace ContinuousLinearMap

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [Module 𝕜 G] [ContinuousConstSMul 𝕜 F]

/--
lemma `continuous_uncurry_of_multilinear` / 引理 `continuous_uncurry_of_multilinear`

English:
lemma continuous_uncurry_of_multilinear
  given: (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F)
  proof: by
  fun_prop

中文:
引理 continuous_uncurry_of_multilinear
  条件: (f : G ->L[𝕜] 连续多重线性映射 𝕜 E F)
  证明: by
  fun_prop

Depends on / 依赖: fun_prop
-/
lemma continuous_uncurry_of_multilinear (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F) :
    Continuous (fun (p : G × (Π i, E i)) => f p.1 p.2) := by
  fun_prop

/--
lemma `continuousOn_uncurry_of_multilinear` / 引理 `continuousOn_uncurry_of_multilinear`

English:
lemma continuousOn_uncurry_of_multilinear
  given: (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F) {s}
  proof: f.continuous_uncurry_of_multilinear.continuousOn

中文:
引理 continuousOn_uncurry_of_multilinear
  条件: (f : G ->L[𝕜] 连续多重线性映射 𝕜 E F) {s}
  证明: f.continuous_uncurry_of_multilinear.continuousOn

Depends on / 依赖: continuousOn, continuous_uncurry_of_multilinear, f.continuous_uncurry_of_multilinear.continuousOn
-/
lemma continuousOn_uncurry_of_multilinear (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F) {s} :
    ContinuousOn (fun (p : G × (Π i, E i)) => f p.1 p.2) s :=
  f.continuous_uncurry_of_multilinear.continuousOn

/--
lemma `continuousAt_uncurry_of_multilinear` / 引理 `continuousAt_uncurry_of_multilinear`

English:
lemma continuousAt_uncurry_of_multilinear
  given: (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F) {x}
  proof: f.continuous_uncurry_of_multilinear.continuousAt

中文:
引理 continuousAt_uncurry_of_multilinear
  条件: (f : G ->L[𝕜] 连续多重线性映射 𝕜 E F) {x}
  证明: f.continuous_uncurry_of_multilinear.continuousAt

Depends on / 依赖: continuousAt, continuous_uncurry_of_multilinear, f.continuous_uncurry_of_multilinear.continuousAt
-/
lemma continuousAt_uncurry_of_multilinear (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F) {x} :
    ContinuousAt (fun (p : G × (Π i, E i)) => f p.1 p.2) x :=
  f.continuous_uncurry_of_multilinear.continuousAt

/--
lemma `continuousWithinAt_uncurry_of_multilinear` / 引理 `continuousWithinAt_uncurry_of_multilinear`

English:
lemma continuousWithinAt_uncurry_of_multilinear
  given: (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F) {s x}
  proof: f.continuous_uncurry_of_multilinear.continuousWithinAt

中文:
引理 continuousWithinAt_uncurry_of_multilinear
  条件: (f : G ->L[𝕜] 连续多重线性映射 𝕜 E F) {s x}
  证明: f.continuous_uncurry_of_multilinear.continuousWithinAt

Depends on / 依赖: continuousWithinAt, continuous_uncurry_of_multilinear, f.continuous_uncurry_of_multilinear.continuousWithinAt
-/
lemma continuousWithinAt_uncurry_of_multilinear (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F) {s x} :
    ContinuousWithinAt (fun (p : G × (Π i, E i)) => f p.1 p.2) s x :=
  f.continuous_uncurry_of_multilinear.continuousWithinAt

end ContinuousLinearMap

end continuous_eval

section Seminorm

variable {𝕜 : Type u} {ι : Type v} {ι' : Type v'} {E : ι -> Type wE} {E₁ : ι -> Type wE₁}
  {E' : ι' -> Type wE'} {G : Type wG} {G' : Type wG'}
  [Fintype ι'] [NontriviallyNormedField 𝕜] [forall i, SeminormedAddCommGroup (E i)]
  [forall i, NormedSpace 𝕜 (E i)] [forall i, SeminormedAddCommGroup (E₁ i)] [forall i, NormedSpace 𝕜 (E₁ i)]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [SeminormedAddCommGroup G'] [NormedSpace 𝕜 G']

/-!
### Continuity properties of multilinear maps

We relate continuity of multilinear maps to the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`, in
both directions. Along the way, we prove useful bounds on the difference `‖f m₁ - f m₂‖`.
-/

namespace MultilinearMap

/--
lemma `norm_map_coord_zero` / 引理 `norm_map_coord_zero`

English:
lemma norm_map_coord_zero
  statement: (f : MultilinearMap 𝕜 E G) (hf : Continuous f)
  proof: by
  classical
  rw [← inseparable_zero_iff_norm] at hi ⊢
have : Inseparable (update m i 0) m := inseparable_pi.2
    (forall_update_iff m fun i a => Inseparable a (m i)).2 ⟨hi.symm, fun _ _ => rfl⟩
  simpa only [map_update_zero] using this.symm.map hf

中文:
引理 norm_map_coord_zero
  结论: (f : 多重线性映射 𝕜 E G) (hf : 连续 f)
  证明: by
  classical
  rw [← inseparable_zero_iff_norm] at hi ⊢
have : Inseparable (update m i 0) m := inseparable_pi.2
    (forall_update_iff m fun i a => Inseparable a (m i)).2 ⟨hi.symm, fun _ _ => rfl⟩
  simpa only [map_update_zero] using this.symm.map hf

Depends on / 依赖: Inseparable, classical, forall_update_iff, hi.symm, inseparable_pi, inseparable_zero_iff_norm, map_update_zero, this.symm.map, update
-/
lemma norm_map_coord_zero (f : MultilinearMap 𝕜 E G) (hf : Continuous f)
    {m : forall i, E i} {i : ι} (hi : ‖m i‖ = 0) : ‖f m‖ = 0 := by
  classical
  rw [← inseparable_zero_iff_norm] at hi ⊢
have : Inseparable (update m i 0) m := inseparable_pi.2
    (forall_update_iff m fun i a => Inseparable a (m i)).2 ⟨hi.symm, fun _ _ => rfl⟩
  simpa only [map_update_zero] using this.symm.map hf

variable [Fintype ι]

/--
theorem `bound_of_shell_of_norm_map_coord_zero` / 定理 `bound_of_shell_of_norm_map_coord_zero`

English:
theorem bound_of_shell_of_norm_map_coord_zero
  statement: (f : MultilinearMap 𝕜 E G)
  proof: by
  by_cases! hm : exists i, ‖m i‖ = 0
  · rcases hm with ⟨i, hi⟩
    rw [hf₀ hi]; rw [prod_eq_zero (mem_univ i) hi]; rw [mul_zero]
  choose δ hδ0 hδm_lt hle_δm _ using fun i => rescale_to_shell_semi_normed (hc i) (hε i) (hm i)
  have hδ0 : 0 < ∏ i, ‖δ i‖ := prod_pos fun i _ => norm_pos_iff.2 (hδ0 i)
  simpa [map_smul_univ, norm_smul, prod_mul_distrib, mul_left_comm C, hδ0] using
    hf (fun i => δ i • m i) hle_δm hδm_lt

中文:
定理 bound_of_shell_of_norm_map_coord_zero
  结论: (f : 多重线性映射 𝕜 E G)
  证明: by
  by_cases! hm : exists i, ‖m i‖ = 0
  · rcases hm with ⟨i, hi⟩
    rw [hf₀ hi]; rw [prod_eq_zero (mem_univ i) hi]; rw [mul_zero]
  choose δ hδ0 hδm_lt hle_δm _ using fun i => rescale_to_shell_semi_normed (hc i) (hε i) (hm i)
  have hδ0 : 0 < ∏ i, ‖δ i‖ := prod_pos fun i _ => norm_pos_iff.2 (hδ0 i)
  simpa [map_smul_univ, norm_smul, prod_mul_distrib, mul_left_comm C, hδ0] using
    hf (fun i => δ i • m i) hle_δm hδm_lt

Depends on / 依赖: map_smul_univ, mem_univ, mul_left_comm, mul_zero, norm_pos_iff, norm_smul, prod_eq_zero, prod_mul_distrib, prod_pos, rescale_to_shell_semi_normed
-/
theorem bound_of_shell_of_norm_map_coord_zero (f : MultilinearMap 𝕜 E G)
    (hf₀ : forall {m i}, ‖m i‖ = 0 -> ‖f m‖ = 0)
    {ε : ι -> Real} {C : Real} (hε : forall i, 0 < ε i) {c : ι -> 𝕜} (hc : forall i, 1 < ‖c i‖)
    (hf : forall m : forall i, E i, (forall i, ε i / ‖c i‖ <= ‖m i‖) -> (forall i, ‖m i‖ < ε i) -> ‖f m‖ <= C * ∏ i, ‖m i‖)
    (m : forall i, E i) : ‖f m‖ <= C * ∏ i, ‖m i‖ := by
  by_cases! hm : exists i, ‖m i‖ = 0
  · rcases hm with ⟨i, hi⟩
    rw [hf₀ hi]; rw [prod_eq_zero (mem_univ i) hi]; rw [mul_zero]
  choose δ hδ0 hδm_lt hle_δm _ using fun i => rescale_to_shell_semi_normed (hc i) (hε i) (hm i)
  have hδ0 : 0 < ∏ i, ‖δ i‖ := prod_pos fun i _ => norm_pos_iff.2 (hδ0 i)
  simpa [map_smul_univ, norm_smul, prod_mul_distrib, mul_left_comm C, hδ0] using
    hf (fun i => δ i • m i) hle_δm hδm_lt

/--
theorem `bound_of_shell_of_continuous` / 定理 `bound_of_shell_of_continuous`

English:
theorem bound_of_shell_of_continuous
  statement: (f : MultilinearMap 𝕜 E G) (hfc : Continuous f)
  proof: bound_of_shell_of_norm_map_coord_zero f (norm_map_coord_zero f hfc) hε hc hf m

中文:
定理 bound_of_shell_of_continuous
  结论: (f : 多重线性映射 𝕜 E G) (hfc : 连续 f)
  证明: bound_of_shell_of_norm_map_coord_zero f (norm_map_coord_zero f hfc) hε hc hf m

Depends on / 依赖: bound_of_shell_of_norm_map_coord_zero, norm_map_coord_zero
-/
theorem bound_of_shell_of_continuous (f : MultilinearMap 𝕜 E G) (hfc : Continuous f)
    {ε : ι -> Real} {C : Real} (hε : forall i, 0 < ε i) {c : ι -> 𝕜} (hc : forall i, 1 < ‖c i‖)
    (hf : forall m : forall i, E i, (forall i, ε i / ‖c i‖ <= ‖m i‖) -> (forall i, ‖m i‖ < ε i) -> ‖f m‖ <= C * ∏ i, ‖m i‖)
    (m : forall i, E i) : ‖f m‖ <= C * ∏ i, ‖m i‖ :=
  bound_of_shell_of_norm_map_coord_zero f (norm_map_coord_zero f hfc) hε hc hf m

/--
theorem `exists_bound_of_continuous` / 定理 `exists_bound_of_continuous`

English:
theorem exists_bound_of_continuous
  given: (f : MultilinearMap 𝕜 E G) (hf : Continuous f)
  proof: by
  cases isEmpty_or_nonempty ι
  · refine ⟨‖f 0‖ + 1, add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one, fun m => ?_⟩
    obtain rfl : m = 0 := funext (IsEmpty.elim ‹_›)
    simp [univ_eq_empty, zero_le_one]
  obtain ⟨ε : Real, ε0 : 0 < ε, hε : forall m : forall i, E i, ‖m - 0‖ < ε -> ‖f m - f 0‖ < 1⟩ :=
    NormedAddCommGroup.tendsto_nhds_nhds.1 (hf.tendsto 0) 1 zero_lt_one
  simp only [sub_zero, f.map_zero] at hε
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have : 0 < (‖c‖ / ε) ^ Fintype.card ι := pow_pos (div_pos (zero_lt_one.trans hc) ε0) _
  refine ⟨_, this, ?_⟩
  refine f.bound_of_shell_of_continuous hf (fun _ => ε0) (fun _ => hc) fun m hcm hm => ?_
  refine (hε m ((pi_norm_lt_iff ε0).2 hm)).le.trans ?_
  rw [← div_le_iff₀' this]; rw [one_div]; rw [← inv_pow]; rw [inv_div]; rw [Fintype.card]; rw [← prod_const]
  gcongr
  apply hcm

中文:
定理 存在_bound_of_continuous
  条件: (f : 多重线性映射 𝕜 E G) (hf : 连续 f)
  证明: by
  cases isEmpty_or_nonempty ι
  · refine ⟨‖f 0‖ + 1, add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one, fun m => ?_⟩
    obtain rfl : m = 0 := funext (IsEmpty.elim ‹_›)
    simp [univ_eq_empty, zero_le_one]
  obtain ⟨ε : Real, ε0 : 0 < ε, hε : forall m : forall i, E i, ‖m - 0‖ < ε -> ‖f m - f 0‖ < 1⟩ :=
    NormedAddCommGroup.tendsto_nhds_nhds.1 (hf.tendsto 0) 1 zero_lt_one
  simp only [sub_zero, f.map_zero] at hε
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have : 0 < (‖c‖ / ε) ^ Fintype.card ι := pow_pos (div_pos (zero_lt_one.trans hc) ε0) _
  refine ⟨_, this, ?_⟩
  refine f.bound_of_shell_of_continuous hf (fun _ => ε0) (fun _ => hc) fun m hcm hm => ?_
  refine (hε m ((pi_norm_lt_iff ε0).2 hm)).le.trans ?_
  rw [← div_le_iff₀' this]; rw [one_div]; rw [← inv_pow]; rw [inv_div]; rw [Fintype.card]; rw [← prod_const]
  gcongr
  apply hcm

Depends on / 依赖: Fintype, Fintype.card, IsEmpty, IsEmpty.elim, NormedAddCommGroup, NormedAddCommGroup.tendsto_nhds_nhds, NormedField, NormedField.exists_one_lt_norm, add_pos_of_nonneg_of_pos, exists_one_lt_norm, f.map_zero, hf.tendsto, isEmpty_or_nonempty, map_zero, norm_nonneg, sub_zero, tendsto, tendsto_nhds_nhds, univ_eq_empty, zero_le_one
-/
theorem exists_bound_of_continuous (f : MultilinearMap 𝕜 E G) (hf : Continuous f) :
    exists C : Real, 0 < C ∧ forall m, ‖f m‖ <= C * ∏ i, ‖m i‖ := by
  cases isEmpty_or_nonempty ι
  · refine ⟨‖f 0‖ + 1, add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one, fun m => ?_⟩
    obtain rfl : m = 0 := funext (IsEmpty.elim ‹_›)
    simp [univ_eq_empty, zero_le_one]
  obtain ⟨ε : Real, ε0 : 0 < ε, hε : forall m : forall i, E i, ‖m - 0‖ < ε -> ‖f m - f 0‖ < 1⟩ :=
    NormedAddCommGroup.tendsto_nhds_nhds.1 (hf.tendsto 0) 1 zero_lt_one
  simp only [sub_zero, f.map_zero] at hε
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have : 0 < (‖c‖ / ε) ^ Fintype.card ι := pow_pos (div_pos (zero_lt_one.trans hc) ε0) _
  refine ⟨_, this, ?_⟩
  refine f.bound_of_shell_of_continuous hf (fun _ => ε0) (fun _ => hc) fun m hcm hm => ?_
  refine (hε m ((pi_norm_lt_iff ε0).2 hm)).le.trans ?_
  rw [← div_le_iff₀' this]; rw [one_div]; rw [← inv_pow]; rw [inv_div]; rw [Fintype.card]; rw [← prod_const]
  gcongr
  apply hcm

/--
theorem `norm_image_sub_le_of_bound'` / 定理 `norm_image_sub_le_of_bound'`

English:
theorem norm_image_sub_le_of_bound'
  statement: [DecidableEq ι] (f : MultilinearMap 𝕜 E G) {C : Real} (hC : 0 <= C)
  proof: by
  have A :
    forall s : Finset ι,
      ‖f m₁ - f (s.piecewise m₂ m₁)‖ <=
        C * ∑ i in s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := fun s => by
    induction s using Finset.induction with
    | empty => simp
    | insert i s his Hrec =>
      have I :
        ‖f (s.piecewise m₂ m₁) - f ((insert i s).piecewise m₂ m₁)‖ <=
          C * ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := by
        have A : (insert i s).piecewise m₂ m₁ = Function.update (s.piecewise m₂ m₁) i (m₂ i) :=
          s.piecewise_insert _ _ _
        have B : s.piecewise m₂ m₁ = Function.update (s.piecewise m₂ m₁) i (m₁ i) := by
          simp [his]
        rw [B]; rw [A]; rw [← f.map_update_sub]
        apply le_trans (H _)
        gcongr with j
        by_cases h : j = i
        · rw [h]
          simp
        · by_cases h' : j in s <;> simp [h', h]
      calc
        ‖f m₁ - f ((insert i s).piecewise m₂ m₁)‖ <=
            ‖f m₁ - f (s.piecewise m₂ m₁)‖ +
              ‖f (s.piecewise m₂ m₁) - f ((insert i s).piecewise m₂ m₁)‖ := by
          rw [← dist_eq_norm]; rw [← dist_eq_norm]; rw [← dist_eq_norm]
          exact dist_triangle _ _ _
        _ <= (C * ∑ i in s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖) +
              C * ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
          (add_le_add Hrec I)
        _ = C * ∑ i in insert i s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := by
          simp [his, add_comm, left_distrib]
  convert! A univ
  simp

中文:
定理 norm_image_sub_le_of_bound'
  结论: [DecidableEq ι] (f : 多重线性映射 𝕜 E G) {C : 实数} (hC : 0 <= C)
  证明: by
  have A :
    forall s : Finset ι,
      ‖f m₁ - f (s.piecewise m₂ m₁)‖ <=
        C * ∑ i in s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := fun s => by
    induction s using Finset.induction with
    | empty => simp
    | insert i s his Hrec =>
      have I :
        ‖f (s.piecewise m₂ m₁) - f ((insert i s).piecewise m₂ m₁)‖ <=
          C * ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := by
        have A : (insert i s).piecewise m₂ m₁ = Function.update (s.piecewise m₂ m₁) i (m₂ i) :=
          s.piecewise_insert _ _ _
        have B : s.piecewise m₂ m₁ = Function.update (s.piecewise m₂ m₁) i (m₁ i) := by
          simp [his]
        rw [B]; rw [A]; rw [← f.map_update_sub]
        apply le_trans (H _)
        gcongr with j
        by_cases h : j = i
        · rw [h]
          simp
        · by_cases h' : j in s <;> simp [h', h]
      calc
        ‖f m₁ - f ((insert i s).piecewise m₂ m₁)‖ <=
            ‖f m₁ - f (s.piecewise m₂ m₁)‖ +
              ‖f (s.piecewise m₂ m₁) - f ((insert i s).piecewise m₂ m₁)‖ := by
          rw [← dist_eq_norm]; rw [← dist_eq_norm]; rw [← dist_eq_norm]
          exact dist_triangle _ _ _
        _ <= (C * ∑ i in s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖) +
              C * ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
          (add_le_add Hrec I)
        _ = C * ∑ i in insert i s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := by
          simp [his, add_comm, left_distrib]
  convert! A univ
  simp

Depends on / 依赖: Finset, Finset.induction, Function, Function.update, insert, piecew, piecewise, piecewise_insert, s.piecew, s.piecewise, s.piecewise_insert, update
-/
theorem norm_image_sub_le_of_bound' [DecidableEq ι] (f : MultilinearMap 𝕜 E G) {C : Real} (hC : 0 <= C)
    (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) (m₁ m₂ : forall i, E i) :
    ‖f m₁ - f m₂‖ <= C * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := by
  have A :
    forall s : Finset ι,
      ‖f m₁ - f (s.piecewise m₂ m₁)‖ <=
        C * ∑ i in s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := fun s => by
    induction s using Finset.induction with
    | empty => simp
    | insert i s his Hrec =>
      have I :
        ‖f (s.piecewise m₂ m₁) - f ((insert i s).piecewise m₂ m₁)‖ <=
          C * ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := by
        have A : (insert i s).piecewise m₂ m₁ = Function.update (s.piecewise m₂ m₁) i (m₂ i) :=
          s.piecewise_insert _ _ _
        have B : s.piecewise m₂ m₁ = Function.update (s.piecewise m₂ m₁) i (m₁ i) := by
          simp [his]
        rw [B]; rw [A]; rw [← f.map_update_sub]
        apply le_trans (H _)
        gcongr with j
        by_cases h : j = i
        · rw [h]
          simp
        · by_cases h' : j in s <;> simp [h', h]
      calc
        ‖f m₁ - f ((insert i s).piecewise m₂ m₁)‖ <=
            ‖f m₁ - f (s.piecewise m₂ m₁)‖ +
              ‖f (s.piecewise m₂ m₁) - f ((insert i s).piecewise m₂ m₁)‖ := by
          rw [← dist_eq_norm]; rw [← dist_eq_norm]; rw [← dist_eq_norm]
          exact dist_triangle _ _ _
        _ <= (C * ∑ i in s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖) +
              C * ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
          (add_le_add Hrec I)
        _ = C * ∑ i in insert i s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := by
          simp [his, add_comm, left_distrib]
  convert! A univ
  simp

/--
theorem `norm_image_sub_le_of_bound` / 定理 `norm_image_sub_le_of_bound`

English:
theorem norm_image_sub_le_of_bound
  statement: (f : MultilinearMap 𝕜 E G)
  proof: by
  classical
  have A :
    forall i : ι,
      ∏ j, (if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖) <=
        ‖m₁ - m₂‖ * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) := by
    intro i
    calc
      ∏ j, (if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖) <=
          ∏ j : ι, Function.update (fun _ => max ‖m₁‖ ‖m₂‖) i ‖m₁ - m₂‖ j := by
        gcongr with j
        rcases eq_or_ne j i with rfl | h
        · simp only [ite_true, Function.update_self]
          exact norm_le_pi_norm (m₁ - m₂) _
        · simp [h, -le_sup_iff, -sup_le_iff, sup_le_sup, norm_le_pi_norm]
      _ = ‖m₁ - m₂‖ * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) := by
        rw [prod_update_of_mem (Finset.mem_univ _)]
        simp [card_univ_sdiff]
  calc
    ‖f m₁ - f m₂‖ <= C * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
      f.norm_image_sub_le_of_bound' hC H m₁ m₂
    _ <= C * ∑ _i, ‖m₁ - m₂‖ * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) := by gcongr; apply A
    _ = C * Fintype.card ι * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ := by
      rw [sum_const]; rw [card_univ]; rw [nsmul_eq_mul]
      ring

中文:
定理 norm_image_sub_le_of_bound
  结论: (f : 多重线性映射 𝕜 E G)
  证明: by
  classical
  have A :
    forall i : ι,
      ∏ j, (if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖) <=
        ‖m₁ - m₂‖ * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) := by
    intro i
    calc
      ∏ j, (if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖) <=
          ∏ j : ι, Function.update (fun _ => max ‖m₁‖ ‖m₂‖) i ‖m₁ - m₂‖ j := by
        gcongr with j
        rcases eq_or_ne j i with rfl | h
        · simp only [ite_true, Function.update_self]
          exact norm_le_pi_norm (m₁ - m₂) _
        · simp [h, -le_sup_iff, -sup_le_iff, sup_le_sup, norm_le_pi_norm]
      _ = ‖m₁ - m₂‖ * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) := by
        rw [prod_update_of_mem (Finset.mem_univ _)]
        simp [card_univ_sdiff]
  calc
    ‖f m₁ - f m₂‖ <= C * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
      f.norm_image_sub_le_of_bound' hC H m₁ m₂
    _ <= C * ∑ _i, ‖m₁ - m₂‖ * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) := by gcongr; apply A
    _ = C * Fintype.card ι * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ := by
      rw [sum_const]; rw [card_univ]; rw [nsmul_eq_mul]
      ring

Depends on / 依赖: Fintype, Fintype.card, Function, Function.update, Function.update_self, classical, eq_or_ne, ite_true, le_sup_iff, norm_le_pi_norm, sup_le_iff, sup_le_sup, update, update_self
-/
theorem norm_image_sub_le_of_bound (f : MultilinearMap 𝕜 E G)
    {C : Real} (hC : 0 <= C) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) (m₁ m₂ : forall i, E i) :
    ‖f m₁ - f m₂‖ <= C * Fintype.card ι * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ := by
  classical
  have A :
    forall i : ι,
      ∏ j, (if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖) <=
        ‖m₁ - m₂‖ * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) := by
    intro i
    calc
      ∏ j, (if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖) <=
          ∏ j : ι, Function.update (fun _ => max ‖m₁‖ ‖m₂‖) i ‖m₁ - m₂‖ j := by
        gcongr with j
        rcases eq_or_ne j i with rfl | h
        · simp only [ite_true, Function.update_self]
          exact norm_le_pi_norm (m₁ - m₂) _
        · simp [h, -le_sup_iff, -sup_le_iff, sup_le_sup, norm_le_pi_norm]
      _ = ‖m₁ - m₂‖ * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) := by
        rw [prod_update_of_mem (Finset.mem_univ _)]
        simp [card_univ_sdiff]
  calc
    ‖f m₁ - f m₂‖ <= C * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
      f.norm_image_sub_le_of_bound' hC H m₁ m₂
    _ <= C * ∑ _i, ‖m₁ - m₂‖ * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) := by gcongr; apply A
    _ = C * Fintype.card ι * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ := by
      rw [sum_const]; rw [card_univ]; rw [nsmul_eq_mul]
      ring

/--
theorem `continuous_of_bound` / 定理 `continuous_of_bound`

English:
theorem continuous_of_bound
  given: (f : MultilinearMap 𝕜 E G) (C : Real) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖)
  proof: by
  let D := max C 1
  have D_pos : 0 <= D := le_trans zero_le_one (le_max_right _ _)
  replace H (m) : ‖f m‖ <= D * ∏ i, ‖m i‖ :=
    (H m).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) <| by positivity)
  refine continuous_iff_continuousAt.2 fun m => ?_
  refine
    continuousAt_of_locally_lipschitz zero_lt_one
      (D * Fintype.card ι * (‖m‖ + 1) ^ (Fintype.card ι - 1)) fun m' h' => ?_
  rw [dist_eq_norm]; rw [dist_eq_norm]
  have : max ‖m'‖ ‖m‖ <= ‖m‖ + 1 := by
    simp [zero_le_one, norm_le_of_mem_closedBall (le_of_lt h')]
  calc
    ‖f m' - f m‖ <= D * Fintype.card ι * max ‖m'‖ ‖m‖ ^ (Fintype.card ι - 1) * ‖m' - m‖ :=
      f.norm_image_sub_le_of_bound D_pos H m' m
    _ <= D * Fintype.card ι * (‖m‖ + 1) ^ (Fintype.card ι - 1) * ‖m' - m‖ := by gcongr

中文:
定理 continuous_of_bound
  条件: (f : 多重线性映射 𝕜 E G) (C : 实数) (H : 对任意 m, ‖f m‖ <= C * ∏ i, ‖m i‖)
  证明: by
  let D := max C 1
  have D_pos : 0 <= D := le_trans zero_le_one (le_max_right _ _)
  replace H (m) : ‖f m‖ <= D * ∏ i, ‖m i‖ :=
    (H m).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) <| by positivity)
  refine continuous_iff_continuousAt.2 fun m => ?_
  refine
    continuousAt_of_locally_lipschitz zero_lt_one
      (D * Fintype.card ι * (‖m‖ + 1) ^ (Fintype.card ι - 1)) fun m' h' => ?_
  rw [dist_eq_norm]; rw [dist_eq_norm]
  have : max ‖m'‖ ‖m‖ <= ‖m‖ + 1 := by
    simp [zero_le_one, norm_le_of_mem_closedBall (le_of_lt h')]
  calc
    ‖f m' - f m‖ <= D * Fintype.card ι * max ‖m'‖ ‖m‖ ^ (Fintype.card ι - 1) * ‖m' - m‖ :=
      f.norm_image_sub_le_of_bound D_pos H m' m
    _ <= D * Fintype.card ι * (‖m‖ + 1) ^ (Fintype.card ι - 1) * ‖m' - m‖ := by gcongr

Depends on / 依赖: D_pos, Fintype, Fintype.card, continuousAt_of_locally_lipschitz, continuous_iff_continuousAt, dist_eq_norm, le_max_left, le_max_right, le_o, le_trans, mul_le_mul_of_nonneg_right, norm_le_of_mem_closedBall, replace, zero_le_one, zero_lt_one
-/
theorem continuous_of_bound (f : MultilinearMap 𝕜 E G) (C : Real) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) :
    Continuous f := by
  let D := max C 1
  have D_pos : 0 <= D := le_trans zero_le_one (le_max_right _ _)
  replace H (m) : ‖f m‖ <= D * ∏ i, ‖m i‖ :=
    (H m).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) <| by positivity)
  refine continuous_iff_continuousAt.2 fun m => ?_
  refine
    continuousAt_of_locally_lipschitz zero_lt_one
      (D * Fintype.card ι * (‖m‖ + 1) ^ (Fintype.card ι - 1)) fun m' h' => ?_
  rw [dist_eq_norm]; rw [dist_eq_norm]
  have : max ‖m'‖ ‖m‖ <= ‖m‖ + 1 := by
    simp [zero_le_one, norm_le_of_mem_closedBall (le_of_lt h')]
  calc
    ‖f m' - f m‖ <= D * Fintype.card ι * max ‖m'‖ ‖m‖ ^ (Fintype.card ι - 1) * ‖m' - m‖ :=
      f.norm_image_sub_le_of_bound D_pos H m' m
    _ <= D * Fintype.card ι * (‖m‖ + 1) ^ (Fintype.card ι - 1) * ‖m' - m‖ := by gcongr

/--
Definition of `mkContinuous` / `mkContinuous` 的定义

English:
definition mkContinuous
  signature: (f : MultilinearMap 𝕜 E G) (C : Real) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖)
  body: { f with cont := f.continuous_of_bound C H }

@[simp]

中文:
定义 mkContinuous
  签名: (f : 多重线性映射 𝕜 E G) (C : 实数) (H : 对任意 m, ‖f m‖ <= C * ∏ i, ‖m i‖)
  定义体: { f with cont := f.continuous_of_bound C H }

@[simp]

Depends on / 依赖: continuous_of_bound, f.continuous_of_bound
-/
def mkContinuous (f : MultilinearMap 𝕜 E G) (C : Real) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) :
    ContinuousMultilinearMap 𝕜 E G :=
  { f with cont := f.continuous_of_bound C H }

@[simp]
/--
theorem `coe_mkContinuous` / 定理 `coe_mkContinuous`

English:
theorem coe_mkContinuous
  given: (f : MultilinearMap 𝕜 E G) (C : Real) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖)
  proof: rfl

中文:
定理 coe_mkContinuous
  条件: (f : 多重线性映射 𝕜 E G) (C : 实数) (H : 对任意 m, ‖f m‖ <= C * ∏ i, ‖m i‖)
  证明: rfl
-/
theorem coe_mkContinuous (f : MultilinearMap 𝕜 E G) (C : Real) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) :
    ⇑(f.mkContinuous C H) = f :=
  rfl

/--
theorem `restr_norm_le` / 定理 `restr_norm_le`

English:
theorem restr_norm_le
  statement: {k n : Nat} (f : MultilinearMap 𝕜 (fun _ : Fin n => G) G')
  proof: by
  rw [mul_right_comm]; rw [mul_assoc]
  convert! H _ using 2
  simp only [apply_dite norm, Fintype.prod_dite, prod_const ‖z‖, Finset.card_univ,
    Fintype.card_of_subtype sᶜ fun _ => mem_compl, card_compl, Fintype.card_fin, hk, ←
    (s.orderIsoOfFin hk).symm.bijective.prod_comp fun x => ‖v x‖]
  convert! rfl

中文:
定理 restr_norm_le
  结论: {k n : 自然数} (f : 多重线性映射 𝕜 (fun _ : 有限集 n => G) G')
  证明: by
  rw [mul_right_comm]; rw [mul_assoc]
  convert! H _ using 2
  simp only [apply_dite norm, Fintype.prod_dite, prod_const ‖z‖, Finset.card_univ,
    Fintype.card_of_subtype sᶜ fun _ => mem_compl, card_compl, Fintype.card_fin, hk, ←
    (s.orderIsoOfFin hk).symm.bijective.prod_comp fun x => ‖v x‖]
  convert! rfl

Depends on / 依赖: Finset, Finset.card_univ, Fintype, Fintype.card_fin, Fintype.card_of_subtype, Fintype.prod_dite, apply_dite, bijective, card_compl, card_fin, card_of_subtype, card_univ, convert, mem_compl, mul_assoc, mul_right_comm, orderIsoOfFin, prod_comp, prod_const, prod_dite
-/
theorem restr_norm_le {k n : Nat} (f : MultilinearMap 𝕜 (fun _ : Fin n => G) G')
    (s : Finset (Fin n)) (hk : #s = k) (z : G) {C : Real} (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖)
    (v : Fin k -> G) : ‖f.restr s hk z v‖ <= C * ‖z‖ ^ (n - k) * ∏ i, ‖v i‖ := by
  rw [mul_right_comm]; rw [mul_assoc]
  convert! H _ using 2
  simp only [apply_dite norm, Fintype.prod_dite, prod_const ‖z‖, Finset.card_univ,
    Fintype.card_of_subtype sᶜ fun _ => mem_compl, card_compl, Fintype.card_fin, hk, ←
    (s.orderIsoOfFin hk).symm.bijective.prod_comp fun x => ‖v x‖]
  convert! rfl

end MultilinearMap

/-!
### Continuous multilinear maps

We define the norm `‖f‖` of a continuous multilinear map `f` in finitely many variables as the
smallest number such that `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖` for all `m`. We show that this
defines a normed space structure on `ContinuousMultilinearMap 𝕜 E G`.
-/

namespace ContinuousMultilinearMap

variable [Fintype ι]

/--
theorem `bound` / 定理 `bound`

English:
theorem bound
  given: (f : ContinuousMultilinearMap 𝕜 E G)
  proof: f.toMultilinearMap.exists_bound_of_continuous f.2

中文:
定理 bound
  条件: (f : 连续多重线性映射 𝕜 E G)
  证明: f.toMultilinearMap.exists_bound_of_continuous f.2

Depends on / 依赖: exists_bound_of_continuous, f.toMultilinearMap.exists_bound_of_continuous, toMultilinearMap
-/
theorem bound (f : ContinuousMultilinearMap 𝕜 E G) :
    exists C : Real, 0 < C ∧ forall m, ‖f m‖ <= C * ∏ i, ‖m i‖ :=
  f.toMultilinearMap.exists_bound_of_continuous f.2

open Real

/--
Definition of `opNorm` / `opNorm` 的定义

English:
definition opNorm
  signature: (f : ContinuousMultilinearMap 𝕜 E G)
  body: sInf { c | 0 <= (c : Real) ∧ forall m, ‖f m‖ <= c * ∏ i, ‖m i‖ }

中文:
定义 opNorm
  签名: (f : 连续多重线性映射 𝕜 E G)
  定义体: sInf { c | 0 <= (c : Real) ∧ forall m, ‖f m‖ <= c * ∏ i, ‖m i‖ }
-/
def opNorm (f : ContinuousMultilinearMap 𝕜 E G) : Real :=
  sInf { c | 0 <= (c : Real) ∧ forall m, ‖f m‖ <= c * ∏ i, ‖m i‖ }

/--
Instance `hasOpNorm` / 实例 `hasOpNorm`

English:
instance hasOpNorm
  signature: : Norm (ContinuousMultilinearMap 𝕜 E G)
  body: ⟨opNorm⟩

中文:
实例 hasOpNorm
  签名: : 范数 (连续多重线性映射 𝕜 E G)
  定义体: ⟨opNorm⟩

Depends on / 依赖: opNorm
-/
instance hasOpNorm : Norm (ContinuousMultilinearMap 𝕜 E G) :=
  ⟨opNorm⟩

/--
Instance `hasOpNorm'` / 实例 `hasOpNorm'`

English:
instance hasOpNorm'
  signature: : Norm (ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G')
  body: ContinuousMultilinearMap.hasOpNorm

中文:
实例 hasOpNorm'
  签名: : 范数 (连续多重线性映射 𝕜 (fun _ : ι => G) G')
  定义体: ContinuousMultilinearMap.hasOpNorm

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.hasOpNorm, hasOpNorm
-/
instance hasOpNorm' : Norm (ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G') :=
  ContinuousMultilinearMap.hasOpNorm

/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  given: (f : ContinuousMultilinearMap 𝕜 E G)
  proof: rfl

中文:
定理 norm_def
  条件: (f : 连续多重线性映射 𝕜 E G)
  证明: rfl
-/
theorem norm_def (f : ContinuousMultilinearMap 𝕜 E G) :
    ‖f‖ = sInf { c | 0 <= (c : Real) ∧ forall m, ‖f m‖ <= c * ∏ i, ‖m i‖ } :=
  rfl

-- So that invocations of `le_csInf` make sense: we show that the set of
-- bounds is nonempty and bounded below.
/--
theorem `bounds_nonempty` / 定理 `bounds_nonempty`

English:
theorem bounds_nonempty
  given: {f : ContinuousMultilinearMap 𝕜 E G}
  proof: let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_lt hMp, hMb⟩

中文:
定理 bounds_nonempty
  条件: {f : 连续多重线性映射 𝕜 E G}
  证明: let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_lt hMp, hMb⟩

Depends on / 依赖: f.bound, le_of_lt
-/
theorem bounds_nonempty {f : ContinuousMultilinearMap 𝕜 E G} :
    exists c, c in { c | 0 <= c ∧ forall m, ‖f m‖ <= c * ∏ i, ‖m i‖ } :=
  let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_lt hMp, hMb⟩

/--
theorem `bounds_bddBelow` / 定理 `bounds_bddBelow`

English:
theorem bounds_bddBelow
  given: {f : ContinuousMultilinearMap 𝕜 E G}
  proof: ⟨0, fun _ ⟨hn, _⟩ => hn⟩

中文:
定理 bounds_bddBelow
  条件: {f : 连续多重线性映射 𝕜 E G}
  证明: ⟨0, fun _ ⟨hn, _⟩ => hn⟩
-/
theorem bounds_bddBelow {f : ContinuousMultilinearMap 𝕜 E G} :
    BddBelow { c | 0 <= c ∧ forall m, ‖f m‖ <= c * ∏ i, ‖m i‖ } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩

/--
theorem `isLeast_opNorm` / 定理 `isLeast_opNorm`

English:
theorem isLeast_opNorm
  given: (f : ContinuousMultilinearMap 𝕜 E G)
  proof: by
  refine IsClosed.isLeast_csInf ?_ bounds_nonempty bounds_bddBelow
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact isClosed_Ici.inter (isClosed_iInter fun m => isClosed_le continuous_const (by fun_prop))

中文:
定理 isLeast_opNorm
  条件: (f : 连续多重线性映射 𝕜 E G)
  证明: by
  refine IsClosed.isLeast_csInf ?_ bounds_nonempty bounds_bddBelow
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact isClosed_Ici.inter (isClosed_iInter fun m => isClosed_le continuous_const (by fun_prop))

Depends on / 依赖: IsClosed, IsClosed.isLeast_csInf, Set.ofPred_and, Set.ofPred_forall, bounds_bddBelow, bounds_nonempty, continuous_const, fun_prop, isClosed_Ici, isClosed_Ici.inter, isClosed_iInter, isClosed_le, isLeast_csInf, ofPred_and, ofPred_forall
-/
theorem isLeast_opNorm (f : ContinuousMultilinearMap 𝕜 E G) :
    IsLeast {c : Real | 0 <= c ∧ forall m, ‖f m‖ <= c * ∏ i, ‖m i‖} ‖f‖ := by
  refine IsClosed.isLeast_csInf ?_ bounds_nonempty bounds_bddBelow
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact isClosed_Ici.inter (isClosed_iInter fun m => isClosed_le continuous_const (by fun_prop))

/--
theorem `opNorm_nonneg` / 定理 `opNorm_nonneg`

English:
theorem opNorm_nonneg
  given: (f : ContinuousMultilinearMap 𝕜 E G)
  statement: 0 <= ‖f‖
  proof: Real.sInf_nonneg fun _ ⟨hx, _⟩ => hx

中文:
定理 opNorm_nonneg
  条件: (f : 连续多重线性映射 𝕜 E G)
  结论: 0 <= ‖f‖
  证明: Real.sInf_nonneg fun _ ⟨hx, _⟩ => hx

Depends on / 依赖: Real.sInf_nonneg, sInf_nonneg
-/
theorem opNorm_nonneg (f : ContinuousMultilinearMap 𝕜 E G) : 0 <= ‖f‖ :=
  Real.sInf_nonneg fun _ ⟨hx, _⟩ => hx

/--
theorem `le_opNorm` / 定理 `le_opNorm`

English:
theorem le_opNorm
  given: (f : ContinuousMultilinearMap 𝕜 E G) (m : forall i, E i)
  proof: f.isLeast_opNorm.1.2 m

中文:
定理 le_opNorm
  条件: (f : 连续多重线性映射 𝕜 E G) (m : 对任意 i, E i)
  证明: f.isLeast_opNorm.1.2 m

Depends on / 依赖: f.isLeast_opNorm, isLeast_opNorm
-/
theorem le_opNorm (f : ContinuousMultilinearMap 𝕜 E G) (m : forall i, E i) :
    ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖ :=
  f.isLeast_opNorm.1.2 m

/--
theorem `le_mul_prod_of_opNorm_le_of_le` / 定理 `le_mul_prod_of_opNorm_le_of_le`

English:
theorem le_mul_prod_of_opNorm_le_of_le
  statement: {f : ContinuousMultilinearMap 𝕜 E G}
  proof: (f.le_opNorm m).trans by gcongr; exacts [f.opNorm_nonneg.trans hC, hm _]

中文:
定理 le_mul_prod_of_opNorm_le_of_le
  结论: {f : 连续多重线性映射 𝕜 E G}
  证明: (f.le_opNorm m).trans by gcongr; exacts [f.opNorm_nonneg.trans hC, hm _]

Depends on / 依赖: exacts, f.le_opNorm, f.opNorm_nonneg.trans, le_opNorm, opNorm_nonneg
-/
theorem le_mul_prod_of_opNorm_le_of_le {f : ContinuousMultilinearMap 𝕜 E G}
    {m : forall i, E i} {C : Real} {b : ι -> Real} (hC : ‖f‖ <= C) (hm : forall i, ‖m i‖ <= b i) :
    ‖f m‖ <= C * ∏ i, b i :=
(f.le_opNorm m).trans by gcongr; exacts [f.opNorm_nonneg.trans hC, hm _]

/--
theorem `le_opNorm_mul_prod_of_le` / 定理 `le_opNorm_mul_prod_of_le`

English:
theorem le_opNorm_mul_prod_of_le
  statement: (f : ContinuousMultilinearMap 𝕜 E G)
  proof: le_mul_prod_of_opNorm_le_of_le le_rfl hm

中文:
定理 le_opNorm_mul_prod_of_le
  结论: (f : 连续多重线性映射 𝕜 E G)
  证明: le_mul_prod_of_opNorm_le_of_le le_rfl hm

Depends on / 依赖: le_mul_prod_of_opNorm_le_of_le, le_rfl
-/
theorem le_opNorm_mul_prod_of_le (f : ContinuousMultilinearMap 𝕜 E G)
    {m : forall i, E i} {b : ι -> Real} (hm : forall i, ‖m i‖ <= b i) : ‖f m‖ <= ‖f‖ * ∏ i, b i :=
  le_mul_prod_of_opNorm_le_of_le le_rfl hm

/--
theorem `le_opNorm_mul_pow_card_of_le` / 定理 `le_opNorm_mul_pow_card_of_le`

English:
theorem le_opNorm_mul_pow_card_of_le
  given: (f : ContinuousMultilinearMap 𝕜 E G) {m b} (hm : ‖m‖ <= b)
  proof: by
  simpa only [prod_const] using! f.le_opNorm_mul_prod_of_le fun i => (norm_le_pi_norm m i).trans hm

中文:
定理 le_opNorm_mul_pow_card_of_le
  条件: (f : 连续多重线性映射 𝕜 E G) {m b} (hm : ‖m‖ <= b)
  证明: by
  simpa only [prod_const] using! f.le_opNorm_mul_prod_of_le fun i => (norm_le_pi_norm m i).trans hm

Depends on / 依赖: f.le_opNorm_mul_prod_of_le, le_opNorm_mul_prod_of_le, norm_le_pi_norm, prod_const
-/
theorem le_opNorm_mul_pow_card_of_le (f : ContinuousMultilinearMap 𝕜 E G) {m b} (hm : ‖m‖ <= b) :
    ‖f m‖ <= ‖f‖ * b ^ Fintype.card ι := by
  simpa only [prod_const] using! f.le_opNorm_mul_prod_of_le fun i => (norm_le_pi_norm m i).trans hm

/--
theorem `le_opNorm_mul_pow_of_le` / 定理 `le_opNorm_mul_pow_of_le`

English:
theorem le_opNorm_mul_pow_of_le
  statement: {n : Nat} {Ei : Fin n -> Type*} [forall i, SeminormedAddCommGroup (Ei i)]
  proof: by
  simpa only [Fintype.card_fin] using f.le_opNorm_mul_pow_card_of_le hm

中文:
定理 le_opNorm_mul_pow_of_le
  结论: {n : 自然数} {Ei : 有限集 n -> 类型} [对任意 i, SeminormedAddComm群 (Ei i)]
  证明: by
  simpa only [Fintype.card_fin] using f.le_opNorm_mul_pow_card_of_le hm

Depends on / 依赖: Fintype, Fintype.card_fin, card_fin, f.le_opNorm_mul_pow_card_of_le, le_opNorm_mul_pow_card_of_le
-/
theorem le_opNorm_mul_pow_of_le {n : Nat} {Ei : Fin n -> Type*} [forall i, SeminormedAddCommGroup (Ei i)]
    [forall i, NormedSpace 𝕜 (Ei i)] (f : ContinuousMultilinearMap 𝕜 Ei G) {m : forall i, Ei i} {b : Real}
    (hm : ‖m‖ <= b) : ‖f m‖ <= ‖f‖ * b ^ n := by
  simpa only [Fintype.card_fin] using f.le_opNorm_mul_pow_card_of_le hm

/--
theorem `le_of_opNorm_le` / 定理 `le_of_opNorm_le`

English:
theorem le_of_opNorm_le
  given: {f : ContinuousMultilinearMap 𝕜 E G} {C : Real} (h : ‖f‖ <= C) (m : forall i, E i)
  proof: le_mul_prod_of_opNorm_le_of_le h fun _ => le_rfl

中文:
定理 le_of_opNorm_le
  条件: {f : 连续多重线性映射 𝕜 E G} {C : 实数} (h : ‖f‖ <= C) (m : 对任意 i, E i)
  证明: le_mul_prod_of_opNorm_le_of_le h fun _ => le_rfl

Depends on / 依赖: le_mul_prod_of_opNorm_le_of_le, le_rfl
-/
theorem le_of_opNorm_le {f : ContinuousMultilinearMap 𝕜 E G} {C : Real} (h : ‖f‖ <= C) (m : forall i, E i) :
    ‖f m‖ <= C * ∏ i, ‖m i‖ :=
  le_mul_prod_of_opNorm_le_of_le h fun _ => le_rfl

/--
theorem `ratio_le_opNorm` / 定理 `ratio_le_opNorm`

English:
theorem ratio_le_opNorm
  given: (f : ContinuousMultilinearMap 𝕜 E G) (m : forall i, E i)
  proof: div_le_of_le_mul₀ (by positivity) (opNorm_nonneg _) (f.le_opNorm m)

中文:
定理 ratio_le_opNorm
  条件: (f : 连续多重线性映射 𝕜 E G) (m : 对任意 i, E i)
  证明: div_le_of_le_mul₀ (by positivity) (opNorm_nonneg _) (f.le_opNorm m)

Depends on / 依赖: f.le_opNorm, le_opNorm, opNorm_nonneg
-/
theorem ratio_le_opNorm (f : ContinuousMultilinearMap 𝕜 E G) (m : forall i, E i) :
    (‖f m‖ / ∏ i, ‖m i‖) <= ‖f‖ :=
  div_le_of_le_mul₀ (by positivity) (opNorm_nonneg _) (f.le_opNorm m)

/--
theorem `unit_le_opNorm` / 定理 `unit_le_opNorm`

English:
theorem unit_le_opNorm
  given: (f : ContinuousMultilinearMap 𝕜 E G) {m : forall i, E i} (h : ‖m‖ <= 1)
  proof: (le_opNorm_mul_pow_card_of_le f h).trans by simp

中文:
定理 unit_le_opNorm
  条件: (f : 连续多重线性映射 𝕜 E G) {m : 对任意 i, E i} (h : ‖m‖ <= 1)
  证明: (le_opNorm_mul_pow_card_of_le f h).trans by simp

Depends on / 依赖: le_opNorm_mul_pow_card_of_le
-/
theorem unit_le_opNorm (f : ContinuousMultilinearMap 𝕜 E G) {m : forall i, E i} (h : ‖m‖ <= 1) :
    ‖f m‖ <= ‖f‖ :=
(le_opNorm_mul_pow_card_of_le f h).trans by simp

/--
theorem `opNorm_le_bound` / 定理 `opNorm_le_bound`

English:
theorem opNorm_le_bound
  statement: {f : ContinuousMultilinearMap 𝕜 E G}
  proof: csInf_le bounds_bddBelow ⟨hMp, hM⟩

中文:
定理 opNorm_le_bound
  结论: {f : 连续多重线性映射 𝕜 E G}
  证明: csInf_le bounds_bddBelow ⟨hMp, hM⟩

Depends on / 依赖: bounds_bddBelow, csInf_le
-/
theorem opNorm_le_bound {f : ContinuousMultilinearMap 𝕜 E G}
    {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ i, ‖m i‖) : ‖f‖ <= M :=
  csInf_le bounds_bddBelow ⟨hMp, hM⟩

/--
theorem `opNorm_le_iff` / 定理 `opNorm_le_iff`

English:
theorem opNorm_le_iff
  given: {f : ContinuousMultilinearMap 𝕜 E G} {C : Real} (hC : 0 <= C)
  proof: ⟨fun h _ => le_of_opNorm_le h _, opNorm_le_bound hC⟩

中文:
定理 opNorm_le_iff
  条件: {f : 连续多重线性映射 𝕜 E G} {C : 实数} (hC : 0 <= C)
  证明: ⟨fun h _ => le_of_opNorm_le h _, opNorm_le_bound hC⟩

Depends on / 依赖: le_of_opNorm_le, opNorm_le_bound
-/
theorem opNorm_le_iff {f : ContinuousMultilinearMap 𝕜 E G} {C : Real} (hC : 0 <= C) :
    ‖f‖ <= C ↔ forall m, ‖f m‖ <= C * ∏ i, ‖m i‖ :=
  ⟨fun h _ => le_of_opNorm_le h _, opNorm_le_bound hC⟩

/--
theorem `opNorm_add_le` / 定理 `opNorm_add_le`

English:
theorem opNorm_add_le
  given: (f g : ContinuousMultilinearMap 𝕜 E G)
  statement: ‖f + g‖ <= ‖f‖ + ‖g‖
  proof: opNorm_le_bound (add_nonneg (opNorm_nonneg f) (opNorm_nonneg g)) fun x => by
    rw [add_mul]
    exact norm_add_le_of_le (le_opNorm _ _) (le_opNorm _ _)

中文:
定理 opNorm_add_le
  条件: (f g : 连续多重线性映射 𝕜 E G)
  结论: ‖f + g‖ <= ‖f‖ + ‖g‖
  证明: opNorm_le_bound (add_nonneg (opNorm_nonneg f) (opNorm_nonneg g)) fun x => by
    rw [add_mul]
    exact norm_add_le_of_le (le_opNorm _ _) (le_opNorm _ _)

Depends on / 依赖: add_mul, add_nonneg, le_opNorm, norm_add_le_of_le, opNorm_le_bound, opNorm_nonneg
-/
theorem opNorm_add_le (f g : ContinuousMultilinearMap 𝕜 E G) : ‖f + g‖ <= ‖f‖ + ‖g‖ :=
  opNorm_le_bound (add_nonneg (opNorm_nonneg f) (opNorm_nonneg g)) fun x => by
    rw [add_mul]
    exact norm_add_le_of_le (le_opNorm _ _) (le_opNorm _ _)

/--
theorem `opNorm_zero` / 定理 `opNorm_zero`

English:
theorem opNorm_zero
  statement: ‖(0 : ContinuousMultilinearMap 𝕜 E G)‖ = 0
  proof: (opNorm_nonneg _).antisymm' opNorm_le_bound le_rfl fun m => by simp

中文:
定理 opNorm_zero
  结论: ‖(0 : 连续多重线性映射 𝕜 E G)‖ = 0
  证明: (opNorm_nonneg _).antisymm' opNorm_le_bound le_rfl fun m => by simp

Depends on / 依赖: antisymm, le_rfl, opNorm_le_bound, opNorm_nonneg
-/
theorem opNorm_zero : ‖(0 : ContinuousMultilinearMap 𝕜 E G)‖ = 0 :=
(opNorm_nonneg _).antisymm' opNorm_le_bound le_rfl fun m => by simp

/--
theorem `opNorm_neg` / 定理 `opNorm_neg`

English:
theorem opNorm_neg
  given: (f : ContinuousMultilinearMap 𝕜 E G)
  statement: ‖-f‖ = ‖f‖
  proof: by simp [norm_def]

中文:
定理 opNorm_neg
  条件: (f : 连续多重线性映射 𝕜 E G)
  结论: ‖-f‖ = ‖f‖
  证明: by simp [norm_def]

Depends on / 依赖: norm_def
-/
theorem opNorm_neg (f : ContinuousMultilinearMap 𝕜 E G) : ‖-f‖ = ‖f‖ := by simp [norm_def]

section

variable {𝕜' : Type*} [SeminormedRing 𝕜'] [Module 𝕜' G] [IsBoundedSMul 𝕜' G] [SMulCommClass 𝕜 𝕜' G]

/--
theorem `opNorm_smul_le` / 定理 `opNorm_smul_le`

English:
theorem opNorm_smul_le
  given: (c : 𝕜') (f : ContinuousMultilinearMap 𝕜 E G)
  statement: ‖c • f‖ <= ‖c‖ * ‖f‖
  proof: (c • f).opNorm_le_bound (mul_nonneg (norm_nonneg _) (opNorm_nonneg _)) fun m => by
    grw [smul_apply, norm_smul_le, mul_assoc, le_opNorm]

中文:
定理 opNorm_smul_le
  条件: (c : 𝕜') (f : 连续多重线性映射 𝕜 E G)
  结论: ‖c • f‖ <= ‖c‖ * ‖f‖
  证明: (c • f).opNorm_le_bound (mul_nonneg (norm_nonneg _) (opNorm_nonneg _)) fun m => by
    grw [smul_apply, norm_smul_le, mul_assoc, le_opNorm]

Depends on / 依赖: le_opNorm, mul_assoc, mul_nonneg, norm_nonneg, norm_smul_le, opNorm_le_bound, opNorm_nonneg, smul_apply
-/
theorem opNorm_smul_le (c : 𝕜') (f : ContinuousMultilinearMap 𝕜 E G) : ‖c • f‖ <= ‖c‖ * ‖f‖ :=
  (c • f).opNorm_le_bound (mul_nonneg (norm_nonneg _) (opNorm_nonneg _)) fun m => by
    grw [smul_apply, norm_smul_le, mul_assoc, le_opNorm]

variable (𝕜 E G) in
/--
Definition of `seminorm` / `seminorm` 的定义

English:
definition seminorm
  signature: : Seminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G)
  body: .ofSMulLE norm opNorm_zero opNorm_add_le fun c f => f.opNorm_smul_le c

中文:
定义 seminorm
  签名: : 半范数 𝕜 (连续多重线性映射 𝕜 E G)
  定义体: .ofSMulLE norm opNorm_zero opNorm_add_le fun c f => f.opNorm_smul_le c
-/
protected def seminorm : Seminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G) :=
  .ofSMulLE norm opNorm_zero opNorm_add_le fun c f => f.opNorm_smul_le c

/--
lemma `uniformity_eq_seminorm` / 引理 `uniformity_eq_seminorm`

English:
lemma uniformity_eq_seminorm
  proof: by
  have A (f : ContinuousMultilinearMap 𝕜 E G × ContinuousMultilinearMap 𝕜 E G) :
      ‖-f.1 + f.2‖ = ‖f.1 - f.2‖ := by rw [← opNorm_neg, neg_add, neg_neg, sub_eq_add_neg]
  simp only [A]
  refine (ContinuousMultilinearMap.seminorm 𝕜 E G).uniformity_eq_of_hasBasis
    (ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall)
    ?_ fun (s, r) ⟨hs, hr⟩ => ?_
  · rcases NormedField.exists_lt_norm 𝕜 1 with ⟨c, hc⟩
    have hc₀ : 0 < ‖c‖ := one_pos.trans hc
    simp only [hasBasis_nhds_zero.mem_iff, Prod.exists]
    use 1, closedBall 0 ‖c‖, closedBall 0 1
    suffices forall f : ContinuousMultilinearMap 𝕜 E G, (forall x, ‖x‖ <= ‖c‖ -> ‖f x‖ <= 1) -> ‖f‖ <= 1 by
      simpa [NormedSpace.isVonNBounded_closedBall, closedBall_mem_nhds, Set.subset_def, Set.MapsTo]
    intro f hf
refine opNorm_le_bound (by positivity)
      f.1.bound_of_shell_of_continuous f.2 (fun _ => hc₀) (fun _ => hc) fun x hcx hx => ?_
    calc
‖f x‖ <= 1 := hf _ (pi_norm_le_iff_of_nonneg (norm_nonneg c)).2 fun i => (hx i).le
      _ = ∏ i : ι, 1 := by simp
      _ <= ∏ i, ‖x i‖ := by gcongr with i; simpa only [div_self hc₀.ne'] using hcx i
      _ = 1 * ∏ i, ‖x i‖ := (one_mul _).symm
  · rcases (NormedSpace.isVonNBounded_iff' _).1 hs with ⟨ε, hε⟩
    rcases exists_pos_mul_lt hr (ε ^ Fintype.card ι) with ⟨δ, hδ₀, hδ⟩
    refine ⟨δ, hδ₀, fun f hf x hx => ?_⟩
    simp only [Seminorm.mem_ball_zero, mem_closedBall_zero_iff] at hf ⊢
    replace hf : ‖f‖ <= δ := hf.le
    replace hx : ‖x‖ <= ε := hε x hx
    calc
      ‖f x‖ <= ‖f‖ * ε ^ Fintype.card ι := le_opNorm_mul_pow_card_of_le f hx
      _ <= δ * ε ^ Fintype.card ι := by have := (norm_nonneg x).trans hx; gcongr
      _ <= r := (mul_comm _ _).trans_le hδ.le

中文:
引理 uniformity_eq_seminorm
  证明: by
  have A (f : ContinuousMultilinearMap 𝕜 E G × ContinuousMultilinearMap 𝕜 E G) :
      ‖-f.1 + f.2‖ = ‖f.1 - f.2‖ := by rw [← opNorm_neg, neg_add, neg_neg, sub_eq_add_neg]
  simp only [A]
  refine (ContinuousMultilinearMap.seminorm 𝕜 E G).uniformity_eq_of_hasBasis
    (ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall)
    ?_ fun (s, r) ⟨hs, hr⟩ => ?_
  · rcases NormedField.exists_lt_norm 𝕜 1 with ⟨c, hc⟩
    have hc₀ : 0 < ‖c‖ := one_pos.trans hc
    simp only [hasBasis_nhds_zero.mem_iff, Prod.exists]
    use 1, closedBall 0 ‖c‖, closedBall 0 1
    suffices forall f : ContinuousMultilinearMap 𝕜 E G, (forall x, ‖x‖ <= ‖c‖ -> ‖f x‖ <= 1) -> ‖f‖ <= 1 by
      simpa [NormedSpace.isVonNBounded_closedBall, closedBall_mem_nhds, Set.subset_def, Set.MapsTo]
    intro f hf
refine opNorm_le_bound (by positivity)
      f.1.bound_of_shell_of_continuous f.2 (fun _ => hc₀) (fun _ => hc) fun x hcx hx => ?_
    calc
‖f x‖ <= 1 := hf _ (pi_norm_le_iff_of_nonneg (norm_nonneg c)).2 fun i => (hx i).le
      _ = ∏ i : ι, 1 := by simp
      _ <= ∏ i, ‖x i‖ := by gcongr with i; simpa only [div_self hc₀.ne'] using hcx i
      _ = 1 * ∏ i, ‖x i‖ := (one_mul _).symm
  · rcases (NormedSpace.isVonNBounded_iff' _).1 hs with ⟨ε, hε⟩
    rcases exists_pos_mul_lt hr (ε ^ Fintype.card ι) with ⟨δ, hδ₀, hδ⟩
    refine ⟨δ, hδ₀, fun f hf x hx => ?_⟩
    simp only [Seminorm.mem_ball_zero, mem_closedBall_zero_iff] at hf ⊢
    replace hf : ‖f‖ <= δ := hf.le
    replace hx : ‖x‖ <= ε := hε x hx
    calc
      ‖f x‖ <= ‖f‖ * ε ^ Fintype.card ι := le_opNorm_mul_pow_card_of_le f hx
      _ <= δ * ε ^ Fintype.card ι := by have := (norm_nonneg x).trans hx; gcongr
      _ <= r := (mul_comm _ _).trans_le hδ.le

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis, ContinuousMultilinearMap.seminorm, Metric, Metric.nhds_basis_closedBall, NormedField, NormedField.exists_lt_norm, exists_lt_norm, hasBasis_nhds_zero, hasBasis_nhds_zero.mem_iff, hasBasis_nhds_zero_of_basis, mem_iff, neg_add, neg_neg, nhds_basis_closedBall, one_pos, one_pos.trans, opNorm_neg, seminorm, sub_eq_add_neg
-/
lemma uniformity_eq_seminorm :
    𝓤 (ContinuousMultilinearMap 𝕜 E G) = ⨅ r > 0, 𝓟 {f | ‖-f.1 + f.2‖ < r} := by
  have A (f : ContinuousMultilinearMap 𝕜 E G × ContinuousMultilinearMap 𝕜 E G) :
      ‖-f.1 + f.2‖ = ‖f.1 - f.2‖ := by rw [← opNorm_neg, neg_add, neg_neg, sub_eq_add_neg]
  simp only [A]
  refine (ContinuousMultilinearMap.seminorm 𝕜 E G).uniformity_eq_of_hasBasis
    (ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall)
    ?_ fun (s, r) ⟨hs, hr⟩ => ?_
  · rcases NormedField.exists_lt_norm 𝕜 1 with ⟨c, hc⟩
    have hc₀ : 0 < ‖c‖ := one_pos.trans hc
    simp only [hasBasis_nhds_zero.mem_iff, Prod.exists]
    use 1, closedBall 0 ‖c‖, closedBall 0 1
    suffices forall f : ContinuousMultilinearMap 𝕜 E G, (forall x, ‖x‖ <= ‖c‖ -> ‖f x‖ <= 1) -> ‖f‖ <= 1 by
      simpa [NormedSpace.isVonNBounded_closedBall, closedBall_mem_nhds, Set.subset_def, Set.MapsTo]
    intro f hf
refine opNorm_le_bound (by positivity)
      f.1.bound_of_shell_of_continuous f.2 (fun _ => hc₀) (fun _ => hc) fun x hcx hx => ?_
    calc
‖f x‖ <= 1 := hf _ (pi_norm_le_iff_of_nonneg (norm_nonneg c)).2 fun i => (hx i).le
      _ = ∏ i : ι, 1 := by simp
      _ <= ∏ i, ‖x i‖ := by gcongr with i; simpa only [div_self hc₀.ne'] using hcx i
      _ = 1 * ∏ i, ‖x i‖ := (one_mul _).symm
  · rcases (NormedSpace.isVonNBounded_iff' _).1 hs with ⟨ε, hε⟩
    rcases exists_pos_mul_lt hr (ε ^ Fintype.card ι) with ⟨δ, hδ₀, hδ⟩
    refine ⟨δ, hδ₀, fun f hf x hx => ?_⟩
    simp only [Seminorm.mem_ball_zero, mem_closedBall_zero_iff] at hf ⊢
    replace hf : ‖f‖ <= δ := hf.le
    replace hx : ‖x‖ <= ε := hε x hx
    calc
      ‖f x‖ <= ‖f‖ * ε ^ Fintype.card ι := le_opNorm_mul_pow_card_of_le f hx
      _ <= δ * ε ^ Fintype.card ι := by have := (norm_nonneg x).trans hx; gcongr
      _ <= r := (mul_comm _ _).trans_le hδ.le

/--
Instance `instPseudoMetricSpace` / 实例 `instPseudoMetricSpace`

English:
instance instPseudoMetricSpace
  signature: : PseudoMetricSpace (ContinuousMultilinearMap 𝕜 E G)
  body: .replaceUniformity
    (ContinuousMultilinearMap.seminorm 𝕜 E G).toSeminormedAddCommGroup.toPseudoMetricSpace
    uniformity_eq_seminorm

中文:
实例 instPseudoMetricSpace
  签名: : 伪度量空间 (连续多重线性映射 𝕜 E G)
  定义体: .replaceUniformity
    (ContinuousMultilinearMap.seminorm 𝕜 E G).toSeminormedAddCommGroup.toPseudoMetricSpace
    uniformity_eq_seminorm

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.seminorm, replaceUniformity, seminorm, toPseudoMetricSpace, toSeminormedAddCommGroup, toSeminormedAddCommGroup.toPseudoMetricSpace, uniformity_eq_seminorm
-/
instance instPseudoMetricSpace : PseudoMetricSpace (ContinuousMultilinearMap 𝕜 E G) :=
  .replaceUniformity
    (ContinuousMultilinearMap.seminorm 𝕜 E G).toSeminormedAddCommGroup.toPseudoMetricSpace
    uniformity_eq_seminorm

/--
Instance `seminormedAddCommGroup` / 实例 `seminormedAddCommGroup`

English:
instance seminormedAddCommGroup
  signature: :
  body: ⟨fun _ _ => rfl⟩

中文:
实例 seminormedAddCommGroup
  签名: :
  定义体: ⟨fun _ _ => rfl⟩
-/
instance seminormedAddCommGroup :
    SeminormedAddCommGroup (ContinuousMultilinearMap 𝕜 E G) := ⟨fun _ _ => rfl⟩

/--
Instance `seminormedAddCommGroup'` / 实例 `seminormedAddCommGroup'`

English:
instance seminormedAddCommGroup'
  signature: :
  body: ContinuousMultilinearMap.seminormedAddCommGroup

中文:
实例 seminormedAddCommGroup'
  签名: :
  定义体: ContinuousMultilinearMap.seminormedAddCommGroup

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.seminormedAddCommGroup, seminormedAddCommGroup
-/
instance seminormedAddCommGroup' :
    SeminormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G') :=
  ContinuousMultilinearMap.seminormedAddCommGroup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsBoundedSMul 𝕜' (ContinuousMultilinearMap 𝕜 E G)
  body: .of_norm_smul_le opNorm_smul_le

中文:
实例 :
  签名: 是BoundedSMul 𝕜' (连续多重线性映射 𝕜 E G)
  定义体: .of_norm_smul_le opNorm_smul_le

Depends on / 依赖: of_norm_smul_le, opNorm_smul_le
-/
instance : IsBoundedSMul 𝕜' (ContinuousMultilinearMap 𝕜 E G) := .of_norm_smul_le opNorm_smul_le

section NormedField
variable {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' G] [SMulCommClass 𝕜 𝕜' G]

/--
Instance `normedSpace` / 实例 `normedSpace`

English:
instance normedSpace
  signature: : NormedSpace 𝕜' (ContinuousMultilinearMap 𝕜 E G)
  body: ⟨fun c f => f.opNorm_smul_le c⟩

中文:
实例 normedSpace
  签名: : 赋范空间 𝕜' (连续多重线性映射 𝕜 E G)
  定义体: ⟨fun c f => f.opNorm_smul_le c⟩

Depends on / 依赖: f.opNorm_smul_le, opNorm_smul_le
-/
instance normedSpace : NormedSpace 𝕜' (ContinuousMultilinearMap 𝕜 E G) :=
  ⟨fun c f => f.opNorm_smul_le c⟩

/--
Instance `normedSpace'` / 实例 `normedSpace'`

English:
instance normedSpace'
  signature: : NormedSpace 𝕜' (ContinuousMultilinearMap 𝕜 (fun _ : ι => G') G)
  body: ContinuousMultilinearMap.normedSpace

中文:
实例 normedSpace'
  签名: : 赋范空间 𝕜' (连续多重线性映射 𝕜 (fun _ : ι => G') G)
  定义体: ContinuousMultilinearMap.normedSpace

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.normedSpace, normedSpace
-/
instance normedSpace' : NormedSpace 𝕜' (ContinuousMultilinearMap 𝕜 (fun _ : ι => G') G) :=
  ContinuousMultilinearMap.normedSpace

end NormedField

/--
theorem `le_opNNNorm` / 定理 `le_opNNNorm`

English:
theorem le_opNNNorm
  given: (f : ContinuousMultilinearMap 𝕜 E G) (m : forall i, E i)
  proof: NNReal.coe_le_coe.1 by
    push_cast
    exact f.le_opNorm m

中文:
定理 le_opNNNorm
  条件: (f : 连续多重线性映射 𝕜 E G) (m : 对任意 i, E i)
  证明: NNReal.coe_le_coe.1 by
    push_cast
    exact f.le_opNorm m

Depends on / 依赖: NNReal, NNReal.coe_le_coe, coe_le_coe, f.le_opNorm, le_opNorm
-/
theorem le_opNNNorm (f : ContinuousMultilinearMap 𝕜 E G) (m : forall i, E i) :
    ‖f m‖₊ <= ‖f‖₊ * ∏ i, ‖m i‖₊ :=
NNReal.coe_le_coe.1 by
    push_cast
    exact f.le_opNorm m

/--
theorem `le_of_opNNNorm_le` / 定理 `le_of_opNNNorm_le`

English:
theorem le_of_opNNNorm_le
  statement: (f : ContinuousMultilinearMap 𝕜 E G)
  proof: (f.le_opNNNorm m).trans mul_le_mul' h le_rfl

中文:
定理 le_of_opNNNorm_le
  结论: (f : 连续多重线性映射 𝕜 E G)
  证明: (f.le_opNNNorm m).trans mul_le_mul' h le_rfl

Depends on / 依赖: f.le_opNNNorm, le_opNNNorm, le_rfl, mul_le_mul
-/
theorem le_of_opNNNorm_le (f : ContinuousMultilinearMap 𝕜 E G)
    {C : Real>=0} (h : ‖f‖₊ <= C) (m : forall i, E i) : ‖f m‖₊ <= C * ∏ i, ‖m i‖₊ :=
(f.le_opNNNorm m).trans mul_le_mul' h le_rfl

/--
theorem `opNNNorm_le_iff` / 定理 `opNNNorm_le_iff`

English:
theorem opNNNorm_le_iff
  given: {f : ContinuousMultilinearMap 𝕜 E G} {C : Real>=0}
  proof: by
  simp only [← NNReal.coe_le_coe]; simp [opNorm_le_iff C.coe_nonneg, NNReal.coe_prod]

中文:
定理 opNNNorm_le_iff
  条件: {f : 连续多重线性映射 𝕜 E G} {C : 实数>=0}
  证明: by
  simp only [← NNReal.coe_le_coe]; simp [opNorm_le_iff C.coe_nonneg, NNReal.coe_prod]

Depends on / 依赖: C.coe_nonneg, NNReal, NNReal.coe_le_coe, NNReal.coe_prod, coe_le_coe, coe_nonneg, coe_prod, opNorm_le_iff
-/
theorem opNNNorm_le_iff {f : ContinuousMultilinearMap 𝕜 E G} {C : Real>=0} :
    ‖f‖₊ <= C ↔ forall m, ‖f m‖₊ <= C * ∏ i, ‖m i‖₊ := by
  simp only [← NNReal.coe_le_coe]; simp [opNorm_le_iff C.coe_nonneg, NNReal.coe_prod]

/--
theorem `isLeast_opNNNorm` / 定理 `isLeast_opNNNorm`

English:
theorem isLeast_opNNNorm
  given: (f : ContinuousMultilinearMap 𝕜 E G)
  proof: by
  simpa only [← opNNNorm_le_iff] using! isLeast_Ici

中文:
定理 isLeast_opNNNorm
  条件: (f : 连续多重线性映射 𝕜 E G)
  证明: by
  simpa only [← opNNNorm_le_iff] using! isLeast_Ici

Depends on / 依赖: isLeast_Ici, opNNNorm_le_iff
-/
theorem isLeast_opNNNorm (f : ContinuousMultilinearMap 𝕜 E G) :
    IsLeast {C : Real>=0 | forall m, ‖f m‖₊ <= C * ∏ i, ‖m i‖₊} ‖f‖₊ := by
  simpa only [← opNNNorm_le_iff] using! isLeast_Ici

/--
theorem `opNNNorm_prod` / 定理 `opNNNorm_prod`

English:
theorem opNNNorm_prod
  given: (f : ContinuousMultilinearMap 𝕜 E G) (g : ContinuousMultilinearMap 𝕜 E G')
  proof: eq_of_forall_ge_iff fun _ => by
    simp only [opNNNorm_le_iff, prod_apply, Prod.nnnorm_def, max_le_iff, forall_and]

中文:
定理 opNNNorm_prod
  条件: (f : 连续多重线性映射 𝕜 E G) (g : 连续多重线性映射 𝕜 E G')
  证明: eq_of_forall_ge_iff fun _ => by
    simp only [opNNNorm_le_iff, prod_apply, Prod.nnnorm_def, max_le_iff, forall_and]

Depends on / 依赖: Prod.nnnorm_def, eq_of_forall_ge_iff, forall_and, max_le_iff, nnnorm_def, opNNNorm_le_iff, prod_apply
-/
theorem opNNNorm_prod (f : ContinuousMultilinearMap 𝕜 E G) (g : ContinuousMultilinearMap 𝕜 E G') :
    ‖f.prod g‖₊ = max ‖f‖₊ ‖g‖₊ :=
  eq_of_forall_ge_iff fun _ => by
    simp only [opNNNorm_le_iff, prod_apply, Prod.nnnorm_def, max_le_iff, forall_and]

/--
theorem `opNorm_prod` / 定理 `opNorm_prod`

English:
theorem opNorm_prod
  given: (f : ContinuousMultilinearMap 𝕜 E G) (g : ContinuousMultilinearMap 𝕜 E G')
  proof: congr_arg NNReal.toReal (opNNNorm_prod f g)

中文:
定理 opNorm_prod
  条件: (f : 连续多重线性映射 𝕜 E G) (g : 连续多重线性映射 𝕜 E G')
  证明: congr_arg NNReal.toReal (opNNNorm_prod f g)

Depends on / 依赖: NNReal, NNReal.toReal, congr_arg, opNNNorm_prod, toReal
-/
theorem opNorm_prod (f : ContinuousMultilinearMap 𝕜 E G) (g : ContinuousMultilinearMap 𝕜 E G') :
    ‖f.prod g‖ = max ‖f‖ ‖g‖ :=
  congr_arg NNReal.toReal (opNNNorm_prod f g)

/--
theorem `opNNNorm_pi` / 定理 `opNNNorm_pi`

English:
theorem opNNNorm_pi
  proof: eq_of_forall_ge_iff fun _ => by simpa [opNNNorm_le_iff, pi_nnnorm_le_iff] using forall_comm

中文:
定理 opNNNorm_pi
  证明: eq_of_forall_ge_iff fun _ => by simpa [opNNNorm_le_iff, pi_nnnorm_le_iff] using forall_comm

Depends on / 依赖: eq_of_forall_ge_iff, forall_comm, opNNNorm_le_iff, pi_nnnorm_le_iff
-/
theorem opNNNorm_pi
    [forall i', SeminormedAddCommGroup (E' i')] [forall i', NormedSpace 𝕜 (E' i')]
    (f : forall i', ContinuousMultilinearMap 𝕜 E (E' i')) : ‖pi f‖₊ = ‖f‖₊ :=
  eq_of_forall_ge_iff fun _ => by simpa [opNNNorm_le_iff, pi_nnnorm_le_iff] using forall_comm

/--
theorem `opNorm_pi` / 定理 `opNorm_pi`

English:
theorem opNorm_pi
  statement: {ι' : Type v'} [Fintype ι'] {E' : ι' -> Type wE'}
  proof: congr_arg NNReal.toReal (opNNNorm_pi f)

中文:
定理 opNorm_pi
  结论: {ι' : 类型v'} [有限类型 ι'] {E' : ι' -> 类型 wE'}
  证明: congr_arg NNReal.toReal (opNNNorm_pi f)

Depends on / 依赖: NNReal, NNReal.toReal, congr_arg, opNNNorm_pi, toReal
-/
theorem opNorm_pi {ι' : Type v'} [Fintype ι'] {E' : ι' -> Type wE'}
    [forall i', SeminormedAddCommGroup (E' i')] [forall i', NormedSpace 𝕜 (E' i')]
    (f : forall i', ContinuousMultilinearMap 𝕜 E (E' i')) :
    ‖pi f‖ = ‖f‖ :=
  congr_arg NNReal.toReal (opNNNorm_pi f)

section

@[simp]
/--
theorem `norm_ofSubsingleton` / 定理 `norm_ofSubsingleton`

English:
theorem norm_ofSubsingleton
  given: [Subsingleton ι] (i : ι) (f : G ->L[𝕜] G')
  proof: by
  let : Unique ι := uniqueOfSubsingleton i
  simp [norm_def, ContinuousLinearMap.norm_def, (Equiv.funUnique _ _).symm.surjective.forall]

@[simp]

中文:
定理 norm_ofSubsingleton
  条件: [子单例 ι] (i : ι) (f : G ->L[𝕜] G')
  证明: by
  let : Unique ι := uniqueOfSubsingleton i
  simp [norm_def, ContinuousLinearMap.norm_def, (Equiv.funUnique _ _).symm.surjective.forall]

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.norm_def, Equiv.funUnique, Unique, funUnique, norm_def, surjective, symm.surjective.forall, uniqueOfSubsingleton
-/
theorem norm_ofSubsingleton [Subsingleton ι] (i : ι) (f : G ->L[𝕜] G') :
    ‖ofSubsingleton 𝕜 G G' i f‖ = ‖f‖ := by
  let : Unique ι := uniqueOfSubsingleton i
  simp [norm_def, ContinuousLinearMap.norm_def, (Equiv.funUnique _ _).symm.surjective.forall]

@[simp]
/--
theorem `nnnorm_ofSubsingleton` / 定理 `nnnorm_ofSubsingleton`

English:
theorem nnnorm_ofSubsingleton
  given: [Subsingleton ι] (i : ι) (f : G ->L[𝕜] G')
  proof: NNReal.eq norm_ofSubsingleton i f

中文:
定理 nnnorm_ofSubsingleton
  条件: [子单例 ι] (i : ι) (f : G ->L[𝕜] G')
  证明: NNReal.eq norm_ofSubsingleton i f

Depends on / 依赖: NNReal, NNReal.eq, norm_ofSubsingleton
-/
theorem nnnorm_ofSubsingleton [Subsingleton ι] (i : ι) (f : G ->L[𝕜] G') :
    ‖ofSubsingleton 𝕜 G G' i f‖₊ = ‖f‖₊ :=
NNReal.eq norm_ofSubsingleton i f

variable (𝕜 G)

/-- Linear isometry between continuous linear maps from `G` to `G'`
and continuous `1`-multilinear maps from `G` to `G'`. -/
@[simps apply symm_apply]
/--
Definition of `ofSubsingletonₗᵢ` / `ofSubsingletonₗᵢ` 的定义

English:
definition ofSubsingletonₗᵢ
  signature: [Subsingleton ι] (i : ι)
  body: { ofSubsingleton 𝕜 G G' i with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    norm_map' := norm_ofSubsingleton i }

中文:
定义 ofSubsingletonₗᵢ
  签名: [子单例 ι] (i : ι)
  定义体: { ofSubsingleton 𝕜 G G' i with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    norm_map' := norm_ofSubsingleton i }

Depends on / 依赖: map_add, map_smul, norm_map, norm_ofSubsingleton, ofSubsingleton
-/
def ofSubsingletonₗᵢ [Subsingleton ι] (i : ι) :
    (G ->L[𝕜] G') ≃ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G' :=
  { ofSubsingleton 𝕜 G G' i with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    norm_map' := norm_ofSubsingleton i }

/--
theorem `norm_ofSubsingleton_id_le` / 定理 `norm_ofSubsingleton_id_le`

English:
theorem norm_ofSubsingleton_id_le
  given: [Subsingleton ι] (i : ι)
  proof: by
  rw [norm_ofSubsingleton]
  apply ContinuousLinearMap.norm_id_le

中文:
定理 norm_ofSubsingleton_id_le
  条件: [子单例 ι] (i : ι)
  证明: by
  rw [norm_ofSubsingleton]
  apply ContinuousLinearMap.norm_id_le

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.norm_id_le, norm_id_le, norm_ofSubsingleton
-/
theorem norm_ofSubsingleton_id_le [Subsingleton ι] (i : ι) :
    ‖ofSubsingleton 𝕜 G G i (.id _ _)‖ <= 1 := by
  rw [norm_ofSubsingleton]
  apply ContinuousLinearMap.norm_id_le

/--
theorem `nnnorm_ofSubsingleton_id_le` / 定理 `nnnorm_ofSubsingleton_id_le`

English:
theorem nnnorm_ofSubsingleton_id_le
  given: [Subsingleton ι] (i : ι)
  proof: norm_ofSubsingleton_id_le _ _ _

中文:
定理 nnnorm_ofSubsingleton_id_le
  条件: [子单例 ι] (i : ι)
  证明: norm_ofSubsingleton_id_le _ _ _

Depends on / 依赖: norm_ofSubsingleton_id_le
-/
theorem nnnorm_ofSubsingleton_id_le [Subsingleton ι] (i : ι) :
    ‖ofSubsingleton 𝕜 G G i (.id _ _)‖₊ <= 1 :=
  norm_ofSubsingleton_id_le _ _ _

variable {G} (E)

@[simp]
/--
theorem `norm_constOfIsEmpty` / 定理 `norm_constOfIsEmpty`

English:
theorem norm_constOfIsEmpty
  given: [IsEmpty ι] (x : G)
  statement: ‖constOfIsEmpty 𝕜 E x‖ = ‖x‖
  proof: by
  apply le_antisymm
  · refine opNorm_le_bound (norm_nonneg _) fun x => ?_
    rw [Fintype.prod_empty]; rw [mul_one]; rw [constOfIsEmpty_apply]
  · simpa using (constOfIsEmpty 𝕜 E x).le_opNorm 0

@[simp]

中文:
定理 norm_constOfIsEmpty
  条件: [是空 ι] (x : G)
  结论: ‖constOfIsEmpty 𝕜 E x‖ = ‖x‖
  证明: by
  apply le_antisymm
  · refine opNorm_le_bound (norm_nonneg _) fun x => ?_
    rw [Fintype.prod_empty]; rw [mul_one]; rw [constOfIsEmpty_apply]
  · simpa using (constOfIsEmpty 𝕜 E x).le_opNorm 0

@[simp]

Depends on / 依赖: Fintype, Fintype.prod_empty, constOfIsEmpty, constOfIsEmpty_apply, le_antisymm, le_opNorm, mul_one, norm_nonneg, opNorm_le_bound, prod_empty
-/
theorem norm_constOfIsEmpty [IsEmpty ι] (x : G) : ‖constOfIsEmpty 𝕜 E x‖ = ‖x‖ := by
  apply le_antisymm
  · refine opNorm_le_bound (norm_nonneg _) fun x => ?_
    rw [Fintype.prod_empty]; rw [mul_one]; rw [constOfIsEmpty_apply]
  · simpa using (constOfIsEmpty 𝕜 E x).le_opNorm 0

@[simp]
/--
theorem `nnnorm_constOfIsEmpty` / 定理 `nnnorm_constOfIsEmpty`

English:
theorem nnnorm_constOfIsEmpty
  given: [IsEmpty ι] (x : G)
  statement: ‖constOfIsEmpty 𝕜 E x‖₊ = ‖x‖₊
  proof: NNReal.eq norm_constOfIsEmpty _ _ _

中文:
定理 nnnorm_constOfIsEmpty
  条件: [是空 ι] (x : G)
  结论: ‖constOfIsEmpty 𝕜 E x‖₊ = ‖x‖₊
  证明: NNReal.eq norm_constOfIsEmpty _ _ _

Depends on / 依赖: NNReal, NNReal.eq, norm_constOfIsEmpty
-/
theorem nnnorm_constOfIsEmpty [IsEmpty ι] (x : G) : ‖constOfIsEmpty 𝕜 E x‖₊ = ‖x‖₊ :=
NNReal.eq norm_constOfIsEmpty _ _ _

end

section

variable (𝕜 E E' G G')

/-- `ContinuousMultilinearMap.prod` as a `LinearIsometryEquiv`. -/
@[simps]
/--
Definition of `prodL` / `prodL` 的定义

English:
definition prodL
  signature: :
  body: prodEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := opNorm_prod f.1 f.2

中文:
定义 prodL
  签名: :
  定义体: prodEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := opNorm_prod f.1 f.2

Depends on / 依赖: prodEquiv
-/
def prodL :
    ContinuousMultilinearMap 𝕜 E G × ContinuousMultilinearMap 𝕜 E G' ≃ₗᵢ[𝕜]
      ContinuousMultilinearMap 𝕜 E (G × G') where
  __ := prodEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := opNorm_prod f.1 f.2

/-- `ContinuousMultilinearMap.pi` as a `LinearIsometryEquiv`. -/
@[simps! apply symm_apply]
/--
Definition of `piₗᵢ` / `piₗᵢ` 的定义

English:
definition piₗᵢ
  signature: {ι' : Type v'} [Fintype ι'] {E' : ι' -> Type wE'} [forall i', NormedAddCommGroup (E' i')]
  body: piLinearEquiv
  norm_map' := opNorm_pi

中文:
定义 piₗᵢ
  签名: {ι' : 类型v'} [有限类型 ι'] {E' : ι' -> 类型 wE'} [对任意 i', 赋范交换加群 (E' i')]
  定义体: piLinearEquiv
  norm_map' := opNorm_pi

Depends on / 依赖: piLinearEquiv
-/
def piₗᵢ {ι' : Type v'} [Fintype ι'] {E' : ι' -> Type wE'} [forall i', NormedAddCommGroup (E' i')]
    [forall i', NormedSpace 𝕜 (E' i')] :
    (Π i', ContinuousMultilinearMap 𝕜 E (E' i'))
      ≃ₗᵢ[𝕜] (ContinuousMultilinearMap 𝕜 E (Π i, E' i)) where
  toLinearEquiv := piLinearEquiv
  norm_map' := opNorm_pi

end

end

section RestrictScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
variable [NormedSpace 𝕜' G] [IsScalarTower 𝕜' 𝕜 G]
variable [forall i, NormedSpace 𝕜' (E i)] [forall i, IsScalarTower 𝕜' 𝕜 (E i)]

@[simp]
/--
theorem `norm_restrictScalars` / 定理 `norm_restrictScalars`

English:
theorem norm_restrictScalars
  given: (f : ContinuousMultilinearMap 𝕜 E G)
  proof: rfl

中文:
定理 norm_restrictScalars
  条件: (f : 连续多重线性映射 𝕜 E G)
  证明: rfl
-/
theorem norm_restrictScalars (f : ContinuousMultilinearMap 𝕜 E G) :
    ‖f.restrictScalars 𝕜'‖ = ‖f‖ :=
  rfl

variable (𝕜')

/--
Definition of `restrictScalarsₗᵢ` / `restrictScalarsₗᵢ` 的定义

English:
definition restrictScalarsₗᵢ
  signature: : ContinuousMultilinearMap 𝕜 E G ->ₗᵢ[𝕜'] ContinuousMultilinearMap 𝕜' E G where
  body: restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

中文:
定义 restrictScalarsₗᵢ
  签名: : 连续多重线性映射 𝕜 E G ->ₗᵢ[𝕜'] 连续多重线性映射 𝕜' E G where
  定义体: restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

Depends on / 依赖: restrictScalars
-/
def restrictScalarsₗᵢ : ContinuousMultilinearMap 𝕜 E G ->ₗᵢ[𝕜'] ContinuousMultilinearMap 𝕜' E G where
  toFun := restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

end RestrictScalars

/--
theorem `norm_image_sub_le'` / 定理 `norm_image_sub_le'`

English:
theorem norm_image_sub_le'
  given: [DecidableEq ι] (f : ContinuousMultilinearMap 𝕜 E G) (m₁ m₂ : forall i, E i)
  proof: f.toMultilinearMap.norm_image_sub_le_of_bound' (norm_nonneg _) f.le_opNorm _ _

中文:
定理 norm_image_sub_le'
  条件: [DecidableEq ι] (f : 连续多重线性映射 𝕜 E G) (m₁ m₂ : 对任意 i, E i)
  证明: f.toMultilinearMap.norm_image_sub_le_of_bound' (norm_nonneg _) f.le_opNorm _ _

Depends on / 依赖: f.le_opNorm, f.toMultilinearMap.norm_image_sub_le_of_bound, le_opNorm, norm_image_sub_le_of_bound, norm_nonneg, toMultilinearMap
-/
theorem norm_image_sub_le' [DecidableEq ι] (f : ContinuousMultilinearMap 𝕜 E G) (m₁ m₂ : forall i, E i) :
    ‖f m₁ - f m₂‖ <= ‖f‖ * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
  f.toMultilinearMap.norm_image_sub_le_of_bound' (norm_nonneg _) f.le_opNorm _ _

/--
theorem `norm_image_sub_le` / 定理 `norm_image_sub_le`

English:
theorem norm_image_sub_le
  given: (f : ContinuousMultilinearMap 𝕜 E G) (m₁ m₂ : forall i, E i)
  proof: f.toMultilinearMap.norm_image_sub_le_of_bound (norm_nonneg _) f.le_opNorm _ _

中文:
定理 norm_image_sub_le
  条件: (f : 连续多重线性映射 𝕜 E G) (m₁ m₂ : 对任意 i, E i)
  证明: f.toMultilinearMap.norm_image_sub_le_of_bound (norm_nonneg _) f.le_opNorm _ _

Depends on / 依赖: f.le_opNorm, f.toMultilinearMap.norm_image_sub_le_of_bound, le_opNorm, norm_image_sub_le_of_bound, norm_nonneg, toMultilinearMap
-/
theorem norm_image_sub_le (f : ContinuousMultilinearMap 𝕜 E G) (m₁ m₂ : forall i, E i) :
    ‖f m₁ - f m₂‖ <= ‖f‖ * Fintype.card ι * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ :=
  f.toMultilinearMap.norm_image_sub_le_of_bound (norm_nonneg _) f.le_opNorm _ _

end ContinuousMultilinearMap

variable [Fintype ι]

/--
theorem `MultilinearMap.mkContinuous_norm_le` / 定理 `MultilinearMap.mkContinuous_norm_le`

English:
theorem MultilinearMap.mkContinuous_norm_le
  statement: (f : MultilinearMap 𝕜 E G) {C : Real} (hC : 0 <= C)
  proof: ContinuousMultilinearMap.opNorm_le_bound hC fun m => H m

中文:
定理 多重线性映射.mkContinuous_norm_le
  结论: (f : 多重线性映射 𝕜 E G) {C : 实数} (hC : 0 <= C)
  证明: ContinuousMultilinearMap.opNorm_le_bound hC fun m => H m

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.opNorm_le_bound, opNorm_le_bound
-/
theorem MultilinearMap.mkContinuous_norm_le (f : MultilinearMap 𝕜 E G) {C : Real} (hC : 0 <= C)
    (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) : ‖f.mkContinuous C H‖ <= C :=
  ContinuousMultilinearMap.opNorm_le_bound hC fun m => H m

/--
theorem `MultilinearMap.mkContinuous_norm_le'` / 定理 `MultilinearMap.mkContinuous_norm_le'`

English:
theorem MultilinearMap.mkContinuous_norm_le'
  statement: (f : MultilinearMap 𝕜 E G) {C : Real}
  proof: ContinuousMultilinearMap.opNorm_le_bound (le_max_right _ _) fun m => (H m).trans
mul_le_mul_of_nonneg_right (le_max_left _ _) by positivity

中文:
定理 多重线性映射.mkContinuous_norm_le'
  结论: (f : 多重线性映射 𝕜 E G) {C : 实数}
  证明: ContinuousMultilinearMap.opNorm_le_bound (le_max_right _ _) fun m => (H m).trans
mul_le_mul_of_nonneg_right (le_max_left _ _) by positivity

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.opNorm_le_bound, le_max_left, le_max_right, mul_le_mul_of_nonneg_right, opNorm_le_bound
-/
theorem MultilinearMap.mkContinuous_norm_le' (f : MultilinearMap 𝕜 E G) {C : Real}
    (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) : ‖f.mkContinuous C H‖ <= max C 0 :=
ContinuousMultilinearMap.opNorm_le_bound (le_max_right _ _) fun m => (H m).trans
mul_le_mul_of_nonneg_right (le_max_left _ _) by positivity

namespace ContinuousMultilinearMap

/--
Definition of `restr` / `restr` 的定义

English:
definition restr
  signature: {k n : Nat} (f : (G [×n]->L[𝕜] G' :)) (s : Finset (Fin n)) (hk : #s = k) (z : G)
  body: (f.toMultilinearMap.restr s hk z).mkContinuous (‖f‖ * ‖z‖ ^ (n - k)) fun _ =>
    MultilinearMap.restr_norm_le _ _ _ _ f.le_opNorm _

中文:
定义 restr
  签名: {k n : 自然数} (f : (G [×n]->L[𝕜] G' :)) (s : 有限集 (有限集 n)) (hk : #s = k) (z : G)
  定义体: (f.toMultilinearMap.restr s hk z).mkContinuous (‖f‖ * ‖z‖ ^ (n - k)) fun _ =>
    MultilinearMap.restr_norm_le _ _ _ _ f.le_opNorm _

Depends on / 依赖: MultilinearMap, MultilinearMap.restr_norm_le, f.le_opNorm, f.toMultilinearMap.restr, le_opNorm, mkContinuous, restr_norm_le, toMultilinearMap
-/
def restr {k n : Nat} (f : (G [×n]->L[𝕜] G' :)) (s : Finset (Fin n)) (hk : #s = k) (z : G) :
    G [×k]->L[𝕜] G' :=
  (f.toMultilinearMap.restr s hk z).mkContinuous (‖f‖ * ‖z‖ ^ (n - k)) fun _ =>
    MultilinearMap.restr_norm_le _ _ _ _ f.le_opNorm _

/--
theorem `norm_restr` / 定理 `norm_restr`

English:
theorem norm_restr
  given: {k n : Nat} (f : G [×n]->L[𝕜] G') (s : Finset (Fin n)) (hk : #s = k) (z : G)
  proof: by
  apply MultilinearMap.mkContinuous_norm_le
  exact mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)

中文:
定理 norm_restr
  条件: {k n : 自然数} (f : G [×n]->L[𝕜] G') (s : 有限集 (有限集 n)) (hk : #s = k) (z : G)
  证明: by
  apply MultilinearMap.mkContinuous_norm_le
  exact mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)

Depends on / 依赖: MultilinearMap, MultilinearMap.mkContinuous_norm_le, mkContinuous_norm_le, mul_nonneg, norm_nonneg, pow_nonneg
-/
theorem norm_restr {k n : Nat} (f : G [×n]->L[𝕜] G') (s : Finset (Fin n)) (hk : #s = k) (z : G) :
    ‖f.restr s hk z‖ <= ‖f‖ * ‖z‖ ^ (n - k) := by
  apply MultilinearMap.mkContinuous_norm_le
  exact mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)

section

variable {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]

@[simp]
/--
theorem `norm_mkPiAlgebra_le` / 定理 `norm_mkPiAlgebra_le`

English:
theorem norm_mkPiAlgebra_le
  given: [Nonempty ι]
  statement: ‖ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A‖ <= 1
  proof: by
  refine opNorm_le_bound zero_le_one fun m => ?_
  simp only [ContinuousMultilinearMap.mkPiAlgebra_apply, one_mul]
  exact norm_prod_le' _ univ_nonempty _

中文:
定理 norm_mkPiAlgebra_le
  条件: [非空 ι]
  结论: ‖连续多重线性映射.mkPiAlgebra 𝕜 ι A‖ <= 1
  证明: by
  refine opNorm_le_bound zero_le_one fun m => ?_
  simp only [ContinuousMultilinearMap.mkPiAlgebra_apply, one_mul]
  exact norm_prod_le' _ univ_nonempty _

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.mkPiAlgebra_apply, mkPiAlgebra_apply, norm_prod_le, one_mul, opNorm_le_bound, univ_nonempty, zero_le_one
-/
theorem norm_mkPiAlgebra_le [Nonempty ι] : ‖ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A‖ <= 1 := by
  refine opNorm_le_bound zero_le_one fun m => ?_
  simp only [ContinuousMultilinearMap.mkPiAlgebra_apply, one_mul]
  exact norm_prod_le' _ univ_nonempty _

/--
theorem `norm_mkPiAlgebra_of_empty` / 定理 `norm_mkPiAlgebra_of_empty`

English:
theorem norm_mkPiAlgebra_of_empty
  given: [IsEmpty ι]
  proof: by
  apply le_antisymm
  · apply opNorm_le_bound <;> simp
  · convert! ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A) fun _ => 1
    simp

@[simp]

中文:
定理 norm_mkPiAlgebra_of_empty
  条件: [是空 ι]
  证明: by
  apply le_antisymm
  · apply opNorm_le_bound <;> simp
  · convert! ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A) fun _ => 1
    simp

@[simp]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.mkPiAlgebra, convert, le_antisymm, mkPiAlgebra, opNorm_le_bound, ratio_le_opNorm
-/
theorem norm_mkPiAlgebra_of_empty [IsEmpty ι] :
    ‖ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A‖ = ‖(1 : A)‖ := by
  apply le_antisymm
  · apply opNorm_le_bound <;> simp
  · convert! ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A) fun _ => 1
    simp

@[simp]
/--
theorem `norm_mkPiAlgebra` / 定理 `norm_mkPiAlgebra`

English:
theorem norm_mkPiAlgebra
  given: [NormOneClass A]
  statement: ‖ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A‖ = 1
  proof: by
  cases isEmpty_or_nonempty ι
  · simp [norm_mkPiAlgebra_of_empty]
  · refine le_antisymm norm_mkPiAlgebra_le ?_
    convert! ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A) fun _ => 1
    simp

中文:
定理 norm_mkPiAlgebra
  条件: [NormOne类 A]
  结论: ‖连续多重线性映射.mkPiAlgebra 𝕜 ι A‖ = 1
  证明: by
  cases isEmpty_or_nonempty ι
  · simp [norm_mkPiAlgebra_of_empty]
  · refine le_antisymm norm_mkPiAlgebra_le ?_
    convert! ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A) fun _ => 1
    simp

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.mkPiAlgebra, convert, isEmpty_or_nonempty, le_antisymm, mkPiAlgebra, norm_mkPiAlgebra_le, norm_mkPiAlgebra_of_empty, ratio_le_opNorm
-/
theorem norm_mkPiAlgebra [NormOneClass A] : ‖ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A‖ = 1 := by
  cases isEmpty_or_nonempty ι
  · simp [norm_mkPiAlgebra_of_empty]
  · refine le_antisymm norm_mkPiAlgebra_le ?_
    convert! ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A) fun _ => 1
    simp

end

section

variable {n : Nat} {A : Type*} [SeminormedRing A] [NormedAlgebra 𝕜 A]

/--
theorem `norm_mkPiAlgebraFin_succ_le` / 定理 `norm_mkPiAlgebraFin_succ_le`

English:
theorem norm_mkPiAlgebraFin_succ_le
  statement: ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n.succ A‖ <= 1
  proof: by
  refine opNorm_le_bound zero_le_one fun m => ?_
  simp only [ContinuousMultilinearMap.mkPiAlgebraFin_apply, one_mul, List.ofFn_eq_map,
    Fin.prod_univ_def]
  refine (List.norm_prod_le' ?_).trans_eq ?_
  · rw [Ne, List.map_eq_nil_iff, List.finRange_eq_nil_iff]
    exact Nat.succ_ne_zero _
  rw [List.map_map]; rw [Function.comp_def]

中文:
定理 norm_mkPiAlgebraFin_succ_le
  结论: ‖连续多重线性映射.mkPiAlgebraFin 𝕜 n.succ A‖ <= 1
  证明: by
  refine opNorm_le_bound zero_le_one fun m => ?_
  simp only [ContinuousMultilinearMap.mkPiAlgebraFin_apply, one_mul, List.ofFn_eq_map,
    Fin.prod_univ_def]
  refine (List.norm_prod_le' ?_).trans_eq ?_
  · rw [Ne, List.map_eq_nil_iff, List.finRange_eq_nil_iff]
    exact Nat.succ_ne_zero _
  rw [List.map_map]; rw [Function.comp_def]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.mkPiAlgebraFin_apply, Fin.prod_univ_def, Function, Function.comp_def, List.finRange_eq_nil_iff, List.map_eq_nil_iff, List.map_map, List.norm_prod_le, List.ofFn_eq_map, Nat.succ_ne_zero, comp_def, finRange_eq_nil_iff, map_eq_nil_iff, map_map, mkPiAlgebraFin_apply, norm_prod_le, ofFn_eq_map, one_mul, opNorm_le_bound
-/
theorem norm_mkPiAlgebraFin_succ_le : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n.succ A‖ <= 1 := by
  refine opNorm_le_bound zero_le_one fun m => ?_
  simp only [ContinuousMultilinearMap.mkPiAlgebraFin_apply, one_mul, List.ofFn_eq_map,
    Fin.prod_univ_def]
  refine (List.norm_prod_le' ?_).trans_eq ?_
  · rw [Ne, List.map_eq_nil_iff, List.finRange_eq_nil_iff]
    exact Nat.succ_ne_zero _
  rw [List.map_map]; rw [Function.comp_def]

/--
theorem `norm_mkPiAlgebraFin_le_of_pos` / 定理 `norm_mkPiAlgebraFin_le_of_pos`

English:
theorem norm_mkPiAlgebraFin_le_of_pos
  given: (hn : 0 < n)
  proof: by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact norm_mkPiAlgebraFin_succ_le

中文:
定理 norm_mkPiAlgebraFin_le_of_pos
  条件: (hn : 0 < n)
  证明: by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact norm_mkPiAlgebraFin_succ_le

Depends on / 依赖: Nat.exists_eq_succ_of_ne_zero, exists_eq_succ_of_ne_zero, hn.ne, norm_mkPiAlgebraFin_succ_le
-/
theorem norm_mkPiAlgebraFin_le_of_pos (hn : 0 < n) :
    ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A‖ <= 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact norm_mkPiAlgebraFin_succ_le

/--
theorem `norm_mkPiAlgebraFin_zero` / 定理 `norm_mkPiAlgebraFin_zero`

English:
theorem norm_mkPiAlgebraFin_zero
  statement: ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 0 A‖ = ‖(1 : A)‖
  proof: by
  refine le_antisymm ?_ ?_
  · refine opNorm_le_bound (norm_nonneg (1 : A)) ?_
    simp
  · convert! ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 0 A) fun _ => (1 : A)
    simp

中文:
定理 norm_mkPiAlgebraFin_zero
  结论: ‖连续多重线性映射.mkPiAlgebraFin 𝕜 0 A‖ = ‖(1 : A)‖
  证明: by
  refine le_antisymm ?_ ?_
  · refine opNorm_le_bound (norm_nonneg (1 : A)) ?_
    simp
  · convert! ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 0 A) fun _ => (1 : A)
    simp

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.mkPiAlgebraFin, convert, le_antisymm, mkPiAlgebraFin, norm_nonneg, opNorm_le_bound, ratio_le_opNorm
-/
theorem norm_mkPiAlgebraFin_zero : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 0 A‖ = ‖(1 : A)‖ := by
  refine le_antisymm ?_ ?_
  · refine opNorm_le_bound (norm_nonneg (1 : A)) ?_
    simp
  · convert! ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 0 A) fun _ => (1 : A)
    simp

/--
theorem `norm_mkPiAlgebraFin_le` / 定理 `norm_mkPiAlgebraFin_le`

English:
theorem norm_mkPiAlgebraFin_le
  proof: by
  cases n
  · exact norm_mkPiAlgebraFin_zero.le.trans (le_max_right _ _)
  · exact (norm_mkPiAlgebraFin_le_of_pos (Nat.zero_lt_succ _)).trans (le_max_left _ _)

@[simp]

中文:
定理 norm_mkPiAlgebraFin_le
  证明: by
  cases n
  · exact norm_mkPiAlgebraFin_zero.le.trans (le_max_right _ _)
  · exact (norm_mkPiAlgebraFin_le_of_pos (Nat.zero_lt_succ _)).trans (le_max_left _ _)

@[simp]

Depends on / 依赖: Nat.zero_lt_succ, le_max_left, le_max_right, norm_mkPiAlgebraFin_le_of_pos, norm_mkPiAlgebraFin_zero, norm_mkPiAlgebraFin_zero.le.trans, zero_lt_succ
-/
theorem norm_mkPiAlgebraFin_le :
    ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A‖ <= max 1 ‖(1 : A)‖ := by
  cases n
  · exact norm_mkPiAlgebraFin_zero.le.trans (le_max_right _ _)
  · exact (norm_mkPiAlgebraFin_le_of_pos (Nat.zero_lt_succ _)).trans (le_max_left _ _)

@[simp]
/--
theorem `norm_mkPiAlgebraFin` / 定理 `norm_mkPiAlgebraFin`

English:
theorem norm_mkPiAlgebraFin
  given: [NormOneClass A]
  proof: by
  cases n
  · rw [norm_mkPiAlgebraFin_zero]
    simp
  · refine le_antisymm norm_mkPiAlgebraFin_succ_le ?_
refine le_of_eq_of_le ?_
      ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 (Nat.succ _) A) fun _ => 1
    simp

中文:
定理 norm_mkPiAlgebraFin
  条件: [NormOne类 A]
  证明: by
  cases n
  · rw [norm_mkPiAlgebraFin_zero]
    simp
  · refine le_antisymm norm_mkPiAlgebraFin_succ_le ?_
refine le_of_eq_of_le ?_
      ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 (Nat.succ _) A) fun _ => 1
    simp

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.mkPiAlgebraFin, Nat.succ, le_antisymm, le_of_eq_of_le, mkPiAlgebraFin, norm_mkPiAlgebraFin_succ_le, norm_mkPiAlgebraFin_zero, ratio_le_opNorm
-/
theorem norm_mkPiAlgebraFin [NormOneClass A] :
    ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A‖ = 1 := by
  cases n
  · rw [norm_mkPiAlgebraFin_zero]
    simp
  · refine le_antisymm norm_mkPiAlgebraFin_succ_le ?_
refine le_of_eq_of_le ?_
      ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 (Nat.succ _) A) fun _ => 1
    simp

end

@[simp]
/--
theorem `nnnorm_smulRight` / 定理 `nnnorm_smulRight`

English:
theorem nnnorm_smulRight
  given: (f : ContinuousMultilinearMap 𝕜 E 𝕜) (z : G)
  proof: by
  refine le_antisymm ?_ ?_
  · refine opNNNorm_le_iff.2 fun m => (nnnorm_smul_le _ _).trans ?_
    rw [mul_right_comm]
    gcongr
    exact le_opNNNorm _ _
  · obtain hz | hz := eq_zero_or_pos ‖z‖₊
    · simp [hz]
    rw [← le_div_iff₀ hz]; rw [opNNNorm_le_iff]
    intro m
    rw [div_mul_eq_mul_div]; rw [le_div_iff₀ hz]
    refine le_trans ?_ ((f.smulRight z).le_opNNNorm m)
    rw [smulRight_apply]; rw [nnnorm_smul]

@[simp]

中文:
定理 nnnorm_smulRight
  条件: (f : 连续多重线性映射 𝕜 E 𝕜) (z : G)
  证明: by
  refine le_antisymm ?_ ?_
  · refine opNNNorm_le_iff.2 fun m => (nnnorm_smul_le _ _).trans ?_
    rw [mul_right_comm]
    gcongr
    exact le_opNNNorm _ _
  · obtain hz | hz := eq_zero_or_pos ‖z‖₊
    · simp [hz]
    rw [← le_div_iff₀ hz]; rw [opNNNorm_le_iff]
    intro m
    rw [div_mul_eq_mul_div]; rw [le_div_iff₀ hz]
    refine le_trans ?_ ((f.smulRight z).le_opNNNorm m)
    rw [smulRight_apply]; rw [nnnorm_smul]

@[simp]

Depends on / 依赖: div_mul_eq_mul_div, eq_zero_or_pos, f.smulRight, le_antisymm, le_opNNNorm, le_trans, mul_right_comm, nnnorm_smul, nnnorm_smul_le, opNNNorm_le_iff, smulRight, smulRight_apply
-/
theorem nnnorm_smulRight (f : ContinuousMultilinearMap 𝕜 E 𝕜) (z : G) :
    ‖f.smulRight z‖₊ = ‖f‖₊ * ‖z‖₊ := by
  refine le_antisymm ?_ ?_
  · refine opNNNorm_le_iff.2 fun m => (nnnorm_smul_le _ _).trans ?_
    rw [mul_right_comm]
    gcongr
    exact le_opNNNorm _ _
  · obtain hz | hz := eq_zero_or_pos ‖z‖₊
    · simp [hz]
    rw [← le_div_iff₀ hz]; rw [opNNNorm_le_iff]
    intro m
    rw [div_mul_eq_mul_div]; rw [le_div_iff₀ hz]
    refine le_trans ?_ ((f.smulRight z).le_opNNNorm m)
    rw [smulRight_apply]; rw [nnnorm_smul]

@[simp]
/--
theorem `norm_smulRight` / 定理 `norm_smulRight`

English:
theorem norm_smulRight
  given: (f : ContinuousMultilinearMap 𝕜 E 𝕜) (z : G)
  proof: congr_arg NNReal.toReal (nnnorm_smulRight f z)

@[simp]

中文:
定理 norm_smulRight
  条件: (f : 连续多重线性映射 𝕜 E 𝕜) (z : G)
  证明: congr_arg NNReal.toReal (nnnorm_smulRight f z)

@[simp]

Depends on / 依赖: NNReal, NNReal.toReal, congr_arg, nnnorm_smulRight, toReal
-/
theorem norm_smulRight (f : ContinuousMultilinearMap 𝕜 E 𝕜) (z : G) :
    ‖f.smulRight z‖ = ‖f‖ * ‖z‖ :=
  congr_arg NNReal.toReal (nnnorm_smulRight f z)

@[simp]
/--
theorem `norm_mkPiRing` / 定理 `norm_mkPiRing`

English:
theorem norm_mkPiRing
  given: (z : G)
  statement: ‖ContinuousMultilinearMap.mkPiRing 𝕜 ι z‖ = ‖z‖
  proof: by
  rw [ContinuousMultilinearMap.mkPiRing]; rw [norm_smulRight]; rw [norm_mkPiAlgebra]; rw [one_mul]

中文:
定理 norm_mkPiRing
  条件: (z : G)
  结论: ‖连续多重线性映射.mkPiRing 𝕜 ι z‖ = ‖z‖
  证明: by
  rw [ContinuousMultilinearMap.mkPiRing]; rw [norm_smulRight]; rw [norm_mkPiAlgebra]; rw [one_mul]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.mkPiRing, mkPiRing, norm_mkPiAlgebra, norm_smulRight, one_mul
-/
theorem norm_mkPiRing (z : G) : ‖ContinuousMultilinearMap.mkPiRing 𝕜 ι z‖ = ‖z‖ := by
  rw [ContinuousMultilinearMap.mkPiRing]; rw [norm_smulRight]; rw [norm_mkPiAlgebra]; rw [one_mul]

variable (𝕜 E G) in
/--
Definition of `smulRightL` / `smulRightL` 的定义

English:
definition smulRightL
  signature: : ContinuousMultilinearMap 𝕜 E 𝕜 ->L[𝕜] G ->L[𝕜] ContinuousMultilinearMap 𝕜 E G
  body: LinearMap.mkContinuous₂
    { toFun := fun f =>
        { toFun := fun z => f.smulRight z
          map_add' := fun x y => by ext; simp
          map_smul' := fun c x => by ext; simp [smul_smul, mul_comm] }
      map_add' := fun f g => by ext; simp [add_smul]
      map_smul' := fun c f => by ext; simp [smul_smul] }
    1 (fun f z => by simp [norm_smulRight])

中文:
定义 smulRightL
  签名: : 连续多重线性映射 𝕜 E 𝕜 ->L[𝕜] G ->L[𝕜] 连续多重线性映射 𝕜 E G
  定义体: LinearMap.mkContinuous₂
    { toFun := fun f =>
        { toFun := fun z => f.smulRight z
          map_add' := fun x y => by ext; simp
          map_smul' := fun c x => by ext; simp [smul_smul, mul_comm] }
      map_add' := fun f g => by ext; simp [add_smul]
      map_smul' := fun c f => by ext; simp [smul_smul] }
    1 (fun f z => by simp [norm_smulRight])

Depends on / 依赖: LinearMap, LinearMap.mkContinuous, add_smul, f.smulRight, map_add, map_smul, mul_comm, norm_smulRight, smulRight, smul_smul
-/
def smulRightL : ContinuousMultilinearMap 𝕜 E 𝕜 ->L[𝕜] G ->L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
  LinearMap.mkContinuous₂
    { toFun := fun f =>
        { toFun := fun z => f.smulRight z
          map_add' := fun x y => by ext; simp
          map_smul' := fun c x => by ext; simp [smul_smul, mul_comm] }
      map_add' := fun f g => by ext; simp [add_smul]
      map_smul' := fun c f => by ext; simp [smul_smul] }
    1 (fun f z => by simp [norm_smulRight])

/--
lemma `smulRightL_apply` / 引理 `smulRightL_apply`

English:
lemma smulRightL_apply
  given: (f : ContinuousMultilinearMap 𝕜 E 𝕜) (z : G)
  proof: rfl

中文:
引理 smulRightL_apply
  条件: (f : 连续多重线性映射 𝕜 E 𝕜) (z : G)
  证明: rfl
-/
@[simp] lemma smulRightL_apply (f : ContinuousMultilinearMap 𝕜 E 𝕜) (z : G) :
    smulRightL 𝕜 E G f z = f.smulRight z := rfl

/--
lemma `norm_smulRightL_le` / 引理 `norm_smulRightL_le`

English:
lemma norm_smulRightL_le
  statement: ‖smulRightL 𝕜 E G‖ <= 1
  proof: LinearMap.mkContinuous₂_norm_le _ zero_le_one _

中文:
引理 norm_smulRightL_le
  结论: ‖smulRightL 𝕜 E G‖ <= 1
  证明: LinearMap.mkContinuous₂_norm_le _ zero_le_one _

Depends on / 依赖: LinearMap, LinearMap.mkContinuous, zero_le_one
-/
lemma norm_smulRightL_le : ‖smulRightL 𝕜 E G‖ <= 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

variable (𝕜 ι G)

/--
Definition of `piFieldEquiv` / `piFieldEquiv` 的定义

English:
definition piFieldEquiv
  signature: : G ≃ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => 𝕜) G where
  body: ContinuousMultilinearMap.mkPiRing 𝕜 ι z
  invFun f := f fun _ => 1
  map_add' z z' := by
    ext
    simp [smul_add]
  map_smul' c z := by
    ext
    simp [smul_smul, mul_comm]
  left_inv z := by simp
  right_inv f := f.mkPiRing_apply_one_eq_self
  norm_map' := norm_mkPiRing

中文:
定义 piFieldEquiv
  签名: : G ≃ₗᵢ[𝕜] 连续多重线性映射 𝕜 (fun _ : ι => 𝕜) G where
  定义体: ContinuousMultilinearMap.mkPiRing 𝕜 ι z
  invFun f := f fun _ => 1
  map_add' z z' := by
    ext
    simp [smul_add]
  map_smul' c z := by
    ext
    simp [smul_smul, mul_comm]
  left_inv z := by simp
  right_inv f := f.mkPiRing_apply_one_eq_self
  norm_map' := norm_mkPiRing
-/
protected def piFieldEquiv : G ≃ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => 𝕜) G where
  toFun z := ContinuousMultilinearMap.mkPiRing 𝕜 ι z
  invFun f := f fun _ => 1
  map_add' z z' := by
    ext
    simp [smul_add]
  map_smul' c z := by
    ext
    simp [smul_smul, mul_comm]
  left_inv z := by simp
  right_inv f := f.mkPiRing_apply_one_eq_self
  norm_map' := norm_mkPiRing

end ContinuousMultilinearMap

open ContinuousMultilinearMap

namespace MultilinearMap

/--
Definition of `mkContinuousLinear` / `mkContinuousLinear` 的定义

English:
definition mkContinuousLinear
  signature: (f : G ->ₗ[𝕜] MultilinearMap 𝕜 E G') (C : Real)
  body: LinearMap.mkContinuous
    { toFun := fun x => (f x).mkContinuous (C * ‖x‖) <| H x
      map_add' := fun x y => by
        ext1
        simp
      map_smul' := fun c x => by
        ext1
        simp }
    (max C 0) fun x => by
simpa using ((f x).mkContinuous_norm_le' _).trans_eq by
        rw [max_mul_of_nonneg _ _ (norm_nonneg x)]; rw [zero_mul]

中文:
定义 mkContinuousLinear
  签名: (f : G ->ₗ[𝕜] 多重线性映射 𝕜 E G') (C : 实数)
  定义体: LinearMap.mkContinuous
    { toFun := fun x => (f x).mkContinuous (C * ‖x‖) <| H x
      map_add' := fun x y => by
        ext1
        simp
      map_smul' := fun c x => by
        ext1
        simp }
    (max C 0) fun x => by
simpa using ((f x).mkContinuous_norm_le' _).trans_eq by
        rw [max_mul_of_nonneg _ _ (norm_nonneg x)]; rw [zero_mul]

Depends on / 依赖: LinearMap, LinearMap.mkContinuous, map_add, map_smul, max_mul_of_nonneg, mkContinuous, mkContinuous_norm_le, norm_nonneg, trans_eq, zero_mul
-/
def mkContinuousLinear (f : G ->ₗ[𝕜] MultilinearMap 𝕜 E G') (C : Real)
    (H : forall x m, ‖f x m‖ <= C * ‖x‖ * ∏ i, ‖m i‖) : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E G' :=
  LinearMap.mkContinuous
    { toFun := fun x => (f x).mkContinuous (C * ‖x‖) <| H x
      map_add' := fun x y => by
        ext1
        simp
      map_smul' := fun c x => by
        ext1
        simp }
    (max C 0) fun x => by
simpa using ((f x).mkContinuous_norm_le' _).trans_eq by
        rw [max_mul_of_nonneg _ _ (norm_nonneg x)]; rw [zero_mul]

/--
theorem `mkContinuousLinear_norm_le'` / 定理 `mkContinuousLinear_norm_le'`

English:
theorem mkContinuousLinear_norm_le'
  statement: (f : G ->ₗ[𝕜] MultilinearMap 𝕜 E G') (C : Real)
  proof: by
  dsimp only [mkContinuousLinear]
  exact LinearMap.mkContinuous_norm_le _ (le_max_right _ _) _

中文:
定理 mkContinuousLinear_norm_le'
  结论: (f : G ->ₗ[𝕜] 多重线性映射 𝕜 E G') (C : 实数)
  证明: by
  dsimp only [mkContinuousLinear]
  exact LinearMap.mkContinuous_norm_le _ (le_max_right _ _) _

Depends on / 依赖: LinearMap, LinearMap.mkContinuous_norm_le, le_max_right, mkContinuousLinear, mkContinuous_norm_le
-/
theorem mkContinuousLinear_norm_le' (f : G ->ₗ[𝕜] MultilinearMap 𝕜 E G') (C : Real)
    (H : forall x m, ‖f x m‖ <= C * ‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuousLinear f C H‖ <= max C 0 := by
  dsimp only [mkContinuousLinear]
  exact LinearMap.mkContinuous_norm_le _ (le_max_right _ _) _

/--
theorem `mkContinuousLinear_norm_le` / 定理 `mkContinuousLinear_norm_le`

English:
theorem mkContinuousLinear_norm_le
  statement: (f : G ->ₗ[𝕜] MultilinearMap 𝕜 E G') {C : Real} (hC : 0 <= C)
  proof: (mkContinuousLinear_norm_le' f C H).trans_eq (max_eq_left hC)

中文:
定理 mkContinuousLinear_norm_le
  结论: (f : G ->ₗ[𝕜] 多重线性映射 𝕜 E G') {C : 实数} (hC : 0 <= C)
  证明: (mkContinuousLinear_norm_le' f C H).trans_eq (max_eq_left hC)

Depends on / 依赖: max_eq_left, mkContinuousLinear_norm_le, trans_eq
-/
theorem mkContinuousLinear_norm_le (f : G ->ₗ[𝕜] MultilinearMap 𝕜 E G') {C : Real} (hC : 0 <= C)
    (H : forall x m, ‖f x m‖ <= C * ‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuousLinear f C H‖ <= C :=
  (mkContinuousLinear_norm_le' f C H).trans_eq (max_eq_left hC)

variable [forall i, SeminormedAddCommGroup (E' i)] [forall i, NormedSpace 𝕜 (E' i)]

/--
Definition of `mkContinuousMultilinear` / `mkContinuousMultilinear` 的定义

English:
definition mkContinuousMultilinear
  signature: (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) (C : Real)
  body: mkContinuous
    { toFun := fun m => mkContinuous (f m) (C * ∏ i, ‖m i‖) <| H m
      map_update_add' := fun m i x y => by
        ext1
        simp
      map_update_smul' := fun m i c x => by
        ext1
        simp }
    (max C 0) fun m => by
      simp only [coe_mk]
      refine ((f m).mkContinuous_norm_le' _).trans_eq ?_
      rw [max_mul_of_nonneg]; rw [zero_mul]
      positivity

@[simp]

中文:
定义 mkContinuousMultilinear
  签名: (f : 多重线性映射 𝕜 E (多重线性映射 𝕜 E' G)) (C : 实数)
  定义体: mkContinuous
    { toFun := fun m => mkContinuous (f m) (C * ∏ i, ‖m i‖) <| H m
      map_update_add' := fun m i x y => by
        ext1
        simp
      map_update_smul' := fun m i c x => by
        ext1
        simp }
    (max C 0) fun m => by
      simp only [coe_mk]
      refine ((f m).mkContinuous_norm_le' _).trans_eq ?_
      rw [max_mul_of_nonneg]; rw [zero_mul]
      positivity

@[simp]

Depends on / 依赖: coe_mk, map_update_add, map_update_smul, max_mul_of_nonneg, mkContinuous, mkContinuous_norm_le, trans_eq, zero_mul
-/
def mkContinuousMultilinear (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) (C : Real)
    (H : forall m₁ m₂, ‖f m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    ContinuousMultilinearMap 𝕜 E (ContinuousMultilinearMap 𝕜 E' G) :=
  mkContinuous
    { toFun := fun m => mkContinuous (f m) (C * ∏ i, ‖m i‖) <| H m
      map_update_add' := fun m i x y => by
        ext1
        simp
      map_update_smul' := fun m i c x => by
        ext1
        simp }
    (max C 0) fun m => by
      simp only [coe_mk]
      refine ((f m).mkContinuous_norm_le' _).trans_eq ?_
      rw [max_mul_of_nonneg]; rw [zero_mul]
      positivity

@[simp]
/--
theorem `mkContinuousMultilinear_apply` / 定理 `mkContinuousMultilinear_apply`

English:
theorem mkContinuousMultilinear_apply
  statement: (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) {C : Real}
  proof: rfl

中文:
定理 mkContinuousMultilinear_apply
  结论: (f : 多重线性映射 𝕜 E (多重线性映射 𝕜 E' G)) {C : 实数}
  证明: rfl
-/
theorem mkContinuousMultilinear_apply (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) {C : Real}
    (H : forall m₁ m₂, ‖f m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) (m : forall i, E i) :
    ⇑(mkContinuousMultilinear f C H m) = f m :=
  rfl

/--
theorem `mkContinuousMultilinear_norm_le'` / 定理 `mkContinuousMultilinear_norm_le'`

English:
theorem mkContinuousMultilinear_norm_le'
  statement: (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) (C : Real)
  proof: by
  dsimp only [mkContinuousMultilinear]
  exact mkContinuous_norm_le _ (le_max_right _ _) _

中文:
定理 mkContinuousMultilinear_norm_le'
  结论: (f : 多重线性映射 𝕜 E (多重线性映射 𝕜 E' G)) (C : 实数)
  证明: by
  dsimp only [mkContinuousMultilinear]
  exact mkContinuous_norm_le _ (le_max_right _ _) _

Depends on / 依赖: le_max_right, mkContinuousMultilinear, mkContinuous_norm_le
-/
theorem mkContinuousMultilinear_norm_le' (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) (C : Real)
    (H : forall m₁ m₂, ‖f m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    ‖mkContinuousMultilinear f C H‖ <= max C 0 := by
  dsimp only [mkContinuousMultilinear]
  exact mkContinuous_norm_le _ (le_max_right _ _) _

/--
theorem `mkContinuousMultilinear_norm_le` / 定理 `mkContinuousMultilinear_norm_le`

English:
theorem mkContinuousMultilinear_norm_le
  statement: (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) {C : Real}
  proof: (mkContinuousMultilinear_norm_le' f C H).trans_eq (max_eq_left hC)

中文:
定理 mkContinuousMultilinear_norm_le
  结论: (f : 多重线性映射 𝕜 E (多重线性映射 𝕜 E' G)) {C : 实数}
  证明: (mkContinuousMultilinear_norm_le' f C H).trans_eq (max_eq_left hC)

Depends on / 依赖: max_eq_left, mkContinuousMultilinear_norm_le, trans_eq
-/
theorem mkContinuousMultilinear_norm_le (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) {C : Real}
    (hC : 0 <= C) (H : forall m₁ m₂, ‖f m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    ‖mkContinuousMultilinear f C H‖ <= C :=
  (mkContinuousMultilinear_norm_le' f C H).trans_eq (max_eq_left hC)

end MultilinearMap

namespace ContinuousLinearMap

/--
theorem `norm_compContinuousMultilinearMap_le` / 定理 `norm_compContinuousMultilinearMap_le`

English:
theorem norm_compContinuousMultilinearMap_le
  given: (g : G ->L[𝕜] G') (f : ContinuousMultilinearMap 𝕜 E G)
  proof: ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m =>
    calc
‖g (f m)‖ <= ‖g‖ * (‖f‖ * ∏ i, ‖m i‖) := g.le_opNorm_of_le f.le_opNorm _
      _ = _ := (mul_assoc _ _ _).symm

中文:
定理 norm_compContinuousMultilinearMap_le
  条件: (g : G ->L[𝕜] G') (f : 连续多重线性映射 𝕜 E G)
  证明: ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m =>
    calc
‖g (f m)‖ <= ‖g‖ * (‖f‖ * ∏ i, ‖m i‖) := g.le_opNorm_of_le f.le_opNorm _
      _ = _ := (mul_assoc _ _ _).symm

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.opNorm_le_bound, f.le_opNorm, g.le_opNorm_of_le, le_opNorm, le_opNorm_of_le, mul_assoc, opNorm_le_bound
-/
theorem norm_compContinuousMultilinearMap_le (g : G ->L[𝕜] G') (f : ContinuousMultilinearMap 𝕜 E G) :
    ‖g.compContinuousMultilinearMap f‖ <= ‖g‖ * ‖f‖ :=
  ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m =>
    calc
‖g (f m)‖ <= ‖g‖ * (‖f‖ * ∏ i, ‖m i‖) := g.le_opNorm_of_le f.le_opNorm _
      _ = _ := (mul_assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Flip arguments in `f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E G'` to get
`ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')` -/
@[simps! apply_apply]
/--
Definition of `flipMultilinear` / `flipMultilinear` 的定义

English:
definition flipMultilinear
  signature: (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E G')
  body: MultilinearMap.mkContinuous
    { toFun := fun m =>
        LinearMap.mkContinuous
          { toFun := (f · m)
            map_add' := by simp
            map_smul' := by simp }
          (‖f‖ * ∏ i, ‖m i‖) fun x => by
          rw [mul_right_comm]
          exact (f x).le_of_opNorm_le (f.le_opNorm x) _
      map_update_add' := fun m i x y => by
        ext1
        simp only [add_apply, ContinuousMultilinearMap.map_update_add, LinearMap.coe_mk,
          LinearMap.mkContinuous_apply, AddHom.coe_mk]
      map_update_smul' := fun m i c x => by
        ext1
        simp only [FunLike.coe_smul, ContinuousMultilinearMap.map_update_smul, LinearMap.coe_mk,
          LinearMap.mkContinuous_apply, Pi.smul_apply, AddHom.coe_mk] }
    ‖f‖ fun m => by
      dsimp only [MultilinearMap.coe_mk]
      exact LinearMap.mkContinuous_norm_le _ (by positivity) _

中文:
定义 flipMultilinear
  签名: (f : G ->L[𝕜] 连续多重线性映射 𝕜 E G')
  定义体: MultilinearMap.mkContinuous
    { toFun := fun m =>
        LinearMap.mkContinuous
          { toFun := (f · m)
            map_add' := by simp
            map_smul' := by simp }
          (‖f‖ * ∏ i, ‖m i‖) fun x => by
          rw [mul_right_comm]
          exact (f x).le_of_opNorm_le (f.le_opNorm x) _
      map_update_add' := fun m i x y => by
        ext1
        simp only [add_apply, ContinuousMultilinearMap.map_update_add, LinearMap.coe_mk,
          LinearMap.mkContinuous_apply, AddHom.coe_mk]
      map_update_smul' := fun m i c x => by
        ext1
        simp only [FunLike.coe_smul, ContinuousMultilinearMap.map_update_smul, LinearMap.coe_mk,
          LinearMap.mkContinuous_apply, Pi.smul_apply, AddHom.coe_mk] }
    ‖f‖ fun m => by
      dsimp only [MultilinearMap.coe_mk]
      exact LinearMap.mkContinuous_norm_le _ (by positivity) _

Depends on / 依赖: AddHom, AddHom.coe_mk, ContinuousMultilinearMap, ContinuousMultilinearMap.map_u, ContinuousMultilinearMap.map_update_add, FunLike, FunLike.coe_smul, LinearMap, LinearMap.coe_mk, LinearMap.mkContinuous, LinearMap.mkContinuous_apply, MultilinearMap, MultilinearMap.mkContinuous, add_apply, coe_mk, coe_smul, f.le_opNorm, le_of_opNorm_le, le_opNorm, map_add
-/
def flipMultilinear (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E G') :
    ContinuousMultilinearMap 𝕜 E (G ->L[𝕜] G') :=
  MultilinearMap.mkContinuous
    { toFun := fun m =>
        LinearMap.mkContinuous
          { toFun := (f · m)
            map_add' := by simp
            map_smul' := by simp }
          (‖f‖ * ∏ i, ‖m i‖) fun x => by
          rw [mul_right_comm]
          exact (f x).le_of_opNorm_le (f.le_opNorm x) _
      map_update_add' := fun m i x y => by
        ext1
        simp only [add_apply, ContinuousMultilinearMap.map_update_add, LinearMap.coe_mk,
          LinearMap.mkContinuous_apply, AddHom.coe_mk]
      map_update_smul' := fun m i c x => by
        ext1
        simp only [FunLike.coe_smul, ContinuousMultilinearMap.map_update_smul, LinearMap.coe_mk,
          LinearMap.mkContinuous_apply, Pi.smul_apply, AddHom.coe_mk] }
    ‖f‖ fun m => by
      dsimp only [MultilinearMap.coe_mk]
      exact LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- Flip arguments in `f : ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')` to get
`G →L[𝕜] ContinuousMultilinearMap 𝕜 E G'` -/
@[simps! apply_apply]
/--
Definition of `_root_.ContinuousMultilinearMap.flipLinear` / `_root_.ContinuousMultilinearMap.flipLinear` 的定义

English:
definition _root_.ContinuousMultilinearMap.flipLinear
  signature: (f : ContinuousMultilinearMap 𝕜 E (G ->L[𝕜] G'))
  body: MultilinearMap.mkContinuousLinear
    { toFun x :=
        { toFun m := f m x
          map_update_add' := by simp
          map_update_smul' := by simp }
      map_add' x y := by ext1; simp
      map_smul' c x := by ext1; simp } ‖f‖ <| fun x m => by
    rw [LinearMap.coe_mk]; rw [AddHom.coe_mk]; rw [MultilinearMap.coe_mk]; rw [mul_right_comm]
    apply ((f m).le_opNorm x).trans
    gcongr
    apply f.le_opNorm

中文:
定义 _root_.连续多重线性映射.flipLinear
  签名: (f : 连续多重线性映射 𝕜 E (G ->L[𝕜] G'))
  定义体: MultilinearMap.mkContinuousLinear
    { toFun x :=
        { toFun m := f m x
          map_update_add' := by simp
          map_update_smul' := by simp }
      map_add' x y := by ext1; simp
      map_smul' c x := by ext1; simp } ‖f‖ <| fun x m => by
    rw [LinearMap.coe_mk]; rw [AddHom.coe_mk]; rw [MultilinearMap.coe_mk]; rw [mul_right_comm]
    apply ((f m).le_opNorm x).trans
    gcongr
    apply f.le_opNorm

Depends on / 依赖: AddHom, AddHom.coe_mk, LinearMap, LinearMap.coe_mk, MultilinearMap, MultilinearMap.coe_mk, MultilinearMap.mkContinuousLinear, coe_mk, f.le_opNorm, le_opNorm, map_add, map_smul, map_update_add, map_update_smul, mkContinuousLinear, mul_right_comm
-/
def _root_.ContinuousMultilinearMap.flipLinear (f : ContinuousMultilinearMap 𝕜 E (G ->L[𝕜] G')) :
    G ->L[𝕜] ContinuousMultilinearMap 𝕜 E G' :=
  MultilinearMap.mkContinuousLinear
    { toFun x :=
        { toFun m := f m x
          map_update_add' := by simp
          map_update_smul' := by simp }
      map_add' x y := by ext1; simp
      map_smul' c x := by ext1; simp } ‖f‖ <| fun x m => by
    rw [LinearMap.coe_mk]; rw [AddHom.coe_mk]; rw [MultilinearMap.coe_mk]; rw [mul_right_comm]
    apply ((f m).le_opNorm x).trans
    gcongr
    apply f.le_opNorm

/--
lemma `flipLinear_flipMultilinear` / 引理 `flipLinear_flipMultilinear`

English:
lemma flipLinear_flipMultilinear
  given: (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E G')
  proof: rfl

中文:
引理 flipLinear_flipMultilinear
  条件: (f : G ->L[𝕜] 连续多重线性映射 𝕜 E G')
  证明: rfl
-/
@[simp] lemma flipLinear_flipMultilinear (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E G') :
    f.flipMultilinear.flipLinear = f := rfl

/--
lemma `_root_.ContinuousMultilinearMap.flipMultilinear_flipLinear` / 引理 `_root_.ContinuousMultilinearMap.flipMultilinear_flipLinear`

English:
lemma _root_.ContinuousMultilinearMap.flipMultilinear_flipLinear
  proof: rfl

中文:
引理 _root_.连续多重线性映射.flipMultilinear_flipLinear
  证明: rfl
-/
@[simp] lemma _root_.ContinuousMultilinearMap.flipMultilinear_flipLinear
    (f : ContinuousMultilinearMap 𝕜 E (G ->L[𝕜] G')) :
    f.flipLinear.flipMultilinear = f := rfl

variable (𝕜 E G G') in
/--
Definition of `flipMultilinearEquivₗ` / `flipMultilinearEquivₗ` 的定义

English:
definition flipMultilinearEquivₗ
  signature: : (G ->L[𝕜] ContinuousMultilinearMap 𝕜 E G') ≃ₗ[𝕜]
  body: f.flipMultilinear
  invFun f := f.flipLinear
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp
  left_inv f := rfl
  right_inv f := rfl

中文:
定义 flipMultilinearEquivₗ
  签名: : (G ->L[𝕜] 连续多重线性映射 𝕜 E G') ≃ₗ[𝕜]
  定义体: f.flipMultilinear
  invFun f := f.flipLinear
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp
  left_inv f := rfl
  right_inv f := rfl

Depends on / 依赖: f.flipMultilinear, flipMultilinear
-/
def flipMultilinearEquivₗ : (G ->L[𝕜] ContinuousMultilinearMap 𝕜 E G') ≃ₗ[𝕜]
    (ContinuousMultilinearMap 𝕜 E (G ->L[𝕜] G')) where
  toFun f := f.flipMultilinear
  invFun f := f.flipLinear
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp
  left_inv f := rfl
  right_inv f := rfl

variable (𝕜 E G G') in
/--
Definition of `flipMultilinearEquiv` / `flipMultilinearEquiv` 的定义

English:
definition flipMultilinearEquiv
  signature: : (G ->L[𝕜] ContinuousMultilinearMap 𝕜 E G') ≃L[𝕜]
  body: by
  refine (flipMultilinearEquivₗ 𝕜 E G G').toContinuousLinearEquivOfBounds 1 1 ?_ ?_
  · intro f
    suffices ‖f.flipMultilinear‖ <= ‖f‖ by simpa
    apply MultilinearMap.mkContinuous_norm_le
    positivity
  · intro f
    suffices ‖f.flipLinear‖ <= ‖f‖ by simpa
    apply MultilinearMap.mkContinuousLinear_norm_le
    positivity

中文:
定义 flipMultilinearEquiv
  签名: : (G ->L[𝕜] 连续多重线性映射 𝕜 E G') ≃L[𝕜]
  定义体: by
  refine (flipMultilinearEquivₗ 𝕜 E G G').toContinuousLinearEquivOfBounds 1 1 ?_ ?_
  · intro f
    suffices ‖f.flipMultilinear‖ <= ‖f‖ by simpa
    apply MultilinearMap.mkContinuous_norm_le
    positivity
  · intro f
    suffices ‖f.flipLinear‖ <= ‖f‖ by simpa
    apply MultilinearMap.mkContinuousLinear_norm_le
    positivity

Depends on / 依赖: MultilinearMap, MultilinearMap.mkContinuousLinear_norm_le, MultilinearMap.mkContinuous_norm_le, f.flipLinear, f.flipMultilinear, flipLinear, flipMultilinear, mkContinuousLinear_norm_le, mkContinuous_norm_le, toContinuousLinearEquivOfBounds
-/
def flipMultilinearEquiv : (G ->L[𝕜] ContinuousMultilinearMap 𝕜 E G') ≃L[𝕜]
    ContinuousMultilinearMap 𝕜 E (G ->L[𝕜] G') := by
  refine (flipMultilinearEquivₗ 𝕜 E G G').toContinuousLinearEquivOfBounds 1 1 ?_ ?_
  · intro f
    suffices ‖f.flipMultilinear‖ <= ‖f‖ by simpa
    apply MultilinearMap.mkContinuous_norm_le
    positivity
  · intro f
    suffices ‖f.flipLinear‖ <= ‖f‖ by simpa
    apply MultilinearMap.mkContinuousLinear_norm_le
    positivity

/--
lemma `coe_flipMultilinearEquiv` / 引理 `coe_flipMultilinearEquiv`

English:
lemma coe_flipMultilinearEquiv
  proof: rfl

中文:
引理 coe_flipMultilinearEquiv
  证明: rfl
-/
@[simp] lemma coe_flipMultilinearEquiv :
    (flipMultilinearEquiv 𝕜 E G G' : (G ->L[𝕜] ContinuousMultilinearMap 𝕜 E G') ->
      (ContinuousMultilinearMap 𝕜 E (G ->L[𝕜] G'))) = flipMultilinear := rfl

/--
lemma `coe_symm_flipMultilinearEquiv` / 引理 `coe_symm_flipMultilinearEquiv`

English:
lemma coe_symm_flipMultilinearEquiv
  proof: rfl

中文:
引理 coe_symm_flipMultilinearEquiv
  证明: rfl
-/
@[simp] lemma coe_symm_flipMultilinearEquiv :
    ((flipMultilinearEquiv 𝕜 E G G').symm : (ContinuousMultilinearMap 𝕜 E (G ->L[𝕜] G')) ->
    (G ->L[𝕜] ContinuousMultilinearMap 𝕜 E G')) = flipLinear := rfl

end ContinuousLinearMap

/--
theorem `LinearIsometry.norm_compContinuousMultilinearMap` / 定理 `LinearIsometry.norm_compContinuousMultilinearMap`

English:
theorem LinearIsometry.norm_compContinuousMultilinearMap
  statement: (g : G ->ₗᵢ[𝕜] G')
  proof: by
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map,
    ContinuousMultilinearMap.norm_def, Function.comp_apply]

中文:
定理 线性等距.norm_compContinuousMultilinearMap
  结论: (g : G ->ₗᵢ[𝕜] G')
  证明: by
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map,
    ContinuousMultilinearMap.norm_def, Function.comp_apply]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.compContinuousMultilinearMap_coe, ContinuousMultilinearMap, ContinuousMultilinearMap.norm_def, Function, Function.comp_apply, LinearIsometry, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map, coe_toContinuousLinearMap, compContinuousMultilinearMap_coe, comp_apply, norm_def, norm_map
-/
theorem LinearIsometry.norm_compContinuousMultilinearMap (g : G ->ₗᵢ[𝕜] G')
    (f : ContinuousMultilinearMap 𝕜 E G) :
    ‖g.toContinuousLinearMap.compContinuousMultilinearMap f‖ = ‖f‖ := by
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map,
    ContinuousMultilinearMap.norm_def, Function.comp_apply]

namespace ContinuousMultilinearMap

/--
theorem `norm_compContinuousLinearMap_le` / 定理 `norm_compContinuousLinearMap_le`

English:
theorem norm_compContinuousLinearMap_le
  statement: (g : ContinuousMultilinearMap 𝕜 E₁ G)
  proof: opNorm_le_bound (by positivity) fun m =>
    calc
      ‖g fun i => f i (m i)‖ <= ‖g‖ * ∏ i, ‖f i (m i)‖ := g.le_opNorm _
      _ <= ‖g‖ * ∏ i, ‖f i‖ * ‖m i‖ := by gcongr with i; exact (f i).le_opNorm (m i)
      _ = (‖g‖ * ∏ i, ‖f i‖) * ∏ i, ‖m i‖ := by rw [prod_mul_distrib, mul_assoc]

中文:
定理 norm_compContinuousLinearMap_le
  结论: (g : 连续多重线性映射 𝕜 E₁ G)
  证明: opNorm_le_bound (by positivity) fun m =>
    calc
      ‖g fun i => f i (m i)‖ <= ‖g‖ * ∏ i, ‖f i (m i)‖ := g.le_opNorm _
      _ <= ‖g‖ * ∏ i, ‖f i‖ * ‖m i‖ := by gcongr with i; exact (f i).le_opNorm (m i)
      _ = (‖g‖ * ∏ i, ‖f i‖) * ∏ i, ‖m i‖ := by rw [prod_mul_distrib, mul_assoc]

Depends on / 依赖: g.le_opNorm, le_opNorm, mul_assoc, opNorm_le_bound, prod_mul_distrib
-/
theorem norm_compContinuousLinearMap_le (g : ContinuousMultilinearMap 𝕜 E₁ G)
    (f : forall i, E i ->L[𝕜] E₁ i) : ‖g.compContinuousLinearMap f‖ <= ‖g‖ * ∏ i, ‖f i‖ :=
  opNorm_le_bound (by positivity) fun m =>
    calc
      ‖g fun i => f i (m i)‖ <= ‖g‖ * ∏ i, ‖f i (m i)‖ := g.le_opNorm _
      _ <= ‖g‖ * ∏ i, ‖f i‖ * ‖m i‖ := by gcongr with i; exact (f i).le_opNorm (m i)
      _ = (‖g‖ * ∏ i, ‖f i‖) * ∏ i, ‖m i‖ := by rw [prod_mul_distrib, mul_assoc]

/--
theorem `norm_compContinuous_linearIsometry_le` / 定理 `norm_compContinuous_linearIsometry_le`

English:
theorem norm_compContinuous_linearIsometry_le
  statement: (g : ContinuousMultilinearMap 𝕜 E₁ G)
  proof: by
  refine opNorm_le_bound (norm_nonneg _) fun m => ?_
  apply (g.le_opNorm _).trans _
  simp only [ContinuousLinearMap.coe_coe, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map, le_rfl]

中文:
定理 norm_compContinuous_linearIsometry_le
  结论: (g : 连续多重线性映射 𝕜 E₁ G)
  证明: by
  refine opNorm_le_bound (norm_nonneg _) fun m => ?_
  apply (g.le_opNorm _).trans _
  simp only [ContinuousLinearMap.coe_coe, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map, le_rfl]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_coe, LinearIsometry, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map, coe_coe, coe_toContinuousLinearMap, g.le_opNorm, le_opNorm, le_rfl, norm_map, norm_nonneg, opNorm_le_bound
-/
theorem norm_compContinuous_linearIsometry_le (g : ContinuousMultilinearMap 𝕜 E₁ G)
    (f : forall i, E i ->ₗᵢ[𝕜] E₁ i) :
    ‖g.compContinuousLinearMap fun i => (f i).toContinuousLinearMap‖ <= ‖g‖ := by
  refine opNorm_le_bound (norm_nonneg _) fun m => ?_
  apply (g.le_opNorm _).trans _
  simp only [ContinuousLinearMap.coe_coe, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map, le_rfl]

/--
theorem `norm_compContinuous_linearIsometryEquiv` / 定理 `norm_compContinuous_linearIsometryEquiv`

English:
theorem norm_compContinuous_linearIsometryEquiv
  statement: (g : ContinuousMultilinearMap 𝕜 E₁ G)
  proof: by
  apply le_antisymm (g.norm_compContinuous_linearIsometry_le fun i => (f i).toLinearIsometry)
  have : g = (g.compContinuousLinearMap fun i => (f i : E i ->L[𝕜] E₁ i)).compContinuousLinearMap
      fun i => ((f i).symm : E₁ i ->L[𝕜] E i) := by
    ext1 m
    simp
  conv_lhs => rw [this]
  apply (g.compContinuousLinearMap fun i =>
    (f i : E i ->L[𝕜] E₁ i)).norm_compContinuous_linearIsometry_le
      fun i => (f i).symm.toLinearIsometry

中文:
定理 norm_compContinuous_linearIsometryEquiv
  结论: (g : 连续多重线性映射 𝕜 E₁ G)
  证明: by
  apply le_antisymm (g.norm_compContinuous_linearIsometry_le fun i => (f i).toLinearIsometry)
  have : g = (g.compContinuousLinearMap fun i => (f i : E i ->L[𝕜] E₁ i)).compContinuousLinearMap
      fun i => ((f i).symm : E₁ i ->L[𝕜] E i) := by
    ext1 m
    simp
  conv_lhs => rw [this]
  apply (g.compContinuousLinearMap fun i =>
    (f i : E i ->L[𝕜] E₁ i)).norm_compContinuous_linearIsometry_le
      fun i => (f i).symm.toLinearIsometry

Depends on / 依赖: compContinuousLinearMap, conv_lhs, g.compContinuousLinearMap, g.norm_compContinuous_linearIsometry_le, le_antisymm, norm_compContinuous_linearIsometry_le, symm.toLinearIsometry, toLinearIsometry
-/
theorem norm_compContinuous_linearIsometryEquiv (g : ContinuousMultilinearMap 𝕜 E₁ G)
    (f : forall i, E i ≃ₗᵢ[𝕜] E₁ i) :
    ‖g.compContinuousLinearMap fun i => (f i : E i ->L[𝕜] E₁ i)‖ = ‖g‖ := by
  apply le_antisymm (g.norm_compContinuous_linearIsometry_le fun i => (f i).toLinearIsometry)
  have : g = (g.compContinuousLinearMap fun i => (f i : E i ->L[𝕜] E₁ i)).compContinuousLinearMap
      fun i => ((f i).symm : E₁ i ->L[𝕜] E i) := by
    ext1 m
    simp
  conv_lhs => rw [this]
  apply (g.compContinuousLinearMap fun i =>
    (f i : E i ->L[𝕜] E₁ i)).norm_compContinuous_linearIsometry_le
      fun i => (f i).symm.toLinearIsometry


variable (G) in
/--
theorem `norm_compContinuousLinearMapL_le` / 定理 `norm_compContinuousLinearMapL_le`

English:
theorem norm_compContinuousLinearMapL_le
  given: (f : forall i, E i ->L[𝕜] E₁ i)
  proof: ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g =>
.trans_eq mul_comm _ _ norm_compContinuousLinearMap_le _ _

中文:
定理 norm_compContinuousLinearMapL_le
  条件: (f : 对任意 i, E i ->L[𝕜] E₁ i)
  证明: ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g =>
.trans_eq mul_comm _ _ norm_compContinuousLinearMap_le _ _
-/
theorem norm_compContinuousLinearMapL_le (f : forall i, E i ->L[𝕜] E₁ i) :
    ‖compContinuousLinearMapL (F := G) f‖ <= ∏ i, ‖f i‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g =>
.trans_eq mul_comm _ _ norm_compContinuousLinearMap_le _ _

/--
Definition of `compContinuousLinearMapLRight` / `compContinuousLinearMapLRight` 的定义

English:
definition compContinuousLinearMapLRight
  signature: (g : ContinuousMultilinearMap 𝕜 E₁ G)
  body: MultilinearMap.mkContinuous
    { toFun := fun f => g.compContinuousLinearMap f
      map_update_add' := by
        intro h f i f₁ f₂
        ext x
        simp only [compContinuousLinearMap_apply, add_apply]
        convert! g.map_update_add (fun j => f j (x j)) i (f₁ (x i)) (f₂ (x i)) <;>
          exact apply_update (fun (i : ι) (f : E i ->L[𝕜] E₁ i) => f (x i)) f i _ _
      map_update_smul' := by
        intro h f i a f₀
        ext x
        simp only [compContinuousLinearMap_apply, smul_apply]
        convert! g.map_update_smul (fun j => f j (x j)) i a (f₀ (x i)) <;>
          exact apply_update (fun (i : ι) (f : E i ->L[𝕜] E₁ i) => f (x i)) f i _ _ }
    (‖g‖) (fun f => by simp [norm_compContinuousLinearMap_le])

@[simp]

中文:
定义 compContinuousLinearMapLRight
  签名: (g : 连续多重线性映射 𝕜 E₁ G)
  定义体: MultilinearMap.mkContinuous
    { toFun := fun f => g.compContinuousLinearMap f
      map_update_add' := by
        intro h f i f₁ f₂
        ext x
        simp only [compContinuousLinearMap_apply, add_apply]
        convert! g.map_update_add (fun j => f j (x j)) i (f₁ (x i)) (f₂ (x i)) <;>
          exact apply_update (fun (i : ι) (f : E i ->L[𝕜] E₁ i) => f (x i)) f i _ _
      map_update_smul' := by
        intro h f i a f₀
        ext x
        simp only [compContinuousLinearMap_apply, smul_apply]
        convert! g.map_update_smul (fun j => f j (x j)) i a (f₀ (x i)) <;>
          exact apply_update (fun (i : ι) (f : E i ->L[𝕜] E₁ i) => f (x i)) f i _ _ }
    (‖g‖) (fun f => by simp [norm_compContinuousLinearMap_le])

@[simp]

Depends on / 依赖: MultilinearMap, MultilinearMap.mkContinuous, add_apply, apply_update, compContinuousLinearMap, compContinuousLinearMap_apply, convert, g.compContinuousLinearMap, g.map_update_add, g.map_update_smul, map_update_add, map_update_smul, mkContinuous, smul_apply
-/
def compContinuousLinearMapLRight (g : ContinuousMultilinearMap 𝕜 E₁ G) :
    ContinuousMultilinearMap 𝕜 (fun i => E i ->L[𝕜] E₁ i) (ContinuousMultilinearMap 𝕜 E G) :=
  MultilinearMap.mkContinuous
    { toFun := fun f => g.compContinuousLinearMap f
      map_update_add' := by
        intro h f i f₁ f₂
        ext x
        simp only [compContinuousLinearMap_apply, add_apply]
        convert! g.map_update_add (fun j => f j (x j)) i (f₁ (x i)) (f₂ (x i)) <;>
          exact apply_update (fun (i : ι) (f : E i ->L[𝕜] E₁ i) => f (x i)) f i _ _
      map_update_smul' := by
        intro h f i a f₀
        ext x
        simp only [compContinuousLinearMap_apply, smul_apply]
        convert! g.map_update_smul (fun j => f j (x j)) i a (f₀ (x i)) <;>
          exact apply_update (fun (i : ι) (f : E i ->L[𝕜] E₁ i) => f (x i)) f i _ _ }
    (‖g‖) (fun f => by simp [norm_compContinuousLinearMap_le])

@[simp]
/--
theorem `compContinuousLinearMapLRight_apply` / 定理 `compContinuousLinearMapLRight_apply`

English:
theorem compContinuousLinearMapLRight_apply
  statement: (g : ContinuousMultilinearMap 𝕜 E₁ G)
  proof: rfl

中文:
定理 compContinuousLinearMapLRight_apply
  结论: (g : 连续多重线性映射 𝕜 E₁ G)
  证明: rfl
-/
theorem compContinuousLinearMapLRight_apply (g : ContinuousMultilinearMap 𝕜 E₁ G)
    (f : forall i, E i ->L[𝕜] E₁ i) : compContinuousLinearMapLRight g f = g.compContinuousLinearMap f :=
  rfl

variable (E) in
/--
theorem `norm_compContinuousLinearMapLRight_le` / 定理 `norm_compContinuousLinearMapLRight_le`

English:
theorem norm_compContinuousLinearMapLRight_le
  given: (g : ContinuousMultilinearMap 𝕜 E₁ G)
  proof: MultilinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

中文:
定理 norm_compContinuousLinearMapLRight_le
  条件: (g : 连续多重线性映射 𝕜 E₁ G)
  证明: MultilinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
-/
theorem norm_compContinuousLinearMapLRight_le (g : ContinuousMultilinearMap 𝕜 E₁ G) :
    ‖compContinuousLinearMapLRight (E := E) g‖ <= ‖g‖ :=
  MultilinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

variable (𝕜 E E₁ G)

open Function in
/--
Definition of `compContinuousLinearMapMultilinear` / `compContinuousLinearMapMultilinear` 的定义

English:
definition compContinuousLinearMapMultilinear
  signature: :
  body: compContinuousLinearMapL
  map_update_add' f i f₁ f₂ := by
    ext g x
    change (g fun j => update f i (f₁ + f₂) j <| x j) =
        (g fun j => update f i f₁ j <| x j) + g fun j => update f i f₂ j (x j)
    convert! g.map_update_add (fun j => f j (x j)) i (f₁ (x i)) (f₂ (x i)) <;>
      exact apply_update (fun (i : ι) (f : E i ->L[𝕜] E₁ i) => f (x i)) f i _ _
  map_update_smul' f i a f₀ := by
    ext g x
    change (g fun j => update f i (a • f₀) j <| x j) = a • g fun j => update f i f₀ j (x j)
    convert! g.map_update_smul (fun j => f j (x j)) i a (f₀ (x i)) <;>
      exact apply_update (fun (i : ι) (f : E i ->L[𝕜] E₁ i) => f (x i)) f i _ _

中文:
定义 compContinuousLinearMapMultilinear
  签名: :
  定义体: compContinuousLinearMapL
  map_update_add' f i f₁ f₂ := by
    ext g x
    change (g fun j => update f i (f₁ + f₂) j <| x j) =
        (g fun j => update f i f₁ j <| x j) + g fun j => update f i f₂ j (x j)
    convert! g.map_update_add (fun j => f j (x j)) i (f₁ (x i)) (f₂ (x i)) <;>
      exact apply_update (fun (i : ι) (f : E i ->L[𝕜] E₁ i) => f (x i)) f i _ _
  map_update_smul' f i a f₀ := by
    ext g x
    change (g fun j => update f i (a • f₀) j <| x j) = a • g fun j => update f i f₀ j (x j)
    convert! g.map_update_smul (fun j => f j (x j)) i a (f₀ (x i)) <;>
      exact apply_update (fun (i : ι) (f : E i ->L[𝕜] E₁ i) => f (x i)) f i _ _

Depends on / 依赖: compContinuousLinearMapL
-/
noncomputable def compContinuousLinearMapMultilinear :
    MultilinearMap 𝕜 (fun i => E i ->L[𝕜] E₁ i)
      ((ContinuousMultilinearMap 𝕜 E₁ G) ->L[𝕜] ContinuousMultilinearMap 𝕜 E G) where
  toFun := compContinuousLinearMapL
  map_update_add' f i f₁ f₂ := by
    ext g x
    change (g fun j => update f i (f₁ + f₂) j <| x j) =
        (g fun j => update f i f₁ j <| x j) + g fun j => update f i f₂ j (x j)
    convert! g.map_update_add (fun j => f j (x j)) i (f₁ (x i)) (f₂ (x i)) <;>
      exact apply_update (fun (i : ι) (f : E i ->L[𝕜] E₁ i) => f (x i)) f i _ _
  map_update_smul' f i a f₀ := by
    ext g x
    change (g fun j => update f i (a • f₀) j <| x j) = a • g fun j => update f i f₀ j (x j)
    convert! g.map_update_smul (fun j => f j (x j)) i a (f₀ (x i)) <;>
      exact apply_update (fun (i : ι) (f : E i ->L[𝕜] E₁ i) => f (x i)) f i _ _

/-- If `f` is a collection of continuous linear maps, then the construction
`ContinuousMultilinearMap.compContinuousLinearMap`
sending a continuous multilinear map `g` to `g (f₁ ·, ..., fₙ ·)` is continuous-linear in `g` and
continuous-multilinear in `f₁, ..., fₙ`. -/
@[simps! apply_apply]
/--
Definition of `compContinuousLinearMapContinuousMultilinear` / `compContinuousLinearMapContinuousMultilinear` 的定义

English:
definition compContinuousLinearMapContinuousMultilinear
  signature: :
  body: MultilinearMap.mkContinuous (𝕜 := 𝕜) (E := fun i => E i ->L[𝕜] E₁ i)
    (G := (ContinuousMultilinearMap 𝕜 E₁ G) ->L[𝕜] ContinuousMultilinearMap 𝕜 E G)
    (compContinuousLinearMapMultilinear 𝕜 E E₁ G) 1 fun f => by
      rw [one_mul]
      apply norm_compContinuousLinearMapL_le

中文:
定义 compContinuousLinearMapContinuousMultilinear
  签名: :
  定义体: MultilinearMap.mkContinuous (𝕜 := 𝕜) (E := fun i => E i ->L[𝕜] E₁ i)
    (G := (ContinuousMultilinearMap 𝕜 E₁ G) ->L[𝕜] ContinuousMultilinearMap 𝕜 E G)
    (compContinuousLinearMapMultilinear 𝕜 E E₁ G) 1 fun f => by
      rw [one_mul]
      apply norm_compContinuousLinearMapL_le

Depends on / 依赖: ContinuousMultilinearMap, MultilinearMap, MultilinearMap.mkContinuous, compContinuousLinearMapMultilinear, mkContinuous, norm_compContinuousLinearMapL_le, one_mul
-/
noncomputable def compContinuousLinearMapContinuousMultilinear :
    ContinuousMultilinearMap 𝕜 (fun i => E i ->L[𝕜] E₁ i)
      ((ContinuousMultilinearMap 𝕜 E₁ G) ->L[𝕜] ContinuousMultilinearMap 𝕜 E G) :=
  MultilinearMap.mkContinuous (𝕜 := 𝕜) (E := fun i => E i ->L[𝕜] E₁ i)
    (G := (ContinuousMultilinearMap 𝕜 E₁ G) ->L[𝕜] ContinuousMultilinearMap 𝕜 E G)
    (compContinuousLinearMapMultilinear 𝕜 E E₁ G) 1 fun f => by
      rw [one_mul]
      apply norm_compContinuousLinearMapL_le

variable {𝕜 E E₁ G}

/--
Definition of `fderivCompContinuousLinearMap` / `fderivCompContinuousLinearMap` 的定义

English:
definition fderivCompContinuousLinearMap
  signature: [DecidableEq ι]
  body: ContinuousLinearMap.apply _ _ f
.compContinuousMultilinearMap (compContinuousLinearMapContinuousMultilinear 𝕜 _ _ _)
.linearDeriv g

@[simp]

中文:
定义 fderivCompContinuousLinearMap
  签名: [DecidableEq ι]
  定义体: ContinuousLinearMap.apply _ _ f
.compContinuousMultilinearMap (compContinuousLinearMapContinuousMultilinear 𝕜 _ _ _)
.linearDeriv g

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.apply, compContinuousLinearMapContinuousMultilinear, compContinuousMultilinearMap, linearDeriv
-/
noncomputable def fderivCompContinuousLinearMap [DecidableEq ι]
    (f : ContinuousMultilinearMap 𝕜 E₁ G) (g : forall i, E i ->L[𝕜] E₁ i) :
    (forall i, E i ->L[𝕜] E₁ i) ->L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
  ContinuousLinearMap.apply _ _ f
.compContinuousMultilinearMap (compContinuousLinearMapContinuousMultilinear 𝕜 _ _ _)
.linearDeriv g

@[simp]
/--
lemma `fderivCompContinuousLinearMap_apply` / 引理 `fderivCompContinuousLinearMap_apply`

English:
lemma fderivCompContinuousLinearMap_apply
  statement: [DecidableEq ι]
  proof: by
  simp [fderivCompContinuousLinearMap]

中文:
引理 fderivCompContinuousLinearMap_apply
  结论: [DecidableEq ι]
  证明: by
  simp [fderivCompContinuousLinearMap]

Depends on / 依赖: fderivCompContinuousLinearMap
-/
lemma fderivCompContinuousLinearMap_apply [DecidableEq ι]
    (f : ContinuousMultilinearMap 𝕜 E₁ G) (g : forall i, E i ->L[𝕜] E₁ i)
    (dg : forall i, E i ->L[𝕜] E₁ i) (v : forall i, E i) :
    f.fderivCompContinuousLinearMap g dg v = ∑ i, f fun j => (update g i (dg i) j) (v j) := by
  simp [fderivCompContinuousLinearMap]

/--
Definition of `iteratedFDerivComponent` / `iteratedFDerivComponent` 的定义

English:
definition iteratedFDerivComponent
  signature: {α : Type*} [Fintype α]
  body: (f.toMultilinearMap.iteratedFDerivComponent e).mkContinuousMultilinear ‖f‖ by
    intro x m
    simp only [MultilinearMap.iteratedFDerivComponent, MultilinearMap.domDomRestrictₗ,
      MultilinearMap.coe_mk, MultilinearMap.domDomRestrict_apply, coe_coe]
    apply (f.le_opNorm _).trans _
    classical
    rw [← prod_compl_mul_prod s.toFinset]; rw [mul_assoc]
    gcongr
    · apply le_of_eq
      have : forall x, x in s.toFinsetᶜ ↔ (fun x => x ∉ s) x := by simp
      rw [prod_subtype _ this]
      congr with i
      simp [i.2]
    · rw [prod_subtype _ (fun _ => s.mem_toFinset), ← Equiv.prod_comp e.symm]
      gcongr with i
      simpa only [i.2, ↓reduceDIte, Subtype.coe_eta] using norm_le_pi_norm (m (e.symm i)) ↑i

中文:
定义 iteratedFDerivComponent
  签名: {α : 类型} [有限类型 α]
  定义体: (f.toMultilinearMap.iteratedFDerivComponent e).mkContinuousMultilinear ‖f‖ by
    intro x m
    simp only [MultilinearMap.iteratedFDerivComponent, MultilinearMap.domDomRestrictₗ,
      MultilinearMap.coe_mk, MultilinearMap.domDomRestrict_apply, coe_coe]
    apply (f.le_opNorm _).trans _
    classical
    rw [← prod_compl_mul_prod s.toFinset]; rw [mul_assoc]
    gcongr
    · apply le_of_eq
      have : forall x, x in s.toFinsetᶜ ↔ (fun x => x ∉ s) x := by simp
      rw [prod_subtype _ this]
      congr with i
      simp [i.2]
    · rw [prod_subtype _ (fun _ => s.mem_toFinset), ← Equiv.prod_comp e.symm]
      gcongr with i
      simpa only [i.2, ↓reduceDIte, Subtype.coe_eta] using norm_le_pi_norm (m (e.symm i)) ↑i

Depends on / 依赖: MultilinearMap, MultilinearMap.coe_mk, MultilinearMap.domDomRestrict, MultilinearMap.domDomRestrict_apply, MultilinearMap.iteratedFDerivComponent, classical, coe_coe, coe_mk, domDomRestrict_apply, f.le_opNorm, f.toMultilinearMap.iteratedFDerivComponent, iteratedFDerivComponent, le_of_eq, le_opNorm, mkContinuousMultilinear, mul_assoc, prod_compl_mul_prod, prod_subtype, s.toFinset, toFinset
-/
noncomputable def iteratedFDerivComponent {α : Type*} [Fintype α]
    (f : ContinuousMultilinearMap 𝕜 E₁ G) {s : Set ι} (e : α ≃ s) [DecidablePred (· in s)] :
    ContinuousMultilinearMap 𝕜 (fun (i : {a : ι // a ∉ s}) => E₁ i)
      (ContinuousMultilinearMap 𝕜 (fun (_ : α) => (forall i, E₁ i)) G) :=
(f.toMultilinearMap.iteratedFDerivComponent e).mkContinuousMultilinear ‖f‖ by
    intro x m
    simp only [MultilinearMap.iteratedFDerivComponent, MultilinearMap.domDomRestrictₗ,
      MultilinearMap.coe_mk, MultilinearMap.domDomRestrict_apply, coe_coe]
    apply (f.le_opNorm _).trans _
    classical
    rw [← prod_compl_mul_prod s.toFinset]; rw [mul_assoc]
    gcongr
    · apply le_of_eq
      have : forall x, x in s.toFinsetᶜ ↔ (fun x => x ∉ s) x := by simp
      rw [prod_subtype _ this]
      congr with i
      simp [i.2]
    · rw [prod_subtype _ (fun _ => s.mem_toFinset), ← Equiv.prod_comp e.symm]
      gcongr with i
      simpa only [i.2, ↓reduceDIte, Subtype.coe_eta] using norm_le_pi_norm (m (e.symm i)) ↑i

/--
lemma `iteratedFDerivComponent_apply` / 引理 `iteratedFDerivComponent_apply`

English:
lemma iteratedFDerivComponent_apply
  statement: {α : Type*} [Fintype α]
  proof: by
  simp [iteratedFDerivComponent, MultilinearMap.iteratedFDerivComponent,
    MultilinearMap.domDomRestrictₗ]

中文:
引理 iteratedFDerivComponent_apply
  结论: {α : 类型} [有限类型 α]
  证明: by
  simp [iteratedFDerivComponent, MultilinearMap.iteratedFDerivComponent,
    MultilinearMap.domDomRestrictₗ]
-/
@[simp] lemma iteratedFDerivComponent_apply {α : Type*} [Fintype α]
    (f : ContinuousMultilinearMap 𝕜 E₁ G) {s : Set ι} (e : α ≃ s) [DecidablePred (· in s)]
    (v : forall i : {a : ι // a ∉ s}, E₁ i) (w : α -> (forall i, E₁ i)) :
    f.iteratedFDerivComponent e v w =
      f (fun j => if h : j in s then w (e.symm ⟨j, h⟩) j else v ⟨j, h⟩) := by
  simp [iteratedFDerivComponent, MultilinearMap.iteratedFDerivComponent,
    MultilinearMap.domDomRestrictₗ]

/--
lemma `norm_iteratedFDerivComponent_le` / 引理 `norm_iteratedFDerivComponent_le`

English:
lemma norm_iteratedFDerivComponent_le
  statement: {α : Type*} [Fintype α]
  proof: calc
  ‖f.iteratedFDerivComponent e (fun i => x i)‖
    <= ‖f.iteratedFDerivComponent e‖ * ∏ i : {a : ι // a ∉ s}, ‖x i‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
  _ <= ‖f‖ * ∏ _i : {a : ι // a ∉ s}, ‖x‖ := by
      gcongr
      · exact MultilinearMap.mkContinuousMultilinear_norm_le _ (norm_nonneg _) _
      · exact norm_le_pi_norm _ _
  _ = ‖f‖ * ‖x‖ ^ (Fintype.card {a : ι // a ∉ s}) := by rw [prod_const, card_univ]
  _ = ‖f‖ * ‖x‖ ^ (Fintype.card ι - Fintype.card α) := by simp [Fintype.card_congr e]

中文:
引理 norm_iteratedFDerivComponent_le
  结论: {α : 类型} [有限类型 α]
  证明: calc
  ‖f.iteratedFDerivComponent e (fun i => x i)‖
    <= ‖f.iteratedFDerivComponent e‖ * ∏ i : {a : ι // a ∉ s}, ‖x i‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
  _ <= ‖f‖ * ∏ _i : {a : ι // a ∉ s}, ‖x‖ := by
      gcongr
      · exact MultilinearMap.mkContinuousMultilinear_norm_le _ (norm_nonneg _) _
      · exact norm_le_pi_norm _ _
  _ = ‖f‖ * ‖x‖ ^ (Fintype.card {a : ι // a ∉ s}) := by rw [prod_const, card_univ]
  _ = ‖f‖ * ‖x‖ ^ (Fintype.card ι - Fintype.card α) := by simp [Fintype.card_congr e]
-/
lemma norm_iteratedFDerivComponent_le {α : Type*} [Fintype α]
    (f : ContinuousMultilinearMap 𝕜 E₁ G) {s : Set ι} (e : α ≃ s) [DecidablePred (· in s)]
    (x : (i : ι) -> E₁ i) :
    ‖f.iteratedFDerivComponent e (x ·)‖ <= ‖f‖ * ‖x‖ ^ (Fintype.card ι - Fintype.card α) := calc
  ‖f.iteratedFDerivComponent e (fun i => x i)‖
    <= ‖f.iteratedFDerivComponent e‖ * ∏ i : {a : ι // a ∉ s}, ‖x i‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
  _ <= ‖f‖ * ∏ _i : {a : ι // a ∉ s}, ‖x‖ := by
      gcongr
      · exact MultilinearMap.mkContinuousMultilinear_norm_le _ (norm_nonneg _) _
      · exact norm_le_pi_norm _ _
  _ = ‖f‖ * ‖x‖ ^ (Fintype.card {a : ι // a ∉ s}) := by rw [prod_const, card_univ]
  _ = ‖f‖ * ‖x‖ ^ (Fintype.card ι - Fintype.card α) := by simp [Fintype.card_congr e]

open scoped Classical in
/--
Definition of `iteratedFDeriv` / `iteratedFDeriv` 的定义

English:
definition iteratedFDeriv
  signature: (f : ContinuousMultilinearMap 𝕜 E₁ G) (k : Nat) (x : (i : ι) -> E₁ i)
  body: ∑ e : Fin k ↪ ι, iteratedFDerivComponent f e.toEquivRange (Pi.compRightL 𝕜 _ Subtype.val x)

中文:
定义 iteratedFDeriv
  签名: (f : 连续多重线性映射 𝕜 E₁ G) (k : 自然数) (x : (i : ι) -> E₁ i)
  定义体: ∑ e : Fin k ↪ ι, iteratedFDerivComponent f e.toEquivRange (Pi.compRightL 𝕜 _ Subtype.val x)
-/
protected def iteratedFDeriv (f : ContinuousMultilinearMap 𝕜 E₁ G) (k : Nat) (x : (i : ι) -> E₁ i) :
    ContinuousMultilinearMap 𝕜 (fun (_ : Fin k) => (forall i, E₁ i)) G :=
  ∑ e : Fin k ↪ ι, iteratedFDerivComponent f e.toEquivRange (Pi.compRightL 𝕜 _ Subtype.val x)

/--
lemma `norm_iteratedFDeriv_le'` / 引理 `norm_iteratedFDeriv_le'`

English:
lemma norm_iteratedFDeriv_le'
  given: (f : ContinuousMultilinearMap 𝕜 E₁ G) (k : Nat) (x : (i : ι) -> E₁ i)
  proof: by
  classical
  calc ‖f.iteratedFDeriv k x‖
  _ <= ∑ e : Fin k ↪ ι, ‖iteratedFDerivComponent f e.toEquivRange (fun i => x i)‖ := norm_sum_le _ _
  _ <= ∑ _ : Fin k ↪ ι, ‖f‖ * ‖x‖ ^ (Fintype.card ι - k) := by
    gcongr with e _
    simpa using norm_iteratedFDerivComponent_le f e.toEquivRange x
  _ = Nat.descFactorial (Fintype.card ι) k * ‖f‖ * ‖x‖ ^ (Fintype.card ι - k) := by
    simp [card_univ, mul_assoc]

中文:
引理 norm_iteratedFDeriv_le'
  条件: (f : 连续多重线性映射 𝕜 E₁ G) (k : 自然数) (x : (i : ι) -> E₁ i)
  证明: by
  classical
  calc ‖f.iteratedFDeriv k x‖
  _ <= ∑ e : Fin k ↪ ι, ‖iteratedFDerivComponent f e.toEquivRange (fun i => x i)‖ := norm_sum_le _ _
  _ <= ∑ _ : Fin k ↪ ι, ‖f‖ * ‖x‖ ^ (Fintype.card ι - k) := by
    gcongr with e _
    simpa using norm_iteratedFDerivComponent_le f e.toEquivRange x
  _ = Nat.descFactorial (Fintype.card ι) k * ‖f‖ * ‖x‖ ^ (Fintype.card ι - k) := by
    simp [card_univ, mul_assoc]

Depends on / 依赖: Fintype, Fintype.card, Nat.descFactorial, card_univ, classical, descFactorial, e.toEquivRange, f.iteratedFDeriv, iteratedFDeriv, iteratedFDerivComponent, mul_assoc, norm_iteratedFDerivComponent_le, norm_sum_le, toEquivRange
-/
lemma norm_iteratedFDeriv_le' (f : ContinuousMultilinearMap 𝕜 E₁ G) (k : Nat) (x : (i : ι) -> E₁ i) :
    ‖f.iteratedFDeriv k x‖
      <= Nat.descFactorial (Fintype.card ι) k * ‖f‖ * ‖x‖ ^ (Fintype.card ι - k) := by
  classical
  calc ‖f.iteratedFDeriv k x‖
  _ <= ∑ e : Fin k ↪ ι, ‖iteratedFDerivComponent f e.toEquivRange (fun i => x i)‖ := norm_sum_le _ _
  _ <= ∑ _ : Fin k ↪ ι, ‖f‖ * ‖x‖ ^ (Fintype.card ι - k) := by
    gcongr with e _
    simpa using norm_iteratedFDerivComponent_le f e.toEquivRange x
  _ = Nat.descFactorial (Fintype.card ι) k * ‖f‖ * ‖x‖ ^ (Fintype.card ι - k) := by
    simp [card_univ, mul_assoc]

end ContinuousMultilinearMap

end Seminorm

section Norm

namespace ContinuousMultilinearMap

/-! Results that are only true if the target space is a `NormedAddCommGroup` (and not just a
`SeminormedAddCommGroup`). -/

variable {𝕜 : Type u} {ι : Type v} {E : ι -> Type wE} {G : Type wG} {G' : Type wG'} [Fintype ι]
  [NontriviallyNormedField 𝕜] [forall i, SeminormedAddCommGroup (E i)] [forall i, NormedSpace 𝕜 (E i)]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [SeminormedAddCommGroup G'] [NormedSpace 𝕜 G']

/--
theorem `opNorm_zero_iff` / 定理 `opNorm_zero_iff`

English:
theorem opNorm_zero_iff
  given: {f : ContinuousMultilinearMap 𝕜 E G}
  statement: ‖f‖ = 0 ↔ f = 0
  proof: by
  simp [← (opNorm_nonneg f).ge_iff_eq', opNorm_le_iff le_rfl, ContinuousMultilinearMap.ext_iff]

中文:
定理 opNorm_zero_iff
  条件: {f : 连续多重线性映射 𝕜 E G}
  结论: ‖f‖ = 0 ↔ f = 0
  证明: by
  simp [← (opNorm_nonneg f).ge_iff_eq', opNorm_le_iff le_rfl, ContinuousMultilinearMap.ext_iff]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.ext_iff, ext_iff, ge_iff_eq, le_rfl, opNorm_le_iff, opNorm_nonneg
-/
theorem opNorm_zero_iff {f : ContinuousMultilinearMap 𝕜 E G} : ‖f‖ = 0 ↔ f = 0 := by
  simp [← (opNorm_nonneg f).ge_iff_eq', opNorm_le_iff le_rfl, ContinuousMultilinearMap.ext_iff]

/--
Instance `normedAddCommGroup` / 实例 `normedAddCommGroup`

English:
instance normedAddCommGroup
  signature: : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 E G)
  body: NormedAddCommGroup.ofSeparation fun _ => opNorm_zero_iff.mp

中文:
实例 normedAddCommGroup
  签名: : 赋范交换加群 (连续多重线性映射 𝕜 E G)
  定义体: NormedAddCommGroup.ofSeparation fun _ => opNorm_zero_iff.mp

Depends on / 依赖: NormedAddCommGroup, NormedAddCommGroup.ofSeparation, ofSeparation, opNorm_zero_iff, opNorm_zero_iff.mp
-/
instance normedAddCommGroup : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 E G) :=
  NormedAddCommGroup.ofSeparation fun _ => opNorm_zero_iff.mp

/--
Instance `normedAddCommGroup'` / 实例 `normedAddCommGroup'`

English:
instance normedAddCommGroup'
  signature: :
  body: ContinuousMultilinearMap.normedAddCommGroup

中文:
实例 normedAddCommGroup'
  签名: :
  定义体: ContinuousMultilinearMap.normedAddCommGroup

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.normedAddCommGroup, normedAddCommGroup
-/
instance normedAddCommGroup' :
    NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : ι => G') G) :=
  ContinuousMultilinearMap.normedAddCommGroup

variable (𝕜 G)

/--
theorem `norm_ofSubsingleton_id` / 定理 `norm_ofSubsingleton_id`

English:
theorem norm_ofSubsingleton_id
  given: [Subsingleton ι] [Nontrivial G] (i : ι)
  proof: by
  simp [ContinuousLinearMap.norm_id]

中文:
定理 norm_ofSubsingleton_id
  条件: [子单例 ι] [非平凡 G] (i : ι)
  证明: by
  simp [ContinuousLinearMap.norm_id]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.norm_id, norm_id
-/
theorem norm_ofSubsingleton_id [Subsingleton ι] [Nontrivial G] (i : ι) :
    ‖ofSubsingleton 𝕜 G G i (.id _ _)‖ = 1 := by
  simp [ContinuousLinearMap.norm_id]

/--
theorem `nnnorm_ofSubsingleton_id` / 定理 `nnnorm_ofSubsingleton_id`

English:
theorem nnnorm_ofSubsingleton_id
  given: [Subsingleton ι] [Nontrivial G] (i : ι)
  proof: NNReal.eq norm_ofSubsingleton_id ..

中文:
定理 nnnorm_ofSubsingleton_id
  条件: [子单例 ι] [非平凡 G] (i : ι)
  证明: NNReal.eq norm_ofSubsingleton_id ..

Depends on / 依赖: NNReal, NNReal.eq, norm_ofSubsingleton_id
-/
theorem nnnorm_ofSubsingleton_id [Subsingleton ι] [Nontrivial G] (i : ι) :
    ‖ofSubsingleton 𝕜 G G i (.id _ _)‖₊ = 1 :=
NNReal.eq norm_ofSubsingleton_id ..

end ContinuousMultilinearMap

end Norm

section Norm

/-! Results that are only true if the source is a `NormedAddCommGroup` (and not just a
`SeminormedAddCommGroup`). -/

variable {𝕜 : Type u} {ι : Type v} {E : ι -> Type wE} {G : Type wG} [Fintype ι]
  [NontriviallyNormedField 𝕜] [forall i, NormedAddCommGroup (E i)] [forall i, NormedSpace 𝕜 (E i)]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace MultilinearMap

/--
theorem `bound_of_shell` / 定理 `bound_of_shell`

English:
theorem bound_of_shell
  statement: (f : MultilinearMap 𝕜 E G) {ε : ι -> Real} {C : Real} {c : ι -> 𝕜}
  proof: bound_of_shell_of_norm_map_coord_zero f
    (fun h => by rw [map_coord_zero f _ (norm_eq_zero.1 h), norm_zero]) hε hc hf m

中文:
定理 bound_of_shell
  结论: (f : 多重线性映射 𝕜 E G) {ε : ι -> 实数} {C : 实数} {c : ι -> 𝕜}
  证明: bound_of_shell_of_norm_map_coord_zero f
    (fun h => by rw [map_coord_zero f _ (norm_eq_zero.1 h), norm_zero]) hε hc hf m

Depends on / 依赖: bound_of_shell_of_norm_map_coord_zero, map_coord_zero, norm_eq_zero, norm_zero
-/
theorem bound_of_shell (f : MultilinearMap 𝕜 E G) {ε : ι -> Real} {C : Real} {c : ι -> 𝕜}
    (hε : forall i, 0 < ε i) (hc : forall i, 1 < ‖c i‖)
    (hf : forall m : forall i, E i, (forall i, ε i / ‖c i‖ <= ‖m i‖) -> (forall i, ‖m i‖ < ε i) -> ‖f m‖ <= C * ∏ i, ‖m i‖)
    (m : forall i, E i) : ‖f m‖ <= C * ∏ i, ‖m i‖ :=
  bound_of_shell_of_norm_map_coord_zero f
    (fun h => by rw [map_coord_zero f _ (norm_eq_zero.1 h), norm_zero]) hε hc hf m

end MultilinearMap

end Norm
