/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
public import Mathlib.Probability.Kernel.SetIntegral

/-!
# Ionescu-Tulcea theorem

This file proves the *Ionescu-Tulcea theorem*. The idea of the statement is as follows:
consider a family of kernels `κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))`.
One can interpret `κ n` as a kernel which takes as an input the trajectory of a point started in
`X 0` and moving `X 0 → X 1 → X 2 → ... → X n` and which outputs the distribution of the next
position of the point in `X (n + 1)`. If `a b : ℕ` and `a < b`, we can compose the kernels,
and `κ a ⊗ₖ κ (a + 1) ⊗ₖ ... ⊗ₖ κ b` will take the trajectory up to time `a` as input and outputs
the distribution of the trajectory on `X (a + 1) × ... × X (b + 1)`.

The Ionescu-Tulcea theorem tells us that these compositions can be extended into a
`Kernel (Π i : Iic a, X i) (Π n > a, X n)` which given the trajectory up to time `a` outputs
the distribution of the infinite trajectory started in `X (a + 1)`. In other words this theorem
makes sense of composing infinitely many kernels together.

In this file we construct this "limit" kernel given the family `κ`. More precisely, for any `a : ℕ`,
we construct the kernel `traj κ a : Kernel (Π i : Iic a, X i) (Π n, X n)`, which takes as input
the trajectory in `X 0 × ... × X a` and outputs the distribution of the whole trajectory. The name
`traj` thus stands for "trajectory". We build a kernel with output in `Π n, X n` instead of
`Π i > a, X i` to make manipulations easier. The first coordinates are deterministic.

We also provide tools to compute integrals against `traj κ a` and an expression for the conditional
expectation.

## Main definitions

* `traj κ a`: a kernel from `Π i : Iic a, X i` to `Π n, X n` which takes as input a trajectory
  up to time `a` and outputs the distribution of the trajectory obtained by iterating the kernels
  `κ`. Its existence is given by the Ionescu-Tulcea theorem.
* `trajMeasure μ₀ κ`: a measure on `Π n, X n` that corresponds to the distribution of the trajectory
  obtained by starting with the distribution `μ₀` and then iterating the kernels `κ`.

## Main statements

* `map_traj_succ_self`: the pushforward of `traj κ a` along the the point at time `a + 1` is the
  kernel `κ a`.
* `eq_traj`: Uniqueness of `traj`: to check that `η = traj κ a` it is enough to show that
  the restriction of `η` to variables `≤ b` is `partialTraj κ a b`.
* `traj_comp_partialTraj`: Given the distribution up to time `a`, `partialTraj κ a b`
  gives the distribution of the trajectory up to time `b`, and composing this with
  `traj κ b` gives the distribution of the whole trajectory.
* `condExp_traj`: If `a ≤ b`, the conditional expectation of `f` with respect to `traj κ a`
  given the information up to time `b` is obtained by integrating `f` against `traj κ b`.
* `condDistrib_trajMeasure`: a regular conditional probability distribution of the point at time
  `a + 1` given the trajectory up to time `a` corresponds to the kernel `κ a`.


## Implementation notes

The kernel `traj κ a` is built using the Carathéodory extension theorem. First we build a projective
family of measures using `inducedFamily` and `partialTraj κ a`. Then we build a
`MeasureTheory.AddContent` on `MeasureTheory.measurableCylinders` called `trajContent` using
`projectiveFamilyContent`. Finally we prove `trajContent_tendsto_zero` which implies the
`σ`-additivity of the content, allowing to turn it into a measure.

## References

We follow the proof of Theorem 8.24 in
[O. Kallenberg, *Foundations of Modern Probability*][kallenberg2021]. For a more detailed proof
in the case of constant kernels (i.e. measures),
see Proposition 10.6.1 in [D. L. Cohn, *Measure Theory*][cohn2013measure].

## Tags

Ionescu-Tulcea theorem
-/

@[expose] public section

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory

open scoped ENNReal Topology

variable {X : Nat -> Type*}

section castLemmas

/--
lemma `Iic_pi_eq` / 引理 `Iic_pi_eq`

English:
lemma Iic_pi_eq
  given: {a b : Nat} (h : a = b)
  proof: by cases h; rfl

中文:
引理 Iic_pi_eq
  条件: {a b : 自然数} (h : a = b)
  证明: by cases h; rfl
-/
private lemma Iic_pi_eq {a b : Nat} (h : a = b) :
    (Π i : Iic a, X i) = (Π i : Iic b, X i) := by cases h; rfl

/--
lemma `cast_pi` / 引理 `cast_pi`

English:
lemma cast_pi
  given: {s t : Set Nat} (h : s = t) (x : (i : s) -> X i) (i : t)
  proof: by
  cases h; rfl

中文:
引理 cast_pi
  条件: {s t : 集合 自然数} (h : s = t) (x : (i : s) -> X i) (i : t)
  证明: by
  cases h; rfl
-/
private lemma cast_pi {s t : Set Nat} (h : s = t) (x : (i : s) -> X i) (i : t) :
    cast (congrArg (fun u : Set Nat => (Π i : u, X i)) h) x i = x ⟨i.1, h.symm ▸ i.2⟩ := by
  cases h; rfl

variable [forall n, MeasurableSpace (X n)]

/--
lemma `measure_cast` / 引理 `measure_cast`

English:
lemma measure_cast
  given: {a b : Nat} (h : a = b) (μ : (n : Nat) -> Measure (Π i : Iic n, X i))
  proof: by
  cases h
  exact Measure.map_id

中文:
引理 measure_cast
  条件: {a b : 自然数} (h : a = b) (μ : (n : 自然数) -> 测度 (Π i : 左无界右闭区间 n, X i))
  证明: by
  cases h
  exact Measure.map_id
-/
private lemma measure_cast {a b : Nat} (h : a = b) (μ : (n : Nat) -> Measure (Π i : Iic n, X i)) :
    (μ a).map (cast (Iic_pi_eq h)) = μ b := by
  cases h
  exact Measure.map_id

/--
lemma `heq_measurableSpace_Iic_pi` / 引理 `heq_measurableSpace_Iic_pi`

English:
lemma heq_measurableSpace_Iic_pi
  given: {a b : Nat} (h : a = b)
  proof: by cases h; rfl

中文:
引理 heq_measurableSpace_Iic_pi
  条件: {a b : 自然数} (h : a = b)
  证明: by cases h; rfl
-/
private lemma heq_measurableSpace_Iic_pi {a b : Nat} (h : a = b) :
    (inferInstance : MeasurableSpace (Π i : Iic a, X i)) ≍
      (inferInstance : MeasurableSpace (Π i : Iic b, X i)) := by cases h; rfl

end castLemmas

section iterateInduction

/--
Definition of `iterateInduction` / `iterateInduction` 的定义

English:
definition iterateInduction
  signature: {a : Nat} (x : Π i : Iic a, X i)

中文:
定义 iterateInduction
  签名: {a : 自然数} (x : Π i : 左无界右闭区间 a, X i)
-/
def iterateInduction {a : Nat} (x : Π i : Iic a, X i)
    (ind : (n : Nat) -> (Π i : Iic n, X i) -> X (n + 1)) : Π n, X n
  | 0 => x ⟨0, mem_Iic.2 zero_le⟩
  | k + 1 => if h : k + 1 <= a
      then x ⟨k + 1, mem_Iic.2 h⟩
      else ind k (fun i => iterateInduction x ind i)
  decreasing_by exact Nat.lt_succ_of_le (mem_Iic.1 i.2)

/--
lemma `frestrictLe_iterateInduction` / 引理 `frestrictLe_iterateInduction`

English:
lemma frestrictLe_iterateInduction
  statement: {a : Nat} (x : Π i : Iic a, X i)
  proof: by
  ext i
  simp only [frestrictLe_apply]
  obtain ⟨(zero | j), hj⟩ := i <;> rw [iterateInduction]
  rw [dif_pos (mem_Iic.1 hj)]

中文:
引理 frestrictLe_iterateInduction
  结论: {a : 自然数} (x : Π i : 左无界右闭区间 a, X i)
  证明: by
  ext i
  simp only [frestrictLe_apply]
  obtain ⟨(zero | j), hj⟩ := i <;> rw [iterateInduction]
  rw [dif_pos (mem_Iic.1 hj)]

Depends on / 依赖: dif_pos, frestrictLe_apply, iterateInduction, mem_Iic
-/
lemma frestrictLe_iterateInduction {a : Nat} (x : Π i : Iic a, X i)
    (ind : (n : Nat) -> (Π i : Iic n, X i) -> X (n + 1)) :
    frestrictLe a (iterateInduction x ind) = x := by
  ext i
  simp only [frestrictLe_apply]
  obtain ⟨(zero | j), hj⟩ := i <;> rw [iterateInduction]
  rw [dif_pos (mem_Iic.1 hj)]

end iterateInduction

variable [forall n, MeasurableSpace (X n)]

section ProjectiveFamily

namespace MeasureTheory

/-! ### Projective families indexed by `Finset ℕ` -/

variable {μ : (n : Nat) -> Measure (Π i : Iic n, X i)}

/--
theorem `isProjectiveLimit_nat_iff'` / 定理 `isProjectiveLimit_nat_iff'`

English:
theorem isProjectiveLimit_nat_iff'
  statement: {μ : (I : Finset Nat) -> Measure (Π i : I, X i)}
  proof: by
  refine ⟨fun h n _ => h (Iic n), fun h I => ?_⟩
  have := (I.subset_Iic_sup_id.trans (Iic_subset_Iic.2 (le_max_left (I.sup id) a)))
  rw [← restrict₂_comp_restrict this]; rw [← Measure.map_map]; rw [← frestrictLe]; rw [h (le_max_right _ _)]; rw [← hμ]
  all_goals fun_prop

中文:
定理 isProjectiveLimit_nat_iff'
  结论: {μ : (I : 有限集 自然数) -> 测度 (Π i : I, X i)}
  证明: by
  refine ⟨fun h n _ => h (Iic n), fun h I => ?_⟩
  have := (I.subset_Iic_sup_id.trans (Iic_subset_Iic.2 (le_max_left (I.sup id) a)))
  rw [← restrict₂_comp_restrict this]; rw [← Measure.map_map]; rw [← frestrictLe]; rw [h (le_max_right _ _)]; rw [← hμ]
  all_goals fun_prop

Depends on / 依赖: I.subset_Iic_sup_id.trans, I.sup, Iic_subset_Iic, Measure, Measure.map_map, all_goals, frestrictLe, fun_prop, le_max_left, le_max_right, map_map, subset_Iic_sup_id
-/
theorem isProjectiveLimit_nat_iff' {μ : (I : Finset Nat) -> Measure (Π i : I, X i)}
    (hμ : IsProjectiveMeasureFamily μ) (ν : Measure (Π n, X n)) (a : Nat) :
    IsProjectiveLimit ν μ ↔ forall ⦃n⦄, a <= n -> ν.map (frestrictLe n) = μ (Iic n) := by
  refine ⟨fun h n _ => h (Iic n), fun h I => ?_⟩
  have := (I.subset_Iic_sup_id.trans (Iic_subset_Iic.2 (le_max_left (I.sup id) a)))
  rw [← restrict₂_comp_restrict this]; rw [← Measure.map_map]; rw [← frestrictLe]; rw [h (le_max_right _ _)]; rw [← hμ]
  all_goals fun_prop

/--
theorem `isProjectiveLimit_nat_iff` / 定理 `isProjectiveLimit_nat_iff`

English:
theorem isProjectiveLimit_nat_iff
  statement: {μ : (I : Finset Nat) -> Measure (Π i : I, X i)}
  proof: by
  rw [isProjectiveLimit_nat_iff' hμ _ 0]
  simp

中文:
定理 isProjectiveLimit_nat_iff
  结论: {μ : (I : 有限集 自然数) -> 测度 (Π i : I, X i)}
  证明: by
  rw [isProjectiveLimit_nat_iff' hμ _ 0]
  simp

Depends on / 依赖: isProjectiveLimit_nat_iff
-/
theorem isProjectiveLimit_nat_iff {μ : (I : Finset Nat) -> Measure (Π i : I, X i)}
    (hμ : IsProjectiveMeasureFamily μ) (ν : Measure (Π n, X n)) :
    IsProjectiveLimit ν μ ↔ forall n, ν.map (frestrictLe n) = μ (Iic n) := by
  rw [isProjectiveLimit_nat_iff' hμ _ 0]
  simp

variable (μ : (n : Nat) -> Measure (Π i : Iic n, X i))

/--
Definition of `inducedFamily` / `inducedFamily` 的定义

English:
definition inducedFamily
  signature: (S : Finset Nat)
  body: (μ (S.sup id)).map (restrict₂ S.subset_Iic_sup_id)

中文:
定义 inducedFamily
  签名: (S : 有限集 自然数)
  定义体: (μ (S.sup id)).map (restrict₂ S.subset_Iic_sup_id)

Depends on / 依赖: S.subset_Iic_sup_id, S.sup, subset_Iic_sup_id
-/
noncomputable def inducedFamily (S : Finset Nat) : Measure ((k : S) -> X k) :=
    (μ (S.sup id)).map (restrict₂ S.subset_Iic_sup_id)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: n, SFinite (μ n)] (I
  body: by rw [inducedFamily]; infer_instance

中文:
实例 [对任意
  签名: n, SFinite (μ n)] (I
  定义体: by rw [inducedFamily]; infer_instance

Depends on / 依赖: inducedFamily, infer_instance
-/
instance [forall n, SFinite (μ n)] (I : Finset Nat) :
    SFinite (inducedFamily μ I) := by rw [inducedFamily]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: n, IsFiniteMeasure (μ n)] (I
  body: by rw [inducedFamily]; infer_instance

中文:
实例 [对任意
  签名: n, 是有限测度 (μ n)] (I
  定义体: by rw [inducedFamily]; infer_instance

Depends on / 依赖: inducedFamily, infer_instance
-/
instance [forall n, IsFiniteMeasure (μ n)] (I : Finset Nat) :
    IsFiniteMeasure (inducedFamily μ I) := by rw [inducedFamily]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: n, IsZeroOrProbabilityMeasure (μ n)] (I
  body: by rw [inducedFamily]; infer_instance

中文:
实例 [对任意
  签名: n, 是ZeroOrProbabilityMeasure (μ n)] (I
  定义体: by rw [inducedFamily]; infer_instance

Depends on / 依赖: inducedFamily, infer_instance
-/
instance [forall n, IsZeroOrProbabilityMeasure (μ n)] (I : Finset Nat) :
    IsZeroOrProbabilityMeasure (inducedFamily μ I) := by rw [inducedFamily]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: n, IsProbabilityMeasure (μ n)] (I
  body: by
  rw [inducedFamily]
  exact Measure.isProbabilityMeasure_map (measurable_restrict₂ _).aemeasurable

中文:
实例 [对任意
  签名: n, 是概率测度 (μ n)] (I
  定义体: by
  rw [inducedFamily]
  exact Measure.isProbabilityMeasure_map (measurable_restrict₂ _).aemeasurable

Depends on / 依赖: Measure, Measure.isProbabilityMeasure_map, aemeasurable, inducedFamily, isProbabilityMeasure_map
-/
instance [forall n, IsProbabilityMeasure (μ n)] (I : Finset Nat) :
    IsProbabilityMeasure (inducedFamily μ I) := by
  rw [inducedFamily]
  exact Measure.isProbabilityMeasure_map (measurable_restrict₂ _).aemeasurable

/--
theorem `inducedFamily_Iic` / 定理 `inducedFamily_Iic`

English:
theorem inducedFamily_Iic
  given: (n : Nat)
  statement: inducedFamily μ (Iic n) = μ n
  proof: by
  rw [inducedFamily]; rw [← measure_cast (sup_Iic n) μ]
  congr with x i
  rw [restrict₂]; rw [cast_pi (by rw [sup_Iic n])]

中文:
定理 inducedFamily_Iic
  条件: (n : 自然数)
  结论: inducedFamily μ (左无界右闭区间 n) = μ n
  证明: by
  rw [inducedFamily]; rw [← measure_cast (sup_Iic n) μ]
  congr with x i
  rw [restrict₂]; rw [cast_pi (by rw [sup_Iic n])]

Depends on / 依赖: cast_pi, inducedFamily, measure_cast, sup_Iic
-/
theorem inducedFamily_Iic (n : Nat) : inducedFamily μ (Iic n) = μ n := by
  rw [inducedFamily]; rw [← measure_cast (sup_Iic n) μ]
  congr with x i
  rw [restrict₂]; rw [cast_pi (by rw [sup_Iic n])]

/--
theorem `isProjectiveMeasureFamily_inducedFamily` / 定理 `isProjectiveMeasureFamily_inducedFamily`

English:
theorem isProjectiveMeasureFamily_inducedFamily
  proof: by
  intro I J hJI
  have sls : J.sup id <= I.sup id := sup_mono hJI
  simp only [inducedFamily]
  rw [Measure.map_map]; rw [restrict₂_comp_restrict₂]; rw [← restrict₂_comp_restrict₂ J.subset_Iic_sup_id (Iic_subset_Iic.2 sls)]; rw [← Measure.map_map]; rw [← frestrictLe₂.eq_def sls]; rw [h (J.sup id) (I.sup id) sls]
  all_goals fun_prop

中文:
定理 isProjectiveMeasureFamily_inducedFamily
  证明: by
  intro I J hJI
  have sls : J.sup id <= I.sup id := sup_mono hJI
  simp only [inducedFamily]
  rw [Measure.map_map]; rw [restrict₂_comp_restrict₂]; rw [← restrict₂_comp_restrict₂ J.subset_Iic_sup_id (Iic_subset_Iic.2 sls)]; rw [← Measure.map_map]; rw [← frestrictLe₂.eq_def sls]; rw [h (J.sup id) (I.sup id) sls]
  all_goals fun_prop

Depends on / 依赖: I.sup, Iic_subset_Iic, J.subset_Iic_sup_id, J.sup, Measure, Measure.map_map, all_goals, eq_def, fun_prop, inducedFamily, map_map, subset_Iic_sup_id, sup_mono
-/
theorem isProjectiveMeasureFamily_inducedFamily
    (h : forall a b : Nat, forall hab : a <= b, (μ b).map (frestrictLe₂ hab) = μ a) :
    IsProjectiveMeasureFamily (inducedFamily μ) := by
  intro I J hJI
  have sls : J.sup id <= I.sup id := sup_mono hJI
  simp only [inducedFamily]
  rw [Measure.map_map]; rw [restrict₂_comp_restrict₂]; rw [← restrict₂_comp_restrict₂ J.subset_Iic_sup_id (Iic_subset_Iic.2 sls)]; rw [← Measure.map_map]; rw [← frestrictLe₂.eq_def sls]; rw [h (J.sup id) (I.sup id) sls]
  all_goals fun_prop

end MeasureTheory

end ProjectiveFamily

variable {κ : (n : Nat) -> Kernel (Π i : Iic n, X i) (X (n + 1))} [forall n, IsMarkovKernel (κ n)]

namespace ProbabilityTheory.Kernel

section definition

/-! ### Definition and basic properties of `traj` -/

variable (κ)

/--
lemma `isProjectiveMeasureFamily_partialTraj` / 引理 `isProjectiveMeasureFamily_partialTraj`

English:
lemma isProjectiveMeasureFamily_partialTraj
  given: {a : Nat} (x₀ : Π i : Iic a, X i)
  proof: isProjectiveMeasureFamily_inducedFamily _
    (fun _ _ => partialTraj_map_frestrictLe₂_apply (κ := κ) x₀)

中文:
引理 isProjectiveMeasureFamily_partialTraj
  条件: {a : 自然数} (x₀ : Π i : 左无界右闭区间 a, X i)
  证明: isProjectiveMeasureFamily_inducedFamily _
    (fun _ _ => partialTraj_map_frestrictLe₂_apply (κ := κ) x₀)

Depends on / 依赖: isProjectiveMeasureFamily_inducedFamily
-/
lemma isProjectiveMeasureFamily_partialTraj {a : Nat} (x₀ : Π i : Iic a, X i) :
    IsProjectiveMeasureFamily (inducedFamily (fun b => partialTraj κ a b x₀)) :=
  isProjectiveMeasureFamily_inducedFamily _
    (fun _ _ => partialTraj_map_frestrictLe₂_apply (κ := κ) x₀)

/--
Definition of `trajContent` / `trajContent` 的定义

English:
definition trajContent
  signature: {a : Nat} (x₀ : Π i : Iic a, X i)
  body: projectiveFamilyContent (isProjectiveMeasureFamily_partialTraj κ x₀)

中文:
定义 trajContent
  签名: {a : 自然数} (x₀ : Π i : 左无界右闭区间 a, X i)
  定义体: projectiveFamilyContent (isProjectiveMeasureFamily_partialTraj κ x₀)

Depends on / 依赖: isProjectiveMeasureFamily_partialTraj, projectiveFamilyContent
-/
noncomputable def trajContent {a : Nat} (x₀ : Π i : Iic a, X i) :
    AddContent Real>=0∞ (measurableCylinders X) :=
  projectiveFamilyContent (isProjectiveMeasureFamily_partialTraj κ x₀)

variable {κ}

/--
theorem `trajContent_cylinder` / 定理 `trajContent_cylinder`

English:
theorem trajContent_cylinder
  statement: {a b : Nat} {S : Set (Π i : Iic b, X i)} (mS : MeasurableSet S)
  proof: by
  rw [trajContent]; rw [projectiveFamilyContent_cylinder _ mS]; rw [inducedFamily_Iic]

中文:
定理 trajContent_cylinder
  结论: {a b : 自然数} {S : 集合 (Π i : 左无界右闭区间 b, X i)} (mS : 可测集 S)
  证明: by
  rw [trajContent]; rw [projectiveFamilyContent_cylinder _ mS]; rw [inducedFamily_Iic]

Depends on / 依赖: inducedFamily_Iic, projectiveFamilyContent_cylinder, trajContent
-/
theorem trajContent_cylinder {a b : Nat} {S : Set (Π i : Iic b, X i)} (mS : MeasurableSet S)
    (x₀ : Π i : Iic a, X i) :
    trajContent κ x₀ (cylinder (Iic b) S) = partialTraj κ a b x₀ S := by
  rw [trajContent]; rw [projectiveFamilyContent_cylinder _ mS]; rw [inducedFamily_Iic]

/--
theorem `trajContent_eq_lmarginalPartialTraj` / 定理 `trajContent_eq_lmarginalPartialTraj`

English:
theorem trajContent_eq_lmarginalPartialTraj
  statement: {b : Nat} {S : Set (Π i : Iic b, X i)}
  proof: by
  rw [trajContent_cylinder mS]; rw [← lintegral_indicator_one mS]; rw [lmarginalPartialTraj]
  congr with x
  apply Set.indicator_const_eq_indicator_const
  rw [mem_cylinder]
  congrm (fun i => ?_) in S
  simp [updateFinset, i.2]

中文:
定理 trajContent_eq_lmarginalPartialTraj
  结论: {b : 自然数} {S : 集合 (Π i : 左无界右闭区间 b, X i)}
  证明: by
  rw [trajContent_cylinder mS]; rw [← lintegral_indicator_one mS]; rw [lmarginalPartialTraj]
  congr with x
  apply Set.indicator_const_eq_indicator_const
  rw [mem_cylinder]
  congrm (fun i => ?_) in S
  simp [updateFinset, i.2]

Depends on / 依赖: Set.indicator_const_eq_indicator_const, congrm, indicator_const_eq_indicator_const, lintegral_indicator_one, lmarginalPartialTraj, mem_cylinder, trajContent_cylinder, updateFinset
-/
theorem trajContent_eq_lmarginalPartialTraj {b : Nat} {S : Set (Π i : Iic b, X i)}
    (mS : MeasurableSet S) (x₀ : Π n, X n) (a : Nat) :
    trajContent κ (frestrictLe a x₀) (cylinder (Iic b) S) =
      lmarginalPartialTraj κ a b ((cylinder (Iic b) S).indicator 1) x₀ := by
  rw [trajContent_cylinder mS]; rw [← lintegral_indicator_one mS]; rw [lmarginalPartialTraj]
  congr with x
  apply Set.indicator_const_eq_indicator_const
  rw [mem_cylinder]
  congrm (fun i => ?_) in S
  simp [updateFinset, i.2]

/--
lemma `trajContent_ne_top` / 引理 `trajContent_ne_top`

English:
lemma trajContent_ne_top
  given: {a : Nat} {x : Π i : Iic a, X i} {s : Set (Π n, X n)}
  proof: projectiveFamilyContent_ne_top (isProjectiveMeasureFamily_partialTraj κ x)

中文:
引理 trajContent_ne_top
  条件: {a : 自然数} {x : Π i : 左无界右闭区间 a, X i} {s : 集合 (Π n, X n)}
  证明: projectiveFamilyContent_ne_top (isProjectiveMeasureFamily_partialTraj κ x)

Depends on / 依赖: isProjectiveMeasureFamily_partialTraj, projectiveFamilyContent_ne_top
-/
lemma trajContent_ne_top {a : Nat} {x : Π i : Iic a, X i} {s : Set (Π n, X n)} :
    trajContent κ x s != ∞ :=
  projectiveFamilyContent_ne_top (isProjectiveMeasureFamily_partialTraj κ x)

/--
theorem `le_lmarginalPartialTraj_succ` / 定理 `le_lmarginalPartialTraj_succ`

English:
theorem le_lmarginalPartialTraj_succ
  statement: {f : Nat -> (Π n, X n) -> Real>=0∞} {a : Nat -> Nat}
  proof: by
  have _ n : Nonempty (X n) := by
    induction n using Nat.case_strong_induction_on with
    | hz => exact ⟨y ⟨0, mem_Iic.2 zero_le⟩⟩
    | hi m hm =>
      have : Nonempty (Π i : Iic m, X i) :=
        ⟨fun i => @Classical.ofNonempty _ (hm i.1 (mem_Iic.1 i.2))⟩
      exact nonempty_of_isProbabilityMeasure (κ m Classical.ofNonempty)
  -- `Fₙ` is the integral of `fₙ` from time `k + 1` to `aₙ`.
  let F n : (Π n, X n) -> Real>=0∞ := lmarginalPartialTraj κ (k + 1) (a n) (f n)
  -- `Fₙ` converges to `l` by hypothesis.
  have tendstoF x : Tendsto (F · x) atTop (𝓝 (l x)) := htendsto x
  -- Integrating `fₙ` between time `k` and `aₙ` is the same as integrating
  -- `Fₙ` between time `k` and time `k + 1`.
  have f_eq x n : lmarginalPartialTraj κ k (a n) (f n) x =
      lmarginalPartialTraj κ k (k + 1) (F n) x := by
    simp_rw [F]
    obtain h | h | h := lt_trichotomy (k + 1) (a n)
    · rw [← lmarginalPartialTraj_self k.le_succ h.le (mf n)]
    · rw [← h, lmarginalPartialTraj_le _ le_rfl (mf n)]
    · rw [lmarginalPartialTraj_le _ _ (mf n), (hcte n).lmarginalPartialTraj_of_le _ (mf n),
        (hcte n).lmarginalPartialTraj_of_le _ (mf n)]
      all_goals lia
  -- `F` is also a bounded sequence.
  have F_le n x : F n x <= bound := by
    simpa [F, lmarginalPartialTraj] using lintegral_le_const (ae_of_all _ fun z => le_bound _ _)
  -- By dominated convergence, the integral of `fₙ` between time `k` and time `a n` converges
  -- to the integral of `l` between time `k` and time `k + 1`.
  have tendsto_int x : Tendsto (fun n => lmarginalPartialTraj κ k (a n) (f n) x) atTop
      (𝓝 (lmarginalPartialTraj κ k (k + 1) l x)) := by
    simp_rw [f_eq, lmarginalPartialTraj]
    exact tendsto_lintegral_of_dominated_convergence (fun _ => bound)
      (fun n => (measurable_lmarginalPartialTraj _ _ (mf n)).comp measurable_updateFinset)
      (fun n => Eventually.of_forall <| fun y => F_le n _)
      (by simp [fin_bound]) (Eventually.of_forall (fun _ => tendstoF _))
  -- By hypothesis, we have `ε ≤ lmarginalPartialTraj κ k (k + 1) (F n) (updateFinset x _ y)`,
  -- so this is also true for `l`.
  have ε_le_lint x : ε <= lmarginalPartialTraj κ k (k + 1) l (updateFinset x _ y) :=
    ge_of_tendsto (tendsto_int _) (by simp [hpos])
  let x_ : Π n, X n := Classical.ofNonempty
  -- We now have that the integral of `l` with respect to a probability measure is greater than `ε`,
  -- therefore there exists `x` such that `ε ≤ l(y, x)`.
  obtain ⟨x, hx⟩ : exists x, ε <= l (update (updateFinset x_ _ y) (k + 1) x) := by
    have : ∫⁻ x, l (update (updateFinset x_ _ y) (k + 1) x) ∂(κ k y) != ∞ :=
ne_top_of_le_ne_top fin_bound lintegral_le_const ae_of_all _
fun y => le_of_tendsto' (tendstoF _) fun _ => F_le _ _
    obtain ⟨x, hx⟩ := exists_lintegral_le this
    refine ⟨x, (ε_le_lint x_).trans ?_⟩
    rwa [lmarginalPartialTraj_succ, frestrictLe_updateFinset]
    exact ENNReal.measurable_of_tendsto (by fun_prop) (tendsto_pi_nhds.2 htendsto)
  refine ⟨x, fun x' n => ?_⟩
  -- As `F` is a non-increasing sequence, we have `ε ≤ Fₙ(y, x)` for any `n`.
  have := le_trans hx ((anti _).le_of_tendsto (tendstoF _) n)
  -- This part below is just to say that this is true for any `x : (i : ι) → X i`,
  -- as `Fₙ` technically depends on all the variables, but really depends only on the first `k + 1`.
  convert! this using 1
  refine (hcte n).dependsOn_lmarginalPartialTraj _ (mf n) fun i hi => ?_
  simp only [update, updateFinset, mem_Iic]
  split_ifs with h1 h2 <;> try rfl
  rw [mem_coe]; rw [mem_Iic] at hi
  lia

中文:
定理 le_lmarginalPartialTraj_succ
  结论: {f : 自然数 -> (Π n, X n) -> 实数>=0∞} {a : 自然数 -> 自然数}
  证明: by
  have _ n : Nonempty (X n) := by
    induction n using Nat.case_strong_induction_on with
    | hz => exact ⟨y ⟨0, mem_Iic.2 zero_le⟩⟩
    | hi m hm =>
      have : Nonempty (Π i : Iic m, X i) :=
        ⟨fun i => @Classical.ofNonempty _ (hm i.1 (mem_Iic.1 i.2))⟩
      exact nonempty_of_isProbabilityMeasure (κ m Classical.ofNonempty)
  -- `Fₙ` is the integral of `fₙ` from time `k + 1` to `aₙ`.
  let F n : (Π n, X n) -> Real>=0∞ := lmarginalPartialTraj κ (k + 1) (a n) (f n)
  -- `Fₙ` converges to `l` by hypothesis.
  have tendstoF x : Tendsto (F · x) atTop (𝓝 (l x)) := htendsto x
  -- Integrating `fₙ` between time `k` and `aₙ` is the same as integrating
  -- `Fₙ` between time `k` and time `k + 1`.
  have f_eq x n : lmarginalPartialTraj κ k (a n) (f n) x =
      lmarginalPartialTraj κ k (k + 1) (F n) x := by
    simp_rw [F]
    obtain h | h | h := lt_trichotomy (k + 1) (a n)
    · rw [← lmarginalPartialTraj_self k.le_succ h.le (mf n)]
    · rw [← h, lmarginalPartialTraj_le _ le_rfl (mf n)]
    · rw [lmarginalPartialTraj_le _ _ (mf n), (hcte n).lmarginalPartialTraj_of_le _ (mf n),
        (hcte n).lmarginalPartialTraj_of_le _ (mf n)]
      all_goals lia
  -- `F` is also a bounded sequence.
  have F_le n x : F n x <= bound := by
    simpa [F, lmarginalPartialTraj] using lintegral_le_const (ae_of_all _ fun z => le_bound _ _)
  -- By dominated convergence, the integral of `fₙ` between time `k` and time `a n` converges
  -- to the integral of `l` between time `k` and time `k + 1`.
  have tendsto_int x : Tendsto (fun n => lmarginalPartialTraj κ k (a n) (f n) x) atTop
      (𝓝 (lmarginalPartialTraj κ k (k + 1) l x)) := by
    simp_rw [f_eq, lmarginalPartialTraj]
    exact tendsto_lintegral_of_dominated_convergence (fun _ => bound)
      (fun n => (measurable_lmarginalPartialTraj _ _ (mf n)).comp measurable_updateFinset)
      (fun n => Eventually.of_forall <| fun y => F_le n _)
      (by simp [fin_bound]) (Eventually.of_forall (fun _ => tendstoF _))
  -- By hypothesis, we have `ε ≤ lmarginalPartialTraj κ k (k + 1) (F n) (updateFinset x _ y)`,
  -- so this is also true for `l`.
  have ε_le_lint x : ε <= lmarginalPartialTraj κ k (k + 1) l (updateFinset x _ y) :=
    ge_of_tendsto (tendsto_int _) (by simp [hpos])
  let x_ : Π n, X n := Classical.ofNonempty
  -- We now have that the integral of `l` with respect to a probability measure is greater than `ε`,
  -- therefore there exists `x` such that `ε ≤ l(y, x)`.
  obtain ⟨x, hx⟩ : exists x, ε <= l (update (updateFinset x_ _ y) (k + 1) x) := by
    have : ∫⁻ x, l (update (updateFinset x_ _ y) (k + 1) x) ∂(κ k y) != ∞ :=
ne_top_of_le_ne_top fin_bound lintegral_le_const ae_of_all _
fun y => le_of_tendsto' (tendstoF _) fun _ => F_le _ _
    obtain ⟨x, hx⟩ := exists_lintegral_le this
    refine ⟨x, (ε_le_lint x_).trans ?_⟩
    rwa [lmarginalPartialTraj_succ, frestrictLe_updateFinset]
    exact ENNReal.measurable_of_tendsto (by fun_prop) (tendsto_pi_nhds.2 htendsto)
  refine ⟨x, fun x' n => ?_⟩
  -- As `F` is a non-increasing sequence, we have `ε ≤ Fₙ(y, x)` for any `n`.
  have := le_trans hx ((anti _).le_of_tendsto (tendstoF _) n)
  -- This part below is just to say that this is true for any `x : (i : ι) → X i`,
  -- as `Fₙ` technically depends on all the variables, but really depends only on the first `k + 1`.
  convert! this using 1
  refine (hcte n).dependsOn_lmarginalPartialTraj _ (mf n) fun i hi => ?_
  simp only [update, updateFinset, mem_Iic]
  split_ifs with h1 h2 <;> try rfl
  rw [mem_coe]; rw [mem_Iic] at hi
  lia

Depends on / 依赖: Classical, Classical.ofNonempty, Nat.case_strong_induction_on, Nonempty, case_strong_induction_on, mem_Iic, nonempty_of_isProbabilityMeasure, ofNonempty, zero_le
-/
theorem le_lmarginalPartialTraj_succ {f : Nat -> (Π n, X n) -> Real>=0∞} {a : Nat -> Nat}
    (hcte : forall n, DependsOn (f n) (Iic (a n))) (mf : forall n, Measurable (f n))
    {bound : Real>=0∞} (fin_bound : bound != ∞) (le_bound : forall n x, f n x <= bound) {k : Nat}
    (anti : forall x, Antitone (fun n => lmarginalPartialTraj κ (k + 1) (a n) (f n) x))
    {l : (Π n, X n) -> Real>=0∞}
    (htendsto : forall x, Tendsto (fun n => lmarginalPartialTraj κ (k + 1) (a n) (f n) x) atTop (𝓝 (l x)))
    (ε : Real>=0∞) (y : Π i : Iic k, X i)
    (hpos : forall x n, ε <= lmarginalPartialTraj κ k (a n) (f n) (updateFinset x (Iic k) y)) :
    exists z, forall x n,
    ε <= lmarginalPartialTraj κ (k + 1) (a n) (f n)
      (update (updateFinset x (Iic k) y) (k + 1) z) := by
  have _ n : Nonempty (X n) := by
    induction n using Nat.case_strong_induction_on with
    | hz => exact ⟨y ⟨0, mem_Iic.2 zero_le⟩⟩
    | hi m hm =>
      have : Nonempty (Π i : Iic m, X i) :=
        ⟨fun i => @Classical.ofNonempty _ (hm i.1 (mem_Iic.1 i.2))⟩
      exact nonempty_of_isProbabilityMeasure (κ m Classical.ofNonempty)
  -- `Fₙ` is the integral of `fₙ` from time `k + 1` to `aₙ`.
  let F n : (Π n, X n) -> Real>=0∞ := lmarginalPartialTraj κ (k + 1) (a n) (f n)
  -- `Fₙ` converges to `l` by hypothesis.
  have tendstoF x : Tendsto (F · x) atTop (𝓝 (l x)) := htendsto x
  -- Integrating `fₙ` between time `k` and `aₙ` is the same as integrating
  -- `Fₙ` between time `k` and time `k + 1`.
  have f_eq x n : lmarginalPartialTraj κ k (a n) (f n) x =
      lmarginalPartialTraj κ k (k + 1) (F n) x := by
    simp_rw [F]
    obtain h | h | h := lt_trichotomy (k + 1) (a n)
    · rw [← lmarginalPartialTraj_self k.le_succ h.le (mf n)]
    · rw [← h, lmarginalPartialTraj_le _ le_rfl (mf n)]
    · rw [lmarginalPartialTraj_le _ _ (mf n), (hcte n).lmarginalPartialTraj_of_le _ (mf n),
        (hcte n).lmarginalPartialTraj_of_le _ (mf n)]
      all_goals lia
  -- `F` is also a bounded sequence.
  have F_le n x : F n x <= bound := by
    simpa [F, lmarginalPartialTraj] using lintegral_le_const (ae_of_all _ fun z => le_bound _ _)
  -- By dominated convergence, the integral of `fₙ` between time `k` and time `a n` converges
  -- to the integral of `l` between time `k` and time `k + 1`.
  have tendsto_int x : Tendsto (fun n => lmarginalPartialTraj κ k (a n) (f n) x) atTop
      (𝓝 (lmarginalPartialTraj κ k (k + 1) l x)) := by
    simp_rw [f_eq, lmarginalPartialTraj]
    exact tendsto_lintegral_of_dominated_convergence (fun _ => bound)
      (fun n => (measurable_lmarginalPartialTraj _ _ (mf n)).comp measurable_updateFinset)
      (fun n => Eventually.of_forall <| fun y => F_le n _)
      (by simp [fin_bound]) (Eventually.of_forall (fun _ => tendstoF _))
  -- By hypothesis, we have `ε ≤ lmarginalPartialTraj κ k (k + 1) (F n) (updateFinset x _ y)`,
  -- so this is also true for `l`.
  have ε_le_lint x : ε <= lmarginalPartialTraj κ k (k + 1) l (updateFinset x _ y) :=
    ge_of_tendsto (tendsto_int _) (by simp [hpos])
  let x_ : Π n, X n := Classical.ofNonempty
  -- We now have that the integral of `l` with respect to a probability measure is greater than `ε`,
  -- therefore there exists `x` such that `ε ≤ l(y, x)`.
  obtain ⟨x, hx⟩ : exists x, ε <= l (update (updateFinset x_ _ y) (k + 1) x) := by
    have : ∫⁻ x, l (update (updateFinset x_ _ y) (k + 1) x) ∂(κ k y) != ∞ :=
ne_top_of_le_ne_top fin_bound lintegral_le_const ae_of_all _
fun y => le_of_tendsto' (tendstoF _) fun _ => F_le _ _
    obtain ⟨x, hx⟩ := exists_lintegral_le this
    refine ⟨x, (ε_le_lint x_).trans ?_⟩
    rwa [lmarginalPartialTraj_succ, frestrictLe_updateFinset]
    exact ENNReal.measurable_of_tendsto (by fun_prop) (tendsto_pi_nhds.2 htendsto)
  refine ⟨x, fun x' n => ?_⟩
  -- As `F` is a non-increasing sequence, we have `ε ≤ Fₙ(y, x)` for any `n`.
  have := le_trans hx ((anti _).le_of_tendsto (tendstoF _) n)
  -- This part below is just to say that this is true for any `x : (i : ι) → X i`,
  -- as `Fₙ` technically depends on all the variables, but really depends only on the first `k + 1`.
  convert! this using 1
  refine (hcte n).dependsOn_lmarginalPartialTraj _ (mf n) fun i hi => ?_
  simp only [update, updateFinset, mem_Iic]
  split_ifs with h1 h2 <;> try rfl
  rw [mem_coe]; rw [mem_Iic] at hi
  lia

/--
theorem `trajContent_tendsto_zero` / 定理 `trajContent_tendsto_zero`

English:
theorem trajContent_tendsto_zero
  statement: {A : Nat -> Set (Π n, X n)}
  proof: by
  have _ n : Nonempty (X n) := by
    induction n using Nat.case_strong_induction_on with
    | hz => exact ⟨x₀ ⟨0, mem_Iic.2 zero_le⟩⟩
    | hi m hm =>
      have : Nonempty (Π i : Iic m, X i) :=
        ⟨fun i => @Classical.ofNonempty _ (hm i.1 (mem_Iic.1 i.2))⟩
      exact nonempty_of_isProbabilityMeasure (κ m Classical.ofNonempty)
  -- `Aₙ` is a cylinder, it can be written as `cylinder (Iic (a n)) Sₙ`.
  have A_cyl n : exists a S, MeasurableSet S ∧ A n = cylinder (Iic a) S := by
    simpa [measurableCylinders_nat] using A_mem n
  choose a S mS A_eq using A_cyl
  -- We write `χₙ` for the indicator function of `Aₙ`.
  let χ n := (A n).indicator (1 : (Π n, X n) -> Real>=0∞)
  -- `χₙ` is measurable.
  have mχ n : Measurable (χ n) := by
    simp_rw [χ, A_eq]
exact (measurable_indicator_const_iff 1).2 (mS n).cylinder
  -- `χₙ` only depends on the first coordinates.
  have χ_dep n : DependsOn (χ n) (Iic (a n)) := by
    simp_rw [χ, A_eq]
    exact dependsOn_cylinder_indicator_const ..
  -- Therefore its integral against `partialTraj κ k (a n)` is constant.
  have lma_const x y n :
      lmarginalPartialTraj κ p (a n) (χ n) (updateFinset x _ x₀) =
      lmarginalPartialTraj κ p (a n) (χ n) (updateFinset y _ x₀) := by
    refine (χ_dep n).dependsOn_lmarginalPartialTraj p (mχ n) fun i hi => ?_
    rw [mem_coe]; rw [mem_Iic] at hi
    simp [updateFinset, hi]
  -- As `(Aₙ)` is non-increasing, so is `(χₙ)`.
  have χ_anti : Antitone χ := fun m n hmn y => by
    apply Set.indicator_le fun a ha => ?_
    simp [χ, A_anti hmn ha]
  -- Integrating `χₙ` further than the last coordinate it depends on does nothing.
  -- This is used to then show that the integral of `χₙ` from time `k` is non-increasing.
  have lma_inv k M n (h : a n <= M) :
      lmarginalPartialTraj κ k M (χ n) = lmarginalPartialTraj κ k (a n) (χ n) :=
    (χ_dep n).lmarginalPartialTraj_const_right (mχ n) h le_rfl
  -- the integral of `χₙ` from time `k` is non-increasing.
  have anti_lma k x : Antitone fun n => lmarginalPartialTraj κ k (a n) (χ n) x := by
    intro m n hmn
    simp only
    rw [← lma_inv k ((a n).max (a m)) n (le_max_left _ _)]; rw [← lma_inv k ((a n).max (a m)) m (le_max_right _ _)]
    exact lmarginalPartialTraj_mono _ _ (χ_anti hmn) _
  -- Therefore it converges to some function `lₖ`.
  have this k x : exists l, Tendsto (fun n => lmarginalPartialTraj κ k (a n) (χ n) x) atTop (𝓝 l) := by
    obtain h | h := tendsto_atTop_of_antitone (anti_lma k x)
    · rw [OrderBot.atBot_eq] at h
exact ⟨0, h.mono_right pure_le_nhds 0⟩
    · exact h
  choose l hl using this
  -- `lₚ` is constant because it is the limit of constant functions: we call it `ε`.
  have l_const x y : l p (updateFinset x _ x₀) = l p (updateFinset y _ x₀) := by
    have := hl p (updateFinset x _ x₀)
    simp_rw [lma_const x y] at this
    exact tendsto_nhds_unique this (hl p _)
  obtain ⟨ε, hε⟩ : exists ε, forall x, l p (updateFinset x _ x₀) = ε :=
      ⟨l p (updateFinset Classical.ofNonempty _ x₀), fun x => l_const _ _⟩
  -- As the sequence is decreasing, `ε ≤ ∫ χₙ`.
  have hpos x n : ε <= lmarginalPartialTraj κ p (a n) (χ n) (updateFinset x _ x₀) :=
    hε x ▸ ((anti_lma p _).le_of_tendsto (hl p _)) n
  -- Also, the indicators are bounded by `1`.
  have χ_le n x : χ n x <= 1 := by
    apply Set.indicator_le
    simp
  -- We have all the conditions to apply `le_lmarginalPartialTraj_succ`.
  -- This allows us to recursively build a sequence `z` with the following property:
  -- for any `k ≥ p` and `n`, integrating `χ n` from time `k` to time `a n`
  -- with the trajectory up to `k` being equal to `z` gives something greater than `ε`.
  choose! ind hind using
    fun k y h => le_lmarginalPartialTraj_succ χ_dep mχ (by simp : (1 : Real>=0∞) != ∞)
      χ_le (anti_lma (k + 1)) (hl (k + 1)) ε y h
  let z := iterateInduction x₀ ind
  have main k (hk : p <= k) : forall x n,
      ε <= lmarginalPartialTraj κ k (a n) (χ n) (updateFinset x _ (frestrictLe k z)) := by
    induction k, hk using Nat.le_induction with
    | base => exact fun x n => by simpa [z, frestrictLe_iterateInduction] using hpos x n
    | succ k hn h =>
      intro x n
      convert! hind k (fun i => z i.1) h x n
      ext i
      simp only [updateFinset, mem_Iic, frestrictLe_apply, dite_eq_ite, update, z]
      split_ifs with h1 h2 h3 h4 h5
      any_goals lia
      cases h2
      rw [iterateInduction]; rw [dif_neg (by lia)]
  -- We now want to prove that the integral of `χₙ`, which is equal to the `trajContent`
  -- of `Aₙ`, converges to `0`.
  have aux x n :
      trajContent κ x₀ (A n) = lmarginalPartialTraj κ p (a n) (χ n) (updateFinset x _ x₀) := by
    simp_rw [χ, A_eq]
    nth_rw 1 [← frestrictLe_updateFinset x x₀]
    exact trajContent_eq_lmarginalPartialTraj (mS n) ..
  simp_rw [aux z]
  convert! hl p _
  rw [hε]
  -- Which means that we want to prove that `ε = 0`. But if `ε > 0`, then for any `n`,
  -- choosing `k > aₙ` we get `ε ≤ χₙ(z₀, ..., z_{aₙ})` and therefore `z ∈ Aₙ`.
  -- This contradicts the fact that `(Aₙ)` has an empty intersection.
  by_contra!
  have mem n : z in A n := by
    have : 0 < χ n z := by
      rw [← lmarginalPartialTraj_le κ (le_max_right p (a n)) (mχ n)]; rw [← updateFinset_frestrictLe (a := a n) z]
      simpa using lt_of_lt_of_le this.symm.bot_lt (main _ (le_max_left _ _) z n)
    exact Set.mem_of_indicator_ne_zero (ne_of_lt this).symm
  exact (A_inter ▸ Set.mem_iInter.2 mem).elim

中文:
定理 trajContent_tendsto_zero
  结论: {A : 自然数 -> 集合 (Π n, X n)}
  证明: by
  have _ n : Nonempty (X n) := by
    induction n using Nat.case_strong_induction_on with
    | hz => exact ⟨x₀ ⟨0, mem_Iic.2 zero_le⟩⟩
    | hi m hm =>
      have : Nonempty (Π i : Iic m, X i) :=
        ⟨fun i => @Classical.ofNonempty _ (hm i.1 (mem_Iic.1 i.2))⟩
      exact nonempty_of_isProbabilityMeasure (κ m Classical.ofNonempty)
  -- `Aₙ` is a cylinder, it can be written as `cylinder (Iic (a n)) Sₙ`.
  have A_cyl n : exists a S, MeasurableSet S ∧ A n = cylinder (Iic a) S := by
    simpa [measurableCylinders_nat] using A_mem n
  choose a S mS A_eq using A_cyl
  -- We write `χₙ` for the indicator function of `Aₙ`.
  let χ n := (A n).indicator (1 : (Π n, X n) -> Real>=0∞)
  -- `χₙ` is measurable.
  have mχ n : Measurable (χ n) := by
    simp_rw [χ, A_eq]
exact (measurable_indicator_const_iff 1).2 (mS n).cylinder
  -- `χₙ` only depends on the first coordinates.
  have χ_dep n : DependsOn (χ n) (Iic (a n)) := by
    simp_rw [χ, A_eq]
    exact dependsOn_cylinder_indicator_const ..
  -- Therefore its integral against `partialTraj κ k (a n)` is constant.
  have lma_const x y n :
      lmarginalPartialTraj κ p (a n) (χ n) (updateFinset x _ x₀) =
      lmarginalPartialTraj κ p (a n) (χ n) (updateFinset y _ x₀) := by
    refine (χ_dep n).dependsOn_lmarginalPartialTraj p (mχ n) fun i hi => ?_
    rw [mem_coe]; rw [mem_Iic] at hi
    simp [updateFinset, hi]
  -- As `(Aₙ)` is non-increasing, so is `(χₙ)`.
  have χ_anti : Antitone χ := fun m n hmn y => by
    apply Set.indicator_le fun a ha => ?_
    simp [χ, A_anti hmn ha]
  -- Integrating `χₙ` further than the last coordinate it depends on does nothing.
  -- This is used to then show that the integral of `χₙ` from time `k` is non-increasing.
  have lma_inv k M n (h : a n <= M) :
      lmarginalPartialTraj κ k M (χ n) = lmarginalPartialTraj κ k (a n) (χ n) :=
    (χ_dep n).lmarginalPartialTraj_const_right (mχ n) h le_rfl
  -- the integral of `χₙ` from time `k` is non-increasing.
  have anti_lma k x : Antitone fun n => lmarginalPartialTraj κ k (a n) (χ n) x := by
    intro m n hmn
    simp only
    rw [← lma_inv k ((a n).max (a m)) n (le_max_left _ _)]; rw [← lma_inv k ((a n).max (a m)) m (le_max_right _ _)]
    exact lmarginalPartialTraj_mono _ _ (χ_anti hmn) _
  -- Therefore it converges to some function `lₖ`.
  have this k x : exists l, Tendsto (fun n => lmarginalPartialTraj κ k (a n) (χ n) x) atTop (𝓝 l) := by
    obtain h | h := tendsto_atTop_of_antitone (anti_lma k x)
    · rw [OrderBot.atBot_eq] at h
exact ⟨0, h.mono_right pure_le_nhds 0⟩
    · exact h
  choose l hl using this
  -- `lₚ` is constant because it is the limit of constant functions: we call it `ε`.
  have l_const x y : l p (updateFinset x _ x₀) = l p (updateFinset y _ x₀) := by
    have := hl p (updateFinset x _ x₀)
    simp_rw [lma_const x y] at this
    exact tendsto_nhds_unique this (hl p _)
  obtain ⟨ε, hε⟩ : exists ε, forall x, l p (updateFinset x _ x₀) = ε :=
      ⟨l p (updateFinset Classical.ofNonempty _ x₀), fun x => l_const _ _⟩
  -- As the sequence is decreasing, `ε ≤ ∫ χₙ`.
  have hpos x n : ε <= lmarginalPartialTraj κ p (a n) (χ n) (updateFinset x _ x₀) :=
    hε x ▸ ((anti_lma p _).le_of_tendsto (hl p _)) n
  -- Also, the indicators are bounded by `1`.
  have χ_le n x : χ n x <= 1 := by
    apply Set.indicator_le
    simp
  -- We have all the conditions to apply `le_lmarginalPartialTraj_succ`.
  -- This allows us to recursively build a sequence `z` with the following property:
  -- for any `k ≥ p` and `n`, integrating `χ n` from time `k` to time `a n`
  -- with the trajectory up to `k` being equal to `z` gives something greater than `ε`.
  choose! ind hind using
    fun k y h => le_lmarginalPartialTraj_succ χ_dep mχ (by simp : (1 : Real>=0∞) != ∞)
      χ_le (anti_lma (k + 1)) (hl (k + 1)) ε y h
  let z := iterateInduction x₀ ind
  have main k (hk : p <= k) : forall x n,
      ε <= lmarginalPartialTraj κ k (a n) (χ n) (updateFinset x _ (frestrictLe k z)) := by
    induction k, hk using Nat.le_induction with
    | base => exact fun x n => by simpa [z, frestrictLe_iterateInduction] using hpos x n
    | succ k hn h =>
      intro x n
      convert! hind k (fun i => z i.1) h x n
      ext i
      simp only [updateFinset, mem_Iic, frestrictLe_apply, dite_eq_ite, update, z]
      split_ifs with h1 h2 h3 h4 h5
      any_goals lia
      cases h2
      rw [iterateInduction]; rw [dif_neg (by lia)]
  -- We now want to prove that the integral of `χₙ`, which is equal to the `trajContent`
  -- of `Aₙ`, converges to `0`.
  have aux x n :
      trajContent κ x₀ (A n) = lmarginalPartialTraj κ p (a n) (χ n) (updateFinset x _ x₀) := by
    simp_rw [χ, A_eq]
    nth_rw 1 [← frestrictLe_updateFinset x x₀]
    exact trajContent_eq_lmarginalPartialTraj (mS n) ..
  simp_rw [aux z]
  convert! hl p _
  rw [hε]
  -- Which means that we want to prove that `ε = 0`. But if `ε > 0`, then for any `n`,
  -- choosing `k > aₙ` we get `ε ≤ χₙ(z₀, ..., z_{aₙ})` and therefore `z ∈ Aₙ`.
  -- This contradicts the fact that `(Aₙ)` has an empty intersection.
  by_contra!
  have mem n : z in A n := by
    have : 0 < χ n z := by
      rw [← lmarginalPartialTraj_le κ (le_max_right p (a n)) (mχ n)]; rw [← updateFinset_frestrictLe (a := a n) z]
      simpa using lt_of_lt_of_le this.symm.bot_lt (main _ (le_max_left _ _) z n)
    exact Set.mem_of_indicator_ne_zero (ne_of_lt this).symm
  exact (A_inter ▸ Set.mem_iInter.2 mem).elim

Depends on / 依赖: Classical, Classical.ofNonempty, Nat.case_strong_induction_on, Nonempty, case_strong_induction_on, mem_Iic, nonempty_of_isProbabilityMeasure, ofNonempty, zero_le
-/
theorem trajContent_tendsto_zero {A : Nat -> Set (Π n, X n)}
    (A_mem : forall n, A n in measurableCylinders X) (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅)
    {p : Nat} (x₀ : Π i : Iic p, X i) :
    Tendsto (fun n => trajContent κ x₀ (A n)) atTop (𝓝 0) := by
  have _ n : Nonempty (X n) := by
    induction n using Nat.case_strong_induction_on with
    | hz => exact ⟨x₀ ⟨0, mem_Iic.2 zero_le⟩⟩
    | hi m hm =>
      have : Nonempty (Π i : Iic m, X i) :=
        ⟨fun i => @Classical.ofNonempty _ (hm i.1 (mem_Iic.1 i.2))⟩
      exact nonempty_of_isProbabilityMeasure (κ m Classical.ofNonempty)
  -- `Aₙ` is a cylinder, it can be written as `cylinder (Iic (a n)) Sₙ`.
  have A_cyl n : exists a S, MeasurableSet S ∧ A n = cylinder (Iic a) S := by
    simpa [measurableCylinders_nat] using A_mem n
  choose a S mS A_eq using A_cyl
  -- We write `χₙ` for the indicator function of `Aₙ`.
  let χ n := (A n).indicator (1 : (Π n, X n) -> Real>=0∞)
  -- `χₙ` is measurable.
  have mχ n : Measurable (χ n) := by
    simp_rw [χ, A_eq]
exact (measurable_indicator_const_iff 1).2 (mS n).cylinder
  -- `χₙ` only depends on the first coordinates.
  have χ_dep n : DependsOn (χ n) (Iic (a n)) := by
    simp_rw [χ, A_eq]
    exact dependsOn_cylinder_indicator_const ..
  -- Therefore its integral against `partialTraj κ k (a n)` is constant.
  have lma_const x y n :
      lmarginalPartialTraj κ p (a n) (χ n) (updateFinset x _ x₀) =
      lmarginalPartialTraj κ p (a n) (χ n) (updateFinset y _ x₀) := by
    refine (χ_dep n).dependsOn_lmarginalPartialTraj p (mχ n) fun i hi => ?_
    rw [mem_coe]; rw [mem_Iic] at hi
    simp [updateFinset, hi]
  -- As `(Aₙ)` is non-increasing, so is `(χₙ)`.
  have χ_anti : Antitone χ := fun m n hmn y => by
    apply Set.indicator_le fun a ha => ?_
    simp [χ, A_anti hmn ha]
  -- Integrating `χₙ` further than the last coordinate it depends on does nothing.
  -- This is used to then show that the integral of `χₙ` from time `k` is non-increasing.
  have lma_inv k M n (h : a n <= M) :
      lmarginalPartialTraj κ k M (χ n) = lmarginalPartialTraj κ k (a n) (χ n) :=
    (χ_dep n).lmarginalPartialTraj_const_right (mχ n) h le_rfl
  -- the integral of `χₙ` from time `k` is non-increasing.
  have anti_lma k x : Antitone fun n => lmarginalPartialTraj κ k (a n) (χ n) x := by
    intro m n hmn
    simp only
    rw [← lma_inv k ((a n).max (a m)) n (le_max_left _ _)]; rw [← lma_inv k ((a n).max (a m)) m (le_max_right _ _)]
    exact lmarginalPartialTraj_mono _ _ (χ_anti hmn) _
  -- Therefore it converges to some function `lₖ`.
  have this k x : exists l, Tendsto (fun n => lmarginalPartialTraj κ k (a n) (χ n) x) atTop (𝓝 l) := by
    obtain h | h := tendsto_atTop_of_antitone (anti_lma k x)
    · rw [OrderBot.atBot_eq] at h
exact ⟨0, h.mono_right pure_le_nhds 0⟩
    · exact h
  choose l hl using this
  -- `lₚ` is constant because it is the limit of constant functions: we call it `ε`.
  have l_const x y : l p (updateFinset x _ x₀) = l p (updateFinset y _ x₀) := by
    have := hl p (updateFinset x _ x₀)
    simp_rw [lma_const x y] at this
    exact tendsto_nhds_unique this (hl p _)
  obtain ⟨ε, hε⟩ : exists ε, forall x, l p (updateFinset x _ x₀) = ε :=
      ⟨l p (updateFinset Classical.ofNonempty _ x₀), fun x => l_const _ _⟩
  -- As the sequence is decreasing, `ε ≤ ∫ χₙ`.
  have hpos x n : ε <= lmarginalPartialTraj κ p (a n) (χ n) (updateFinset x _ x₀) :=
    hε x ▸ ((anti_lma p _).le_of_tendsto (hl p _)) n
  -- Also, the indicators are bounded by `1`.
  have χ_le n x : χ n x <= 1 := by
    apply Set.indicator_le
    simp
  -- We have all the conditions to apply `le_lmarginalPartialTraj_succ`.
  -- This allows us to recursively build a sequence `z` with the following property:
  -- for any `k ≥ p` and `n`, integrating `χ n` from time `k` to time `a n`
  -- with the trajectory up to `k` being equal to `z` gives something greater than `ε`.
  choose! ind hind using
    fun k y h => le_lmarginalPartialTraj_succ χ_dep mχ (by simp : (1 : Real>=0∞) != ∞)
      χ_le (anti_lma (k + 1)) (hl (k + 1)) ε y h
  let z := iterateInduction x₀ ind
  have main k (hk : p <= k) : forall x n,
      ε <= lmarginalPartialTraj κ k (a n) (χ n) (updateFinset x _ (frestrictLe k z)) := by
    induction k, hk using Nat.le_induction with
    | base => exact fun x n => by simpa [z, frestrictLe_iterateInduction] using hpos x n
    | succ k hn h =>
      intro x n
      convert! hind k (fun i => z i.1) h x n
      ext i
      simp only [updateFinset, mem_Iic, frestrictLe_apply, dite_eq_ite, update, z]
      split_ifs with h1 h2 h3 h4 h5
      any_goals lia
      cases h2
      rw [iterateInduction]; rw [dif_neg (by lia)]
  -- We now want to prove that the integral of `χₙ`, which is equal to the `trajContent`
  -- of `Aₙ`, converges to `0`.
  have aux x n :
      trajContent κ x₀ (A n) = lmarginalPartialTraj κ p (a n) (χ n) (updateFinset x _ x₀) := by
    simp_rw [χ, A_eq]
    nth_rw 1 [← frestrictLe_updateFinset x x₀]
    exact trajContent_eq_lmarginalPartialTraj (mS n) ..
  simp_rw [aux z]
  convert! hl p _
  rw [hε]
  -- Which means that we want to prove that `ε = 0`. But if `ε > 0`, then for any `n`,
  -- choosing `k > aₙ` we get `ε ≤ χₙ(z₀, ..., z_{aₙ})` and therefore `z ∈ Aₙ`.
  -- This contradicts the fact that `(Aₙ)` has an empty intersection.
  by_contra!
  have mem n : z in A n := by
    have : 0 < χ n z := by
      rw [← lmarginalPartialTraj_le κ (le_max_right p (a n)) (mχ n)]; rw [← updateFinset_frestrictLe (a := a n) z]
      simpa using lt_of_lt_of_le this.symm.bot_lt (main _ (le_max_left _ _) z n)
    exact Set.mem_of_indicator_ne_zero (ne_of_lt this).symm
  exact (A_inter ▸ Set.mem_iInter.2 mem).elim

variable (κ)

/--
theorem `isSigmaSubadditive_trajContent` / 定理 `isSigmaSubadditive_trajContent`

English:
theorem isSigmaSubadditive_trajContent
  given: {a : Nat} (x₀ : Π i : Iic a, X i)
  proof: by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hf_Union hf' => ?_)
  refine addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (trajContent κ x₀) (fun _ _ => trajContent_ne_top) ?_ hf hf_Union hf'
  exact fun s hs anti_s inter_s => trajContent_tendsto_zero hs anti_s inter_s x₀

中文:
定理 isSigmaSubadditive_trajContent
  条件: {a : 自然数} (x₀ : Π i : 左无界右闭区间 a, X i)
  证明: by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hf_Union hf' => ?_)
  refine addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (trajContent κ x₀) (fun _ _ => trajContent_ne_top) ?_ hf hf_Union hf'
  exact fun s hs anti_s inter_s => trajContent_tendsto_zero hs anti_s inter_s x₀

Depends on / 依赖: addContent_iUnion_eq_sum_of_tendsto_zero, anti_s, hf_Union, inter_s, isSetRing_measurableCylinders, isSigmaSubadditive_of_addContent_iUnion_eq_tsum, trajContent, trajContent_ne_top, trajContent_tendsto_zero
-/
theorem isSigmaSubadditive_trajContent {a : Nat} (x₀ : Π i : Iic a, X i) :
    (trajContent κ x₀).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hf_Union hf' => ?_)
  refine addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (trajContent κ x₀) (fun _ _ => trajContent_ne_top) ?_ hf hf_Union hf'
  exact fun s hs anti_s inter_s => trajContent_tendsto_zero hs anti_s inter_s x₀

/--
Definition of `trajFun` / `trajFun` 的定义

English:
definition trajFun
  signature: (a : Nat) (x₀ : Π i : Iic a, X i)
  body: (trajContent κ x₀).measure isSetSemiring_measurableCylinders generateFrom_measurableCylinders.ge
    (isSigmaSubadditive_trajContent κ x₀)

中文:
定义 trajFun
  签名: (a : 自然数) (x₀ : Π i : 左无界右闭区间 a, X i)
  定义体: (trajContent κ x₀).measure isSetSemiring_measurableCylinders generateFrom_measurableCylinders.ge
    (isSigmaSubadditive_trajContent κ x₀)

Depends on / 依赖: generateFrom_measurableCylinders, generateFrom_measurableCylinders.ge, isSetSemiring_measurableCylinders, isSigmaSubadditive_trajContent, measure, trajContent
-/
noncomputable def trajFun (a : Nat) (x₀ : Π i : Iic a, X i) : Measure (Π n, X n) :=
  (trajContent κ x₀).measure isSetSemiring_measurableCylinders generateFrom_measurableCylinders.ge
    (isSigmaSubadditive_trajContent κ x₀)

/--
theorem `isProbabilityMeasure_trajFun` / 定理 `isProbabilityMeasure_trajFun`

English:
theorem isProbabilityMeasure_trajFun
  given: (a : Nat) (x₀ : Π i : Iic a, X i)
  proof: by
    rw [← cylinder_univ (Iic 0)]; rw [trajFun]; rw [AddContent.measure_eq]; rw [trajContent_cylinder .univ]; rw [measure_univ]
    · exact generateFrom_measurableCylinders.symm
    · exact cylinder_mem_measurableCylinders _ _ .univ

中文:
定理 isProbabilityMeasure_trajFun
  条件: (a : 自然数) (x₀ : Π i : 左无界右闭区间 a, X i)
  证明: by
    rw [← cylinder_univ (Iic 0)]; rw [trajFun]; rw [AddContent.measure_eq]; rw [trajContent_cylinder .univ]; rw [measure_univ]
    · exact generateFrom_measurableCylinders.symm
    · exact cylinder_mem_measurableCylinders _ _ .univ

Depends on / 依赖: AddContent, AddContent.measure_eq, cylinder_mem_measurableCylinders, cylinder_univ, generateFrom_measurableCylinders, generateFrom_measurableCylinders.symm, measure_eq, measure_univ, trajContent_cylinder, trajFun
-/
theorem isProbabilityMeasure_trajFun (a : Nat) (x₀ : Π i : Iic a, X i) :
    IsProbabilityMeasure (trajFun κ a x₀) where
  measure_univ := by
    rw [← cylinder_univ (Iic 0)]; rw [trajFun]; rw [AddContent.measure_eq]; rw [trajContent_cylinder .univ]; rw [measure_univ]
    · exact generateFrom_measurableCylinders.symm
    · exact cylinder_mem_measurableCylinders _ _ .univ

/--
theorem `isProjectiveLimit_trajFun` / 定理 `isProjectiveLimit_trajFun`

English:
theorem isProjectiveLimit_trajFun
  given: (a : Nat) (x₀ : Π i : Iic a, X i)
  proof: by
.2 fun n => ?_ refine isProjectiveLimit_nat_iff (isProjectiveMeasureFamily_partialTraj κ x₀) _
  ext s ms
  rw [Measure.map_apply (measurable_frestrictLe n) ms]; rw [trajFun]; rw [AddContent.measure_eq]; rw [trajContent]; rw [projectiveFamilyContent_congr _ (frestrictLe n ⁻¹' s) rfl ms]
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders _ _ ms

中文:
定理 isProjectiveLimit_trajFun
  条件: (a : 自然数) (x₀ : Π i : 左无界右闭区间 a, X i)
  证明: by
.2 fun n => ?_ refine isProjectiveLimit_nat_iff (isProjectiveMeasureFamily_partialTraj κ x₀) _
  ext s ms
  rw [Measure.map_apply (measurable_frestrictLe n) ms]; rw [trajFun]; rw [AddContent.measure_eq]; rw [trajContent]; rw [projectiveFamilyContent_congr _ (frestrictLe n ⁻¹' s) rfl ms]
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders _ _ ms

Depends on / 依赖: AddContent, AddContent.measure_eq, Measure, Measure.map_apply, cylinder_mem_measurableCylinders, frestrictLe, generateFrom_measurableCylinders, generateFrom_measurableCylinders.symm, isProjectiveLimit_nat_iff, isProjectiveMeasureFamily_partialTraj, map_apply, measurable_frestrictLe, measure_eq, projectiveFamilyContent_congr, trajContent, trajFun
-/
theorem isProjectiveLimit_trajFun (a : Nat) (x₀ : Π i : Iic a, X i) :
    IsProjectiveLimit (trajFun κ a x₀) (inducedFamily (fun n => partialTraj κ a n x₀)) := by
.2 fun n => ?_ refine isProjectiveLimit_nat_iff (isProjectiveMeasureFamily_partialTraj κ x₀) _
  ext s ms
  rw [Measure.map_apply (measurable_frestrictLe n) ms]; rw [trajFun]; rw [AddContent.measure_eq]; rw [trajContent]; rw [projectiveFamilyContent_congr _ (frestrictLe n ⁻¹' s) rfl ms]
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders _ _ ms

variable {κ} in
/--
theorem `measurable_trajFun` / 定理 `measurable_trajFun`

English:
theorem measurable_trajFun
  given: (a : Nat)
  statement: Measurable (trajFun κ a)
  proof: by
  apply Measure.measurable_of_measurable_coe
  refine MeasurableSpace.induction_on_inter
    (C := fun t ht => Measurable (fun x₀ => trajFun κ a x₀ t))
    (s := measurableCylinders X) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (by simp) (fun t ht => ?cylinder) (fun t mt ht => ?compl)
    (fun f disf mf hf => ?union)
  · obtain ⟨N, S, mS, t_eq⟩ : exists N S, MeasurableSet S ∧ t = cylinder (Iic N) S := by
      simpa [measurableCylinders_nat] using ht
    simp_rw [trajFun, AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm _ ht,
      trajContent, projectiveFamilyContent_congr _ t t_eq mS, inducedFamily]
    refine Measure.measurable_measure.1 ?_ _ mS
    exact (Measure.measurable_map _ (measurable_restrict₂ _)).comp (measurable _)
  · have := isProbabilityMeasure_trajFun κ a
    simpa [measure_compl mt (measure_ne_top _ _)] using Measurable.const_sub ht _
  · simpa [measure_iUnion disf mf] using Measurable.tsum hf

中文:
定理 measurable_trajFun
  条件: (a : 自然数)
  结论: 可测 (trajFun κ a)
  证明: by
  apply Measure.measurable_of_measurable_coe
  refine MeasurableSpace.induction_on_inter
    (C := fun t ht => Measurable (fun x₀ => trajFun κ a x₀ t))
    (s := measurableCylinders X) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (by simp) (fun t ht => ?cylinder) (fun t mt ht => ?compl)
    (fun f disf mf hf => ?union)
  · obtain ⟨N, S, mS, t_eq⟩ : exists N S, MeasurableSet S ∧ t = cylinder (Iic N) S := by
      simpa [measurableCylinders_nat] using ht
    simp_rw [trajFun, AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm _ ht,
      trajContent, projectiveFamilyContent_congr _ t t_eq mS, inducedFamily]
    refine Measure.measurable_measure.1 ?_ _ mS
    exact (Measure.measurable_map _ (measurable_restrict₂ _)).comp (measurable _)
  · have := isProbabilityMeasure_trajFun κ a
    simpa [measure_compl mt (measure_ne_top _ _)] using Measurable.const_sub ht _
  · simpa [measure_iUnion disf mf] using Measurable.tsum hf

Depends on / 依赖: AddContent, AddContent.measure_eq, Measurable, MeasurableSet, MeasurableSpace, MeasurableSpace.induction_on_inter, Measure, Measure.measurable_of_measurable_coe, cylinder, generateFrom_measurableCylinders, generateFrom_measurableCylinders.symm, induction_on_inter, isPiSystem_measurableCylinders, measurableCylinders, measurableCylinders_nat, measurable_of_measurable_coe, measure_eq, simp_rw, t_eq, trajFun
-/
theorem measurable_trajFun (a : Nat) : Measurable (trajFun κ a) := by
  apply Measure.measurable_of_measurable_coe
  refine MeasurableSpace.induction_on_inter
    (C := fun t ht => Measurable (fun x₀ => trajFun κ a x₀ t))
    (s := measurableCylinders X) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (by simp) (fun t ht => ?cylinder) (fun t mt ht => ?compl)
    (fun f disf mf hf => ?union)
  · obtain ⟨N, S, mS, t_eq⟩ : exists N S, MeasurableSet S ∧ t = cylinder (Iic N) S := by
      simpa [measurableCylinders_nat] using ht
    simp_rw [trajFun, AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm _ ht,
      trajContent, projectiveFamilyContent_congr _ t t_eq mS, inducedFamily]
    refine Measure.measurable_measure.1 ?_ _ mS
    exact (Measure.measurable_map _ (measurable_restrict₂ _)).comp (measurable _)
  · have := isProbabilityMeasure_trajFun κ a
    simpa [measure_compl mt (measure_ne_top _ _)] using Measurable.const_sub ht _
  · simpa [measure_iUnion disf mf] using Measurable.tsum hf

/--
Definition of `traj` / `traj` 的定义

English:
definition traj
  signature: (a : Nat)
  body: trajFun κ a
  measurable' := measurable_trajFun a

中文:
定义 traj
  签名: (a : 自然数)
  定义体: trajFun κ a
  measurable' := measurable_trajFun a

Depends on / 依赖: trajFun
-/
noncomputable def traj (a : Nat) : Kernel (Π i : Iic a, X i) (Π n, X n) where
  toFun := trajFun κ a
  measurable' := measurable_trajFun a

end definition

section basic

/--
lemma `traj_apply` / 引理 `traj_apply`

English:
lemma traj_apply
  given: (a : Nat) (x : Π i : Iic a, X i)
  statement: traj κ a x = trajFun κ a x
  proof: rfl

中文:
引理 traj_apply
  条件: (a : 自然数) (x : Π i : 左无界右闭区间 a, X i)
  结论: traj κ a x = trajFun κ a x
  证明: rfl
-/
lemma traj_apply (a : Nat) (x : Π i : Iic a, X i) : traj κ a x = trajFun κ a x := rfl

instance (a : Nat) : IsMarkovKernel (traj κ a) := ⟨fun _ => isProbabilityMeasure_trajFun ..⟩

/--
lemma `traj_map_frestrictLe` / 引理 `traj_map_frestrictLe`

English:
lemma traj_map_frestrictLe
  given: (a b : Nat)
  statement: (traj κ a).map (frestrictLe b) = partialTraj κ a b
  proof: by
  ext x
  rw [map_apply]; rw [traj_apply]; rw [frestrictLe]; rw [isProjectiveLimit_trajFun]; rw [inducedFamily_Iic]
  fun_prop

中文:
引理 traj_map_frestrictLe
  条件: (a b : 自然数)
  结论: (traj κ a).map (frestrictLe b) = partialTraj κ a b
  证明: by
  ext x
  rw [map_apply]; rw [traj_apply]; rw [frestrictLe]; rw [isProjectiveLimit_trajFun]; rw [inducedFamily_Iic]
  fun_prop

Depends on / 依赖: frestrictLe, fun_prop, inducedFamily_Iic, isProjectiveLimit_trajFun, map_apply, traj_apply
-/
lemma traj_map_frestrictLe (a b : Nat) : (traj κ a).map (frestrictLe b) = partialTraj κ a b := by
  ext x
  rw [map_apply]; rw [traj_apply]; rw [frestrictLe]; rw [isProjectiveLimit_trajFun]; rw [inducedFamily_Iic]
  fun_prop

/--
lemma `traj_map_frestrictLe_apply` / 引理 `traj_map_frestrictLe_apply`

English:
lemma traj_map_frestrictLe_apply
  given: (a b : Nat) (x : Π i : Iic a, X i)
  proof: by
  rw [← map_apply _ (measurable_frestrictLe b)]; rw [traj_map_frestrictLe]

中文:
引理 traj_map_frestrictLe_apply
  条件: (a b : 自然数) (x : Π i : 左无界右闭区间 a, X i)
  证明: by
  rw [← map_apply _ (measurable_frestrictLe b)]; rw [traj_map_frestrictLe]

Depends on / 依赖: map_apply, measurable_frestrictLe, traj_map_frestrictLe
-/
lemma traj_map_frestrictLe_apply (a b : Nat) (x : Π i : Iic a, X i) :
    (traj κ a x).map (frestrictLe b) = partialTraj κ a b x := by
  rw [← map_apply _ (measurable_frestrictLe b)]; rw [traj_map_frestrictLe]

/--
lemma `traj_map_frestrictLe_of_le` / 引理 `traj_map_frestrictLe_of_le`

English:
lemma traj_map_frestrictLe_of_le
  given: {a b : Nat} (hab : a <= b)
  proof: by
  rw [traj_map_frestrictLe]; rw [partialTraj_le]

中文:
引理 traj_map_frestrictLe_of_le
  条件: {a b : 自然数} (hab : a <= b)
  证明: by
  rw [traj_map_frestrictLe]; rw [partialTraj_le]

Depends on / 依赖: partialTraj_le, traj_map_frestrictLe
-/
lemma traj_map_frestrictLe_of_le {a b : Nat} (hab : a <= b) :
    (traj κ b).map (frestrictLe a) =
      deterministic (frestrictLe₂ hab) (measurable_frestrictLe₂ _) := by
  rw [traj_map_frestrictLe]; rw [partialTraj_le]

/--
lemma `map_traj_succ_self` / 引理 `map_traj_succ_self`

English:
lemma map_traj_succ_self
  given: {a : Nat}
  statement: (traj κ a).map (fun x => x (a + 1)) = κ a
  proof: by
  have hf : (fun x : Π n, X n => x (a + 1)) =
      (fun x => x ⟨a + 1, mem_Iic.2 le_rfl⟩) ∘ frestrictLe (a + 1) := rfl
  rw [hf]; rw [map_comp_right _ (by fun_prop) (by fun_prop)]; rw [traj_map_frestrictLe]; rw [map_partialTraj_succ_self]

中文:
引理 map_traj_succ_self
  条件: {a : 自然数}
  结论: (traj κ a).map (fun x => x (a + 1)) = κ a
  证明: by
  have hf : (fun x : Π n, X n => x (a + 1)) =
      (fun x => x ⟨a + 1, mem_Iic.2 le_rfl⟩) ∘ frestrictLe (a + 1) := rfl
  rw [hf]; rw [map_comp_right _ (by fun_prop) (by fun_prop)]; rw [traj_map_frestrictLe]; rw [map_partialTraj_succ_self]

Depends on / 依赖: frestrictLe, fun_prop, le_rfl, map_comp_right, map_partialTraj_succ_self, mem_Iic, traj_map_frestrictLe
-/
lemma map_traj_succ_self {a : Nat} : (traj κ a).map (fun x => x (a + 1)) = κ a := by
  have hf : (fun x : Π n, X n => x (a + 1)) =
      (fun x => x ⟨a + 1, mem_Iic.2 le_rfl⟩) ∘ frestrictLe (a + 1) := rfl
  rw [hf]; rw [map_comp_right _ (by fun_prop) (by fun_prop)]; rw [traj_map_frestrictLe]; rw [map_partialTraj_succ_self]

variable (κ)

/--
theorem `eq_traj'` / 定理 `eq_traj'`

English:
theorem eq_traj'
  statement: {a : Nat} (n : Nat) (η : Kernel (Π i : Iic a, X i) (Π n, X n))
  proof: by
  ext x : 1
  refine ((isProjectiveLimit_trajFun _ _ _).unique ?_).symm
  rw [isProjectiveLimit_nat_iff' _ _ n]
  · intro k hk
    rw [inducedFamily_Iic]; rw [← map_apply _ (measurable_frestrictLe k)]; rw [hη k hk]
  · exact isProjectiveMeasureFamily_partialTraj κ x

中文:
定理 eq_traj'
  结论: {a : 自然数} (n : 自然数) (η : 核 (Π i : 左无界右闭区间 a, X i) (Π n, X n))
  证明: by
  ext x : 1
  refine ((isProjectiveLimit_trajFun _ _ _).unique ?_).symm
  rw [isProjectiveLimit_nat_iff' _ _ n]
  · intro k hk
    rw [inducedFamily_Iic]; rw [← map_apply _ (measurable_frestrictLe k)]; rw [hη k hk]
  · exact isProjectiveMeasureFamily_partialTraj κ x

Depends on / 依赖: inducedFamily_Iic, isProjectiveLimit_nat_iff, isProjectiveLimit_trajFun, isProjectiveMeasureFamily_partialTraj, map_apply, measurable_frestrictLe, unique
-/
theorem eq_traj' {a : Nat} (n : Nat) (η : Kernel (Π i : Iic a, X i) (Π n, X n))
    (hη : forall b >= n, η.map (frestrictLe b) = partialTraj κ a b) : η = traj κ a := by
  ext x : 1
  refine ((isProjectiveLimit_trajFun _ _ _).unique ?_).symm
  rw [isProjectiveLimit_nat_iff' _ _ n]
  · intro k hk
    rw [inducedFamily_Iic]; rw [← map_apply _ (measurable_frestrictLe k)]; rw [hη k hk]
  · exact isProjectiveMeasureFamily_partialTraj κ x

/--
theorem `eq_traj` / 定理 `eq_traj`

English:
theorem eq_traj
  statement: {a : Nat} (η : Kernel (Π i : Iic a, X i) (Π n, X n))
  proof: eq_traj' κ 0 η fun b _ => hη b

中文:
定理 eq_traj
  结论: {a : 自然数} (η : 核 (Π i : 左无界右闭区间 a, X i) (Π n, X n))
  证明: eq_traj' κ 0 η fun b _ => hη b

Depends on / 依赖: eq_traj
-/
theorem eq_traj {a : Nat} (η : Kernel (Π i : Iic a, X i) (Π n, X n))
    (hη : forall b, η.map (frestrictLe b) = partialTraj κ a b) : η = traj κ a :=
  eq_traj' κ 0 η fun b _ => hη b

variable {κ}

/--
theorem `traj_comp_partialTraj` / 定理 `traj_comp_partialTraj`

English:
theorem traj_comp_partialTraj
  given: {a b : Nat} (hab : a <= b)
  proof: by
  refine eq_traj _ _ fun n => ?_
  rw [map_comp]; rw [traj_map_frestrictLe]; rw [partialTraj_comp_partialTraj' _ hab]

中文:
定理 traj_comp_partialTraj
  条件: {a b : 自然数} (hab : a <= b)
  证明: by
  refine eq_traj _ _ fun n => ?_
  rw [map_comp]; rw [traj_map_frestrictLe]; rw [partialTraj_comp_partialTraj' _ hab]

Depends on / 依赖: eq_traj, map_comp, partialTraj_comp_partialTraj, traj_map_frestrictLe
-/
theorem traj_comp_partialTraj {a b : Nat} (hab : a <= b) :
    (traj κ b) ∘ₖ (partialTraj κ a b) = traj κ a := by
  refine eq_traj _ _ fun n => ?_
  rw [map_comp]; rw [traj_map_frestrictLe]; rw [partialTraj_comp_partialTraj' _ hab]

/--
theorem `traj_eq_prod` / 定理 `traj_eq_prod`

English:
theorem traj_eq_prod
  given: (a : Nat)
  proof: by
  refine (eq_traj' _ (a + 1) _ fun b hb => ?_).symm
  rw [← map_comp_right]
  conv_lhs => enter [2]; change (IicProdIoc a b) ∘
    (Prod.map id (fun x i => x ⟨i.1, Set.mem_Ioi.2 (mem_Ioc.1 i.2).1⟩))
  · rw [map_comp_right, ← map_prod_map, ← map_comp_right]
    · conv_lhs => enter [1, 2, 2]; change (Ioc a b).restrict
      rw [← restrict₂_comp_restrict Ioc_subset_Iic_self]; rw [← frestrictLe]; rw [map_comp_right]; rw [traj_map_frestrictLe]; rw [map_id]; rw [← partialTraj_eq_prod]
      all_goals fun_prop
    all_goals fun_prop
  all_goals fun_prop

中文:
定理 traj_eq_prod
  条件: (a : 自然数)
  证明: by
  refine (eq_traj' _ (a + 1) _ fun b hb => ?_).symm
  rw [← map_comp_right]
  conv_lhs => enter [2]; change (IicProdIoc a b) ∘
    (Prod.map id (fun x i => x ⟨i.1, Set.mem_Ioi.2 (mem_Ioc.1 i.2).1⟩))
  · rw [map_comp_right, ← map_prod_map, ← map_comp_right]
    · conv_lhs => enter [1, 2, 2]; change (Ioc a b).restrict
      rw [← restrict₂_comp_restrict Ioc_subset_Iic_self]; rw [← frestrictLe]; rw [map_comp_right]; rw [traj_map_frestrictLe]; rw [map_id]; rw [← partialTraj_eq_prod]
      all_goals fun_prop
    all_goals fun_prop
  all_goals fun_prop

Depends on / 依赖: IicProdIoc, Ioc_subset_Iic_self, Prod.map, Set.mem_Ioi, all_goals, conv_lhs, eq_traj, frestrictLe, fun_pr, fun_prop, map_comp_right, map_id, map_prod_map, mem_Ioc, mem_Ioi, partialTraj_eq_prod, restrict, traj_map_frestrictLe
-/
theorem traj_eq_prod (a : Nat) :
    traj κ a = (Kernel.id ×ₖ (traj κ a).map (Set.Ioi a).domRestrict).map (IicProdIoi a) := by
  refine (eq_traj' _ (a + 1) _ fun b hb => ?_).symm
  rw [← map_comp_right]
  conv_lhs => enter [2]; change (IicProdIoc a b) ∘
    (Prod.map id (fun x i => x ⟨i.1, Set.mem_Ioi.2 (mem_Ioc.1 i.2).1⟩))
  · rw [map_comp_right, ← map_prod_map, ← map_comp_right]
    · conv_lhs => enter [1, 2, 2]; change (Ioc a b).restrict
      rw [← restrict₂_comp_restrict Ioc_subset_Iic_self]; rw [← frestrictLe]; rw [map_comp_right]; rw [traj_map_frestrictLe]; rw [map_id]; rw [← partialTraj_eq_prod]
      all_goals fun_prop
    all_goals fun_prop
  all_goals fun_prop

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `traj_map_updateFinset` / 定理 `traj_map_updateFinset`

English:
theorem traj_map_updateFinset
  given: {n : Nat} (x : Π i : Iic n, X i)
  proof: by
  nth_rw 2 [traj_eq_prod]
  have : (updateFinset · _ x) = IicProdIoi n ∘ (Prod.mk x) ∘ (Set.Ioi n).domRestrict := by
    ext; simp [IicProdIoi, updateFinset]
  rw [this]; rw [← Function.comp_assoc]; rw [← Measure.map_map]; rw [← Measure.map_map]; rw [map_apply]; rw [prod_apply]; rw [map_apply]; rw [id_apply]; rw [Measure.dirac_prod]
  all_goals fun_prop

中文:
定理 traj_map_updateFinset
  条件: {n : 自然数} (x : Π i : 左无界右闭区间 n, X i)
  证明: by
  nth_rw 2 [traj_eq_prod]
  have : (updateFinset · _ x) = IicProdIoi n ∘ (Prod.mk x) ∘ (Set.Ioi n).domRestrict := by
    ext; simp [IicProdIoi, updateFinset]
  rw [this]; rw [← Function.comp_assoc]; rw [← Measure.map_map]; rw [← Measure.map_map]; rw [map_apply]; rw [prod_apply]; rw [map_apply]; rw [id_apply]; rw [Measure.dirac_prod]
  all_goals fun_prop

Depends on / 依赖: Function, Function.comp_assoc, IicProdIoi, Measure, Measure.dirac_prod, Measure.map_map, Prod.mk, Set.Ioi, all_goals, comp_assoc, dirac_prod, domRestrict, fun_prop, id_apply, map_apply, map_map, nth_rw, prod_apply, traj_eq_prod, updateFinset
-/
theorem traj_map_updateFinset {n : Nat} (x : Π i : Iic n, X i) :
    (traj κ n x).map (updateFinset · (Iic n) x) = traj κ n x := by
  nth_rw 2 [traj_eq_prod]
  have : (updateFinset · _ x) = IicProdIoi n ∘ (Prod.mk x) ∘ (Set.Ioi n).domRestrict := by
    ext; simp [IicProdIoi, updateFinset]
  rw [this]; rw [← Function.comp_assoc]; rw [← Measure.map_map]; rw [← Measure.map_map]; rw [map_apply]; rw [prod_apply]; rw [map_apply]; rw [id_apply]; rw [Measure.dirac_prod]
  all_goals fun_prop

end basic

section integral


/--
theorem `lintegral_traj₀` / 定理 `lintegral_traj₀`

English:
theorem lintegral_traj₀
  statement: {a : Nat} (x₀ : Π i : Iic a, X i) {f : (Π n, X n) -> Real>=0∞}
  proof: by
  nth_rw 1 [← traj_map_updateFinset, MeasureTheory.lintegral_map']
  · convert! mf
    exact traj_map_updateFinset x₀
  · exact measurable_updateFinset_left.aemeasurable

中文:
定理 lintegral_traj₀
  结论: {a : 自然数} (x₀ : Π i : 左无界右闭区间 a, X i) {f : (Π n, X n) -> 实数>=0∞}
  证明: by
  nth_rw 1 [← traj_map_updateFinset, MeasureTheory.lintegral_map']
  · convert! mf
    exact traj_map_updateFinset x₀
  · exact measurable_updateFinset_left.aemeasurable

Depends on / 依赖: MeasureTheory, MeasureTheory.lintegral_map, aemeasurable, convert, lintegral_map, measurable_updateFinset_left, measurable_updateFinset_left.aemeasurable, nth_rw, traj_map_updateFinset
-/
theorem lintegral_traj₀ {a : Nat} (x₀ : Π i : Iic a, X i) {f : (Π n, X n) -> Real>=0∞}
    (mf : AEMeasurable f (traj κ a x₀)) :
    ∫⁻ x, f x ∂traj κ a x₀ = ∫⁻ x, f (updateFinset x (Iic a) x₀) ∂traj κ a x₀ := by
  nth_rw 1 [← traj_map_updateFinset, MeasureTheory.lintegral_map']
  · convert! mf
    exact traj_map_updateFinset x₀
  · exact measurable_updateFinset_left.aemeasurable

/--
theorem `lintegral_traj` / 定理 `lintegral_traj`

English:
theorem lintegral_traj
  statement: {a : Nat} (x₀ : Π i : Iic a, X i) {f : (Π n, X n) -> Real>=0∞}
  proof: lintegral_traj₀ x₀ mf.aemeasurable

中文:
定理 lintegral_traj
  结论: {a : 自然数} (x₀ : Π i : 左无界右闭区间 a, X i) {f : (Π n, X n) -> 实数>=0∞}
  证明: lintegral_traj₀ x₀ mf.aemeasurable

Depends on / 依赖: aemeasurable, mf.aemeasurable
-/
theorem lintegral_traj {a : Nat} (x₀ : Π i : Iic a, X i) {f : (Π n, X n) -> Real>=0∞}
    (mf : Measurable f) :
    ∫⁻ x, f x ∂traj κ a x₀ = ∫⁻ x, f (updateFinset x (Iic a) x₀) ∂traj κ a x₀ :=
  lintegral_traj₀ x₀ mf.aemeasurable

variable {E : Type*} [NormedAddCommGroup E]

/--
theorem `integrable_traj` / 定理 `integrable_traj`

English:
theorem integrable_traj
  statement: {a b : Nat} (hab : a <= b) {f : (Π n, X n) -> E}
  proof: by
  rw [← traj_comp_partialTraj hab]; rw [integrable_comp_iff] at i_f
  · apply ae_of_ae_map (p := fun x => Integrable f (traj κ b x))
    · fun_prop
    · convert! i_f.1
      rw [← traj_map_frestrictLe]; rw [Kernel.map_apply _ (measurable_frestrictLe _)]
  · exact i_f.aestronglyMeasurable

中文:
定理 integrable_traj
  结论: {a b : 自然数} (hab : a <= b) {f : (Π n, X n) -> E}
  证明: by
  rw [← traj_comp_partialTraj hab]; rw [integrable_comp_iff] at i_f
  · apply ae_of_ae_map (p := fun x => Integrable f (traj κ b x))
    · fun_prop
    · convert! i_f.1
      rw [← traj_map_frestrictLe]; rw [Kernel.map_apply _ (measurable_frestrictLe _)]
  · exact i_f.aestronglyMeasurable

Depends on / 依赖: Integrable, Kernel, Kernel.map_apply, ae_of_ae_map, aestronglyMeasurable, convert, fun_prop, i_f.aestronglyMeasurable, integrable_comp_iff, map_apply, measurable_frestrictLe, traj_comp_partialTraj, traj_map_frestrictLe
-/
theorem integrable_traj {a b : Nat} (hab : a <= b) {f : (Π n, X n) -> E}
    (x₀ : Π i : Iic a, X i) (i_f : Integrable f (traj κ a x₀)) :
    forallᵐ x ∂traj κ a x₀, Integrable f (traj κ b (frestrictLe b x)) := by
  rw [← traj_comp_partialTraj hab]; rw [integrable_comp_iff] at i_f
  · apply ae_of_ae_map (p := fun x => Integrable f (traj κ b x))
    · fun_prop
    · convert! i_f.1
      rw [← traj_map_frestrictLe]; rw [Kernel.map_apply _ (measurable_frestrictLe _)]
  · exact i_f.aestronglyMeasurable

/--
theorem `aestronglyMeasurable_traj` / 定理 `aestronglyMeasurable_traj`

English:
theorem aestronglyMeasurable_traj
  statement: {a b : Nat} (hab : a <= b) {f : (Π n, X n) -> E}
  proof: by
  rw [← traj_comp_partialTraj hab] at hf
  exact hf.comp

中文:
定理 aestronglyMeasurable_traj
  结论: {a b : 自然数} (hab : a <= b) {f : (Π n, X n) -> E}
  证明: by
  rw [← traj_comp_partialTraj hab] at hf
  exact hf.comp

Depends on / 依赖: hf.comp, traj_comp_partialTraj
-/
theorem aestronglyMeasurable_traj {a b : Nat} (hab : a <= b) {f : (Π n, X n) -> E}
    {x₀ : Π i : Iic a, X i} (hf : AEStronglyMeasurable f (traj κ a x₀)) :
    forallᵐ x ∂partialTraj κ a b x₀, AEStronglyMeasurable f (traj κ b x) := by
  rw [← traj_comp_partialTraj hab] at hf
  exact hf.comp

variable [NormedSpace Real E]

/--
theorem `integral_traj` / 定理 `integral_traj`

English:
theorem integral_traj
  statement: {a : Nat} (x₀ : Π i : Iic a, X i) {f : (Π n, X n) -> E}
  proof: by
  nth_rw 1 [← traj_map_updateFinset, integral_map]
  · exact measurable_updateFinset_left.aemeasurable
  · convert! mf
    rw [traj_map_updateFinset]

中文:
定理 integral_traj
  结论: {a : 自然数} (x₀ : Π i : 左无界右闭区间 a, X i) {f : (Π n, X n) -> E}
  证明: by
  nth_rw 1 [← traj_map_updateFinset, integral_map]
  · exact measurable_updateFinset_left.aemeasurable
  · convert! mf
    rw [traj_map_updateFinset]

Depends on / 依赖: aemeasurable, convert, integral_map, measurable_updateFinset_left, measurable_updateFinset_left.aemeasurable, nth_rw, traj_map_updateFinset
-/
theorem integral_traj {a : Nat} (x₀ : Π i : Iic a, X i) {f : (Π n, X n) -> E}
    (mf : AEStronglyMeasurable f (traj κ a x₀)) :
    ∫ x, f x ∂traj κ a x₀ = ∫ x, f (updateFinset x (Iic a) x₀) ∂traj κ a x₀ := by
  nth_rw 1 [← traj_map_updateFinset, integral_map]
  · exact measurable_updateFinset_left.aemeasurable
  · convert! mf
    rw [traj_map_updateFinset]

/--
lemma `partialTraj_compProd_traj` / 引理 `partialTraj_compProd_traj`

English:
lemma partialTraj_compProd_traj
  given: {a b : Nat} (hab : a <= b) (u : Π i : Iic a, X i)
  proof: by
  ext s ms
  rw [Measure.map_apply]; rw [Measure.compProd_apply]; rw [← traj_comp_partialTraj hab]; rw [comp_apply']
  · congr 1 with x
    rw [← traj_map_updateFinset]; rw [Measure.map_apply]; rw [Measure.map_apply]
    · congr 1 with y
      simp only [Set.mem_preimage]
      congrm (fun i => ?_, fun i => ?_) in s <;> simp [updateFinset]
    any_goals fun_prop
    all_goals exact ms.preimage (by fun_prop)
  any_goals exact ms.preimage (by fun_prop)
  fun_prop

中文:
引理 partialTraj_compProd_traj
  条件: {a b : 自然数} (hab : a <= b) (u : Π i : 左无界右闭区间 a, X i)
  证明: by
  ext s ms
  rw [Measure.map_apply]; rw [Measure.compProd_apply]; rw [← traj_comp_partialTraj hab]; rw [comp_apply']
  · congr 1 with x
    rw [← traj_map_updateFinset]; rw [Measure.map_apply]; rw [Measure.map_apply]
    · congr 1 with y
      simp only [Set.mem_preimage]
      congrm (fun i => ?_, fun i => ?_) in s <;> simp [updateFinset]
    any_goals fun_prop
    all_goals exact ms.preimage (by fun_prop)
  any_goals exact ms.preimage (by fun_prop)
  fun_prop

Depends on / 依赖: Measure, Measure.compProd_apply, Measure.map_apply, Set.mem_preimage, all_goals, any_goals, compProd_apply, comp_apply, congrm, fun_prop, map_apply, mem_preimage, ms.preimage, preimage, traj_comp_partialTraj, traj_map_updateFinset, updateFinset
-/
lemma partialTraj_compProd_traj {a b : Nat} (hab : a <= b) (u : Π i : Iic a, X i) :
    (partialTraj κ a b u) otimesₘ (traj κ b) = (traj κ a u).map (fun x => (frestrictLe b x, x)) := by
  ext s ms
  rw [Measure.map_apply]; rw [Measure.compProd_apply]; rw [← traj_comp_partialTraj hab]; rw [comp_apply']
  · congr 1 with x
    rw [← traj_map_updateFinset]; rw [Measure.map_apply]; rw [Measure.map_apply]
    · congr 1 with y
      simp only [Set.mem_preimage]
      congrm (fun i => ?_, fun i => ?_) in s <;> simp [updateFinset]
    any_goals fun_prop
    all_goals exact ms.preimage (by fun_prop)
  any_goals exact ms.preimage (by fun_prop)
  fun_prop

/--
lemma `partialTraj_compProd_eq_map_traj` / 引理 `partialTraj_compProd_eq_map_traj`

English:
lemma partialTraj_compProd_eq_map_traj
  given: {a b : Nat} (hab : a <= b) {x₀ : Π n : Iic a, X n}
  proof: by
  have hf : (fun x : Π n, X n => (frestrictLe b x, x (b + 1))) =
      (Prod.map id (fun x => x (b + 1))) ∘ (fun x => (frestrictLe b x, x)) := rfl
  rw [hf]; rw [← Measure.map_map (by fun_prop) (by fun_prop)]; rw [← partialTraj_compProd_traj hab]; rw [← Measure.compProd_map (by fun_prop)]; rw [map_traj_succ_self]

中文:
引理 partialTraj_compProd_eq_map_traj
  条件: {a b : 自然数} (hab : a <= b) {x₀ : Π n : 左无界右闭区间 a, X n}
  证明: by
  have hf : (fun x : Π n, X n => (frestrictLe b x, x (b + 1))) =
      (Prod.map id (fun x => x (b + 1))) ∘ (fun x => (frestrictLe b x, x)) := rfl
  rw [hf]; rw [← Measure.map_map (by fun_prop) (by fun_prop)]; rw [← partialTraj_compProd_traj hab]; rw [← Measure.compProd_map (by fun_prop)]; rw [map_traj_succ_self]

Depends on / 依赖: Measure, Measure.compProd_map, Measure.map_map, Prod.map, compProd_map, frestrictLe, fun_prop, map_map, map_traj_succ_self, partialTraj_compProd_traj
-/
lemma partialTraj_compProd_eq_map_traj {a b : Nat} (hab : a <= b) {x₀ : Π n : Iic a, X n} :
    (partialTraj κ a b x₀) otimesₘ (κ b) = (traj κ a x₀).map (fun x => (frestrictLe b x, x (b + 1))) := by
  have hf : (fun x : Π n, X n => (frestrictLe b x, x (b + 1))) =
      (Prod.map id (fun x => x (b + 1))) ∘ (fun x => (frestrictLe b x, x)) := rfl
  rw [hf]; rw [← Measure.map_map (by fun_prop) (by fun_prop)]; rw [← partialTraj_compProd_traj hab]; rw [← Measure.compProd_map (by fun_prop)]; rw [map_traj_succ_self]

/--
theorem `integral_traj_partialTraj'` / 定理 `integral_traj_partialTraj'`

English:
theorem integral_traj_partialTraj'
  statement: {a b : Nat} (hab : a <= b) {x₀ : Π i : Iic a, X i}
  proof: by
  have hf' := hf
  rw [partialTraj_compProd_traj hab] at hf'
  simp_rw [← uncurry_apply_pair f, ← Measure.integral_compProd hf,
    partialTraj_compProd_traj hab, integral_map (by fun_prop) hf'.1]

中文:
定理 integral_traj_partialTraj'
  结论: {a b : 自然数} (hab : a <= b) {x₀ : Π i : 左无界右闭区间 a, X i}
  证明: by
  have hf' := hf
  rw [partialTraj_compProd_traj hab] at hf'
  simp_rw [← uncurry_apply_pair f, ← Measure.integral_compProd hf,
    partialTraj_compProd_traj hab, integral_map (by fun_prop) hf'.1]

Depends on / 依赖: Measure, Measure.integral_compProd, fun_prop, integral_compProd, integral_map, partialTraj_compProd_traj, simp_rw, uncurry_apply_pair
-/
theorem integral_traj_partialTraj' {a b : Nat} (hab : a <= b) {x₀ : Π i : Iic a, X i}
    {f : (Π i : Iic b, X i) -> (Π n : Nat, X n) -> E}
    (hf : Integrable f.uncurry ((partialTraj κ a b x₀) otimesₘ (traj κ b))) :
    ∫ x, ∫ y, f x y ∂traj κ b x ∂partialTraj κ a b x₀ =
    ∫ x, f (frestrictLe b x) x ∂traj κ a x₀ := by
  have hf' := hf
  rw [partialTraj_compProd_traj hab] at hf'
  simp_rw [← uncurry_apply_pair f, ← Measure.integral_compProd hf,
    partialTraj_compProd_traj hab, integral_map (by fun_prop) hf'.1]

/--
theorem `integral_traj_partialTraj` / 定理 `integral_traj_partialTraj`

English:
theorem integral_traj_partialTraj
  statement: {a b : Nat} (hab : a <= b) {x₀ : Π i : Iic a, X i}
  proof: by
  apply integral_traj_partialTraj' hab
  rw [← traj_comp_partialTraj hab]; rw [comp_apply]; rw [← Measure.snd_compProd] at hf
  exact hf.comp_measurable measurable_snd

中文:
定理 integral_traj_partialTraj
  结论: {a b : 自然数} (hab : a <= b) {x₀ : Π i : 左无界右闭区间 a, X i}
  证明: by
  apply integral_traj_partialTraj' hab
  rw [← traj_comp_partialTraj hab]; rw [comp_apply]; rw [← Measure.snd_compProd] at hf
  exact hf.comp_measurable measurable_snd

Depends on / 依赖: Measure, Measure.snd_compProd, comp_apply, comp_measurable, hf.comp_measurable, integral_traj_partialTraj, measurable_snd, snd_compProd, traj_comp_partialTraj
-/
theorem integral_traj_partialTraj {a b : Nat} (hab : a <= b) {x₀ : Π i : Iic a, X i}
    {f : (Π n : Nat, X n) -> E} (hf : Integrable f (traj κ a x₀)) :
    ∫ x, ∫ y, f y ∂traj κ b x ∂partialTraj κ a b x₀ = ∫ x, f x ∂traj κ a x₀ := by
  apply integral_traj_partialTraj' hab
  rw [← traj_comp_partialTraj hab]; rw [comp_apply]; rw [← Measure.snd_compProd] at hf
  exact hf.comp_measurable measurable_snd

/--
theorem `setIntegral_traj_partialTraj'` / 定理 `setIntegral_traj_partialTraj'`

English:
theorem setIntegral_traj_partialTraj'
  statement: {a b : Nat} (hab : a <= b) {u : (Π i : Iic a, X i)}
  proof: by
  rw [← integral_integral_indicator _ _ _ hA]; rw [integral_traj_partialTraj' hab]
  · simp_rw [← Set.indicator_comp_right, ← integral_indicator (measurable_frestrictLe b hA)]
    rfl
  convert! hf.indicator (hA.prod .univ)
  ext ⟨x, y⟩
  by_cases hx : x in A <;> simp [uncurry_def, hx]

中文:
定理 set整数egral_traj_partialTraj'
  结论: {a b : 自然数} (hab : a <= b) {u : (Π i : 左无界右闭区间 a, X i)}
  证明: by
  rw [← integral_integral_indicator _ _ _ hA]; rw [integral_traj_partialTraj' hab]
  · simp_rw [← Set.indicator_comp_right, ← integral_indicator (measurable_frestrictLe b hA)]
    rfl
  convert! hf.indicator (hA.prod .univ)
  ext ⟨x, y⟩
  by_cases hx : x in A <;> simp [uncurry_def, hx]

Depends on / 依赖: Set.indicator_comp_right, convert, hA.prod, hf.indicator, indicator, indicator_comp_right, integral_indicator, integral_integral_indicator, integral_traj_partialTraj, measurable_frestrictLe, simp_rw, uncurry_def
-/
theorem setIntegral_traj_partialTraj' {a b : Nat} (hab : a <= b) {u : (Π i : Iic a, X i)}
    {f : (Π i : Iic b, X i) -> (Π n : Nat, X n) -> E}
    (hf : Integrable f.uncurry ((partialTraj κ a b u) otimesₘ (traj κ b)))
    {A : Set (Π i : Iic b, X i)} (hA : MeasurableSet A) :
    ∫ x in A, ∫ y, f x y ∂traj κ b x ∂partialTraj κ a b u =
      ∫ y in frestrictLe b ⁻¹' A, f (frestrictLe b y) y ∂traj κ a u := by
  rw [← integral_integral_indicator _ _ _ hA]; rw [integral_traj_partialTraj' hab]
  · simp_rw [← Set.indicator_comp_right, ← integral_indicator (measurable_frestrictLe b hA)]
    rfl
  convert! hf.indicator (hA.prod .univ)
  ext ⟨x, y⟩
  by_cases hx : x in A <;> simp [uncurry_def, hx]

/--
theorem `setIntegral_traj_partialTraj` / 定理 `setIntegral_traj_partialTraj`

English:
theorem setIntegral_traj_partialTraj
  statement: {a b : Nat} (hab : a <= b) {x₀ : (Π i : Iic a, X i)}
  proof: by
  refine setIntegral_traj_partialTraj' hab ?_ hA
  rw [← traj_comp_partialTraj hab]; rw [comp_apply]; rw [← Measure.snd_compProd] at hf
  exact hf.comp_measurable measurable_snd

中文:
定理 set整数egral_traj_partialTraj
  结论: {a b : 自然数} (hab : a <= b) {x₀ : (Π i : 左无界右闭区间 a, X i)}
  证明: by
  refine setIntegral_traj_partialTraj' hab ?_ hA
  rw [← traj_comp_partialTraj hab]; rw [comp_apply]; rw [← Measure.snd_compProd] at hf
  exact hf.comp_measurable measurable_snd

Depends on / 依赖: Measure, Measure.snd_compProd, comp_apply, comp_measurable, hf.comp_measurable, measurable_snd, setIntegral_traj_partialTraj, snd_compProd, traj_comp_partialTraj
-/
theorem setIntegral_traj_partialTraj {a b : Nat} (hab : a <= b) {x₀ : (Π i : Iic a, X i)}
    {f : (Π n : Nat, X n) -> E} (hf : Integrable f (traj κ a x₀))
    {A : Set (Π i : Iic b, X i)} (hA : MeasurableSet A) :
    ∫ x in A, ∫ y, f y ∂traj κ b x ∂partialTraj κ a b x₀ =
      ∫ y in frestrictLe b ⁻¹' A, f y ∂traj κ a x₀ := by
  refine setIntegral_traj_partialTraj' hab ?_ hA
  rw [← traj_comp_partialTraj hab]; rw [comp_apply]; rw [← Measure.snd_compProd] at hf
  exact hf.comp_measurable measurable_snd

variable [CompleteSpace E]

open Filtration

/--
theorem `condExp_traj` / 定理 `condExp_traj`

English:
theorem condExp_traj
  statement: {a b : Nat} (hab : a <= b) {x₀ : Π i : Iic a, X i}
  proof: by
  have i_f' : Integrable (fun x => ∫ y, f y ∂(traj κ b) x)
      (((traj κ a) x₀).map (frestrictLe b)) := by
    rw [← map_apply _ (measurable_frestrictLe _)]; rw [traj_map_frestrictLe _ _]
    rw [← traj_comp_partialTraj hab] at i_f
    exact i_f.integral_comp
  refine ae_eq_condExp_of_forall_setIntegral_eq (piLE.le _) i_f
    (fun s _ _ => i_f'.comp_aemeasurable (measurable_frestrictLe b).aemeasurable |>.integrableOn)
.symm <;> rw [piLE_eq_comap_frestrictLe] ?_ ?_
  · rintro - ⟨t, mt, rfl⟩ -
    simp_rw [Function.comp_apply]
    rw [← setIntegral_map mt i_f'.1]; rw [← map_apply]; rw [traj_map_frestrictLe]; rw [setIntegral_traj_partialTraj hab i_f mt]
    all_goals fun_prop
  · exact (i_f'.1.comp_ae_measurable' (measurable_frestrictLe b).aemeasurable)

中文:
定理 condExp_traj
  结论: {a b : 自然数} (hab : a <= b) {x₀ : Π i : 左无界右闭区间 a, X i}
  证明: by
  have i_f' : Integrable (fun x => ∫ y, f y ∂(traj κ b) x)
      (((traj κ a) x₀).map (frestrictLe b)) := by
    rw [← map_apply _ (measurable_frestrictLe _)]; rw [traj_map_frestrictLe _ _]
    rw [← traj_comp_partialTraj hab] at i_f
    exact i_f.integral_comp
  refine ae_eq_condExp_of_forall_setIntegral_eq (piLE.le _) i_f
    (fun s _ _ => i_f'.comp_aemeasurable (measurable_frestrictLe b).aemeasurable |>.integrableOn)
.symm <;> rw [piLE_eq_comap_frestrictLe] ?_ ?_
  · rintro - ⟨t, mt, rfl⟩ -
    simp_rw [Function.comp_apply]
    rw [← setIntegral_map mt i_f'.1]; rw [← map_apply]; rw [traj_map_frestrictLe]; rw [setIntegral_traj_partialTraj hab i_f mt]
    all_goals fun_prop
  · exact (i_f'.1.comp_ae_measurable' (measurable_frestrictLe b).aemeasurable)

Depends on / 依赖: Function, Function.comp_app, Integrable, ae_eq_condExp_of_forall_setIntegral_eq, aemeasurable, comp_aemeasurable, comp_app, frestrictLe, i_f.integral_comp, integrableOn, integral_comp, map_apply, measurable_frestrictLe, piLE.le, piLE_eq_comap_frestrictLe, simp_rw, traj_comp_partialTraj, traj_map_frestrictLe
-/
theorem condExp_traj {a b : Nat} (hab : a <= b) {x₀ : Π i : Iic a, X i}
    {f : (Π n, X n) -> E} (i_f : Integrable f (traj κ a x₀)) :
    (traj κ a x₀)[f | piLE b] =ᵐ[traj κ a x₀]
      fun x => ∫ y, f y ∂traj κ b (frestrictLe b x) := by
  have i_f' : Integrable (fun x => ∫ y, f y ∂(traj κ b) x)
      (((traj κ a) x₀).map (frestrictLe b)) := by
    rw [← map_apply _ (measurable_frestrictLe _)]; rw [traj_map_frestrictLe _ _]
    rw [← traj_comp_partialTraj hab] at i_f
    exact i_f.integral_comp
  refine ae_eq_condExp_of_forall_setIntegral_eq (piLE.le _) i_f
    (fun s _ _ => i_f'.comp_aemeasurable (measurable_frestrictLe b).aemeasurable |>.integrableOn)
.symm <;> rw [piLE_eq_comap_frestrictLe] ?_ ?_
  · rintro - ⟨t, mt, rfl⟩ -
    simp_rw [Function.comp_apply]
    rw [← setIntegral_map mt i_f'.1]; rw [← map_apply]; rw [traj_map_frestrictLe]; rw [setIntegral_traj_partialTraj hab i_f mt]
    all_goals fun_prop
  · exact (i_f'.1.comp_ae_measurable' (measurable_frestrictLe b).aemeasurable)

/--
theorem `condExp_traj'` / 定理 `condExp_traj'`

English:
theorem condExp_traj'
  statement: {a b c : Nat} (hab : a <= b) (hbc : b <= c)
  proof: by
  have i_cf : Integrable ((traj κ a x₀)[f | piLE c]) (traj κ a x₀) :=
    integrable_condExp
  have mcf : StronglyMeasurable ((traj κ a x₀)[f | piLE c]) :=
    stronglyMeasurable_condExp.mono (piLE.le c)
  filter_upwards [piLE.condExp_condExp f hbc, condExp_traj hab i_cf] with x h1 h2
  rw [← h1]; rw [h2]; rw [← traj_map_frestrictLe]; rw [Kernel.map_apply]; rw [integral_map]
  · congr with y
    apply stronglyMeasurable_condExp.dependsOn_of_piLE
    simp only [Set.mem_Iic, updateFinset, mem_Iic, frestrictLe_apply, dite_eq_ite]
    exact fun i hi => (if_pos hi).symm
  any_goals fun_prop
  exact (mcf.comp_measurable measurable_updateFinset).aestronglyMeasurable

中文:
定理 condExp_traj'
  结论: {a b c : 自然数} (hab : a <= b) (hbc : b <= c)
  证明: by
  have i_cf : Integrable ((traj κ a x₀)[f | piLE c]) (traj κ a x₀) :=
    integrable_condExp
  have mcf : StronglyMeasurable ((traj κ a x₀)[f | piLE c]) :=
    stronglyMeasurable_condExp.mono (piLE.le c)
  filter_upwards [piLE.condExp_condExp f hbc, condExp_traj hab i_cf] with x h1 h2
  rw [← h1]; rw [h2]; rw [← traj_map_frestrictLe]; rw [Kernel.map_apply]; rw [integral_map]
  · congr with y
    apply stronglyMeasurable_condExp.dependsOn_of_piLE
    simp only [Set.mem_Iic, updateFinset, mem_Iic, frestrictLe_apply, dite_eq_ite]
    exact fun i hi => (if_pos hi).symm
  any_goals fun_prop
  exact (mcf.comp_measurable measurable_updateFinset).aestronglyMeasurable

Depends on / 依赖: Integrable, Kernel, Kernel.map_apply, Set.mem_Iic, StronglyMeasurable, condExp_condExp, condExp_traj, dependsOn_of_piLE, filter_upwards, frestrictLe_apply, i_cf, integrable_condExp, integral_map, map_apply, mem_Iic, piLE.condExp_condExp, piLE.le, stronglyMeasurable_condExp, stronglyMeasurable_condExp.dependsOn_of_piLE, stronglyMeasurable_condExp.mono
-/
theorem condExp_traj' {a b c : Nat} (hab : a <= b) (hbc : b <= c)
    (x₀ : Π i : Iic a, X i) (f : (Π n, X n) -> E) :
    (traj κ a x₀)[f | piLE b] =ᵐ[traj κ a x₀]
      fun x => ∫ y, ((traj κ a x₀)[f | piLE c]) (updateFinset x (Iic c) y)
        ∂partialTraj κ b c (frestrictLe b x) := by
  have i_cf : Integrable ((traj κ a x₀)[f | piLE c]) (traj κ a x₀) :=
    integrable_condExp
  have mcf : StronglyMeasurable ((traj κ a x₀)[f | piLE c]) :=
    stronglyMeasurable_condExp.mono (piLE.le c)
  filter_upwards [piLE.condExp_condExp f hbc, condExp_traj hab i_cf] with x h1 h2
  rw [← h1]; rw [h2]; rw [← traj_map_frestrictLe]; rw [Kernel.map_apply]; rw [integral_map]
  · congr with y
    apply stronglyMeasurable_condExp.dependsOn_of_piLE
    simp only [Set.mem_Iic, updateFinset, mem_Iic, frestrictLe_apply, dite_eq_ite]
    exact fun i hi => (if_pos hi).symm
  any_goals fun_prop
  exact (mcf.comp_measurable measurable_updateFinset).aestronglyMeasurable

end integral

section trajMeasure

/-- Distribution of the trajectory obtained by starting with `μ₀` and iterating the kernels `κ`. -/
noncomputable
/--
Definition of `trajMeasure` / `trajMeasure` 的定义

English:
definition trajMeasure
  signature: (μ₀ : Measure (X 0)) (κ : (n : Nat) -> Kernel (Π i : Iic n, X i) (X (n + 1)))
  body: (traj κ 0) ∘ₘ (μ₀.map (MeasurableEquiv.piUnique _).symm)

中文:
定义 trajMeasure
  签名: (μ₀ : 测度 (X 0)) (κ : (n : 自然数) -> 核 (Π i : 左无界右闭区间 n, X i) (X (n + 1)))
  定义体: (traj κ 0) ∘ₘ (μ₀.map (MeasurableEquiv.piUnique _).symm)

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.piUnique, piUnique
-/
def trajMeasure (μ₀ : Measure (X 0)) (κ : (n : Nat) -> Kernel (Π i : Iic n, X i) (X (n + 1)))
    [forall n, IsMarkovKernel (κ n)] :
    Measure (Π n, X n) :=
  (traj κ 0) ∘ₘ (μ₀.map (MeasurableEquiv.piUnique _).symm)

variable {μ₀ : Measure (X 0)} [IsProbabilityMeasure μ₀]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsProbabilityMeasure (trajMeasure μ₀ κ)
  body: by
  rw [trajMeasure]
  have : IsProbabilityMeasure (μ₀.map (MeasurableEquiv.piUnique ((fun i : Iic 0 => X i))).symm) :=
Measure.isProbabilityMeasure_map by fun_prop
  infer_instance

中文:
实例 :
  签名: 是概率测度 (trajMeasure μ₀ κ)
  定义体: by
  rw [trajMeasure]
  have : IsProbabilityMeasure (μ₀.map (MeasurableEquiv.piUnique ((fun i : Iic 0 => X i))).symm) :=
Measure.isProbabilityMeasure_map by fun_prop
  infer_instance

Depends on / 依赖: IsProbabilityMeasure, MeasurableEquiv, MeasurableEquiv.piUnique, Measure, Measure.isProbabilityMeasure_map, fun_prop, infer_instance, isProbabilityMeasure_map, piUnique, trajMeasure
-/
instance : IsProbabilityMeasure (trajMeasure μ₀ κ) := by
  rw [trajMeasure]
  have : IsProbabilityMeasure (μ₀.map (MeasurableEquiv.piUnique ((fun i : Iic 0 => X i))).symm) :=
Measure.isProbabilityMeasure_map by fun_prop
  infer_instance

/--
lemma `map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure` / 引理 `map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`

English:
lemma map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  given: {a : Nat}
  proof: by
  rw [Measure.compProd_eq_comp_prod]; rw [trajMeasure]; rw [Measure.map_comp _ _ (by fun_prop)]; rw [traj_map_frestrictLe]; rw [Measure.comp_assoc]; rw [Measure.map_comp _ _ (by fun_prop)]
  congr with x₀ : 1
  rw [comp_apply]; rw [← Measure.compProd_eq_comp_prod]; rw [map_apply _ (by fun_prop)]; rw [partialTraj_compProd_eq_map_traj zero_le]

中文:
引理 map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  条件: {a : 自然数}
  证明: by
  rw [Measure.compProd_eq_comp_prod]; rw [trajMeasure]; rw [Measure.map_comp _ _ (by fun_prop)]; rw [traj_map_frestrictLe]; rw [Measure.comp_assoc]; rw [Measure.map_comp _ _ (by fun_prop)]
  congr with x₀ : 1
  rw [comp_apply]; rw [← Measure.compProd_eq_comp_prod]; rw [map_apply _ (by fun_prop)]; rw [partialTraj_compProd_eq_map_traj zero_le]

Depends on / 依赖: Measure, Measure.compProd_eq_comp_prod, Measure.comp_assoc, Measure.map_comp, compProd_eq_comp_prod, comp_apply, comp_assoc, fun_prop, map_apply, map_comp, partialTraj_compProd_eq_map_traj, trajMeasure, traj_map_frestrictLe, zero_le
-/
lemma map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure {a : Nat} :
    (trajMeasure μ₀ κ).map (frestrictLe a) otimesₘ κ a =
      (trajMeasure μ₀ κ).map (fun x => (frestrictLe a x, x (a + 1))) := by
  rw [Measure.compProd_eq_comp_prod]; rw [trajMeasure]; rw [Measure.map_comp _ _ (by fun_prop)]; rw [traj_map_frestrictLe]; rw [Measure.comp_assoc]; rw [Measure.map_comp _ _ (by fun_prop)]
  congr with x₀ : 1
  rw [comp_apply]; rw [← Measure.compProd_eq_comp_prod]; rw [map_apply _ (by fun_prop)]; rw [partialTraj_compProd_eq_map_traj zero_le]

/--
lemma `condDistrib_trajMeasure` / 引理 `condDistrib_trajMeasure`

English:
lemma condDistrib_trajMeasure
  given: {a : Nat} [StandardBorelSpace (X (a + 1))] [Nonempty (X (a + 1))]
  proof: by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (by fun_prop) (by fun_prop)
  exact map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm

中文:
引理 condDistrib_trajMeasure
  条件: {a : 自然数} [StandardBorel空间 (X (a + 1))] [非空 (X (a + 1))]
  证明: by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (by fun_prop) (by fun_prop)
  exact map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm

Depends on / 依赖: condDistrib_ae_eq_of_measure_eq_compProd_of_measurable, fun_prop, map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure, map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm
-/
lemma condDistrib_trajMeasure {a : Nat} [StandardBorelSpace (X (a + 1))] [Nonempty (X (a + 1))] :
    condDistrib (fun x => x (a + 1)) (frestrictLe a) (trajMeasure μ₀ κ)
      =ᵐ[(trajMeasure μ₀ κ).map (frestrictLe a)] κ a := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (by fun_prop) (by fun_prop)
  exact map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm

end trajMeasure

end ProbabilityTheory.Kernel
