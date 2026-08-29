/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Dynamics.Ergodic.Action.Regular
public import Mathlib.MeasureTheory.Measure.ContinuousPreimage
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Ergodicity from minimality

In this file we prove that the left shift `(a * ·)` on a compact topological group `G`
is ergodic with respect to the Haar measure if and only if it is minimal,
i.e., the powers `a ^ n` are dense in `G`.

The proof of the more difficult "if minimal, then ergodic" implication
is based on the ergodicity of the left action of a group on itself
and the following fact that we prove in `ergodic_smul_of_denseRange_pow` below:

If a monoid `M` continuously acts on an R₁ topological space `X`,
`g` is an element of `M` such that its natural powers are dense in `M`,
and `μ` is a finite inner regular measure on `X` which is ergodic with respect to the action of `M`,
then the scalar multiplication by `g` is an ergodic map.

We also prove that a continuous monoid homomorphism `f : G →* G` is ergodic,
if it is surjective and the preimages of `1` under iterations of `f` are dense in the group.
This theorem applies, e.g., to the map `z ↦ n • z` on the additive circle or a torus.
-/

public section

open MeasureTheory Filter Set Function
open scoped Pointwise Topology

section SMul

variable {M : Type*} [TopologicalSpace M]
  {X : Type*} [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
  [SMul M X] [ContinuousSMul M X]
  {μ : Measure X} [IsFiniteMeasure μ] [μ.InnerRegular] [ErgodicSMul M X μ] {s : Set X}

/-- Let `M` act continuously on an R₁ topological space `X`.
Let `μ` be a finite inner regular measure on `X` which is ergodic with respect to this action.
If a null measurable set `s` is a.e. equal
to its preimages under the action of a dense set of elements of `M`,
then it is either null or conull. -/
@[to_additive /-- Let `M` act continuously on an R₁ topological space `X`.
Let `μ` be a finite inner regular measure on `X` which is ergodic with respect to this action.
If a null measurable set `s` is a.e. equal
to its preimages under the action of a dense set of elements of `M`,
then it is either null or conull. -/]
/--
theorem `aeconst_of_dense_setOfPred_preimage_smul_ae` / 定理 `aeconst_of_dense_setOfPred_preimage_smul_ae`

English:
theorem aeconst_of_dense_setOfPred_preimage_smul_ae
  statement: (hsm : NullMeasurableSet s μ)
  proof: by
  borelize M
  refine aeconst_of_forall_preimage_smul_ae_eq M hsm ?_
  rwa [dense_iff_closure_eq, IsClosed.closure_eq, eq_univ_iff_forall] at hd
  let f : C(M × X, X) := ⟨(· • ·).uncurry, continuous_smul⟩
  exact isClosed_setOfPred_preimage_ae_eq f.curry.continuous (measurePreserving_smul · μ) _ hsm
    (measure_ne_top _ _)

@[deprecated (since := "2026-07-09")]
alias aeconst_of_dense_setOf_preimage_smul_ae := aeconst_of_dense_setOfPred_preimage_smul_ae

@[deprecated (since := "2026-07-09")]
alias aeconst_of_dense_setOf_preimage_vadd_ae := aeconst_of_dense_setOfPred_preimage_vadd_ae

@[to_additive]

中文:
定理 aeconst_of_dense_setOfPred_preimage_smul_ae
  结论: (hsm : NullMeasurableSet s μ)
  证明: by
  borelize M
  refine aeconst_of_forall_preimage_smul_ae_eq M hsm ?_
  rwa [dense_iff_closure_eq, IsClosed.closure_eq, eq_univ_iff_forall] at hd
  let f : C(M × X, X) := ⟨(· • ·).uncurry, continuous_smul⟩
  exact isClosed_setOfPred_preimage_ae_eq f.curry.continuous (measurePreserving_smul · μ) _ hsm
    (measure_ne_top _ _)

@[deprecated (since := "2026-07-09")]
alias aeconst_of_dense_setOf_preimage_smul_ae := aeconst_of_dense_setOfPred_preimage_smul_ae

@[deprecated (since := "2026-07-09")]
alias aeconst_of_dense_setOf_preimage_vadd_ae := aeconst_of_dense_setOfPred_preimage_vadd_ae

@[to_additive]

Depends on / 依赖: IsClosed, IsClosed.closure_eq, aeconst_of_forall_preimage_smul_ae_eq, borelize, closure_eq, continuous, continuous_smul, dense_iff_closure_eq, eq_univ_iff_forall, f.curry.continuous, isClosed_setOfPred_preimage_ae_eq, measurePreserving_smul, measure_ne_top, uncurry
-/
theorem aeconst_of_dense_setOfPred_preimage_smul_ae (hsm : NullMeasurableSet s μ)
    (hd : Dense {g : M | (g • ·) ⁻¹' s =ᵐ[μ] s}) : EventuallyConst s (ae μ) := by
  borelize M
  refine aeconst_of_forall_preimage_smul_ae_eq M hsm ?_
  rwa [dense_iff_closure_eq, IsClosed.closure_eq, eq_univ_iff_forall] at hd
  let f : C(M × X, X) := ⟨(· • ·).uncurry, continuous_smul⟩
  exact isClosed_setOfPred_preimage_ae_eq f.curry.continuous (measurePreserving_smul · μ) _ hsm
    (measure_ne_top _ _)

@[deprecated (since := "2026-07-09")]
alias aeconst_of_dense_setOf_preimage_smul_ae := aeconst_of_dense_setOfPred_preimage_smul_ae

@[deprecated (since := "2026-07-09")]
alias aeconst_of_dense_setOf_preimage_vadd_ae := aeconst_of_dense_setOfPred_preimage_vadd_ae

@[to_additive]
/--
theorem `aeconst_of_dense_setOfPred_preimage_smul_eq` / 定理 `aeconst_of_dense_setOfPred_preimage_smul_eq`

English:
theorem aeconst_of_dense_setOfPred_preimage_smul_eq
  statement: (hsm : NullMeasurableSet s μ)
  proof: aeconst_of_dense_setOfPred_preimage_smul_ae hsm hd.mono fun _ h => mem_ofPred.2 .of_eq h

@[deprecated (since := "2026-07-09")]
alias aeconst_of_dense_setOf_preimage_smul_eq := aeconst_of_dense_setOfPred_preimage_smul_eq

@[deprecated (since := "2026-07-09")]
alias aeconst_of_dense_setOf_preimage_vadd_eq := aeconst_of_dense_setOfPred_preimage_vadd_eq

中文:
定理 aeconst_of_dense_setOfPred_preimage_smul_eq
  结论: (hsm : NullMeasurableSet s μ)
  证明: aeconst_of_dense_setOfPred_preimage_smul_ae hsm hd.mono fun _ h => mem_ofPred.2 .of_eq h

@[deprecated (since := "2026-07-09")]
alias aeconst_of_dense_setOf_preimage_smul_eq := aeconst_of_dense_setOfPred_preimage_smul_eq

@[deprecated (since := "2026-07-09")]
alias aeconst_of_dense_setOf_preimage_vadd_eq := aeconst_of_dense_setOfPred_preimage_vadd_eq

Depends on / 依赖: aeconst_of_dense_setOfPred_preimage_smul_ae, hd.mono, mem_ofPred, of_eq
-/
theorem aeconst_of_dense_setOfPred_preimage_smul_eq (hsm : NullMeasurableSet s μ)
    (hd : Dense {g : M | (g • ·) ⁻¹' s = s}) : EventuallyConst s (ae μ) :=
aeconst_of_dense_setOfPred_preimage_smul_ae hsm hd.mono fun _ h => mem_ofPred.2 .of_eq h

@[deprecated (since := "2026-07-09")]
alias aeconst_of_dense_setOf_preimage_smul_eq := aeconst_of_dense_setOfPred_preimage_smul_eq

@[deprecated (since := "2026-07-09")]
alias aeconst_of_dense_setOf_preimage_vadd_eq := aeconst_of_dense_setOfPred_preimage_vadd_eq

/-- If a monoid `M` continuously acts on an R₁ topological space `X`,
`g` is an element of `M` such that its natural powers are dense in `M`,
and `μ` is a finite inner regular measure on `X` which is ergodic with respect to the action of `M`,
then the scalar multiplication by `g` is an ergodic map. -/
@[to_additive /-- If an additive monoid `M` continuously acts on an R₁ topological space `X`,
`g` is an element of `M` such that its natural multiples are dense in `M`,
and `μ` is a finite inner regular measure on `X` which is ergodic with respect to the action of `M`,
then the vector addition of `g` is an ergodic map. -/]
/--
theorem `ergodic_smul_of_denseRange_pow` / 定理 `ergodic_smul_of_denseRange_pow`

English:
theorem ergodic_smul_of_denseRange_pow
  statement: {M : Type*} [Monoid M] [TopologicalSpace M]
  proof: by
  borelize M
  refine ⟨measurePreserving_smul _ _, ⟨fun s hsm hs => ?_⟩⟩
  refine aeconst_of_dense_setOfPred_preimage_smul_eq hsm.nullMeasurableSet (hg.mono ?_)
  refine range_subset_iff.2 fun n => ?_
  rw [mem_ofPred]; rw [← smul_iterate]; rw [preimage_iterate_eq]; rw [iterate_fixed hs]

中文:
定理 ergodic_smul_of_denseRange_pow
  结论: {M : 类型} [幺半群 M] [拓扑空间 M]
  证明: by
  borelize M
  refine ⟨measurePreserving_smul _ _, ⟨fun s hsm hs => ?_⟩⟩
  refine aeconst_of_dense_setOfPred_preimage_smul_eq hsm.nullMeasurableSet (hg.mono ?_)
  refine range_subset_iff.2 fun n => ?_
  rw [mem_ofPred]; rw [← smul_iterate]; rw [preimage_iterate_eq]; rw [iterate_fixed hs]

Depends on / 依赖: aeconst_of_dense_setOfPred_preimage_smul_eq, borelize, hg.mono, hsm.nullMeasurableSet, iterate_fixed, measurePreserving_smul, mem_ofPred, nullMeasurableSet, preimage_iterate_eq, range_subset_iff, smul_iterate
-/
theorem ergodic_smul_of_denseRange_pow {M : Type*} [Monoid M] [TopologicalSpace M]
    [MulAction M X] [ContinuousSMul M X] {g : M} (hg : DenseRange (g ^ · : Nat -> M))
    (μ : Measure X) [IsFiniteMeasure μ] [μ.InnerRegular] [ErgodicSMul M X μ] :
    Ergodic (g • ·) μ := by
  borelize M
  refine ⟨measurePreserving_smul _ _, ⟨fun s hsm hs => ?_⟩⟩
  refine aeconst_of_dense_setOfPred_preimage_smul_eq hsm.nullMeasurableSet (hg.mono ?_)
  refine range_subset_iff.2 fun n => ?_
  rw [mem_ofPred]; rw [← smul_iterate]; rw [preimage_iterate_eq]; rw [iterate_fixed hs]

end SMul

section IsScalarTower

variable {M X : Type*} [Monoid M] [SMul M X]
  [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ] [μ.InnerRegular]

/-- If `N` acts continuously and ergodically on `X` and `M` acts minimally on `N`,
then the corresponding action of `M` on `X` is ergodic. -/
@[to_additive
  /-- If `N` acts additively continuously and ergodically on `X` and `M` acts minimally on `N`,
then the corresponding action of `M` on `X` is ergodic. -/]
/--
theorem `ErgodicSMul.trans_isMinimal` / 定理 `ErgodicSMul.trans_isMinimal`

English:
theorem ErgodicSMul.trans_isMinimal
  statement: (N : Type*) [MulAction M N]
  proof: by
    simpa only [smul_one_smul] using SMulInvariantMeasure.measure_preimage_smul (c • 1 : N) hsm
  aeconst_of_forall_preimage_smul_ae_eq {s} hsm hs := by
    refine aeconst_of_dense_setOfPred_preimage_smul_ae (M := N) hsm.nullMeasurableSet ?_
    refine (MulAction.dense_orbit M 1).mono ?_
    rintro _ ⟨g, rfl⟩
    simpa using hs g

中文:
定理 ErgodicSMul.trans_isMinimal
  结论: (N : 类型) [乘法作用 M N]
  证明: by
    simpa only [smul_one_smul] using SMulInvariantMeasure.measure_preimage_smul (c • 1 : N) hsm
  aeconst_of_forall_preimage_smul_ae_eq {s} hsm hs := by
    refine aeconst_of_dense_setOfPred_preimage_smul_ae (M := N) hsm.nullMeasurableSet ?_
    refine (MulAction.dense_orbit M 1).mono ?_
    rintro _ ⟨g, rfl⟩
    simpa using hs g

Depends on / 依赖: MulAction, MulAction.dense_orbit, SMulInvariantMeasure, SMulInvariantMeasure.measure_preimage_smul, aeconst_of_dense_setOfPred_preimage_smul_ae, aeconst_of_forall_preimage_smul_ae_eq, dense_orbit, hsm.nullMeasurableSet, measure_preimage_smul, nullMeasurableSet, smul_one_smul
-/
theorem ErgodicSMul.trans_isMinimal (N : Type*) [MulAction M N]
    [Monoid N] [TopologicalSpace N] [MulAction.IsMinimal M N]
    [MulAction N X] [IsScalarTower M N X] [ContinuousSMul N X] [ErgodicSMul N X μ] :
    ErgodicSMul M X μ where
  measure_preimage_smul c s hsm := by
    simpa only [smul_one_smul] using SMulInvariantMeasure.measure_preimage_smul (c • 1 : N) hsm
  aeconst_of_forall_preimage_smul_ae_eq {s} hsm hs := by
    refine aeconst_of_dense_setOfPred_preimage_smul_ae (M := N) hsm.nullMeasurableSet ?_
    refine (MulAction.dense_orbit M 1).mono ?_
    rintro _ ⟨g, rfl⟩
    simpa using hs g

end IsScalarTower

section MulActionGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G]
  {X : Type*} [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
  [MulAction G X] [ContinuousSMul G X]
  {μ : Measure X} [IsFiniteMeasure μ] [μ.InnerRegular] [ErgodicSMul G X μ] {s : Set X}

@[to_additive]
/--
theorem `aeconst_of_dense_aestabilizer_smul` / 定理 `aeconst_of_dense_aestabilizer_smul`

English:
theorem aeconst_of_dense_aestabilizer_smul
  statement: (hsm : NullMeasurableSet s μ)
  proof: aeconst_of_dense_setOfPred_preimage_smul_ae hsm
    (hd.preimage (isOpenMap_inv _)).mono fun g hg => by
    simpa only [preimage_smul] using! hg

中文:
定理 aeconst_of_dense_aestabilizer_smul
  结论: (hsm : NullMeasurableSet s μ)
  证明: aeconst_of_dense_setOfPred_preimage_smul_ae hsm
    (hd.preimage (isOpenMap_inv _)).mono fun g hg => by
    simpa only [preimage_smul] using! hg

Depends on / 依赖: aeconst_of_dense_setOfPred_preimage_smul_ae, hd.preimage, isOpenMap_inv, preimage, preimage_smul
-/
theorem aeconst_of_dense_aestabilizer_smul (hsm : NullMeasurableSet s μ)
    (hd : Dense (MulAction.aestabilizer G μ s : Set G)) : EventuallyConst s (ae μ) :=
aeconst_of_dense_setOfPred_preimage_smul_ae hsm
    (hd.preimage (isOpenMap_inv _)).mono fun g hg => by
    simpa only [preimage_smul] using! hg

set_option backward.isDefEq.respectTransparency.types false in
/-- If a monoid `M` continuously acts on an R₁ topological space `X`,
`g` is an element of `M` such that its integer powers are dense in `M`,
and `μ` is a finite inner regular measure on `X` which is ergodic with respect to the action of `M`,
then the scalar multiplication by `g` is an ergodic map. -/
@[to_additive /-- If an additive monoid `M` continuously acts on an R₁ topological space `X`,
`g` is an element of `M` such that its integer multiples are dense in `M`,
and `μ` is a finite inner regular measure on `X` which is ergodic with respect to the action of `M`,
then the vector addition of `g` is an ergodic map. -/]
/--
theorem `ergodic_smul_of_denseRange_zpow` / 定理 `ergodic_smul_of_denseRange_zpow`

English:
theorem ergodic_smul_of_denseRange_zpow
  statement: {g : G} (hg : DenseRange (g ^ · : Int -> G))
  proof: by
  borelize G
  refine ⟨measurePreserving_smul _ _, ⟨fun s hsm hs => ?_⟩⟩
  refine aeconst_of_dense_aestabilizer_smul hsm.nullMeasurableSet (hg.mono ?_)
  rw [← Subgroup.coe_zpowers]; rw [SetLike.coe_subset_coe]; rw [← Subgroup.zpowers_inv]; rw [Subgroup.zpowers_le]; rw [MulAction.mem_aestabilizer]; rw [← preimage_smul]; rw [hs]

中文:
定理 ergodic_smul_of_denseRange_zpow
  结论: {g : G} (hg : DenseRange (g ^ · : 整数 -> G))
  证明: by
  borelize G
  refine ⟨measurePreserving_smul _ _, ⟨fun s hsm hs => ?_⟩⟩
  refine aeconst_of_dense_aestabilizer_smul hsm.nullMeasurableSet (hg.mono ?_)
  rw [← Subgroup.coe_zpowers]; rw [SetLike.coe_subset_coe]; rw [← Subgroup.zpowers_inv]; rw [Subgroup.zpowers_le]; rw [MulAction.mem_aestabilizer]; rw [← preimage_smul]; rw [hs]

Depends on / 依赖: MulAction, MulAction.mem_aestabilizer, SetLike, SetLike.coe_subset_coe, Subgroup, Subgroup.coe_zpowers, Subgroup.zpowers_inv, Subgroup.zpowers_le, aeconst_of_dense_aestabilizer_smul, borelize, coe_subset_coe, coe_zpowers, hg.mono, hsm.nullMeasurableSet, measurePreserving_smul, mem_aestabilizer, nullMeasurableSet, preimage_smul, zpowers_inv, zpowers_le
-/
theorem ergodic_smul_of_denseRange_zpow {g : G} (hg : DenseRange (g ^ · : Int -> G))
    (μ : Measure X) [IsFiniteMeasure μ] [μ.InnerRegular] [ErgodicSMul G X μ] :
    Ergodic (g • ·) μ := by
  borelize G
  refine ⟨measurePreserving_smul _ _, ⟨fun s hsm hs => ?_⟩⟩
  refine aeconst_of_dense_aestabilizer_smul hsm.nullMeasurableSet (hg.mono ?_)
  rw [← Subgroup.coe_zpowers]; rw [SetLike.coe_subset_coe]; rw [← Subgroup.zpowers_inv]; rw [Subgroup.zpowers_le]; rw [MulAction.mem_aestabilizer]; rw [← preimage_smul]; rw [hs]

end MulActionGroup

section IsTopologicalGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]

/-- If the left multiplication by `g` is ergodic
with respect to a measure which is positive on nonempty open sets,
then the integer powers of `g` are dense in `G`. -/
@[to_additive /-- If the left addition of `g` is ergodic
with respect to a measure which is positive on nonempty open sets,
then the integer multiples of `g` are dense in `G`. -/]
/--
theorem `DenseRange.zpow_of_ergodic_mul_left` / 定理 `DenseRange.zpow_of_ergodic_mul_left`

English:
theorem DenseRange.zpow_of_ergodic_mul_left
  statement: [OpensMeasurableSpace G]
  proof: by
  intro a
  by_contra h
  obtain ⟨V, hV₁, hVo, hV⟩ :
      exists V : Set G, 1 in V ∧ IsOpen V ∧ forall x in V, forall y in V, forall m : Int, g ^ m != a * x / y := by
    rw [← mem_compl_iff]; rw [← interior_compl]; rw [mem_interior_iff_mem_nhds] at h
    have : Tendsto (fun (x, y) => a * x / y) (𝓝 1) (𝓝 a) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    rw [nhds_prod_eq] at this
    simpa [(nhds_basis_opens (1 : G)).prod_self.mem_iff, prod_subset_iff, and_assoc] using this h
  set s := ⋃ m : Int, g ^ m • V
  have hso : IsOpen s := isOpen_iUnion fun m => hVo.smul _
  have hsne : s.Nonempty := ⟨1, mem_iUnion.2 ⟨0, by simpa⟩⟩
  have hd : Disjoint s (a • V) := by
    simp_rw [s, disjoint_iUnion_left, disjoint_left]
    rintro m _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    apply hV y hy x hx m
    simp_all
  have hgs : (g * ·) ⁻¹' s = s := by
    simp only [s, preimage_iUnion, ← smul_eq_mul, preimage_smul]
    refine iUnion_congr_of_surjective _ (add_left_surjective (-1)) fun m => ?_
    simp [zpow_add, mul_smul]
  cases hg.measure_self_or_compl_eq_zero hso.measurableSet hgs with
  | inl h => exact hso.measure_ne_zero _ hsne h
  | inr h =>
    refine (hVo.smul a).measure_ne_zero μ (.image _ ⟨1, hV₁⟩) (measure_mono_null ?_ h)
    rwa [disjoint_right] at hd

中文:
定理 DenseRange.zpow_of_ergodic_mul_left
  结论: [OpensMeasurable空间 G]
  证明: by
  intro a
  by_contra h
  obtain ⟨V, hV₁, hVo, hV⟩ :
      exists V : Set G, 1 in V ∧ IsOpen V ∧ forall x in V, forall y in V, forall m : Int, g ^ m != a * x / y := by
    rw [← mem_compl_iff]; rw [← interior_compl]; rw [mem_interior_iff_mem_nhds] at h
    have : Tendsto (fun (x, y) => a * x / y) (𝓝 1) (𝓝 a) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    rw [nhds_prod_eq] at this
    simpa [(nhds_basis_opens (1 : G)).prod_self.mem_iff, prod_subset_iff, and_assoc] using this h
  set s := ⋃ m : Int, g ^ m • V
  have hso : IsOpen s := isOpen_iUnion fun m => hVo.smul _
  have hsne : s.Nonempty := ⟨1, mem_iUnion.2 ⟨0, by simpa⟩⟩
  have hd : Disjoint s (a • V) := by
    simp_rw [s, disjoint_iUnion_left, disjoint_left]
    rintro m _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    apply hV y hy x hx m
    simp_all
  have hgs : (g * ·) ⁻¹' s = s := by
    simp only [s, preimage_iUnion, ← smul_eq_mul, preimage_smul]
    refine iUnion_congr_of_surjective _ (add_left_surjective (-1)) fun m => ?_
    simp [zpow_add, mul_smul]
  cases hg.measure_self_or_compl_eq_zero hso.measurableSet hgs with
  | inl h => exact hso.measure_ne_zero _ hsne h
  | inr h =>
    refine (hVo.smul a).measure_ne_zero μ (.image _ ⟨1, hV₁⟩) (measure_mono_null ?_ h)
    rwa [disjoint_right] at hd

Depends on / 依赖: Continuous, Continuous.tendsto, IsOpen, Tendsto, and_assoc, fun_prop, interior_compl, mem_compl_iff, mem_iff, mem_interior_iff_mem_nhds, nhds_basis_opens, nhds_prod_eq, prod_self, prod_self.mem_iff, prod_subset_iff, tendsto
-/
theorem DenseRange.zpow_of_ergodic_mul_left [OpensMeasurableSpace G]
    {μ : Measure G} [μ.IsOpenPosMeasure] {g : G} (hg : Ergodic (g * ·) μ) :
    DenseRange (g ^ · : Int -> G) := by
  intro a
  by_contra h
  obtain ⟨V, hV₁, hVo, hV⟩ :
      exists V : Set G, 1 in V ∧ IsOpen V ∧ forall x in V, forall y in V, forall m : Int, g ^ m != a * x / y := by
    rw [← mem_compl_iff]; rw [← interior_compl]; rw [mem_interior_iff_mem_nhds] at h
    have : Tendsto (fun (x, y) => a * x / y) (𝓝 1) (𝓝 a) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    rw [nhds_prod_eq] at this
    simpa [(nhds_basis_opens (1 : G)).prod_self.mem_iff, prod_subset_iff, and_assoc] using this h
  set s := ⋃ m : Int, g ^ m • V
  have hso : IsOpen s := isOpen_iUnion fun m => hVo.smul _
  have hsne : s.Nonempty := ⟨1, mem_iUnion.2 ⟨0, by simpa⟩⟩
  have hd : Disjoint s (a • V) := by
    simp_rw [s, disjoint_iUnion_left, disjoint_left]
    rintro m _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    apply hV y hy x hx m
    simp_all
  have hgs : (g * ·) ⁻¹' s = s := by
    simp only [s, preimage_iUnion, ← smul_eq_mul, preimage_smul]
    refine iUnion_congr_of_surjective _ (add_left_surjective (-1)) fun m => ?_
    simp [zpow_add, mul_smul]
  cases hg.measure_self_or_compl_eq_zero hso.measurableSet hgs with
  | inl h => exact hso.measure_ne_zero _ hsne h
  | inr h =>
    refine (hVo.smul a).measure_ne_zero μ (.image _ ⟨1, hV₁⟩) (measure_mono_null ?_ h)
    rwa [disjoint_right] at hd

variable [SecondCountableTopology G] [BorelSpace G] {g : G}

@[to_additive]
/--
theorem `ergodic_mul_left_of_denseRange_pow` / 定理 `ergodic_mul_left_of_denseRange_pow`

English:
theorem ergodic_mul_left_of_denseRange_pow
  statement: (hg : DenseRange (g ^ · : Nat -> G))
  proof: ergodic_smul_of_denseRange_pow hg μ

@[to_additive]

中文:
定理 ergodic_mul_left_of_denseRange_pow
  结论: (hg : DenseRange (g ^ · : 自然数 -> G))
  证明: ergodic_smul_of_denseRange_pow hg μ

@[to_additive]

Depends on / 依赖: ergodic_smul_of_denseRange_pow
-/
theorem ergodic_mul_left_of_denseRange_pow (hg : DenseRange (g ^ · : Nat -> G))
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegular] [μ.IsMulLeftInvariant] :
    Ergodic (g * ·) μ :=
  ergodic_smul_of_denseRange_pow hg μ

@[to_additive]
/--
theorem `ergodic_mul_left_of_denseRange_zpow` / 定理 `ergodic_mul_left_of_denseRange_zpow`

English:
theorem ergodic_mul_left_of_denseRange_zpow
  statement: (hg : DenseRange (g ^ · : Int -> G))
  proof: ergodic_smul_of_denseRange_zpow hg μ

@[to_additive]

中文:
定理 ergodic_mul_left_of_denseRange_zpow
  结论: (hg : DenseRange (g ^ · : 整数 -> G))
  证明: ergodic_smul_of_denseRange_zpow hg μ

@[to_additive]

Depends on / 依赖: ergodic_smul_of_denseRange_zpow
-/
theorem ergodic_mul_left_of_denseRange_zpow (hg : DenseRange (g ^ · : Int -> G))
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegular] [μ.IsMulLeftInvariant] :
    Ergodic (g * ·) μ :=
  ergodic_smul_of_denseRange_zpow hg μ

@[to_additive]
/--
theorem `ergodic_mul_left_iff_denseRange_zpow` / 定理 `ergodic_mul_left_iff_denseRange_zpow`

English:
theorem ergodic_mul_left_iff_denseRange_zpow
  statement: (μ : Measure G) [IsFiniteMeasure μ]
  proof: ⟨.zpow_of_ergodic_mul_left, (ergodic_mul_left_of_denseRange_zpow · μ)⟩

中文:
定理 ergodic_mul_left_iff_denseRange_zpow
  结论: (μ : 测度 G) [是有限测度 μ]
  证明: ⟨.zpow_of_ergodic_mul_left, (ergodic_mul_left_of_denseRange_zpow · μ)⟩

Depends on / 依赖: ergodic_mul_left_of_denseRange_zpow, zpow_of_ergodic_mul_left
-/
theorem ergodic_mul_left_iff_denseRange_zpow (μ : Measure G) [IsFiniteMeasure μ]
    [μ.InnerRegular] [μ.IsMulLeftInvariant] [NeZero μ] :
    Ergodic (g * ·) μ ↔ DenseRange (g ^ · : Int -> G) :=
  ⟨.zpow_of_ergodic_mul_left, (ergodic_mul_left_of_denseRange_zpow · μ)⟩

end IsTopologicalGroup

namespace MonoidHom

variable {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- Let `f : G →* G` be a group endomorphism of a topological group with second countable topology.
If the preimages of `1` under the iterations of `f` are dense,
then it is pre-ergodic with respect to any finite inner regular left invariant measure. -/
@[to_additive /-- Let `f : G →+ G` be an additive group endomorphism
of a topological additive group with second countable topology.
If the preimages of `0` under the iterations of `f` are dense,
then it is pre-ergodic with respect to any finite inner regular left invariant measure. -/]
/--
theorem `preErgodic_of_dense_iUnion_preimage_one` / 定理 `preErgodic_of_dense_iUnion_preimage_one`

English:
theorem preErgodic_of_dense_iUnion_preimage_one
  proof: by
  refine ⟨fun s hsm hs =>
    aeconst_of_dense_setOfPred_preimage_smul_eq (M := G) hsm.nullMeasurableSet ?_⟩
refine hf.mono iUnion_subset fun n x hx => ?_
  have hsn : f^[n] ⁻¹' s = s := by
    rw [preimage_iterate_eq]; rw [iterate_fixed hs]
  rw [mem_preimage]; rw [Set.mem_one] at hx
  rw [mem_ofPred]; rw [← hsn]
  ext y
  simp [hx]

中文:
定理 preErgodic_of_dense_iUnion_preimage_one
  证明: by
  refine ⟨fun s hsm hs =>
    aeconst_of_dense_setOfPred_preimage_smul_eq (M := G) hsm.nullMeasurableSet ?_⟩
refine hf.mono iUnion_subset fun n x hx => ?_
  have hsn : f^[n] ⁻¹' s = s := by
    rw [preimage_iterate_eq]; rw [iterate_fixed hs]
  rw [mem_preimage]; rw [Set.mem_one] at hx
  rw [mem_ofPred]; rw [← hsn]
  ext y
  simp [hx]

Depends on / 依赖: Set.mem_one, aeconst_of_dense_setOfPred_preimage_smul_eq, hf.mono, hsm.nullMeasurableSet, iUnion_subset, iterate_fixed, mem_ofPred, mem_one, mem_preimage, nullMeasurableSet, preimage_iterate_eq
-/
theorem preErgodic_of_dense_iUnion_preimage_one
    {μ : Measure G} [IsFiniteMeasure μ] [μ.InnerRegular] [μ.IsMulLeftInvariant]
    (f : G ->* G) (hf : Dense (⋃ n, f^[n] ⁻¹' 1)) : PreErgodic f μ := by
  refine ⟨fun s hsm hs =>
    aeconst_of_dense_setOfPred_preimage_smul_eq (M := G) hsm.nullMeasurableSet ?_⟩
refine hf.mono iUnion_subset fun n x hx => ?_
  have hsn : f^[n] ⁻¹' s = s := by
    rw [preimage_iterate_eq]; rw [iterate_fixed hs]
  rw [mem_preimage]; rw [Set.mem_one] at hx
  rw [mem_ofPred]; rw [← hsn]
  ext y
  simp [hx]

/-- Let `f : G →* G` be a continuous surjective group endomorphism
of a compact topological group with second countable topology.
If the preimages of `1` under the iterations of `f` are dense,
then `f` is ergodic with respect to any finite inner regular left invariant measure. -/
@[to_additive /-- Let `f : G →+ G` be a continuous surjective additive group endomorphism
of a compact topological additive group with second countable topology.
If the preimages of `0` under the iterations of `f` are dense,
then `f` is ergodic with respect to any finite inner regular left invariant measure. -/]
/--
theorem `ergodic_of_dense_iUnion_preimage_one` / 定理 `ergodic_of_dense_iUnion_preimage_one`

English:
theorem ergodic_of_dense_iUnion_preimage_one
  statement: [CompactSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  proof: ⟨f.measurePreserving hcont hsurj rfl, f.preErgodic_of_dense_iUnion_preimage_one hf⟩

中文:
定理 ergodic_of_dense_iUnion_preimage_one
  结论: [紧空间 G] {μ : 测度 G} [μ.是Haar测度]
  证明: ⟨f.measurePreserving hcont hsurj rfl, f.preErgodic_of_dense_iUnion_preimage_one hf⟩

Depends on / 依赖: f.measurePreserving, f.preErgodic_of_dense_iUnion_preimage_one, measurePreserving, preErgodic_of_dense_iUnion_preimage_one
-/
theorem ergodic_of_dense_iUnion_preimage_one [CompactSpace G] {μ : Measure G} [μ.IsHaarMeasure]
    (f : G ->* G) (hf : Dense (⋃ n, f^[n] ⁻¹' 1)) (hcont : Continuous f) (hsurj : Surjective f) :
    Ergodic f μ :=
  ⟨f.measurePreserving hcont hsurj rfl, f.preErgodic_of_dense_iUnion_preimage_one hf⟩

end MonoidHom
