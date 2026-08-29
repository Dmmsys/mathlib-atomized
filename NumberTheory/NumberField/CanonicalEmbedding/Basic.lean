/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.NumberTheory.NumberField.FractionalIdeal
public import Mathlib.NumberTheory.NumberField.Units.Basic

/-!
# Canonical embedding of a number field

The canonical embedding of a number field `K` of degree `n` is the ring homomorphism
`K →+* ℂ^n` that sends `x ∈ K` to `(φ_₁(x),...,φ_n(x))` where the `φ_i`'s are the complex
embeddings of `K`. Note that we do not choose an ordering of the embeddings, but instead map `K`
into the type `(K →+* ℂ) → ℂ` of `ℂ`-vectors indexed by the complex embeddings.

## Main definitions and results

* `NumberField.canonicalEmbedding`: the ring homomorphism `K →+* ((K →+* ℂ) → ℂ)` defined by
  sending `x : K` to the vector `(φ x)` indexed by `φ : K →+* ℂ`.

* `NumberField.canonicalEmbedding.integerLattice.inter_ball_finite`: the intersection of the
  image of the ring of integers by the canonical embedding and any ball centered at `0` of finite
  radius is finite.

* `NumberField.mixedEmbedding`: the ring homomorphism from `K` to the mixed space
  `K →+* ({ w // IsReal w } → ℝ) × ({ w // IsComplex w } → ℂ)` that sends `x ∈ K` to `(φ_w x)_w`
  where `φ_w` is the embedding associated to the infinite place `w`. In particular, if `w` is real
  then `φ_w : K →+* ℝ` and, if `w` is complex, `φ_w` is an arbitrary choice between the two complex
  embeddings defining the place `w`.

## Tags

number field, infinite places
-/

@[expose] public section

open Module

variable (K : Type*) [Field K]

namespace NumberField.canonicalEmbedding

/--
Definition of `_root_.NumberField.canonicalEmbedding` / `_root_.NumberField.canonicalEmbedding` 的定义

English:
definition _root_.NumberField.canonicalEmbedding
  signature: : K ->+* ((K ->+* Complex) -> Complex)
  body: RingHom.pi fun φ => φ

中文:
定义 _root_.数域.canonicalEmbedding
  签名: : K ->+* ((K ->+* 复形) -> 复形)
  定义体: RingHom.pi fun φ => φ

Depends on / 依赖: RingHom, RingHom.pi
-/
def _root_.NumberField.canonicalEmbedding : K ->+* ((K ->+* Complex) -> Complex) := RingHom.pi fun φ => φ

/--
theorem `_root_.NumberField.canonicalEmbedding_injective` / 定理 `_root_.NumberField.canonicalEmbedding_injective`

English:
theorem _root_.NumberField.canonicalEmbedding_injective
  given: [NumberField K]
  proof: RingHom.injective _

中文:
定理 _root_.数域.canonicalEmbedding_injective
  条件: [数域 K]
  证明: RingHom.injective _

Depends on / 依赖: RingHom, RingHom.injective, injective
-/
theorem _root_.NumberField.canonicalEmbedding_injective [NumberField K] :
    Function.Injective (NumberField.canonicalEmbedding K) := RingHom.injective _

variable {K}

@[simp]
/--
theorem `apply_at` / 定理 `apply_at`

English:
theorem apply_at
  given: (φ : K ->+* Complex) (x : K)
  statement: (NumberField.canonicalEmbedding K x) φ = φ x
  proof: rfl

中文:
定理 apply_at
  条件: (φ : K ->+* 复形) (x : K)
  结论: (数域.canonicalEmbedding K x) φ = φ x
  证明: rfl
-/
theorem apply_at (φ : K ->+* Complex) (x : K) : (NumberField.canonicalEmbedding K x) φ = φ x := rfl

open scoped ComplexConjugate

/--
theorem `conj_apply` / 定理 `conj_apply`

English:
theorem conj_apply
  statement: {x : ((K ->+* Complex) -> Complex)} (φ : K ->+* Complex)
  proof: by
  refine Submodule.span_induction ?_ ?_ (fun _ _ _ _ hx hy => ?_) (fun a _ _ hx => ?_) hx
  · rintro _ ⟨x, rfl⟩
    rw [apply_at]; rw [apply_at]; rw [ComplexEmbedding.conjugate_coe_eq]
  · rw [Pi.zero_apply, Pi.zero_apply, map_zero]
  · rw [Pi.add_apply, Pi.add_apply, map_add, hx, hy]
  · rw [Pi.

中文:
定理 conj_apply
  结论: {x : ((K ->+* 复形) -> 复形)} (φ : K ->+* 复形)
  证明: by
  refine Submodule.span_induction ?_ ?_ (fun _ _ _ _ hx hy => ?_) (fun a _ _ hx => ?_) hx
  · rintro _ ⟨x, rfl⟩
    rw [apply_at]; rw [apply_at]; rw [ComplexEmbedding.conjugate_coe_eq]
  · rw [Pi.zero_apply, Pi.zero_apply, map_zero]
  · rw [Pi.add_apply, Pi.add_apply, map_add, hx, hy]
  · rw [Pi.

Depends on / 依赖: Complex.conj_ofReal, Complex.real_smul, ComplexEmbedding, ComplexEmbedding.conjugate_coe_eq, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, Submodule, Submodule.span_induction, add_apply, apply_at, conj_ofReal, conjugate_coe_eq, map_add, map_mul, map_zero, real_smul, smul_apply, span_induction, zero_apply
-/
theorem conj_apply {x : ((K ->+* Complex) -> Complex)} (φ : K ->+* Complex)
    (hx : x in Submodule.span Real (Set.range (canonicalEmbedding K))) :
    conj (x φ) = x (ComplexEmbedding.conjugate φ) := by
  refine Submodule.span_induction ?_ ?_ (fun _ _ _ _ hx hy => ?_) (fun a _ _ hx => ?_) hx
  · rintro _ ⟨x, rfl⟩
    rw [apply_at]; rw [apply_at]; rw [ComplexEmbedding.conjugate_coe_eq]
  · rw [Pi.zero_apply, Pi.zero_apply, map_zero]
  · rw [Pi.add_apply, Pi.add_apply, map_add, hx, hy]
  · rw [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    exact congrArg ((a : Complex) * ·) hx

/--
theorem `nnnorm_eq` / 定理 `nnnorm_eq`

English:
theorem nnnorm_eq
  given: [NumberField K] (x : K)
  proof: by
  simp_rw [Pi.nnnorm_def, apply_at]

中文:
定理 nnnorm_eq
  条件: [数域 K] (x : K)
  证明: by
  simp_rw [Pi.nnnorm_def, apply_at]

Depends on / 依赖: Pi.nnnorm_def, apply_at, nnnorm_def, simp_rw
-/
theorem nnnorm_eq [NumberField K] (x : K) :
    ‖canonicalEmbedding K x‖₊ = Finset.univ.sup (fun φ : K ->+* Complex => ‖φ x‖₊) := by
  simp_rw [Pi.nnnorm_def, apply_at]

/--
theorem `norm_le_iff` / 定理 `norm_le_iff`

English:
theorem norm_le_iff
  given: [NumberField K] (x : K) (r : Real)
  proof: by
  obtain hr | hr := lt_or_ge r 0
  · obtain ⟨φ⟩ := (inferInstance : Nonempty (K ->+* Complex))
    refine iff_of_false ?_ ?_
    · exact (hr.trans_le (norm_nonneg _)).not_ge
    · exact fun h => hr.not_ge (le_trans (norm_nonneg _) (h φ))
  · lift r to NNReal using hr
    simp_rw [← coe_nnnorm, nn

中文:
定理 norm_le_iff
  条件: [数域 K] (x : K) (r : 实数)
  证明: by
  obtain hr | hr := lt_or_ge r 0
  · obtain ⟨φ⟩ := (inferInstance : Nonempty (K ->+* Complex))
    refine iff_of_false ?_ ?_
    · exact (hr.trans_le (norm_nonneg _)).not_ge
    · exact fun h => hr.not_ge (le_trans (norm_nonneg _) (h φ))
  · lift r to NNReal using hr
    simp_rw [← coe_nnnorm, nn

Depends on / 依赖: Finset, Finset.mem_univ, Finset.sup_le_iff, NNReal, NNReal.coe_le_coe, Nonempty, coe_le_coe, coe_nnnorm, exists_le_maximal, forall_true_left, hr.not_ge, hr.trans_le, iff_of_false, le_trans, lt_or_ge, mem_univ, nnnorm_eq, norm_nonneg, not_ge, simp_rw
-/
theorem norm_le_iff [NumberField K] (x : K) (r : Real) :
    ‖canonicalEmbedding K x‖ <= r ↔ forall φ : K ->+* Complex, ‖φ x‖ <= r := by
  obtain hr | hr := lt_or_ge r 0
  · obtain ⟨φ⟩ := (inferInstance : Nonempty (K ->+* Complex))
    refine iff_of_false ?_ ?_
    · exact (hr.trans_le (norm_nonneg _)).not_ge
    · exact fun h => hr.not_ge (le_trans (norm_nonneg _) (h φ))
  · lift r to NNReal using hr
    simp_rw [← coe_nnnorm, nnnorm_eq, NNReal.coe_le_coe, Finset.sup_le_iff, Finset.mem_univ,
      forall_true_left]

variable (K)

/--
Definition of `integerLattice` / `integerLattice` 的定义

English:
definition integerLattice
  signature: : Subring ((K ->+* Complex) -> Complex)
  body: (RingHom.range (algebraMap (𝓞 K) K)).map (canonicalEmbedding K)

中文:
定义 integerLattice
  签名: : 子环 ((K ->+* 复形) -> 复形)
  定义体: (RingHom.range (algebraMap (𝓞 K) K)).map (canonicalEmbedding K)

Depends on / 依赖: RingHom, RingHom.range, algebraMap, canonicalEmbedding
-/
def integerLattice : Subring ((K ->+* Complex) -> Complex) :=
  (RingHom.range (algebraMap (𝓞 K) K)).map (canonicalEmbedding K)

/--
theorem `integerLattice.inter_ball_finite` / 定理 `integerLattice.inter_ball_finite`

English:
theorem integerLattice.inter_ball_finite
  given: [NumberField K] (r : Real)
  proof: by
  obtain hr | _ := lt_or_ge r 0
  · simp [Metric.closedBall_eq_empty.2 hr]
  · have heq : forall x, canonicalEmbedding K x in Metric.closedBall 0 r ↔
        forall φ : K ->+* Complex, ‖φ x‖ <= r := by
      intro x; rw [← norm_le_iff, mem_closedBall_zero_iff]
    convert! (Embeddings.finite_of_n

中文:
定理 integerLattice.inter_ball_finite
  条件: [数域 K] (r : 实数)
  证明: by
  obtain hr | _ := lt_or_ge r 0
  · simp [Metric.closedBall_eq_empty.2 hr]
  · have heq : forall x, canonicalEmbedding K x in Metric.closedBall 0 r ↔
        forall φ : K ->+* Complex, ‖φ x‖ <= r := by
      intro x; rw [← norm_le_iff, mem_closedBall_zero_iff]
    convert! (Embeddings.finite_of_n

Depends on / 依赖: Embeddings, Embeddings.finite_of_norm_le, Metric, Metric.closedBall, Metric.closedBall_eq_empty, SetLike, SetLike.coe_mem, canonicalEmbedding, closedBall, closedBall_eq_empty, coe_mem, convert, finite_of_norm_le, lt_or_ge, mem_closedBall_zero_iff, norm_le_iff
-/
theorem integerLattice.inter_ball_finite [NumberField K] (r : Real) :
    ((integerLattice K : Set ((K ->+* Complex) -> Complex)) inter Metric.closedBall 0 r).Finite := by
  obtain hr | _ := lt_or_ge r 0
  · simp [Metric.closedBall_eq_empty.2 hr]
  · have heq : forall x, canonicalEmbedding K x in Metric.closedBall 0 r ↔
        forall φ : K ->+* Complex, ‖φ x‖ <= r := by
      intro x; rw [← norm_le_iff, mem_closedBall_zero_iff]
    convert! (Embeddings.finite_of_norm_le K Complex r).image (canonicalEmbedding K)
    ext; constructor
    · rintro ⟨⟨_, ⟨x, rfl⟩, rfl⟩, hx⟩
      exact ⟨x, ⟨SetLike.coe_mem x, fun φ => (heq _).mp hx φ⟩, rfl⟩
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      exact ⟨⟨x, ⟨⟨x, hx1⟩, rfl⟩, rfl⟩, (heq x).mpr hx2⟩

/--
Definition of `latticeBasis` / `latticeBasis` 的定义

English:
definition latticeBasis
  signature: [NumberField K]
  body: by
  classical
  -- Let `B` be the canonical basis of `(K →+* ℂ) → ℂ`. We prove that the determinant of
  -- the image by `canonicalEmbedding` of the integral basis of `K` is nonzero. This
  -- will imply the result.
    let B := Pi.basisFun Complex (K ->+* Complex)
    let e : (K ->+* Complex) ≃ Fr

中文:
定义 latticeBasis
  签名: [数域 K]
  定义体: by
  classical
  -- Let `B` be the canonical basis of `(K →+* ℂ) → ℂ`. We prove that the determinant of
  -- the image by `canonicalEmbedding` of the integral basis of `K` is nonzero. This
  -- will imply the result.
    let B := Pi.basisFun Complex (K ->+* Complex)
    let e : (K ->+* Complex) ≃ Fr

Depends on / 依赖: classical
-/
noncomputable def latticeBasis [NumberField K] :
    Basis (Free.ChooseBasisIndex Int (𝓞 K)) Complex ((K ->+* Complex) -> Complex) := by
  classical
  -- Let `B` be the canonical basis of `(K →+* ℂ) → ℂ`. We prove that the determinant of
  -- the image by `canonicalEmbedding` of the integral basis of `K` is nonzero. This
  -- will imply the result.
    let B := Pi.basisFun Complex (K ->+* Complex)
    let e : (K ->+* Complex) ≃ Free.ChooseBasisIndex Int (𝓞 K) :=
      Fintype.equivOfCardEq ((Embeddings.card K Complex).trans (finrank_eq_card_basis (integralBasis K)))
    let M := B.toMatrix (fun i => canonicalEmbedding K (integralBasis K (e i)))
    suffices M.det != 0 by
      rw [← isUnit_iff_ne_zero]; rw [← Basis.det_apply]; rw [← Basis.is_basis_iff_det] at this
      exact (basisOfPiSpaceOfLinearIndependent this.1).reindex e
  -- In order to prove that the determinant is nonzero, we show that it is equal to the
  -- square of the discriminant of the integral basis and thus it is not zero
    let N := Algebra.embeddingsMatrixReindex Rat Complex (fun i => integralBasis K (e i))
      (RingHom.equivRatAlgHom K Complex)
    rw [show M = N.transpose by { ext : 2; rfl }]
    rw [Matrix.det_transpose]; rw [← pow_ne_zero_iff two_ne_zero]
    convert!
      (map_ne_zero_iff _ (algebraMap Rat Complex).injective).mpr
        (Algebra.discr_not_zero_of_basis Rat (integralBasis K))
    rw [← Algebra.discr_reindex Rat (integralBasis K) e.symm]
    exact (Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two Rat Complex
      (fun i => integralBasis K (e i)) (RingHom.equivRatAlgHom K Complex)).symm

@[simp]
/--
theorem `latticeBasis_apply` / 定理 `latticeBasis_apply`

English:
theorem latticeBasis_apply
  given: [NumberField K] (i : Free.ChooseBasisIndex Int (𝓞 K))
  proof: by
  simp [latticeBasis, integralBasis_apply, coe_basisOfPiSpaceOfLinearIndependent,
    Function.comp_apply, Equiv.apply_symm_apply]

中文:
定理 latticeBasis_apply
  条件: [数域 K] (i : 自由.ChooseBasisIndex 整数 (𝓞 K))
  证明: by
  simp [latticeBasis, integralBasis_apply, coe_basisOfPiSpaceOfLinearIndependent,
    Function.comp_apply, Equiv.apply_symm_apply]

Depends on / 依赖: Equiv.apply_symm_apply, Function, Function.comp_apply, apply_symm_apply, coe_basisOfPiSpaceOfLinearIndependent, comp_apply, integralBasis_apply, latticeBasis
-/
theorem latticeBasis_apply [NumberField K] (i : Free.ChooseBasisIndex Int (𝓞 K)) :
    latticeBasis K i = (canonicalEmbedding K) (integralBasis K i) := by
  simp [latticeBasis, integralBasis_apply, coe_basisOfPiSpaceOfLinearIndependent,
    Function.comp_apply, Equiv.apply_symm_apply]

/--
theorem `mem_span_latticeBasis` / 定理 `mem_span_latticeBasis`

English:
theorem mem_span_latticeBasis
  given: [NumberField K] {x : (K ->+* Complex) -> Complex}
  proof: by
  rw [show Set.range (latticeBasis K) =
      (canonicalEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (integralBasis K)) by
    rw [← Set.range_comp]; exact congrArg Set.range (funext (fun i => latticeBasis_apply K i))]
  rw [← Submodule.map_span]; rw [← SetLike.mem_coe]; rw [Submodule.map_c

中文:
定理 mem_span_latticeBasis
  条件: [数域 K] {x : (K ->+* 复形) -> 复形}
  证明: by
  rw [show Set.range (latticeBasis K) =
      (canonicalEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (integralBasis K)) by
    rw [← Set.range_comp]; exact congrArg Set.range (funext (fun i => latticeBasis_apply K i))]
  rw [← Submodule.map_span]; rw [← SetLike.mem_coe]; rw [Submodule.map_c

Depends on / 依赖: RingHom, RingHom.map_range, Set.mem_image, Set.range, Set.range_comp, SetLike, SetLike.mem_coe, Submodule, Submodule.map_coe, Submodule.map_span, Subring, Subring.mem_map, canonicalEmbedding, integralBasis, latticeBasis, latticeBasis_apply, map_coe, map_range, map_span, mem_coe
-/
theorem mem_span_latticeBasis [NumberField K] {x : (K ->+* Complex) -> Complex} :
    x in Submodule.span Int (Set.range (latticeBasis K)) ↔
      x in ((canonicalEmbedding K).comp (algebraMap (𝓞 K) K)).range := by
  rw [show Set.range (latticeBasis K) =
      (canonicalEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (integralBasis K)) by
    rw [← Set.range_comp]; exact congrArg Set.range (funext (fun i => latticeBasis_apply K i))]
  rw [← Submodule.map_span]; rw [← SetLike.mem_coe]; rw [Submodule.map_coe]
  rw [← RingHom.map_range]; rw [Subring.mem_map]; rw [Set.mem_image]
  simp only [SetLike.mem_coe, mem_span_integralBasis K]
  rfl

/--
theorem `mem_rat_span_latticeBasis` / 定理 `mem_rat_span_latticeBasis`

English:
theorem mem_rat_span_latticeBasis
  given: [NumberField K] (x : K)
  proof: by
  rw [← Basis.sum_repr (integralBasis K) x]; rw [map_sum]
  simp_rw [map_rat_smul]
  refine Submodule.sum_smul_mem _ _ (fun i _ => Submodule.subset_span ?_)
  rw [← latticeBasis_apply]
  exact Set.mem_range_self i

中文:
定理 mem_rat_span_latticeBasis
  条件: [数域 K] (x : K)
  证明: by
  rw [← Basis.sum_repr (integralBasis K) x]; rw [map_sum]
  simp_rw [map_rat_smul]
  refine Submodule.sum_smul_mem _ _ (fun i _ => Submodule.subset_span ?_)
  rw [← latticeBasis_apply]
  exact Set.mem_range_self i

Depends on / 依赖: Basis.sum_repr, Set.mem_range_self, Submodule, Submodule.subset_span, Submodule.sum_smul_mem, integralBasis, latticeBasis_apply, map_rat_smul, map_sum, mem_range_self, simp_rw, subset_span, sum_repr, sum_smul_mem
-/
theorem mem_rat_span_latticeBasis [NumberField K] (x : K) :
    canonicalEmbedding K x in Submodule.span Rat (Set.range (latticeBasis K)) := by
  rw [← Basis.sum_repr (integralBasis K) x]; rw [map_sum]
  simp_rw [map_rat_smul]
  refine Submodule.sum_smul_mem _ _ (fun i _ => Submodule.subset_span ?_)
  rw [← latticeBasis_apply]
  exact Set.mem_range_self i

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `integralBasis_repr_apply` / 定理 `integralBasis_repr_apply`

English:
theorem integralBasis_repr_apply
  given: [NumberField K] (x : K) (i : Free.ChooseBasisIndex Int (𝓞 K))
  proof: by
  rw [← Basis.restrictScalars_repr_apply Rat _ ⟨_]; rw [mem_rat_span_latticeBasis K x⟩]; rw [eq_ratCast]; rw [Rat.cast_inj]
  let f := (canonicalEmbedding K).toRatAlgHom.toLinearMap.codRestrict _
    (fun x => mem_rat_span_latticeBasis K x)
  suffices ((latticeBasis K).restrictScalars Rat).repr.t

中文:
定理 integralBasis_repr_apply
  条件: [数域 K] (x : K) (i : 自由.ChooseBasisIndex 整数 (𝓞 K))
  证明: by
  rw [← Basis.restrictScalars_repr_apply Rat _ ⟨_]; rw [mem_rat_span_latticeBasis K x⟩]; rw [eq_ratCast]; rw [Rat.cast_inj]
  let f := (canonicalEmbedding K).toRatAlgHom.toLinearMap.codRestrict _
    (fun x => mem_rat_span_latticeBasis K x)
  suffices ((latticeBasis K).restrictScalars Rat).repr.t

Depends on / 依赖: Basis.ext, Basis.restrictScalars_repr_apply, DFunLike, DFunLike.congr_fun, LinearMap, LinearMap.congr_fun, Rat.cast_inj, canonicalEmbedding, cast_inj, codRestrict, congr_fun, eq_ratCast, integralBasis, latticeBasis, mem_rat_span_latticeBasis, repr.toLinearMap, restrictScalars, restrictScalars_repr_apply, toLinearMap, toRatAlgHom
-/
theorem integralBasis_repr_apply [NumberField K] (x : K) (i : Free.ChooseBasisIndex Int (𝓞 K)) :
    (latticeBasis K).repr (canonicalEmbedding K x) i = (integralBasis K).repr x i := by
  rw [← Basis.restrictScalars_repr_apply Rat _ ⟨_]; rw [mem_rat_span_latticeBasis K x⟩]; rw [eq_ratCast]; rw [Rat.cast_inj]
  let f := (canonicalEmbedding K).toRatAlgHom.toLinearMap.codRestrict _
    (fun x => mem_rat_span_latticeBasis K x)
  suffices ((latticeBasis K).restrictScalars Rat).repr.toLinearMap ∘ₗ f =
    (integralBasis K).repr.toLinearMap from DFunLike.congr_fun (LinearMap.congr_fun this x) i
  refine Basis.ext (integralBasis K) (fun i => ?_)
  have : f (integralBasis K i) = ((latticeBasis K).restrictScalars Rat) i := by
    apply Subtype.val_injective
    rw [LinearMap.codRestrict_apply]; rw [AlgHom.toLinearMap_apply]; rw [Basis.restrictScalars_apply]; rw [latticeBasis_apply]
    rfl
  simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this, Basis.repr_self]

end NumberField.canonicalEmbedding

namespace NumberField.mixedEmbedding

open NumberField.InfinitePlace Module Finset

/--
Definition of `mixedSpace` / `mixedSpace` 的定义

English:
abbreviation mixedSpace
  body: ({w : InfinitePlace K // IsReal w} -> Real) × ({w : InfinitePlace K // IsComplex w} -> Complex)

中文:
缩写 mixedSpace
  定义体: ({w : InfinitePlace K // IsReal w} -> Real) × ({w : InfinitePlace K // IsComplex w} -> Complex)

Depends on / 依赖: InfinitePlace, IsComplex, IsReal
-/
abbrev mixedSpace :=
  ({w : InfinitePlace K // IsReal w} -> Real) × ({w : InfinitePlace K // IsComplex w} -> Complex)

/--
Definition of `_root_.NumberField.mixedEmbedding` / `_root_.NumberField.mixedEmbedding` 的定义

English:
definition _root_.NumberField.mixedEmbedding
  signature: : K ->+* (mixedSpace K)
  body: RingHom.prod (RingHom.pi fun w => embedding_of_isReal w.prop)
    (RingHom.pi fun w => w.val.embedding)

@[simp]

中文:
定义 _root_.数域.mixedEmbedding
  签名: : K ->+* (mixedSpace K)
  定义体: RingHom.prod (RingHom.pi fun w => embedding_of_isReal w.prop)
    (RingHom.pi fun w => w.val.embedding)

@[simp]

Depends on / 依赖: RingHom, RingHom.pi, RingHom.prod, embedding, embedding_of_isReal, w.prop, w.val.embedding
-/
noncomputable def _root_.NumberField.mixedEmbedding : K ->+* (mixedSpace K) :=
  RingHom.prod (RingHom.pi fun w => embedding_of_isReal w.prop)
    (RingHom.pi fun w => w.val.embedding)

@[simp]
/--
theorem `mixedEmbedding_apply_isReal` / 定理 `mixedEmbedding_apply_isReal`

English:
theorem mixedEmbedding_apply_isReal
  given: (x : K) (w : {w // IsReal w})
  proof: by
  simp_rw [mixedEmbedding, RingHom.prod_apply, RingHom.pi_apply]

@[simp]

中文:
定理 mixedEmbedding_apply_is实数
  条件: (x : K) (w : {w // Is实数 w})
  证明: by
  simp_rw [mixedEmbedding, RingHom.prod_apply, RingHom.pi_apply]

@[simp]

Depends on / 依赖: RingHom, RingHom.pi_apply, RingHom.prod_apply, mixedEmbedding, pi_apply, prod_apply, simp_rw
-/
theorem mixedEmbedding_apply_isReal (x : K) (w : {w // IsReal w}) :
    (mixedEmbedding K x).1 w = embedding_of_isReal w.prop x := by
  simp_rw [mixedEmbedding, RingHom.prod_apply, RingHom.pi_apply]

@[simp]
/--
theorem `mixedEmbedding_apply_isComplex` / 定理 `mixedEmbedding_apply_isComplex`

English:
theorem mixedEmbedding_apply_isComplex
  given: (x : K) (w : {w // IsComplex w})
  proof: by
  simp_rw [mixedEmbedding, RingHom.prod_apply, RingHom.pi_apply]

中文:
定理 mixedEmbedding_apply_isComplex
  条件: (x : K) (w : {w // 是复形 w})
  证明: by
  simp_rw [mixedEmbedding, RingHom.prod_apply, RingHom.pi_apply]

Depends on / 依赖: RingHom, RingHom.pi_apply, RingHom.prod_apply, mixedEmbedding, pi_apply, prod_apply, simp_rw
-/
theorem mixedEmbedding_apply_isComplex (x : K) (w : {w // IsComplex w}) :
    (mixedEmbedding K x).2 w = w.val.embedding x := by
  simp_rw [mixedEmbedding, RingHom.prod_apply, RingHom.pi_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NumberField
  signature: K] : Nontrivial (mixedSpace K)
  body: by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  obtain hw | hw := w.isReal_or_isComplex
  · have : Nonempty {w : InfinitePlace K // IsReal w} := ⟨⟨w, hw⟩⟩
    exact nontrivial_prod_left
  · have : Nonempty {w : InfinitePlace K // IsComplex w} := ⟨⟨w, hw⟩⟩
    exact nontrivial_prod_

中文:
实例 [数域
  签名: K] : 非平凡 (mixedSpace K)
  定义体: by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  obtain hw | hw := w.isReal_or_isComplex
  · have : Nonempty {w : InfinitePlace K // IsReal w} := ⟨⟨w, hw⟩⟩
    exact nontrivial_prod_left
  · have : Nonempty {w : InfinitePlace K // IsComplex w} := ⟨⟨w, hw⟩⟩
    exact nontrivial_prod_

Depends on / 依赖: InfinitePlace, IsComplex, IsReal, Nonempty, isReal_or_isComplex, nontrivial_prod_left, nontrivial_prod_right, w.isReal_or_isComplex
-/
instance [NumberField K] : Nontrivial (mixedSpace K) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  obtain hw | hw := w.isReal_or_isComplex
  · have : Nonempty {w : InfinitePlace K // IsReal w} := ⟨⟨w, hw⟩⟩
    exact nontrivial_prod_left
  · have : Nonempty {w : InfinitePlace K // IsComplex w} := ⟨⟨w, hw⟩⟩
    exact nontrivial_prod_right

/--
theorem `finrank` / 定理 `finrank`

English:
theorem finrank
  given: [NumberField K]
  statement: finrank Real (mixedSpace K) = finrank Rat K
  proof: by
  classical
  rw [finrank_prod]; rw [finrank_pi]; rw [finrank_pi_fintype]; rw [Complex.finrank_real_complex]; rw [sum_const]; rw [card_univ]; rw [← nrRealPlaces]; rw [← nrComplexPlaces]; rw [← card_real_embeddings]; rw [smul_eq_mul]; rw [mul_comm]; rw [← card_complex_embeddings]; rw [← NumberFiel

中文:
定理 finrank
  条件: [数域 K]
  结论: finrank 实数 (mixedSpace K) = finrank 有理数 K
  证明: by
  classical
  rw [finrank_prod]; rw [finrank_pi]; rw [finrank_pi_fintype]; rw [Complex.finrank_real_complex]; rw [sum_const]; rw [card_univ]; rw [← nrRealPlaces]; rw [← nrComplexPlaces]; rw [← card_real_embeddings]; rw [smul_eq_mul]; rw [mul_comm]; rw [← card_complex_embeddings]; rw [← NumberFiel
-/
protected theorem finrank [NumberField K] : finrank Real (mixedSpace K) = finrank Rat K := by
  classical
  rw [finrank_prod]; rw [finrank_pi]; rw [finrank_pi_fintype]; rw [Complex.finrank_real_complex]; rw [sum_const]; rw [card_univ]; rw [← nrRealPlaces]; rw [← nrComplexPlaces]; rw [← card_real_embeddings]; rw [smul_eq_mul]; rw [mul_comm]; rw [← card_complex_embeddings]; rw [← NumberField.Embeddings.card K Complex]; rw [Fintype.card_subtype_compl]; rw [Nat.add_sub_of_le (Fintype.card_subtype_le _)]

/--
theorem `_root_.NumberField.mixedEmbedding_injective` / 定理 `_root_.NumberField.mixedEmbedding_injective`

English:
theorem _root_.NumberField.mixedEmbedding_injective
  given: [NumberField K]
  proof: by
  exact RingHom.injective _

中文:
定理 _root_.数域.mixedEmbedding_injective
  条件: [数域 K]
  证明: by
  exact RingHom.injective _

Depends on / 依赖: RingHom, RingHom.injective, injective
-/
theorem _root_.NumberField.mixedEmbedding_injective [NumberField K] :
    Function.Injective (NumberField.mixedEmbedding K) := by
  exact RingHom.injective _

section Measure

open MeasureTheory.Measure MeasureTheory

variable [NumberField K]

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddHaarMeasure (volume : Measure (mixedSpace K))
  body: prod.instIsAddHaarMeasure volume volume

中文:
实例 :
  签名: 是加法Haar测度 (volume : 测度 (mixedSpace K))
  定义体: prod.instIsAddHaarMeasure volume volume

Depends on / 依赖: instIsAddHaarMeasure, prod.instIsAddHaarMeasure, volume
-/
instance : IsAddHaarMeasure (volume : Measure (mixedSpace K)) :=
  prod.instIsAddHaarMeasure volume volume

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NullSingletonClass (volume : Measure (mixedSpace K))
  body: by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  by_cases hw : IsReal w
  · have : NullSingletonClass (volume : Measure ({w : InfinitePlace K // IsReal w} -> Real)) :=
      pi_nullSingletonClass ⟨w, hw⟩
    exact prod.instNullSingletonClass_fst
  · have : NullSingletonClass (volume

中文:
实例 :
  签名: NullSingleton类 (volume : 测度 (mixedSpace K))
  定义体: by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  by_cases hw : IsReal w
  · have : NullSingletonClass (volume : Measure ({w : InfinitePlace K // IsReal w} -> Real)) :=
      pi_nullSingletonClass ⟨w, hw⟩
    exact prod.instNullSingletonClass_fst
  · have : NullSingletonClass (volume

Depends on / 依赖: InfinitePlace, IsComplex, IsReal, Measure, Nonempty, NullSingletonClass, instNullSingletonClass_fst, instNullSingletonClass_snd, not_isReal_iff_isComplex, not_isReal_iff_isComplex.mp, pi_nullSingletonClass, prod.instNullSingletonClass_fst, prod.instNullSingletonClass_snd, volume
-/
instance : NullSingletonClass (volume : Measure (mixedSpace K)) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  by_cases hw : IsReal w
  · have : NullSingletonClass (volume : Measure ({w : InfinitePlace K // IsReal w} -> Real)) :=
      pi_nullSingletonClass ⟨w, hw⟩
    exact prod.instNullSingletonClass_fst
  · have : NullSingletonClass (volume : Measure ({w : InfinitePlace K // IsComplex w} -> Complex)) :=
      pi_nullSingletonClass ⟨w, not_isReal_iff_isComplex.mp hw⟩
    exact prod.instNullSingletonClass_snd

set_option backward.isDefEq.respectTransparency.types false in
variable {K} in
open scoped Classical in
/--
theorem `volume_eq_zero` / 定理 `volume_eq_zero`

English:
theorem volume_eq_zero
  given: (w : {w // IsReal w})
  proof: by
  let A : AffineSubspace Real (mixedSpace K) :=
    Submodule.toAffineSubspace (Submodule.mk ⟨⟨{x | x.1 w = 0}, by simp_all⟩, rfl⟩ (by simp_all))
  convert! Measure.addHaar_affineSubspace volume A fun h => ?_
  simpa [A] using (h ▸ Set.mem_univ _ : 1 in A)

中文:
定理 volume_eq_zero
  条件: (w : {w // Is实数 w})
  证明: by
  let A : AffineSubspace Real (mixedSpace K) :=
    Submodule.toAffineSubspace (Submodule.mk ⟨⟨{x | x.1 w = 0}, by simp_all⟩, rfl⟩ (by simp_all))
  convert! Measure.addHaar_affineSubspace volume A fun h => ?_
  simpa [A] using (h ▸ Set.mem_univ _ : 1 in A)

Depends on / 依赖: AffineSubspace, Measure, Measure.addHaar_affineSubspace, Set.mem_univ, Submodule, Submodule.mk, Submodule.toAffineSubspace, addHaar_affineSubspace, convert, mem_univ, mixedSpace, toAffineSubspace, volume
-/
theorem volume_eq_zero (w : {w // IsReal w}) :
    volume ({x : mixedSpace K | x.1 w = 0}) = 0 := by
  let A : AffineSubspace Real (mixedSpace K) :=
    Submodule.toAffineSubspace (Submodule.mk ⟨⟨{x | x.1 w = 0}, by simp_all⟩, rfl⟩ (by simp_all))
  convert! Measure.addHaar_affineSubspace volume A fun h => ?_
  simpa [A] using (h ▸ Set.mem_univ _ : 1 in A)

end Measure

section commMap

/--
Definition of `commMap` / `commMap` 的定义

English:
definition commMap
  signature: : ((K ->+* Complex) -> Complex) ->ₗ[Real] (mixedSpace K) where
  body: fun x => ⟨fun w => (x w.val.embedding).re, fun w => x w.val.embedding⟩
  map_add' := by
    simp only [Pi.add_apply, Complex.add_re, Prod.mk_add_mk, Prod.mk.injEq]
    exact fun _ _ => ⟨rfl, rfl⟩
  map_smul' := by
    simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
  

中文:
定义 commMap
  签名: : ((K ->+* 复形) -> 复形) ->ₗ[实数] (mixedSpace K) where
  定义体: fun x => ⟨fun w => (x w.val.embedding).re, fun w => x w.val.embedding⟩
  map_add' := by
    simp only [Pi.add_apply, Complex.add_re, Prod.mk_add_mk, Prod.mk.injEq]
    exact fun _ _ => ⟨rfl, rfl⟩
  map_smul' := by
    simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
  

Depends on / 依赖: embedding, w.val.embedding
-/
noncomputable def commMap : ((K ->+* Complex) -> Complex) ->ₗ[Real] (mixedSpace K) where
  toFun := fun x => ⟨fun w => (x w.val.embedding).re, fun w => x w.val.embedding⟩
  map_add' := by
    simp only [Pi.add_apply, Complex.add_re, Prod.mk_add_mk, Prod.mk.injEq]
    exact fun _ _ => ⟨rfl, rfl⟩
  map_smul' := by
    simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, RingHom.id_apply, Prod.smul_mk, Prod.mk.injEq]
    exact fun _ _ => ⟨rfl, rfl⟩

/--
theorem `commMap_apply_of_isReal` / 定理 `commMap_apply_of_isReal`

English:
theorem commMap_apply_of_isReal
  given: (x : (K ->+* Complex) -> Complex) {w : InfinitePlace K} (hw : IsReal w)
  proof: rfl

中文:
定理 commMap_apply_of_is实数
  条件: (x : (K ->+* 复形) -> 复形) {w : InfinitePlace K} (hw : Is实数 w)
  证明: rfl
-/
theorem commMap_apply_of_isReal (x : (K ->+* Complex) -> Complex) {w : InfinitePlace K} (hw : IsReal w) :
    (commMap K x).1 ⟨w, hw⟩ = (x w.embedding).re := rfl

/--
theorem `commMap_apply_of_isComplex` / 定理 `commMap_apply_of_isComplex`

English:
theorem commMap_apply_of_isComplex
  given: (x : (K ->+* Complex) -> Complex) {w : InfinitePlace K} (hw : IsComplex w)
  proof: rfl

@[simp]

中文:
定理 commMap_apply_of_isComplex
  条件: (x : (K ->+* 复形) -> 复形) {w : InfinitePlace K} (hw : 是复形 w)
  证明: rfl

@[simp]
-/
theorem commMap_apply_of_isComplex (x : (K ->+* Complex) -> Complex) {w : InfinitePlace K} (hw : IsComplex w) :
    (commMap K x).2 ⟨w, hw⟩ = x w.embedding := rfl

@[simp]
/--
theorem `commMap_canonical_eq_mixed` / 定理 `commMap_canonical_eq_mixed`

English:
theorem commMap_canonical_eq_mixed
  given: (x : K)
  proof: by
  simp only [canonicalEmbedding, commMap, LinearMap.coe_mk, AddHom.coe_mk, RingHom.pi_apply,
    mixedEmbedding, RingHom.prod_apply, Prod.mk.injEq]
  exact ⟨rfl, rfl⟩

中文:
定理 commMap_canonical_eq_mixed
  条件: (x : K)
  证明: by
  simp only [canonicalEmbedding, commMap, LinearMap.coe_mk, AddHom.coe_mk, RingHom.pi_apply,
    mixedEmbedding, RingHom.prod_apply, Prod.mk.injEq]
  exact ⟨rfl, rfl⟩

Depends on / 依赖: AddHom, AddHom.coe_mk, LinearMap, LinearMap.coe_mk, Prod.mk.injEq, RingHom, RingHom.pi_apply, RingHom.prod_apply, canonicalEmbedding, coe_mk, commMap, mixedEmbedding, pi_apply, prod_apply
-/
theorem commMap_canonical_eq_mixed (x : K) :
    commMap K (canonicalEmbedding K x) = mixedEmbedding K x := by
  simp only [canonicalEmbedding, commMap, LinearMap.coe_mk, AddHom.coe_mk, RingHom.pi_apply,
    mixedEmbedding, RingHom.prod_apply, Prod.mk.injEq]
  exact ⟨rfl, rfl⟩

/--
theorem `disjoint_span_commMap_ker` / 定理 `disjoint_span_commMap_ker`

English:
theorem disjoint_span_commMap_ker
  given: [NumberField K]
  proof: by
  refine LinearMap.disjoint_ker.mpr (fun x h_mem h_zero => ?_)
  replace h_mem : x in Submodule.span Real (Set.range (canonicalEmbedding K)) := by
    refine (Submodule.span_mono ?_) h_mem
    rintro _ ⟨i, rfl⟩
    exact ⟨integralBasis K i, (canonicalEmbedding.latticeBasis_apply K i).symm⟩
  ext1

中文:
定理 disjoint_span_commMap_ker
  条件: [数域 K]
  证明: by
  refine LinearMap.disjoint_ker.mpr (fun x h_mem h_zero => ?_)
  replace h_mem : x in Submodule.span Real (Set.range (canonicalEmbedding K)) := by
    refine (Submodule.span_mono ?_) h_mem
    rintro _ ⟨i, rfl⟩
    exact ⟨integralBasis K i, (canonicalEmbedding.latticeBasis_apply K i).symm⟩
  ext1

Depends on / 依赖: Complex.ext, ComplexEmbedding, ComplexEmbedding.IsReal, IsReal, LinearMap, LinearMap.disjoint_ker.mpr, Pi.zero_apply, Set.range, Submodule, Submodule.span, Submodule.span_mono, canonicalEmbedding, canonicalEmbedding.latticeBasis_apply, commMap_apply_of_isReal, disjoint_ker, embedding_mk_eq_of_isReal, h_mem, h_zero, integralBasis, latticeBasis_apply
-/
theorem disjoint_span_commMap_ker [NumberField K] :
    Disjoint (Submodule.span Real (Set.range (canonicalEmbedding.latticeBasis K)))
      (LinearMap.ker (commMap K)) := by
  refine LinearMap.disjoint_ker.mpr (fun x h_mem h_zero => ?_)
  replace h_mem : x in Submodule.span Real (Set.range (canonicalEmbedding K)) := by
    refine (Submodule.span_mono ?_) h_mem
    rintro _ ⟨i, rfl⟩
    exact ⟨integralBasis K i, (canonicalEmbedding.latticeBasis_apply K i).symm⟩
  ext1 φ
  rw [Pi.zero_apply]
  by_cases hφ : ComplexEmbedding.IsReal φ
  · apply Complex.ext
    · rw [← embedding_mk_eq_of_isReal hφ, ← commMap_apply_of_isReal K x ⟨φ, hφ, rfl⟩]
      exact congrFun (congrArg (fun x => x.1) h_zero) ⟨InfinitePlace.mk φ, _⟩
    · rw [Complex.zero_im, ← Complex.conj_eq_iff_im, canonicalEmbedding.conj_apply _ h_mem,
        ComplexEmbedding.isReal_iff.mp hφ]
  · have := congrFun (congrArg (fun x => x.2) h_zero) ⟨InfinitePlace.mk φ, ⟨φ, hφ, rfl⟩⟩
    cases embedding_mk_eq φ with
    | inl h => rwa [← h, ← commMap_apply_of_isComplex K x ⟨φ, hφ, rfl⟩]
    | inr h =>
        apply RingHom.injective (starRingEnd Complex)
        rwa [canonicalEmbedding.conj_apply _ h_mem, ← h, map_zero,
          ← commMap_apply_of_isComplex K x ⟨φ, hφ, rfl⟩]

end commMap

noncomputable section norm

variable {K}

open scoped Classical in
/--
Definition of `normAtPlace` / `normAtPlace` 的定义

English:
definition normAtPlace
  signature: (w : InfinitePlace K)
  body: if hw : IsReal w then ‖x.1 ⟨w, hw⟩‖ else ‖x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by split_ifs <;> simp

中文:
定义 normAtPlace
  签名: (w : InfinitePlace K)
  定义体: if hw : IsReal w then ‖x.1 ⟨w, hw⟩‖ else ‖x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by split_ifs <;> simp

Depends on / 依赖: IsReal, not_isReal_iff_isComplex, not_isReal_iff_isComplex.mp
-/
def normAtPlace (w : InfinitePlace K) : (mixedSpace K) ->*₀ Real where
  toFun x := if hw : IsReal w then ‖x.1 ⟨w, hw⟩‖ else ‖x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by split_ifs <;> simp

/--
theorem `normAtPlace_nonneg` / 定理 `normAtPlace_nonneg`

English:
theorem normAtPlace_nonneg
  given: (w : InfinitePlace K) (x : mixedSpace K)
  proof: by
  rw [normAtPlace]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]
  split_ifs <;> exact norm_nonneg _

中文:
定理 normAtPlace_nonneg
  条件: (w : InfinitePlace K) (x : mixedSpace K)
  证明: by
  rw [normAtPlace]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]
  split_ifs <;> exact norm_nonneg _

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom, ZeroHom.coe_mk, coe_mk, normAtPlace, norm_nonneg, split_ifs
-/
theorem normAtPlace_nonneg (w : InfinitePlace K) (x : mixedSpace K) :
    0 <= normAtPlace w x := by
  rw [normAtPlace]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]
  split_ifs <;> exact norm_nonneg _

/--
theorem `normAtPlace_neg` / 定理 `normAtPlace_neg`

English:
theorem normAtPlace_neg
  given: (w : InfinitePlace K) (x : mixedSpace K)
  proof: by
  rw [normAtPlace]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]
  split_ifs <;> simp

中文:
定理 normAtPlace_neg
  条件: (w : InfinitePlace K) (x : mixedSpace K)
  证明: by
  rw [normAtPlace]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]
  split_ifs <;> simp

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom, ZeroHom.coe_mk, coe_mk, normAtPlace, split_ifs
-/
theorem normAtPlace_neg (w : InfinitePlace K) (x : mixedSpace K) :
    normAtPlace w (-x) = normAtPlace w x := by
  rw [normAtPlace]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]
  split_ifs <;> simp

/--
theorem `normAtPlace_add_le` / 定理 `normAtPlace_add_le`

English:
theorem normAtPlace_add_le
  given: (w : InfinitePlace K) (x y : mixedSpace K)
  proof: by
  rw [normAtPlace]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]
  split_ifs <;> exact norm_add_le _ _

中文:
定理 normAtPlace_add_le
  条件: (w : InfinitePlace K) (x y : mixedSpace K)
  证明: by
  rw [normAtPlace]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]
  split_ifs <;> exact norm_add_le _ _

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom, ZeroHom.coe_mk, coe_mk, normAtPlace, norm_add_le, split_ifs
-/
theorem normAtPlace_add_le (w : InfinitePlace K) (x y : mixedSpace K) :
    normAtPlace w (x + y) <= normAtPlace w x + normAtPlace w y := by
  rw [normAtPlace]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]
  split_ifs <;> exact norm_add_le _ _

/--
theorem `normAtPlace_smul` / 定理 `normAtPlace_smul`

English:
theorem normAtPlace_smul
  given: (w : InfinitePlace K) (x : mixedSpace K) (c : Real)
  proof: by
  rw [normAtPlace]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]
  split_ifs <;> simp

中文:
定理 normAtPlace_smul
  条件: (w : InfinitePlace K) (x : mixedSpace K) (c : 实数)
  证明: by
  rw [normAtPlace]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]
  split_ifs <;> simp

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom, ZeroHom.coe_mk, coe_mk, normAtPlace, split_ifs
-/
theorem normAtPlace_smul (w : InfinitePlace K) (x : mixedSpace K) (c : Real) :
    normAtPlace w (c • x) = |c| * normAtPlace w x := by
  rw [normAtPlace]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]
  split_ifs <;> simp

/--
theorem `normAtPlace_real` / 定理 `normAtPlace_real`

English:
theorem normAtPlace_real
  given: (w : InfinitePlace K) (c : Real)
  proof: by
  rw [show ((fun _ => c]; rw [fun _ => c) : (mixedSpace K)) = c • 1 by ext <;> simp]; rw [normAtPlace_smul]; rw [map_one]; rw [mul_one]

中文:
定理 normAtPlace_real
  条件: (w : InfinitePlace K) (c : 实数)
  证明: by
  rw [show ((fun _ => c]; rw [fun _ => c) : (mixedSpace K)) = c • 1 by ext <;> simp]; rw [normAtPlace_smul]; rw [map_one]; rw [mul_one]

Depends on / 依赖: map_one, mixedSpace, mul_one, normAtPlace_smul
-/
theorem normAtPlace_real (w : InfinitePlace K) (c : Real) :
    normAtPlace w ((fun _ => c, fun _ => c) : (mixedSpace K)) = |c| := by
  rw [show ((fun _ => c]; rw [fun _ => c) : (mixedSpace K)) = c • 1 by ext <;> simp]; rw [normAtPlace_smul]; rw [map_one]; rw [mul_one]

/--
theorem `normAtPlace_apply_of_isReal` / 定理 `normAtPlace_apply_of_isReal`

English:
theorem normAtPlace_apply_of_isReal
  given: {w : InfinitePlace K} (hw : IsReal w) (x : mixedSpace K)
  proof: by
  rw [normAtPlace]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]; rw [dif_pos]

中文:
定理 normAtPlace_apply_of_is实数
  条件: {w : InfinitePlace K} (hw : Is实数 w) (x : mixedSpace K)
  证明: by
  rw [normAtPlace]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]; rw [dif_pos]

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom, ZeroHom.coe_mk, coe_mk, dif_pos, normAtPlace
-/
theorem normAtPlace_apply_of_isReal {w : InfinitePlace K} (hw : IsReal w) (x : mixedSpace K) :
    normAtPlace w x = ‖x.1 ⟨w, hw⟩‖ := by
  rw [normAtPlace]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]; rw [dif_pos]

/--
theorem `normAtPlace_apply_of_isComplex` / 定理 `normAtPlace_apply_of_isComplex`

English:
theorem normAtPlace_apply_of_isComplex
  given: {w : InfinitePlace K} (hw : IsComplex w) (x : mixedSpace K)
  proof: by
  rw [normAtPlace]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]; rw [dif_neg (not_isReal_iff_isComplex.mpr hw)]

@[simp]

中文:
定理 normAtPlace_apply_of_isComplex
  条件: {w : InfinitePlace K} (hw : 是复形 w) (x : mixedSpace K)
  证明: by
  rw [normAtPlace]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]; rw [dif_neg (not_isReal_iff_isComplex.mpr hw)]

@[simp]

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom, ZeroHom.coe_mk, coe_mk, dif_neg, normAtPlace, not_isReal_iff_isComplex, not_isReal_iff_isComplex.mpr
-/
theorem normAtPlace_apply_of_isComplex {w : InfinitePlace K} (hw : IsComplex w) (x : mixedSpace K) :
    normAtPlace w x = ‖x.2 ⟨w, hw⟩‖ := by
  rw [normAtPlace]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]; rw [dif_neg (not_isReal_iff_isComplex.mpr hw)]

@[simp]
/--
theorem `normAtPlace_apply` / 定理 `normAtPlace_apply`

English:
theorem normAtPlace_apply
  given: (w : InfinitePlace K) (x : K)
  proof: by
  simp_rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, mixedEmbedding,
    RingHom.prod_apply, RingHom.pi_apply, norm_embedding_of_isReal, norm_embedding_eq, dite_eq_ite,
    ite_id]

中文:
定理 normAtPlace_apply
  条件: (w : InfinitePlace K) (x : K)
  证明: by
  simp_rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, mixedEmbedding,
    RingHom.prod_apply, RingHom.pi_apply, norm_embedding_of_isReal, norm_embedding_eq, dite_eq_ite,
    ite_id]

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.coe_mk, RingHom, RingHom.pi_apply, RingHom.prod_apply, ZeroHom, ZeroHom.coe_mk, coe_mk, dite_eq_ite, ite_id, mixedEmbedding, normAtPlace, norm_embedding_eq, norm_embedding_of_isReal, pi_apply, prod_apply, simp_rw
-/
theorem normAtPlace_apply (w : InfinitePlace K) (x : K) :
    normAtPlace w (mixedEmbedding K x) = w x := by
  simp_rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, mixedEmbedding,
    RingHom.prod_apply, RingHom.pi_apply, norm_embedding_of_isReal, norm_embedding_eq, dite_eq_ite,
    ite_id]

/--
theorem `forall_normAtPlace_eq_zero_iff` / 定理 `forall_normAtPlace_eq_zero_iff`

English:
theorem forall_normAtPlace_eq_zero_iff
  given: {x : mixedSpace K}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · ext w
    · exact norm_eq_zero.mp (normAtPlace_apply_of_isReal w.prop _ ▸ h w.1)
    · exact norm_eq_zero.mp (normAtPlace_apply_of_isComplex w.prop _ ▸ h w.1)
  · simp_rw [h, map_zero, implies_true]

@[simp]

中文:
定理 对任意_normAtPlace_eq_zero_iff
  条件: {x : mixedSpace K}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · ext w
    · exact norm_eq_zero.mp (normAtPlace_apply_of_isReal w.prop _ ▸ h w.1)
    · exact norm_eq_zero.mp (normAtPlace_apply_of_isComplex w.prop _ ▸ h w.1)
  · simp_rw [h, map_zero, implies_true]

@[simp]

Depends on / 依赖: implies_true, map_zero, normAtPlace_apply_of_isComplex, normAtPlace_apply_of_isReal, norm_eq_zero, norm_eq_zero.mp, simp_rw, w.prop
-/
theorem forall_normAtPlace_eq_zero_iff {x : mixedSpace K} :
    (forall w, normAtPlace w x = 0) ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · ext w
    · exact norm_eq_zero.mp (normAtPlace_apply_of_isReal w.prop _ ▸ h w.1)
    · exact norm_eq_zero.mp (normAtPlace_apply_of_isComplex w.prop _ ▸ h w.1)
  · simp_rw [h, map_zero, implies_true]

@[simp]
/--
theorem `exists_normAtPlace_ne_zero_iff` / 定理 `exists_normAtPlace_ne_zero_iff`

English:
theorem exists_normAtPlace_ne_zero_iff
  given: {x : mixedSpace K}
  proof: by
  rw [ne_eq]; rw [← forall_normAtPlace_eq_zero_iff]; rw [not_forall]

@[fun_prop]

中文:
定理 存在_normAtPlace_ne_zero_iff
  条件: {x : mixedSpace K}
  证明: by
  rw [ne_eq]; rw [← forall_normAtPlace_eq_zero_iff]; rw [not_forall]

@[fun_prop]

Depends on / 依赖: forall_normAtPlace_eq_zero_iff, ne_eq, not_forall
-/
theorem exists_normAtPlace_ne_zero_iff {x : mixedSpace K} :
    (exists w, normAtPlace w x != 0) ↔ x != 0 := by
  rw [ne_eq]; rw [← forall_normAtPlace_eq_zero_iff]; rw [not_forall]

@[fun_prop]
/--
theorem `continuous_normAtPlace` / 定理 `continuous_normAtPlace`

English:
theorem continuous_normAtPlace
  given: (w : InfinitePlace K)
  proof: by
  simp_rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs <;> fun_prop

中文:
定理 continuous_normAtPlace
  条件: (w : InfinitePlace K)
  证明: by
  simp_rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs <;> fun_prop

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom, ZeroHom.coe_mk, coe_mk, fun_prop, normAtPlace, simp_rw, split_ifs
-/
theorem continuous_normAtPlace (w : InfinitePlace K) :
    Continuous (normAtPlace w) := by
  simp_rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs <;> fun_prop

variable [NumberField K]

open scoped Classical in
/--
theorem `nnnorm_eq_sup_normAtPlace` / 定理 `nnnorm_eq_sup_normAtPlace`

English:
theorem nnnorm_eq_sup_normAtPlace
  given: (x : mixedSpace K)
  proof: by
  have :
      (univ : Finset (InfinitePlace K)) =
      (univ.image (fun w : {w : InfinitePlace K // IsReal w} => w.1)) union
      (univ.image (fun w : {w : InfinitePlace K // IsComplex w} => w.1)) := by
    ext; simp [isReal_or_isComplex]
  rw [this]; rw [sup_union]; rw [univ.sup_image]; rw [u

中文:
定理 nnnorm_eq_sup_normAtPlace
  条件: (x : mixedSpace K)
  证明: by
  have :
      (univ : Finset (InfinitePlace K)) =
      (univ.image (fun w : {w : InfinitePlace K // IsReal w} => w.1)) union
      (univ.image (fun w : {w : InfinitePlace K // IsComplex w} => w.1)) := by
    ext; simp [isReal_or_isComplex]
  rw [this]; rw [sup_union]; rw [univ.sup_image]; rw [u

Depends on / 依赖: Finset, InfinitePlace, IsComplex, IsReal, Pi.nnnorm_def, Prod.nnnorm_def, isReal_or_isComplex, nnnorm_def, normAtPlace_apply_of_isComplex, normAtPlace_apply_of_isReal, sup_image, sup_union, univ.image, univ.sup_image, w.prop
-/
theorem nnnorm_eq_sup_normAtPlace (x : mixedSpace K) :
    ‖x‖₊ = univ.sup fun w => .mk (normAtPlace w x) (normAtPlace_nonneg w x) := by
  have :
      (univ : Finset (InfinitePlace K)) =
      (univ.image (fun w : {w : InfinitePlace K // IsReal w} => w.1)) union
      (univ.image (fun w : {w : InfinitePlace K // IsComplex w} => w.1)) := by
    ext; simp [isReal_or_isComplex]
  rw [this]; rw [sup_union]; rw [univ.sup_image]; rw [univ.sup_image]; rw [Prod.nnnorm_def]; rw [Pi.nnnorm_def]; rw [Pi.nnnorm_def]
  congr
  · ext w
    simp [normAtPlace_apply_of_isReal w.prop]
  · ext w
    simp [normAtPlace_apply_of_isComplex w.prop]

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
theorem `norm_eq_sup'_normAtPlace` / 定理 `norm_eq_sup'_normAtPlace`

English:
theorem norm_eq_sup'_normAtPlace
  given: (x : mixedSpace K)
  proof: by
  rw [← coe_nnnorm]; rw [nnnorm_eq_sup_normAtPlace]; rw [← sup'_eq_sup univ_nonempty]; rw [← NNReal.val_eq_coe]; rw [← OrderHom.Subtype.val_coe]; rw [map_finset_sup']; rw [OrderHom.Subtype.val_coe]
  simp

中文:
定理 norm_eq_sup'_normAtPlace
  条件: (x : mixedSpace K)
  证明: by
  rw [← coe_nnnorm]; rw [nnnorm_eq_sup_normAtPlace]; rw [← sup'_eq_sup univ_nonempty]; rw [← NNReal.val_eq_coe]; rw [← OrderHom.Subtype.val_coe]; rw [map_finset_sup']; rw [OrderHom.Subtype.val_coe]
  simp

Depends on / 依赖: NNReal, NNReal.val_eq_coe, OrderHom, OrderHom.Subtype.val_coe, Subtype, _eq_sup, coe_nnnorm, map_finset_sup, nnnorm_eq_sup_normAtPlace, univ_nonempty, val_coe, val_eq_coe
-/
theorem norm_eq_sup'_normAtPlace (x : mixedSpace K) :
    ‖x‖ = univ.sup' univ_nonempty fun w => normAtPlace w x := by
  rw [← coe_nnnorm]; rw [nnnorm_eq_sup_normAtPlace]; rw [← sup'_eq_sup univ_nonempty]; rw [← NNReal.val_eq_coe]; rw [← OrderHom.Subtype.val_coe]; rw [map_finset_sup']; rw [OrderHom.Subtype.val_coe]
  simp

/--
Definition of `norm` / `norm` 的定义

English:
definition norm
  signature: : (mixedSpace K) ->*₀ Real where
  body: ∏ w, (normAtPlace w x) ^ (mult w)
  map_one' := by simp only [map_one, one_pow, prod_const_one]
  map_zero' := by simp [mult]
  map_mul' _ _ := by simp only [map_mul, mul_pow, prod_mul_distrib]

中文:
定义 norm
  签名: : (mixedSpace K) ->*₀ 实数 where
  定义体: ∏ w, (normAtPlace w x) ^ (mult w)
  map_one' := by simp only [map_one, one_pow, prod_const_one]
  map_zero' := by simp [mult]
  map_mul' _ _ := by simp only [map_mul, mul_pow, prod_mul_distrib]
-/
protected def norm : (mixedSpace K) ->*₀ Real where
  toFun x := ∏ w, (normAtPlace w x) ^ (mult w)
  map_one' := by simp only [map_one, one_pow, prod_const_one]
  map_zero' := by simp [mult]
  map_mul' _ _ := by simp only [map_mul, mul_pow, prod_mul_distrib]

/--
theorem `norm_apply` / 定理 `norm_apply`

English:
theorem norm_apply
  given: (x : mixedSpace K)
  proof: rfl

中文:
定理 norm_apply
  条件: (x : mixedSpace K)
  证明: rfl
-/
protected theorem norm_apply (x : mixedSpace K) :
    mixedEmbedding.norm x = ∏ w, (normAtPlace w x) ^ (mult w) := rfl

/--
theorem `norm_nonneg` / 定理 `norm_nonneg`

English:
theorem norm_nonneg
  given: (x : mixedSpace K)
  proof: univ.prod_nonneg fun _ _ => pow_nonneg (normAtPlace_nonneg _ _) _

中文:
定理 norm_nonneg
  条件: (x : mixedSpace K)
  证明: univ.prod_nonneg fun _ _ => pow_nonneg (normAtPlace_nonneg _ _) _
-/
protected theorem norm_nonneg (x : mixedSpace K) :
    0 <= mixedEmbedding.norm x := univ.prod_nonneg fun _ _ => pow_nonneg (normAtPlace_nonneg _ _) _

/--
theorem `norm_eq_zero_iff` / 定理 `norm_eq_zero_iff`

English:
theorem norm_eq_zero_iff
  given: {x : mixedSpace K}
  proof: by
  simp_rw [mixedEmbedding.norm, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, prod_eq_zero_iff,
    mem_univ, true_and, pow_eq_zero_iff mult_ne_zero]

中文:
定理 norm_eq_zero_iff
  条件: {x : mixedSpace K}
  证明: by
  simp_rw [mixedEmbedding.norm, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, prod_eq_zero_iff,
    mem_univ, true_and, pow_eq_zero_iff mult_ne_zero]
-/
protected theorem norm_eq_zero_iff {x : mixedSpace K} :
    mixedEmbedding.norm x = 0 ↔ exists w, normAtPlace w x = 0 := by
  simp_rw [mixedEmbedding.norm, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, prod_eq_zero_iff,
    mem_univ, true_and, pow_eq_zero_iff mult_ne_zero]

/--
theorem `norm_ne_zero_iff` / 定理 `norm_ne_zero_iff`

English:
theorem norm_ne_zero_iff
  given: {x : mixedSpace K}
  proof: by
  rw [← not_iff_not]
  simp_rw [ne_eq, mixedEmbedding.norm_eq_zero_iff, not_not, not_forall, not_not]

中文:
定理 norm_ne_zero_iff
  条件: {x : mixedSpace K}
  证明: by
  rw [← not_iff_not]
  simp_rw [ne_eq, mixedEmbedding.norm_eq_zero_iff, not_not, not_forall, not_not]
-/
protected theorem norm_ne_zero_iff {x : mixedSpace K} :
    mixedEmbedding.norm x != 0 ↔ forall w, normAtPlace w x != 0 := by
  rw [← not_iff_not]
  simp_rw [ne_eq, mixedEmbedding.norm_eq_zero_iff, not_not, not_forall, not_not]

/--
theorem `norm_eq_of_normAtPlace_eq` / 定理 `norm_eq_of_normAtPlace_eq`

English:
theorem norm_eq_of_normAtPlace_eq
  statement: {x y : mixedSpace K}
  proof: by
  simp_rw [mixedEmbedding.norm_apply, h]

中文:
定理 norm_eq_of_normAtPlace_eq
  结论: {x y : mixedSpace K}
  证明: by
  simp_rw [mixedEmbedding.norm_apply, h]

Depends on / 依赖: mixedEmbedding, mixedEmbedding.norm_apply, norm_apply, simp_rw
-/
theorem norm_eq_of_normAtPlace_eq {x y : mixedSpace K}
    (h : forall w, normAtPlace w x = normAtPlace w y) :
    mixedEmbedding.norm x = mixedEmbedding.norm y := by
  simp_rw [mixedEmbedding.norm_apply, h]

/--
theorem `norm_smul` / 定理 `norm_smul`

English:
theorem norm_smul
  given: (c : Real) (x : mixedSpace K)
  proof: by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_smul, mul_pow, prod_mul_distrib,
    prod_pow_eq_pow_sum, sum_mult_eq]

中文:
定理 norm_smul
  条件: (c : 实数) (x : mixedSpace K)
  证明: by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_smul, mul_pow, prod_mul_distrib,
    prod_pow_eq_pow_sum, sum_mult_eq]

Depends on / 依赖: mixedEmbedding, mixedEmbedding.norm_apply, mul_pow, normAtPlace_smul, norm_apply, prod_mul_distrib, prod_pow_eq_pow_sum, simp_rw, sum_mult_eq
-/
theorem norm_smul (c : Real) (x : mixedSpace K) :
    mixedEmbedding.norm (c • x) = |c| ^ finrank Rat K * (mixedEmbedding.norm x) := by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_smul, mul_pow, prod_mul_distrib,
    prod_pow_eq_pow_sum, sum_mult_eq]

/--
theorem `norm_real` / 定理 `norm_real`

English:
theorem norm_real
  given: (c : Real)
  proof: by
  rw [show ((fun _ => c]; rw [fun _ => c) : (mixedSpace K)) = c • 1 by ext <;> simp]; rw [norm_smul]; rw [map_one]; rw [mul_one]

@[simp]

中文:
定理 norm_real
  条件: (c : 实数)
  证明: by
  rw [show ((fun _ => c]; rw [fun _ => c) : (mixedSpace K)) = c • 1 by ext <;> simp]; rw [norm_smul]; rw [map_one]; rw [mul_one]

@[simp]

Depends on / 依赖: map_one, mixedSpace, mul_one, norm_smul
-/
theorem norm_real (c : Real) :
    mixedEmbedding.norm ((fun _ => c, fun _ => c) : (mixedSpace K)) = |c| ^ finrank Rat K := by
  rw [show ((fun _ => c]; rw [fun _ => c) : (mixedSpace K)) = c • 1 by ext <;> simp]; rw [norm_smul]; rw [map_one]; rw [mul_one]

@[simp]
/--
theorem `norm_eq_norm` / 定理 `norm_eq_norm`

English:
theorem norm_eq_norm
  given: (x : K)
  proof: by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_apply, prod_eq_abs_norm]

中文:
定理 norm_eq_norm
  条件: (x : K)
  证明: by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_apply, prod_eq_abs_norm]

Depends on / 依赖: mixedEmbedding, mixedEmbedding.norm_apply, normAtPlace_apply, norm_apply, prod_eq_abs_norm, simp_rw
-/
theorem norm_eq_norm (x : K) :
    mixedEmbedding.norm (mixedEmbedding K x) = |Algebra.norm Rat x| := by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_apply, prod_eq_abs_norm]

/--
theorem `norm_unit` / 定理 `norm_unit`

English:
theorem norm_unit
  given: (u : (𝓞 K)ˣ)
  proof: by
  rw [norm_eq_norm]; rw [Units.norm]; rw [Rat.cast_one]

中文:
定理 norm_unit
  条件: (u : (𝓞 K)ˣ)
  证明: by
  rw [norm_eq_norm]; rw [Units.norm]; rw [Rat.cast_one]

Depends on / 依赖: Rat.cast_one, Units.norm, cast_one, norm_eq_norm
-/
theorem norm_unit (u : (𝓞 K)ˣ) :
    mixedEmbedding.norm (mixedEmbedding K u) = 1 := by
  rw [norm_eq_norm]; rw [Units.norm]; rw [Rat.cast_one]

/--
theorem `norm_eq_zero_iff'` / 定理 `norm_eq_zero_iff'`

English:
theorem norm_eq_zero_iff'
  given: {x : mixedSpace K} (hx : x in Set.range (mixedEmbedding K))
  proof: by
  obtain ⟨a, rfl⟩ := hx
  rw [norm_eq_norm]; rw [Rat.cast_abs]; rw [abs_eq_zero]; rw [Rat.cast_eq_zero]; rw [Algebra.norm_eq_zero_iff]; rw [map_eq_zero]

中文:
定理 norm_eq_zero_iff'
  条件: {x : mixedSpace K} (hx : x in 集合.range (mixedEmbedding K))
  证明: by
  obtain ⟨a, rfl⟩ := hx
  rw [norm_eq_norm]; rw [Rat.cast_abs]; rw [abs_eq_zero]; rw [Rat.cast_eq_zero]; rw [Algebra.norm_eq_zero_iff]; rw [map_eq_zero]

Depends on / 依赖: Algebra, Algebra.norm_eq_zero_iff, Rat.cast_abs, Rat.cast_eq_zero, abs_eq_zero, cast_abs, cast_eq_zero, map_eq_zero, norm_eq_norm, norm_eq_zero_iff
-/
theorem norm_eq_zero_iff' {x : mixedSpace K} (hx : x in Set.range (mixedEmbedding K)) :
    mixedEmbedding.norm x = 0 ↔ x = 0 := by
  obtain ⟨a, rfl⟩ := hx
  rw [norm_eq_norm]; rw [Rat.cast_abs]; rw [abs_eq_zero]; rw [Rat.cast_eq_zero]; rw [Algebra.norm_eq_zero_iff]; rw [map_eq_zero]

variable (K) in
@[fun_prop]
/--
theorem `continuous_norm` / 定理 `continuous_norm`

English:
theorem continuous_norm
  statement: Continuous (mixedEmbedding.norm : (mixedSpace K) -> Real)
  proof: by
  refine continuous_finsetProd Finset.univ fun _ _ => ?_
  simp_rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, dite_pow]
  split_ifs <;> fun_prop

中文:
定理 continuous_norm
  结论: 连续 (mixedEmbedding.norm : (mixedSpace K) -> 实数)
  证明: by
  refine continuous_finsetProd Finset.univ fun _ _ => ?_
  simp_rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, dite_pow]
  split_ifs <;> fun_prop
-/
protected theorem continuous_norm : Continuous (mixedEmbedding.norm : (mixedSpace K) -> Real) := by
  refine continuous_finsetProd Finset.univ fun _ _ => ?_
  simp_rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, dite_pow]
  split_ifs <;> fun_prop

end norm

noncomputable section stdBasis

open Complex MeasureTheory MeasureTheory.Measure ZSpan Matrix ComplexConjugate

variable [NumberField K]

/--
Definition of `index` / `index` 的定义

English:
abbreviation index
  body: {w : InfinitePlace K // IsReal w} oplus ({w : InfinitePlace K // IsComplex w}) × (Fin 2)

中文:
缩写 index
  定义体: {w : InfinitePlace K // IsReal w} oplus ({w : InfinitePlace K // IsComplex w}) × (Fin 2)

Depends on / 依赖: InfinitePlace, IsComplex, IsReal
-/
abbrev index := {w : InfinitePlace K // IsReal w} oplus ({w : InfinitePlace K // IsComplex w}) × (Fin 2)

open scoped Classical in
/--
Definition of `stdBasis` / `stdBasis` 的定义

English:
definition stdBasis
  signature: : Basis (index K) Real (mixedSpace K)
  body: Basis.prod (Pi.basisFun Real _)
    (Basis.reindex (Pi.basis fun _ => basisOneI) (Equiv.sigmaEquivProd _ _))

中文:
定义 stdBasis
  签名: : 基 (index K) 实数 (mixedSpace K)
  定义体: Basis.prod (Pi.basisFun Real _)
    (Basis.reindex (Pi.basis fun _ => basisOneI) (Equiv.sigmaEquivProd _ _))

Depends on / 依赖: Basis.prod, Basis.reindex, Equiv.sigmaEquivProd, Pi.basis, Pi.basisFun, basisFun, basisOneI, reindex, sigmaEquivProd
-/
def stdBasis : Basis (index K) Real (mixedSpace K) :=
  Basis.prod (Pi.basisFun Real _)
    (Basis.reindex (Pi.basis fun _ => basisOneI) (Equiv.sigmaEquivProd _ _))

variable {K}

@[simp]
/--
theorem `stdBasis_apply_isReal` / 定理 `stdBasis_apply_isReal`

English:
theorem stdBasis_apply_isReal
  given: (x : mixedSpace K) (w : {w : InfinitePlace K // IsReal w})
  proof: rfl

@[simp]

中文:
定理 stdBasis_apply_is实数
  条件: (x : mixedSpace K) (w : {w : InfinitePlace K // Is实数 w})
  证明: rfl

@[simp]
-/
theorem stdBasis_apply_isReal (x : mixedSpace K) (w : {w : InfinitePlace K // IsReal w}) :
    (stdBasis K).repr x (Sum.inl w) = x.1 w := rfl

@[simp]
/--
theorem `stdBasis_apply_isComplex_fst` / 定理 `stdBasis_apply_isComplex_fst`

English:
theorem stdBasis_apply_isComplex_fst
  statement: (x : mixedSpace K)
  proof: rfl

@[simp]

中文:
定理 stdBasis_apply_isComplex_fst
  结论: (x : mixedSpace K)
  证明: rfl

@[simp]
-/
theorem stdBasis_apply_isComplex_fst (x : mixedSpace K)
    (w : {w : InfinitePlace K // IsComplex w}) :
    (stdBasis K).repr x (Sum.inr ⟨w, 0⟩) = (x.2 w).re := rfl

@[simp]
/--
theorem `stdBasis_apply_isComplex_snd` / 定理 `stdBasis_apply_isComplex_snd`

English:
theorem stdBasis_apply_isComplex_snd
  statement: (x : mixedSpace K)
  proof: rfl

中文:
定理 stdBasis_apply_isComplex_snd
  结论: (x : mixedSpace K)
  证明: rfl
-/
theorem stdBasis_apply_isComplex_snd (x : mixedSpace K)
    (w : {w : InfinitePlace K // IsComplex w}) :
    (stdBasis K).repr x (Sum.inr ⟨w, 1⟩) = (x.2 w).im := rfl

variable (K)

open scoped Classical in
/--
theorem `fundamentalDomain_stdBasis` / 定理 `fundamentalDomain_stdBasis`

English:
theorem fundamentalDomain_stdBasis
  proof: by
  ext
  simp [stdBasis, mem_fundamentalDomain, Complex.measurableEquivPi]

中文:
定理 fundamentalDomain_stdBasis
  证明: by
  ext
  simp [stdBasis, mem_fundamentalDomain, Complex.measurableEquivPi]

Depends on / 依赖: Complex.measurableEquivPi, measurableEquivPi, mem_fundamentalDomain, stdBasis
-/
theorem fundamentalDomain_stdBasis :
    fundamentalDomain (stdBasis K) =
      (Set.univ.pi fun _ => Set.Ico 0 1) ×ˢ
      (Set.univ.pi fun _ => Complex.measurableEquivPi ⁻¹' (Set.univ.pi fun _ => Set.Ico 0 1)) := by
  ext
  simp [stdBasis, mem_fundamentalDomain, Complex.measurableEquivPi]

open scoped Classical in
/--
theorem `volume_fundamentalDomain_stdBasis` / 定理 `volume_fundamentalDomain_stdBasis`

English:
theorem volume_fundamentalDomain_stdBasis
  proof: by
  rw [fundamentalDomain_stdBasis]; rw [volume_eq_prod]; rw [prod_prod]; rw [volume_pi]; rw [volume_pi]; rw [pi_pi]; rw [pi_pi]; rw [Complex.volume_preserving_equiv_pi.measure_preimage ?_]; rw [volume_pi]; rw [pi_pi]; rw [Real.volume_Ico]; rw [sub_zero]; rw [ENNReal.ofReal_one]; rw [prod_const_one

中文:
定理 volume_fundamentalDomain_stdBasis
  证明: by
  rw [fundamentalDomain_stdBasis]; rw [volume_eq_prod]; rw [prod_prod]; rw [volume_pi]; rw [volume_pi]; rw [pi_pi]; rw [pi_pi]; rw [Complex.volume_preserving_equiv_pi.measure_preimage ?_]; rw [volume_pi]; rw [pi_pi]; rw [Real.volume_Ico]; rw [sub_zero]; rw [ENNReal.ofReal_one]; rw [prod_const_one

Depends on / 依赖: Complex.volume_preserving_equiv_pi.measure_preimage, ENNReal, ENNReal.ofReal_one, MeasurableSet, MeasurableSet.pi, Real.volume_Ico, Set.countable_univ, countable_univ, fundamentalDomain_stdBasis, measurableSet_Ico, measure_preimage, nullMeasurableSet, ofReal_one, one_mul, pi_pi, prod_const_one, prod_prod, sub_zero, volume_Ico, volume_eq_prod
-/
theorem volume_fundamentalDomain_stdBasis :
    volume (fundamentalDomain (stdBasis K)) = 1 := by
  rw [fundamentalDomain_stdBasis]; rw [volume_eq_prod]; rw [prod_prod]; rw [volume_pi]; rw [volume_pi]; rw [pi_pi]; rw [pi_pi]; rw [Complex.volume_preserving_equiv_pi.measure_preimage ?_]; rw [volume_pi]; rw [pi_pi]; rw [Real.volume_Ico]; rw [sub_zero]; rw [ENNReal.ofReal_one]; rw [prod_const_one]; rw [prod_const_one]; rw [prod_const_one]; rw [one_mul]
  exact (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)).nullMeasurableSet

open scoped Classical in
/--
Definition of `indexEquiv` / `indexEquiv` 的定义

English:
definition indexEquiv
  signature: : (index K) ≃ (K ->+* Complex)
  body: by
  refine Equiv.ofBijective (fun c => ?_)
    ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨?_, ?_⟩)
  · cases c with
    | inl w => exact w.val.embedding
    | inr wj => rcases wj with ⟨w, j⟩
                exact if j = 0 then w.val.embedding else ComplexEmbedding.conjugate w.val.embedding

中文:
定义 indexEquiv
  签名: : (index K) ≃ (K ->+* 复形)
  定义体: by
  refine Equiv.ofBijective (fun c => ?_)
    ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨?_, ?_⟩)
  · cases c with
    | inl w => exact w.val.embedding
    | inr wj => rcases wj with ⟨w, j⟩
                exact if j = 0 then w.val.embedding else ComplexEmbedding.conjugate w.val.embedding

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.IsReal, ComplexEmbedding.conjugate, Equiv.ofBijective, Fintype, Fintype.bijective_iff_surjective_and_card, InfinitePlace, InfinitePlace.mk, InfinitePlace.mkComplex, InfinitePlace.mkReal, IsReal, Sum.inl, Sum.inr, bijective_iff_surjective_and_card, conjugate, embedding, embedding_mk_eq_of_isReal, mkComplex, mkReal, ofBijective
-/
def indexEquiv : (index K) ≃ (K ->+* Complex) := by
  refine Equiv.ofBijective (fun c => ?_)
    ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨?_, ?_⟩)
  · cases c with
    | inl w => exact w.val.embedding
    | inr wj => rcases wj with ⟨w, j⟩
                exact if j = 0 then w.val.embedding else ComplexEmbedding.conjugate w.val.embedding
  · intro φ
    by_cases hφ : ComplexEmbedding.IsReal φ
    · exact ⟨Sum.inl (InfinitePlace.mkReal ⟨φ, hφ⟩), by simp [embedding_mk_eq_of_isReal hφ]⟩
    · by_cases hw : (InfinitePlace.mk φ).embedding = φ
      · exact ⟨Sum.inr ⟨InfinitePlace.mkComplex ⟨φ, hφ⟩, 0⟩, by simp [hw]⟩
      · exact ⟨Sum.inr ⟨InfinitePlace.mkComplex ⟨φ, hφ⟩, 1⟩,
          by simp [(embedding_mk_eq φ).resolve_left hw]⟩
  · rw [Embeddings.card, ← mixedEmbedding.finrank K,
      ← Module.finrank_eq_card_basis (stdBasis K)]

variable {K}

@[simp]
/--
theorem `indexEquiv_apply_isReal` / 定理 `indexEquiv_apply_isReal`

English:
theorem indexEquiv_apply_isReal
  given: (w : {w : InfinitePlace K // IsReal w})
  proof: rfl

@[simp]

中文:
定理 indexEquiv_apply_is实数
  条件: (w : {w : InfinitePlace K // Is实数 w})
  证明: rfl

@[simp]
-/
theorem indexEquiv_apply_isReal (w : {w : InfinitePlace K // IsReal w}) :
    (indexEquiv K) (Sum.inl w) = w.val.embedding := rfl

@[simp]
/--
theorem `indexEquiv_apply_isComplex_fst` / 定理 `indexEquiv_apply_isComplex_fst`

English:
theorem indexEquiv_apply_isComplex_fst
  given: (w : {w : InfinitePlace K // IsComplex w})
  proof: rfl

@[simp]

中文:
定理 indexEquiv_apply_isComplex_fst
  条件: (w : {w : InfinitePlace K // 是复形 w})
  证明: rfl

@[simp]
-/
theorem indexEquiv_apply_isComplex_fst (w : {w : InfinitePlace K // IsComplex w}) :
    (indexEquiv K) (Sum.inr ⟨w, 0⟩) = w.val.embedding := rfl

@[simp]
/--
theorem `indexEquiv_apply_isComplex_snd` / 定理 `indexEquiv_apply_isComplex_snd`

English:
theorem indexEquiv_apply_isComplex_snd
  given: (w : {w : InfinitePlace K // IsComplex w})
  proof: rfl

中文:
定理 indexEquiv_apply_isComplex_snd
  条件: (w : {w : InfinitePlace K // 是复形 w})
  证明: rfl
-/
theorem indexEquiv_apply_isComplex_snd (w : {w : InfinitePlace K // IsComplex w}) :
    (indexEquiv K) (Sum.inr ⟨w, 1⟩) = ComplexEmbedding.conjugate w.val.embedding := rfl

variable (K)

open scoped Classical in
/--
Definition of `matrixToStdBasis` / `matrixToStdBasis` 的定义

English:
definition matrixToStdBasis
  signature: : Matrix (index K) (index K) Complex
  body: fromBlocks (diagonal fun _ => 1) 0 0 reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
    (blockDiagonal (fun _ => (2 : Complex)⁻¹ • !![1, 1; -I, I]))

中文:
定义 matrixToStdBasis
  签名: : 矩阵 (index K) (index K) 复形
  定义体: fromBlocks (diagonal fun _ => 1) 0 0 reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
    (blockDiagonal (fun _ => (2 : Complex)⁻¹ • !![1, 1; -I, I]))

Depends on / 依赖: Equiv.prodComm, blockDiagonal, diagonal, fromBlocks, prodComm, reindex
-/
def matrixToStdBasis : Matrix (index K) (index K) Complex :=
fromBlocks (diagonal fun _ => 1) 0 0 reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
    (blockDiagonal (fun _ => (2 : Complex)⁻¹ • !![1, 1; -I, I]))

open scoped Classical in
/--
theorem `det_matrixToStdBasis` / 定理 `det_matrixToStdBasis`

English:
theorem det_matrixToStdBasis
  proof: calc
  _ = ∏ _k : { w : InfinitePlace K // IsComplex w }, det ((2 : Complex)⁻¹ • !![1, 1; -I, I]) := by
      rw [matrixToStdBasis]; rw [det_fromBlocks_zero₂₁]; rw [det_diagonal]; rw [prod_const_one]; rw [one_mul]; rw [det_reindex_self]; rw [det_blockDiagonal]
  _ = ∏ _k : { w : InfinitePlace K // I

中文:
定理 det_matrixToStdBasis
  证明: calc
  _ = ∏ _k : { w : InfinitePlace K // IsComplex w }, det ((2 : Complex)⁻¹ • !![1, 1; -I, I]) := by
      rw [matrixToStdBasis]; rw [det_fromBlocks_zero₂₁]; rw [det_diagonal]; rw [prod_const_one]; rw [one_mul]; rw [det_reindex_self]; rw [det_blockDiagonal]
  _ = ∏ _k : { w : InfinitePlace K // I

Depends on / 依赖: Complex.I, Eq.refl, Fintyp, Fintype, Fintype.card, InfinitePlace, IsComplex, det_blockDiagonal, det_diagonal, det_reindex_self, matrixToStdBasis, one_mul, prod_congr, prod_const, prod_const_one
-/
theorem det_matrixToStdBasis :
    (matrixToStdBasis K).det = (2⁻¹ * I) ^ nrComplexPlaces K :=
  calc
  _ = ∏ _k : { w : InfinitePlace K // IsComplex w }, det ((2 : Complex)⁻¹ • !![1, 1; -I, I]) := by
      rw [matrixToStdBasis]; rw [det_fromBlocks_zero₂₁]; rw [det_diagonal]; rw [prod_const_one]; rw [one_mul]; rw [det_reindex_self]; rw [det_blockDiagonal]
  _ = ∏ _k : { w : InfinitePlace K // IsComplex w }, (2⁻¹ * Complex.I) := by
      refine prod_congr (Eq.refl _) (fun _ _ => ?_)
      simp [field]; ring
  _ = (2⁻¹ * Complex.I) ^ Fintype.card {w : InfinitePlace K // IsComplex w} := by
      rw [prod_const]; rw [Fintype.card]

open scoped Classical in
/--
theorem `stdBasis_repr_eq_matrixToStdBasis_mul` / 定理 `stdBasis_repr_eq_matrixToStdBasis_mul`

English:
theorem stdBasis_repr_eq_matrixToStdBasis_mul
  statement: (x : (K ->+* Complex) -> Complex)
  proof: by
  simp_rw [commMap, matrixToStdBasis, LinearMap.coe_mk, AddHom.coe_mk,
    mulVec, dotProduct, Function.comp_apply, index, Fintype.sum_sum_type,
    diagonal_one, reindex_apply, ← univ_product_univ, sum_product,
    indexEquiv_apply_isReal, Fin.sum_univ_two, indexEquiv_apply_isComplex_fst,
    in

中文:
定理 stdBasis_repr_eq_matrixToStdBasis_mul
  结论: (x : (K ->+* 复形) -> 复形)
  证明: by
  simp_rw [commMap, matrixToStdBasis, LinearMap.coe_mk, AddHom.coe_mk,
    mulVec, dotProduct, Function.comp_apply, index, Fintype.sum_sum_type,
    diagonal_one, reindex_apply, ← univ_product_univ, sum_product,
    indexEquiv_apply_isReal, Fin.sum_univ_two, indexEquiv_apply_isComplex_fst,
    in

Depends on / 依赖: AddHom, AddHom.coe_mk, Equiv.coe_prodComm, Equiv.prodComm_symm, Fin.sum_univ_two, Fintype, Fintype.sum_sum_type, Function, Function.comp_apply, LinearMap, LinearMap.coe_mk, Matrix, Matrix.smul_empty, RelEmbedding, RelEmbedding.refl, coe_mk, coe_prodComm, commMap, comp_apply, diagonal_one
-/
theorem stdBasis_repr_eq_matrixToStdBasis_mul (x : (K ->+* Complex) -> Complex)
    (hx : forall φ, conj (x φ) = x (ComplexEmbedding.conjugate φ)) (c : index K) :
    ((stdBasis K).repr (commMap K x) c : Complex) =
      (matrixToStdBasis K *ᵥ (x ∘ (indexEquiv K))) c := by
  simp_rw [commMap, matrixToStdBasis, LinearMap.coe_mk, AddHom.coe_mk,
    mulVec, dotProduct, Function.comp_apply, index, Fintype.sum_sum_type,
    diagonal_one, reindex_apply, ← univ_product_univ, sum_product,
    indexEquiv_apply_isReal, Fin.sum_univ_two, indexEquiv_apply_isComplex_fst,
    indexEquiv_apply_isComplex_snd, smul_of, smul_cons, smul_eq_mul,
    mul_one, Matrix.smul_empty, Equiv.prodComm_symm, Equiv.coe_prodComm]
  cases c with
  | inl w =>
      simp_rw [stdBasis_apply_isReal, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        one_apply, Matrix.zero_apply, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true,
        add_zero, sum_const_zero, add_zero, ← conj_eq_iff_re, hx (embedding w.val),
        conjugate_embedding_eq_of_isReal w.prop]
  | inr c =>
    rcases c with ⟨w, j⟩
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, stdBasis_apply_isComplex_fst, re_eq_add_conj,
        mul_neg, fromBlocks_apply₂₁, Matrix.zero_apply, zero_mul, sum_const_zero,
        fromBlocks_apply₂₂, submatrix_apply, Prod.swap_prod_mk, blockDiagonal_apply, of_apply,
        cons_val', cons_val_zero, empty_val', cons_val_fin_one, ite_mul, cons_val_one,
        sum_add_distrib, sum_ite_eq, mem_univ, ↓reduceIte, ← hx (embedding w), zero_add]
      ring
    · simp only [Fin.mk_one, Fin.isValue, stdBasis_apply_isComplex_snd, im_eq_sub_conj,
        mul_neg, fromBlocks_apply₂₁, Matrix.zero_apply, zero_mul, sum_const_zero,
        fromBlocks_apply₂₂, submatrix_apply, Prod.swap_prod_mk, blockDiagonal_apply, of_apply,
        cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_one, ite_mul, neg_mul,
        sum_add_distrib, sum_ite_eq, mem_univ, ↓reduceIte, ← hx (embedding w), zero_add]
      ring_nf; simp [field]

end stdBasis

noncomputable section integerLattice

variable [NumberField K]

open Module.Free

open scoped nonZeroDivisors

/--
Definition of `integerLattice` / `integerLattice` 的定义

English:
abbreviation integerLattice
  signature: : Submodule Int (mixedSpace K)
  body: LinearMap.range ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)).toIntAlgHom.toLinearMap

中文:
缩写 integerLattice
  签名: : 子模 整数 (mixedSpace K)
  定义体: LinearMap.range ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)).toIntAlgHom.toLinearMap
-/
protected abbrev integerLattice : Submodule Int (mixedSpace K) :=
  LinearMap.range ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)).toIntAlgHom.toLinearMap

/--
Definition of `latticeBasis` / `latticeBasis` 的定义

English:
definition latticeBasis
  signature: :
  body: by
  classical
    -- We construct an `ℝ`-linear independent family from the image of
    -- `canonicalEmbedding.lattice_basis` by `commMap`
    have := LinearIndependent.map (LinearIndependent.restrict_scalars
      (by { simpa only [Complex.real_smul, mul_one] using Complex.ofReal_injective })
   

中文:
定义 latticeBasis
  签名: :
  定义体: by
  classical
    -- We construct an `ℝ`-linear independent family from the image of
    -- `canonicalEmbedding.lattice_basis` by `commMap`
    have := LinearIndependent.map (LinearIndependent.restrict_scalars
      (by { simpa only [Complex.real_smul, mul_one] using Complex.ofReal_injective })
   

Depends on / 依赖: classical
-/
def latticeBasis :
    Basis (ChooseBasisIndex Int (𝓞 K)) Real (mixedSpace K) := by
  classical
    -- We construct an `ℝ`-linear independent family from the image of
    -- `canonicalEmbedding.lattice_basis` by `commMap`
    have := LinearIndependent.map (LinearIndependent.restrict_scalars
      (by { simpa only [Complex.real_smul, mul_one] using Complex.ofReal_injective })
      (canonicalEmbedding.latticeBasis K).linearIndependent)
      (disjoint_span_commMap_ker K)
    -- and it's a basis since it has the right cardinality
    refine basisOfLinearIndependentOfCardEqFinrank this ?_
    rw [← finrank_eq_card_chooseBasisIndex]; rw [RingOfIntegers.rank]; rw [finrank_prod]; rw [finrank_pi]; rw [finrank_pi_fintype]; rw [Complex.finrank_real_complex]; rw [sum_const]; rw [card_univ]; rw [← nrRealPlaces]; rw [← nrComplexPlaces]; rw [← card_real_embeddings]; rw [smul_eq_mul]; rw [mul_comm]; rw [← card_complex_embeddings]; rw [← NumberField.Embeddings.card K Complex]; rw [Fintype.card_subtype_compl]; rw [Nat.add_sub_of_le (Fintype.card_subtype_le _)]

@[simp]
/--
theorem `latticeBasis_apply` / 定理 `latticeBasis_apply`

English:
theorem latticeBasis_apply
  given: (i : ChooseBasisIndex Int (𝓞 K))
  proof: by
  simp only [latticeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, Function.comp_apply,
    canonicalEmbedding.latticeBasis_apply, integralBasis_apply, commMap_canonical_eq_mixed]

中文:
定理 latticeBasis_apply
  条件: (i : ChooseBasisIndex 整数 (𝓞 K))
  证明: by
  simp only [latticeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, Function.comp_apply,
    canonicalEmbedding.latticeBasis_apply, integralBasis_apply, commMap_canonical_eq_mixed]

Depends on / 依赖: Function, Function.comp_apply, canonicalEmbedding, canonicalEmbedding.latticeBasis_apply, coe_basisOfLinearIndependentOfCardEqFinrank, commMap_canonical_eq_mixed, comp_apply, integralBasis_apply, latticeBasis, latticeBasis_apply
-/
theorem latticeBasis_apply (i : ChooseBasisIndex Int (𝓞 K)) :
    latticeBasis K i = (mixedEmbedding K) (integralBasis K i) := by
  simp only [latticeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, Function.comp_apply,
    canonicalEmbedding.latticeBasis_apply, integralBasis_apply, commMap_canonical_eq_mixed]

/--
theorem `mem_span_latticeBasis` / 定理 `mem_span_latticeBasis`

English:
theorem mem_span_latticeBasis
  given: {x : (mixedSpace K)}
  proof: by
  rw [show Set.range (latticeBasis K) =
      (mixedEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (integralBasis K)) by
    rw [← Set.range_comp]; exact congrArg Set.range (funext (fun i => latticeBasis_apply K i))]
  rw [← Submodule.map_span]; rw [← SetLike.mem_coe]; rw [Submodule.map_coe]


中文:
定理 mem_span_latticeBasis
  条件: {x : (mixedSpace K)}
  证明: by
  rw [show Set.range (latticeBasis K) =
      (mixedEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (integralBasis K)) by
    rw [← Set.range_comp]; exact congrArg Set.range (funext (fun i => latticeBasis_apply K i))]
  rw [← Submodule.map_span]; rw [← SetLike.mem_coe]; rw [Submodule.map_coe]


Depends on / 依赖: RingHom, RingHom.mem_range, Set.mem_image, Set.range, Set.range_comp, SetLike, SetLike.mem_coe, Submodule, Submodule.map_coe, Submodule.map_span, exists_exists_eq_and, integralBasis, latticeBasis, latticeBasis_apply, map_coe, map_span, mem_coe, mem_image, mem_range, mem_span_integralBasis
-/
theorem mem_span_latticeBasis {x : (mixedSpace K)} :
    x in Submodule.span Int (Set.range (latticeBasis K)) ↔
      x in mixedEmbedding.integerLattice K := by
  rw [show Set.range (latticeBasis K) =
      (mixedEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (integralBasis K)) by
    rw [← Set.range_comp]; exact congrArg Set.range (funext (fun i => latticeBasis_apply K i))]
  rw [← Submodule.map_span]; rw [← SetLike.mem_coe]; rw [Submodule.map_coe]
  simp only [Set.mem_image, SetLike.mem_coe, mem_span_integralBasis K,
    RingHom.mem_range, exists_exists_eq_and]
  rfl

/--
theorem `span_latticeBasis` / 定理 `span_latticeBasis`

English:
theorem span_latticeBasis
  proof: Submodule.ext_iff.mpr fun _ => mem_span_latticeBasis K

中文:
定理 span_latticeBasis
  证明: Submodule.ext_iff.mpr fun _ => mem_span_latticeBasis K

Depends on / 依赖: Submodule, Submodule.ext_iff.mpr, ext_iff, mem_span_latticeBasis
-/
theorem span_latticeBasis :
    Submodule.span Int (Set.range (latticeBasis K)) = mixedEmbedding.integerLattice K :=
  Submodule.ext_iff.mpr fun _ => mem_span_latticeBasis K

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiscreteTopology (mixedEmbedding.integerLattice K)
  body: by
  classical
  rw [← span_latticeBasis]
  infer_instance

中文:
实例 :
  签名: 离散拓扑 (mixedEmbedding.integerLattice K)
  定义体: by
  classical
  rw [← span_latticeBasis]
  infer_instance

Depends on / 依赖: classical, infer_instance, span_latticeBasis
-/
instance : DiscreteTopology (mixedEmbedding.integerLattice K) := by
  classical
  rw [← span_latticeBasis]
  infer_instance

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZLattice Real (mixedEmbedding.integerLattice K)
  body: by
  simp_rw [← span_latticeBasis]
  infer_instance

中文:
实例 :
  签名: 是Z格 实数 (mixedEmbedding.integerLattice K)
  定义体: by
  simp_rw [← span_latticeBasis]
  infer_instance

Depends on / 依赖: infer_instance, simp_rw, span_latticeBasis
-/
instance : IsZLattice Real (mixedEmbedding.integerLattice K) := by
  simp_rw [← span_latticeBasis]
  infer_instance

open scoped Classical in
/--
theorem `fundamentalDomain_integerLattice` / 定理 `fundamentalDomain_integerLattice`

English:
theorem fundamentalDomain_integerLattice
  proof: by
  rw [← span_latticeBasis]
  exact ZSpan.isAddFundamentalDomain (latticeBasis K) _

中文:
定理 fundamentalDomain_integerLattice
  证明: by
  rw [← span_latticeBasis]
  exact ZSpan.isAddFundamentalDomain (latticeBasis K) _

Depends on / 依赖: ZSpan.isAddFundamentalDomain, isAddFundamentalDomain, latticeBasis, span_latticeBasis
-/
theorem fundamentalDomain_integerLattice :
    MeasureTheory.IsAddFundamentalDomain (mixedEmbedding.integerLattice K)
      (ZSpan.fundamentalDomain (latticeBasis K)) := by
  rw [← span_latticeBasis]
  exact ZSpan.isAddFundamentalDomain (latticeBasis K) _

/--
theorem `mem_rat_span_latticeBasis` / 定理 `mem_rat_span_latticeBasis`

English:
theorem mem_rat_span_latticeBasis
  given: (x : K)
  proof: by
  rw [← Basis.sum_repr (integralBasis K) x]; rw [map_sum]
  simp_rw [map_rat_smul]
  refine Submodule.sum_smul_mem _ _ (fun i _ => Submodule.subset_span ?_)
  rw [← latticeBasis_apply]
  exact Set.mem_range_self i

中文:
定理 mem_rat_span_latticeBasis
  条件: (x : K)
  证明: by
  rw [← Basis.sum_repr (integralBasis K) x]; rw [map_sum]
  simp_rw [map_rat_smul]
  refine Submodule.sum_smul_mem _ _ (fun i _ => Submodule.subset_span ?_)
  rw [← latticeBasis_apply]
  exact Set.mem_range_self i

Depends on / 依赖: Basis.sum_repr, Set.mem_range_self, Submodule, Submodule.subset_span, Submodule.sum_smul_mem, integralBasis, latticeBasis_apply, map_rat_smul, map_sum, mem_range_self, simp_rw, subset_span, sum_repr, sum_smul_mem
-/
theorem mem_rat_span_latticeBasis (x : K) :
    mixedEmbedding K x in Submodule.span Rat (Set.range (latticeBasis K)) := by
  rw [← Basis.sum_repr (integralBasis K) x]; rw [map_sum]
  simp_rw [map_rat_smul]
  refine Submodule.sum_smul_mem _ _ (fun i _ => Submodule.subset_span ?_)
  rw [← latticeBasis_apply]
  exact Set.mem_range_self i

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `latticeBasis_repr_apply` / 定理 `latticeBasis_repr_apply`

English:
theorem latticeBasis_repr_apply
  given: (x : K) (i : ChooseBasisIndex Int (𝓞 K))
  proof: by
  rw [← Basis.restrictScalars_repr_apply Rat _ ⟨_]; rw [mem_rat_span_latticeBasis K x⟩]; rw [eq_ratCast]; rw [Rat.cast_inj]
  let f := (mixedEmbedding K).toRatAlgHom.toLinearMap.codRestrict _
    (fun x => mem_rat_span_latticeBasis K x)
  suffices ((latticeBasis K).restrictScalars Rat).repr.toLin

中文:
定理 latticeBasis_repr_apply
  条件: (x : K) (i : ChooseBasisIndex 整数 (𝓞 K))
  证明: by
  rw [← Basis.restrictScalars_repr_apply Rat _ ⟨_]; rw [mem_rat_span_latticeBasis K x⟩]; rw [eq_ratCast]; rw [Rat.cast_inj]
  let f := (mixedEmbedding K).toRatAlgHom.toLinearMap.codRestrict _
    (fun x => mem_rat_span_latticeBasis K x)
  suffices ((latticeBasis K).restrictScalars Rat).repr.toLin

Depends on / 依赖: Basis.ext, Basis.restrictScalars_repr_apply, DFunLike, DFunLike.congr_fun, LinearMap, LinearMap.congr_fun, Rat.cast_inj, cast_inj, codRestrict, congr_fun, eq_ratCast, integralBasis, latticeBasis, mem_rat_span_latticeBasis, mixedEmbedding, repr.toLinearMap, restrict, restrictScalars, restrictScalars_repr_apply, toLinearMap
-/
theorem latticeBasis_repr_apply (x : K) (i : ChooseBasisIndex Int (𝓞 K)) :
    (latticeBasis K).repr (mixedEmbedding K x) i = (integralBasis K).repr x i := by
  rw [← Basis.restrictScalars_repr_apply Rat _ ⟨_]; rw [mem_rat_span_latticeBasis K x⟩]; rw [eq_ratCast]; rw [Rat.cast_inj]
  let f := (mixedEmbedding K).toRatAlgHom.toLinearMap.codRestrict _
    (fun x => mem_rat_span_latticeBasis K x)
  suffices ((latticeBasis K).restrictScalars Rat).repr.toLinearMap ∘ₗ f =
    (integralBasis K).repr.toLinearMap from DFunLike.congr_fun (LinearMap.congr_fun this x) i
  refine Basis.ext (integralBasis K) (fun i => ?_)
  have : f (integralBasis K i) = ((latticeBasis K).restrictScalars Rat) i := by
    apply Subtype.val_injective
    rw [LinearMap.codRestrict_apply]; rw [AlgHom.toLinearMap_apply]; rw [Basis.restrictScalars_apply]; rw [latticeBasis_apply]
    rfl
  simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this, Basis.repr_self]

variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/--
Definition of `idealLattice` / `idealLattice` 的定义

English:
abbreviation idealLattice
  signature: (K : Type*) [Field K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  body: LinearMap.range
  (mixedEmbedding K).toIntAlgHom.toLinearMap ∘ₗ ((I : Submodule (𝓞 K) K).subtype.restrictScalars Int)

中文:
缩写 idealLattice
  签名: (K : 类型) [域 K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  定义体: LinearMap.range
  (mixedEmbedding K).toIntAlgHom.toLinearMap ∘ₗ ((I : Submodule (𝓞 K) K).subtype.restrictScalars Int)

Depends on / 依赖: LinearMap, LinearMap.range
-/
abbrev idealLattice (K : Type*) [Field K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
Submodule Int (mixedSpace K) := LinearMap.range
  (mixedEmbedding K).toIntAlgHom.toLinearMap ∘ₗ ((I : Submodule (𝓞 K) K).subtype.restrictScalars Int)

/--
theorem `mem_idealLattice` / 定理 `mem_idealLattice`

English:
theorem mem_idealLattice
  statement: (K : Type*) [Field K]
  proof: by
  simp [idealLattice]

中文:
定理 mem_idealLattice
  结论: (K : 类型) [域 K]
  证明: by
  simp [idealLattice]

Depends on / 依赖: idealLattice
-/
theorem mem_idealLattice (K : Type*) [Field K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : mixedSpace K} :
    x in idealLattice K I ↔ exists y, y in (I : Set K) ∧ mixedEmbedding K y = x := by
  simp [idealLattice]

/--
theorem `det_basisOfFractionalIdeal_eq_norm` / 定理 `det_basisOfFractionalIdeal_eq_norm`

English:
theorem det_basisOfFractionalIdeal_eq_norm
  proof: by
  suffices Basis.det (latticeBasis K) ((mixedEmbedding K ∘ (basisOfFractionalIdeal K I) ∘ e)) =
      (algebraMap Rat Real) ((Basis.det (integralBasis K)) ((basisOfFractionalIdeal K I) ∘ e)) by
    rw [this]; rw [eq_ratCast]; rw [← Rat.cast_abs]; rw [← Equiv.symm_symm e]; rw [← Basis.coe_reindex]

中文:
定理 det_basisOfFractionalIdeal_eq_norm
  证明: by
  suffices Basis.det (latticeBasis K) ((mixedEmbedding K ∘ (basisOfFractionalIdeal K I) ∘ e)) =
      (algebraMap Rat Real) ((Basis.det (integralBasis K)) ((basisOfFractionalIdeal K I) ∘ e)) by
    rw [this]; rw [eq_ratCast]; rw [← Rat.cast_abs]; rw [← Equiv.symm_symm e]; rw [← Basis.coe_reindex]

Depends on / 依赖: Basis.coe_reindex, Basis.det, Basis.det_apply, Basis.toMatrix_apply, Equiv.symm_symm, Function, Matrix, Matrix.map_apply, Rat.cast_abs, RingHom, RingHom.mapMatrix_apply, RingHom.map_det, algebraMap, basisOfFractionalIdeal, cast_abs, coe_reindex, det_apply, det_basisOfFractionalIdeal_eq_absNorm, eq_ratCast, integralBasis
-/
theorem det_basisOfFractionalIdeal_eq_norm
    (e : (ChooseBasisIndex Int (𝓞 K)) ≃ (ChooseBasisIndex Int I)) :
    |Basis.det (latticeBasis K) ((mixedEmbedding K ∘ (basisOfFractionalIdeal K I) ∘ e))| =
      FractionalIdeal.absNorm I.1 := by
  suffices Basis.det (latticeBasis K) ((mixedEmbedding K ∘ (basisOfFractionalIdeal K I) ∘ e)) =
      (algebraMap Rat Real) ((Basis.det (integralBasis K)) ((basisOfFractionalIdeal K I) ∘ e)) by
    rw [this]; rw [eq_ratCast]; rw [← Rat.cast_abs]; rw [← Equiv.symm_symm e]; rw [← Basis.coe_reindex]; rw [det_basisOfFractionalIdeal_eq_absNorm K I e]
  rw [Basis.det_apply]; rw [Basis.det_apply]; rw [RingHom.map_det]
  congr
  ext i j
  simp_rw [RingHom.mapMatrix_apply, Matrix.map_apply, Basis.toMatrix_apply, Function.comp_apply]
  exact latticeBasis_repr_apply K _ i

/--
Definition of `fractionalIdealLatticeBasis` / `fractionalIdealLatticeBasis` 的定义

English:
definition fractionalIdealLatticeBasis
  signature: :
  body: by
  let e : (ChooseBasisIndex Int (𝓞 K)) ≃ (ChooseBasisIndex Int I) := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex]; rw [← finrank_eq_card_chooseBasisIndex]; rw [fractionalIdeal_rank]
  refine Basis.reindex ?_ e
  suffices IsUnit ((latticeBasis K).det ((mixedEm

中文:
定义 fractionalIdealLatticeBasis
  签名: :
  定义体: by
  let e : (ChooseBasisIndex Int (𝓞 K)) ≃ (ChooseBasisIndex Int I) := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex]; rw [← finrank_eq_card_chooseBasisIndex]; rw [fractionalIdeal_rank]
  refine Basis.reindex ?_ e
  suffices IsUnit ((latticeBasis K).det ((mixedEm

Depends on / 依赖: Basis.is_basis_iff_det, Basis.mk, Basis.reindex, ChooseBasisIndex, Fintype, Fintype.equivOfCardEq, IsUnit, abs_eq_zero, abs_eq_zero.not, basisOfFractionalIdeal, det_basisOfFractional, equivOfCardEq, finrank_eq_card_chooseBasisIndex, fractionalIdeal_rank, isUnit_iff_ne_zero, is_basis_iff_det, latticeBasis, mixedEmbedding, ne_eq, reindex
-/
def fractionalIdealLatticeBasis :
    Basis (ChooseBasisIndex Int I) Real (mixedSpace K) := by
  let e : (ChooseBasisIndex Int (𝓞 K)) ≃ (ChooseBasisIndex Int I) := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex]; rw [← finrank_eq_card_chooseBasisIndex]; rw [fractionalIdeal_rank]
  refine Basis.reindex ?_ e
  suffices IsUnit ((latticeBasis K).det ((mixedEmbedding K) ∘ (basisOfFractionalIdeal K I) ∘ e)) by
    rw [← Basis.is_basis_iff_det] at this
    exact Basis.mk this.1 (by rw [this.2])
  rw [isUnit_iff_ne_zero]; rw [ne_eq]; rw [← abs_eq_zero.not]; rw [det_basisOfFractionalIdeal_eq_norm]; rw [Rat.cast_eq_zero]; rw [FractionalIdeal.absNorm_eq_zero_iff]
  exact Units.ne_zero I

@[simp]
/--
theorem `fractionalIdealLatticeBasis_apply` / 定理 `fractionalIdealLatticeBasis_apply`

English:
theorem fractionalIdealLatticeBasis_apply
  given: (i : ChooseBasisIndex Int I)
  proof: by
  simp only [fractionalIdealLatticeBasis, Basis.coe_reindex, Basis.coe_mk, Function.comp_apply,
    Equiv.apply_symm_apply]

中文:
定理 fractionalIdealLatticeBasis_apply
  条件: (i : ChooseBasisIndex 整数 I)
  证明: by
  simp only [fractionalIdealLatticeBasis, Basis.coe_reindex, Basis.coe_mk, Function.comp_apply,
    Equiv.apply_symm_apply]

Depends on / 依赖: Basis.coe_mk, Basis.coe_reindex, Equiv.apply_symm_apply, Function, Function.comp_apply, apply_symm_apply, coe_mk, coe_reindex, comp_apply, fractionalIdealLatticeBasis
-/
theorem fractionalIdealLatticeBasis_apply (i : ChooseBasisIndex Int I) :
    fractionalIdealLatticeBasis K I i = (mixedEmbedding K) (basisOfFractionalIdeal K I i) := by
  simp only [fractionalIdealLatticeBasis, Basis.coe_reindex, Basis.coe_mk, Function.comp_apply,
    Equiv.apply_symm_apply]

/--
theorem `mem_span_fractionalIdealLatticeBasis` / 定理 `mem_span_fractionalIdealLatticeBasis`

English:
theorem mem_span_fractionalIdealLatticeBasis
  given: {x : (mixedSpace K)}
  proof: by
  rw [show Set.range (fractionalIdealLatticeBasis K I) =
        (mixedEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (basisOfFractionalIdeal K I)) by
      rw [← Set.range_comp]
      exact congr_arg Set.range (funext (fun i => fractionalIdealLatticeBasis_apply K I i))]
  rw [← Submodule.map

中文:
定理 mem_span_fractionalIdealLatticeBasis
  条件: {x : (mixedSpace K)}
  证明: by
  rw [show Set.range (fractionalIdealLatticeBasis K I) =
        (mixedEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (basisOfFractionalIdeal K I)) by
      rw [← Set.range_comp]
      exact congr_arg Set.range (funext (fun i => fractionalIdealLatticeBasis_apply K I i))]
  rw [← Submodule.map

Depends on / 依赖: Set.range, Set.range_comp, SetLike, SetLike.mem_coe, Submodule, Submodule.map_coe, Submodule.map_span, Submodule.span, basisOfFractionalIdeal, congr_arg, fractionalIdealLatticeBasis, fractionalIdealLatticeBasis_apply, map_coe, map_span, mem_coe, mem_span_basisOfFractionalIdeal, mixedEmbedding, range_comp, toIntAlgHom, toIntAlgHom.toLinearMap
-/
theorem mem_span_fractionalIdealLatticeBasis {x : (mixedSpace K)} :
    x in Submodule.span Int (Set.range (fractionalIdealLatticeBasis K I)) ↔
      x in mixedEmbedding K '' I := by
  rw [show Set.range (fractionalIdealLatticeBasis K I) =
        (mixedEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (basisOfFractionalIdeal K I)) by
      rw [← Set.range_comp]
      exact congr_arg Set.range (funext (fun i => fractionalIdealLatticeBasis_apply K I i))]
  rw [← Submodule.map_span]; rw [← SetLike.mem_coe]; rw [Submodule.map_coe]
  rw [show Submodule.span Int (Set.range (basisOfFractionalIdeal K I)) = (I : Set K) by
        ext; simp [mem_span_basisOfFractionalIdeal]]
  rfl

/--
theorem `span_idealLatticeBasis` / 定理 `span_idealLatticeBasis`

English:
theorem span_idealLatticeBasis
  proof: by
  ext x
  simp [mem_span_fractionalIdealLatticeBasis]

中文:
定理 span_idealLatticeBasis
  证明: by
  ext x
  simp [mem_span_fractionalIdealLatticeBasis]

Depends on / 依赖: mem_span_fractionalIdealLatticeBasis
-/
theorem span_idealLatticeBasis :
    (Submodule.span Int (Set.range (fractionalIdealLatticeBasis K I))) =
      (mixedEmbedding.idealLattice K I) := by
  ext x
  simp [mem_span_fractionalIdealLatticeBasis]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiscreteTopology (mixedEmbedding.idealLattice K I)
  body: by
  classical
  rw [← span_idealLatticeBasis]
  infer_instance

中文:
实例 :
  签名: 离散拓扑 (mixedEmbedding.idealLattice K I)
  定义体: by
  classical
  rw [← span_idealLatticeBasis]
  infer_instance

Depends on / 依赖: classical, infer_instance, span_idealLatticeBasis
-/
instance : DiscreteTopology (mixedEmbedding.idealLattice K I) := by
  classical
  rw [← span_idealLatticeBasis]
  infer_instance

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZLattice Real (mixedEmbedding.idealLattice K I)
  body: by
  simp_rw [← span_idealLatticeBasis]
  infer_instance

中文:
实例 :
  签名: 是Z格 实数 (mixedEmbedding.idealLattice K I)
  定义体: by
  simp_rw [← span_idealLatticeBasis]
  infer_instance

Depends on / 依赖: infer_instance, simp_rw, span_idealLatticeBasis
-/
instance : IsZLattice Real (mixedEmbedding.idealLattice K I) := by
  simp_rw [← span_idealLatticeBasis]
  infer_instance

open scoped Classical in
/--
theorem `fundamentalDomain_idealLattice` / 定理 `fundamentalDomain_idealLattice`

English:
theorem fundamentalDomain_idealLattice
  proof: by
  rw [← span_idealLatticeBasis]
  exact ZSpan.isAddFundamentalDomain (fractionalIdealLatticeBasis K I) _

中文:
定理 fundamentalDomain_idealLattice
  证明: by
  rw [← span_idealLatticeBasis]
  exact ZSpan.isAddFundamentalDomain (fractionalIdealLatticeBasis K I) _

Depends on / 依赖: ZSpan.isAddFundamentalDomain, fractionalIdealLatticeBasis, isAddFundamentalDomain, span_idealLatticeBasis
-/
theorem fundamentalDomain_idealLattice :
    MeasureTheory.IsAddFundamentalDomain (mixedEmbedding.idealLattice K I)
      (ZSpan.fundamentalDomain (fractionalIdealLatticeBasis K I)) := by
  rw [← span_idealLatticeBasis]
  exact ZSpan.isAddFundamentalDomain (fractionalIdealLatticeBasis K I) _

end integerLattice

noncomputable section

namespace euclidean

open MeasureTheory NumberField Submodule

/--
Definition of `mixedSpace` / `mixedSpace` 的定义

English:
abbreviation mixedSpace
  body: (WithLp 2 ((EuclideanSpace Real {w : InfinitePlace K // IsReal w}) ×
      (EuclideanSpace Complex {w : InfinitePlace K // IsComplex w})))

中文:
缩写 mixedSpace
  定义体: (WithLp 2 ((EuclideanSpace Real {w : InfinitePlace K // IsReal w}) ×
      (EuclideanSpace Complex {w : InfinitePlace K // IsComplex w})))
-/
protected abbrev mixedSpace :=
    (WithLp 2 ((EuclideanSpace Real {w : InfinitePlace K // IsReal w}) ×
      (EuclideanSpace Complex {w : InfinitePlace K // IsComplex w})))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Ring (euclidean.mixedSpace K)
  body: have : Ring (EuclideanSpace Real {w : InfinitePlace K // IsReal w}) := (WithLp.equiv 2 _).ring
  have : Ring (EuclideanSpace Complex {w : InfinitePlace K // IsComplex w}) := (WithLp.equiv 2 _).ring
  (WithLp.equiv 2 _).ring

中文:
实例 :
  签名: 环 (euclidean.mixedSpace K)
  定义体: have : Ring (EuclideanSpace Real {w : InfinitePlace K // IsReal w}) := (WithLp.equiv 2 _).ring
  have : Ring (EuclideanSpace Complex {w : InfinitePlace K // IsComplex w}) := (WithLp.equiv 2 _).ring
  (WithLp.equiv 2 _).ring

Depends on / 依赖: EuclideanSpace, InfinitePlace, IsComplex, IsReal, WithLp, WithLp.equiv
-/
instance : Ring (euclidean.mixedSpace K) :=
  have : Ring (EuclideanSpace Real {w : InfinitePlace K // IsReal w}) := (WithLp.equiv 2 _).ring
  have : Ring (EuclideanSpace Complex {w : InfinitePlace K // IsComplex w}) := (WithLp.equiv 2 _).ring
  (WithLp.equiv 2 _).ring

variable [NumberField K]

open scoped Classical in
/--
Definition of `toMixed` / `toMixed` 的定义

English:
definition toMixed
  signature: : (euclidean.mixedSpace K) ≃L[Real] (mixedSpace K)
  body: (WithLp.linearEquiv _ _ _).trans
.toContinuousLinearEquiv ((WithLp.linearEquiv _ _ _).prodCongr (WithLp.linearEquiv _ _ _))

中文:
定义 toMixed
  签名: : (euclidean.mixedSpace K) ≃L[实数] (mixedSpace K)
  定义体: (WithLp.linearEquiv _ _ _).trans
.toContinuousLinearEquiv ((WithLp.linearEquiv _ _ _).prodCongr (WithLp.linearEquiv _ _ _))

Depends on / 依赖: WithLp, WithLp.linearEquiv, linearEquiv, prodCongr, toContinuousLinearEquiv
-/
def toMixed : (euclidean.mixedSpace K) ≃L[Real] (mixedSpace K) :=
  (WithLp.linearEquiv _ _ _).trans
.toContinuousLinearEquiv ((WithLp.linearEquiv _ _ _).prodCongr (WithLp.linearEquiv _ _ _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nontrivial (euclidean.mixedSpace K)
  body: (toMixed K).toEquiv.nontrivial

中文:
实例 :
  签名: 非平凡 (euclidean.mixedSpace K)
  定义体: (toMixed K).toEquiv.nontrivial

Depends on / 依赖: nontrivial, toEquiv, toEquiv.nontrivial, toMixed
-/
instance : Nontrivial (euclidean.mixedSpace K) := (toMixed K).toEquiv.nontrivial

/--
theorem `finrank` / 定理 `finrank`

English:
theorem finrank
  proof: by
  rw [LinearEquiv.finrank_eq (toMixed K).toLinearEquiv]; rw [mixedEmbedding.finrank]

中文:
定理 finrank
  证明: by
  rw [LinearEquiv.finrank_eq (toMixed K).toLinearEquiv]; rw [mixedEmbedding.finrank]
-/
protected theorem finrank :
    finrank Real (euclidean.mixedSpace K) = finrank Rat K := by
  rw [LinearEquiv.finrank_eq (toMixed K).toLinearEquiv]; rw [mixedEmbedding.finrank]

open scoped Classical in
/--
Definition of `stdOrthonormalBasis` / `stdOrthonormalBasis` 的定义

English:
definition stdOrthonormalBasis
  signature: : OrthonormalBasis (index K) Real (euclidean.mixedSpace K)
  body: OrthonormalBasis.prod (EuclideanSpace.basisFun _ Real)
    ((Pi.orthonormalBasis fun _ => Complex.orthonormalBasisOneI).reindex (Equiv.sigmaEquivProd _ _))

中文:
定义 stdOrthonormalBasis
  签名: : 正交标准基 (index K) 实数 (euclidean.mixedSpace K)
  定义体: OrthonormalBasis.prod (EuclideanSpace.basisFun _ Real)
    ((Pi.orthonormalBasis fun _ => Complex.orthonormalBasisOneI).reindex (Equiv.sigmaEquivProd _ _))

Depends on / 依赖: Complex.orthonormalBasisOneI, Equiv.sigmaEquivProd, EuclideanSpace, EuclideanSpace.basisFun, OrthonormalBasis, OrthonormalBasis.prod, Pi.orthonormalBasis, basisFun, orthonormalBasis, orthonormalBasisOneI, reindex, sigmaEquivProd
-/
def stdOrthonormalBasis : OrthonormalBasis (index K) Real (euclidean.mixedSpace K) :=
  OrthonormalBasis.prod (EuclideanSpace.basisFun _ Real)
    ((Pi.orthonormalBasis fun _ => Complex.orthonormalBasisOneI).reindex (Equiv.sigmaEquivProd _ _))

open scoped Classical in
/--
theorem `stdOrthonormalBasis_map_eq` / 定理 `stdOrthonormalBasis_map_eq`

English:
theorem stdOrthonormalBasis_map_eq
  proof: by
  ext <;> rfl

中文:
定理 stdOrthonormalBasis_map_eq
  证明: by
  ext <;> rfl
-/
theorem stdOrthonormalBasis_map_eq :
    (euclidean.stdOrthonormalBasis K).toBasis.map (toMixed K).toLinearEquiv =
      mixedEmbedding.stdBasis K := by
  ext <;> rfl

open scoped Classical in
/--
theorem `volumePreserving_toMixed` / 定理 `volumePreserving_toMixed`

English:
theorem volumePreserving_toMixed
  proof: (toMixed K).continuous.measurable
  map_eq := by
    rw [← (OrthonormalBasis.addHaar_eq_volume (euclidean.stdOrthonormalBasis K))]; rw [Basis.map_addHaar]; rw [stdOrthonormalBasis_map_eq]; rw [Basis.addHaar_eq_iff]; rw [Basis.coe_parallelepiped]; rw [← measure_congr (ZSpan.fundamentalDomain_ae_paral

中文:
定理 volumePreserving_toMixed
  证明: (toMixed K).continuous.measurable
  map_eq := by
    rw [← (OrthonormalBasis.addHaar_eq_volume (euclidean.stdOrthonormalBasis K))]; rw [Basis.map_addHaar]; rw [stdOrthonormalBasis_map_eq]; rw [Basis.addHaar_eq_iff]; rw [Basis.coe_parallelepiped]; rw [← measure_congr (ZSpan.fundamentalDomain_ae_paral

Depends on / 依赖: continuous, continuous.measurable, measurable, toMixed
-/
theorem volumePreserving_toMixed :
    MeasurePreserving (toMixed K) where
  measurable := (toMixed K).continuous.measurable
  map_eq := by
    rw [← (OrthonormalBasis.addHaar_eq_volume (euclidean.stdOrthonormalBasis K))]; rw [Basis.map_addHaar]; rw [stdOrthonormalBasis_map_eq]; rw [Basis.addHaar_eq_iff]; rw [Basis.coe_parallelepiped]; rw [← measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped (stdBasis K) volume)]; rw [volume_fundamentalDomain_stdBasis K]

open scoped Classical in
/--
theorem `volumePreserving_toMixed_symm` / 定理 `volumePreserving_toMixed_symm`

English:
theorem volumePreserving_toMixed_symm
  proof: by
  have : MeasurePreserving (toMixed K).toHomeomorph.toMeasurableEquiv := volumePreserving_toMixed K
  exact this.symm

中文:
定理 volumePreserving_toMixed_symm
  证明: by
  have : MeasurePreserving (toMixed K).toHomeomorph.toMeasurableEquiv := volumePreserving_toMixed K
  exact this.symm

Depends on / 依赖: MeasurePreserving, this.symm, toHomeomorph, toHomeomorph.toMeasurableEquiv, toMeasurableEquiv, toMixed, volumePreserving_toMixed
-/
theorem volumePreserving_toMixed_symm :
    MeasurePreserving (toMixed K).symm := by
  have : MeasurePreserving (toMixed K).toHomeomorph.toMeasurableEquiv := volumePreserving_toMixed K
  exact this.symm

open scoped Classical in
/--
Definition of `integerLattice` / `integerLattice` 的定义

English:
definition integerLattice
  signature: : Submodule Int (euclidean.mixedSpace K)
  body: ZLattice.comap Real (mixedEmbedding.integerLattice K) (toMixed K).toLinearMap

中文:
定义 integerLattice
  签名: : 子模 整数 (euclidean.mixedSpace K)
  定义体: ZLattice.comap Real (mixedEmbedding.integerLattice K) (toMixed K).toLinearMap
-/
protected def integerLattice : Submodule Int (euclidean.mixedSpace K) :=
  ZLattice.comap Real (mixedEmbedding.integerLattice K) (toMixed K).toLinearMap

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiscreteTopology (euclidean.integerLattice K)
  body: by
  rw [euclidean.integerLattice]
  infer_instance

中文:
实例 :
  签名: 离散拓扑 (euclidean.integerLattice K)
  定义体: by
  rw [euclidean.integerLattice]
  infer_instance

Depends on / 依赖: euclidean, euclidean.integerLattice, infer_instance, integerLattice
-/
instance : DiscreteTopology (euclidean.integerLattice K) := by
  rw [euclidean.integerLattice]
  infer_instance

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZLattice Real (euclidean.integerLattice K)
  body: by
  simp_rw [euclidean.integerLattice]
  infer_instance

中文:
实例 :
  签名: 是Z格 实数 (euclidean.integerLattice K)
  定义体: by
  simp_rw [euclidean.integerLattice]
  infer_instance

Depends on / 依赖: euclidean, euclidean.integerLattice, infer_instance, integerLattice, simp_rw
-/
instance : IsZLattice Real (euclidean.integerLattice K) := by
  simp_rw [euclidean.integerLattice]
  infer_instance

end euclidean

end

noncomputable section plusPart

open ContinuousLinearEquiv

variable {K} (s : Set {w : InfinitePlace K // IsReal w})

open scoped Classical in
/--
Definition of `negAt` / `negAt` 的定义

English:
definition negAt
  signature: :
  body: (piCongrRight fun w => if w in s then neg Real else ContinuousLinearEquiv.refl Real Real).prodCongr
    (ContinuousLinearEquiv.refl Real _)

中文:
定义 negAt
  签名: :
  定义体: (piCongrRight fun w => if w in s then neg Real else ContinuousLinearEquiv.refl Real Real).prodCongr
    (ContinuousLinearEquiv.refl Real _)

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.refl, piCongrRight, prodCongr
-/
def negAt :
    mixedSpace K ≃L[Real] mixedSpace K :=
  (piCongrRight fun w => if w in s then neg Real else ContinuousLinearEquiv.refl Real Real).prodCongr
    (ContinuousLinearEquiv.refl Real _)

variable {s}

@[simp]
/--
theorem `negAt_apply_isReal_and_mem` / 定理 `negAt_apply_isReal_and_mem`

English:
theorem negAt_apply_isReal_and_mem
  given: (x : mixedSpace K) {w : {w // IsReal w}} (hw : w in s)
  proof: by
  simp_rw [negAt, prodCongr_apply, piCongrRight_apply, if_pos hw,
    ContinuousLinearEquiv.neg_apply]

@[simp]

中文:
定理 negAt_apply_is实数_and_mem
  条件: (x : mixedSpace K) {w : {w // Is实数 w}} (hw : w in s)
  证明: by
  simp_rw [negAt, prodCongr_apply, piCongrRight_apply, if_pos hw,
    ContinuousLinearEquiv.neg_apply]

@[simp]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.neg_apply, if_pos, neg_apply, piCongrRight_apply, prodCongr_apply, simp_rw
-/
theorem negAt_apply_isReal_and_mem (x : mixedSpace K) {w : {w // IsReal w}} (hw : w in s) :
    (negAt s x).1 w = -x.1 w := by
  simp_rw [negAt, prodCongr_apply, piCongrRight_apply, if_pos hw,
    ContinuousLinearEquiv.neg_apply]

@[simp]
/--
theorem `negAt_apply_isReal_and_notMem` / 定理 `negAt_apply_isReal_and_notMem`

English:
theorem negAt_apply_isReal_and_notMem
  given: (x : mixedSpace K) {w : {w // IsReal w}} (hw : w ∉ s)
  proof: by
  simp_rw [negAt, prodCongr_apply, piCongrRight_apply, if_neg hw,
    ContinuousLinearEquiv.refl_apply]

@[simp]

中文:
定理 negAt_apply_is实数_and_notMem
  条件: (x : mixedSpace K) {w : {w // Is实数 w}} (hw : w ∉ s)
  证明: by
  simp_rw [negAt, prodCongr_apply, piCongrRight_apply, if_neg hw,
    ContinuousLinearEquiv.refl_apply]

@[simp]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.refl_apply, if_neg, piCongrRight_apply, prodCongr_apply, refl_apply, simp_rw
-/
theorem negAt_apply_isReal_and_notMem (x : mixedSpace K) {w : {w // IsReal w}} (hw : w ∉ s) :
    (negAt s x).1 w = x.1 w := by
  simp_rw [negAt, prodCongr_apply, piCongrRight_apply, if_neg hw,
    ContinuousLinearEquiv.refl_apply]

@[simp]
/--
theorem `negAt_apply_isComplex` / 定理 `negAt_apply_isComplex`

English:
theorem negAt_apply_isComplex
  given: (x : mixedSpace K) (w : {w // IsComplex w})
  proof: rfl

@[simp]

中文:
定理 negAt_apply_isComplex
  条件: (x : mixedSpace K) (w : {w // 是复形 w})
  证明: rfl

@[simp]
-/
theorem negAt_apply_isComplex (x : mixedSpace K) (w : {w // IsComplex w}) :
    (negAt s x).2 w = x.2 w := rfl

@[simp]
/--
theorem `negAt_apply_snd` / 定理 `negAt_apply_snd`

English:
theorem negAt_apply_snd
  given: (x : mixedSpace K)
  proof: rfl

中文:
定理 negAt_apply_snd
  条件: (x : mixedSpace K)
  证明: rfl
-/
theorem negAt_apply_snd (x : mixedSpace K) :
    (negAt s x).2 = x.2 := rfl

/--
theorem `negAt_apply_norm_isReal` / 定理 `negAt_apply_norm_isReal`

English:
theorem negAt_apply_norm_isReal
  given: (x : mixedSpace K) (w : {w // IsReal w})
  proof: by
  by_cases hw : w in s <;> simp [hw]

中文:
定理 negAt_apply_norm_is实数
  条件: (x : mixedSpace K) (w : {w // Is实数 w})
  证明: by
  by_cases hw : w in s <;> simp [hw]
-/
theorem negAt_apply_norm_isReal (x : mixedSpace K) (w : {w // IsReal w}) :
    ‖(negAt s x).1 w‖ = ‖x.1 w‖ := by
  by_cases hw : w in s <;> simp [hw]

open MeasureTheory Classical in
/--
theorem `volume_preserving_negAt` / 定理 `volume_preserving_negAt`

English:
theorem volume_preserving_negAt
  given: [NumberField K]
  proof: by
  refine MeasurePreserving.prod (volume_preserving_pi fun w => ?_) (MeasurePreserving.id _)
  by_cases hw : w in s
  · simp_rw [if_pos hw]
    exact Measure.measurePreserving_neg _
  · simp_rw [if_neg hw]
    exact MeasurePreserving.id _

中文:
定理 volume_preserving_negAt
  条件: [数域 K]
  证明: by
  refine MeasurePreserving.prod (volume_preserving_pi fun w => ?_) (MeasurePreserving.id _)
  by_cases hw : w in s
  · simp_rw [if_pos hw]
    exact Measure.measurePreserving_neg _
  · simp_rw [if_neg hw]
    exact MeasurePreserving.id _

Depends on / 依赖: Measure, Measure.measurePreserving_neg, MeasurePreserving, MeasurePreserving.id, MeasurePreserving.prod, if_neg, if_pos, measurePreserving_neg, simp_rw, volume_preserving_pi
-/
theorem volume_preserving_negAt [NumberField K] :
    MeasurePreserving (negAt s) := by
  refine MeasurePreserving.prod (volume_preserving_pi fun w => ?_) (MeasurePreserving.id _)
  by_cases hw : w in s
  · simp_rw [if_pos hw]
    exact Measure.measurePreserving_neg _
  · simp_rw [if_neg hw]
    exact MeasurePreserving.id _

variable (s) in
/-- `negAt` preserves `normAtPlace`. -/
@[simp]
/--
theorem `normAtPlace_negAt` / 定理 `normAtPlace_negAt`

English:
theorem normAtPlace_negAt
  given: (x : mixedSpace K) (w : InfinitePlace K)
  proof: by
  obtain hw | hw := isReal_or_isComplex w
  · simp_rw [normAtPlace_apply_of_isReal hw, negAt_apply_norm_isReal]
  · simp_rw [normAtPlace_apply_of_isComplex hw, negAt_apply_isComplex]

中文:
定理 normAtPlace_negAt
  条件: (x : mixedSpace K) (w : InfinitePlace K)
  证明: by
  obtain hw | hw := isReal_or_isComplex w
  · simp_rw [normAtPlace_apply_of_isReal hw, negAt_apply_norm_isReal]
  · simp_rw [normAtPlace_apply_of_isComplex hw, negAt_apply_isComplex]

Depends on / 依赖: isReal_or_isComplex, negAt_apply_isComplex, negAt_apply_norm_isReal, normAtPlace_apply_of_isComplex, normAtPlace_apply_of_isReal, simp_rw
-/
theorem normAtPlace_negAt (x : mixedSpace K) (w : InfinitePlace K) :
    normAtPlace w (negAt s x) = normAtPlace w x := by
  obtain hw | hw := isReal_or_isComplex w
  · simp_rw [normAtPlace_apply_of_isReal hw, negAt_apply_norm_isReal]
  · simp_rw [normAtPlace_apply_of_isComplex hw, negAt_apply_isComplex]

/-- `negAt` preserves the `norm`. -/
@[simp]
/--
theorem `norm_negAt` / 定理 `norm_negAt`

English:
theorem norm_negAt
  given: [NumberField K] (x : mixedSpace K)
  proof: norm_eq_of_normAtPlace_eq (fun w => normAtPlace_negAt _ _ w)

中文:
定理 norm_negAt
  条件: [数域 K] (x : mixedSpace K)
  证明: norm_eq_of_normAtPlace_eq (fun w => normAtPlace_negAt _ _ w)

Depends on / 依赖: normAtPlace_negAt, norm_eq_of_normAtPlace_eq
-/
theorem norm_negAt [NumberField K] (x : mixedSpace K) :
    mixedEmbedding.norm (negAt s x) = mixedEmbedding.norm x :=
  norm_eq_of_normAtPlace_eq (fun w => normAtPlace_negAt _ _ w)

/-- `negAt` is its own inverse. -/
@[simp]
/--
theorem `negAt_symm` / 定理 `negAt_symm`

English:
theorem negAt_symm
  proof: by
  ext x w
  · by_cases hw : w in s
    · simp_rw [negAt_apply_isReal_and_mem _ hw, negAt, prodCongr_symm,
        prodCongr_apply, piCongrRight_symm_apply, if_pos hw, symm_neg,
        ContinuousLinearEquiv.neg_apply]
    · simp_rw [negAt_apply_isReal_and_notMem _ hw, negAt, prodCongr_symm,
     

中文:
定理 negAt_symm
  证明: by
  ext x w
  · by_cases hw : w in s
    · simp_rw [negAt_apply_isReal_and_mem _ hw, negAt, prodCongr_symm,
        prodCongr_apply, piCongrRight_symm_apply, if_pos hw, symm_neg,
        ContinuousLinearEquiv.neg_apply]
    · simp_rw [negAt_apply_isReal_and_notMem _ hw, negAt, prodCongr_symm,
     

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.neg_apply, if_neg, if_pos, negAt_apply_isReal_and_mem, negAt_apply_isReal_and_notMem, neg_apply, piCongrRight_symm_apply, prodCongr_apply, prodCongr_symm, refl_apply, refl_symm, simp_rw, symm_neg
-/
theorem negAt_symm :
    (negAt s).symm = negAt s := by
  ext x w
  · by_cases hw : w in s
    · simp_rw [negAt_apply_isReal_and_mem _ hw, negAt, prodCongr_symm,
        prodCongr_apply, piCongrRight_symm_apply, if_pos hw, symm_neg,
        ContinuousLinearEquiv.neg_apply]
    · simp_rw [negAt_apply_isReal_and_notMem _ hw, negAt, prodCongr_symm,
        prodCongr_apply, piCongrRight_symm_apply, if_neg hw, refl_symm,
        refl_apply]
  · rfl

/--
Definition of `signSet` / `signSet` 的定义

English:
definition signSet
  signature: (x : mixedSpace K)
  body: {w | x.1 w <= 0}

@[simp]

中文:
定义 signSet
  签名: (x : mixedSpace K)
  定义体: {w | x.1 w <= 0}

@[simp]
-/
def signSet (x : mixedSpace K) : Set {w : InfinitePlace K // IsReal w} := {w | x.1 w <= 0}

@[simp]
/--
theorem `negAt_signSet_apply_isReal` / 定理 `negAt_signSet_apply_isReal`

English:
theorem negAt_signSet_apply_isReal
  given: (x : mixedSpace K) (w : {w // IsReal w})
  proof: by
  by_cases hw : x.1 w <= 0
  · rw [negAt_apply_isReal_and_mem _ hw, Real.norm_of_nonpos hw]
  · rw [negAt_apply_isReal_and_notMem _ hw, Real.norm_of_nonneg (lt_of_not_ge hw).le]

@[simp]

中文:
定理 negAt_signSet_apply_is实数
  条件: (x : mixedSpace K) (w : {w // Is实数 w})
  证明: by
  by_cases hw : x.1 w <= 0
  · rw [negAt_apply_isReal_and_mem _ hw, Real.norm_of_nonpos hw]
  · rw [negAt_apply_isReal_and_notMem _ hw, Real.norm_of_nonneg (lt_of_not_ge hw).le]

@[simp]

Depends on / 依赖: Real.norm_of_nonneg, Real.norm_of_nonpos, lt_of_not_ge, negAt_apply_isReal_and_mem, negAt_apply_isReal_and_notMem, norm_of_nonneg, norm_of_nonpos
-/
theorem negAt_signSet_apply_isReal (x : mixedSpace K) (w : {w // IsReal w}) :
    (negAt (signSet x) x).1 w = ‖x.1 w‖ := by
  by_cases hw : x.1 w <= 0
  · rw [negAt_apply_isReal_and_mem _ hw, Real.norm_of_nonpos hw]
  · rw [negAt_apply_isReal_and_notMem _ hw, Real.norm_of_nonneg (lt_of_not_ge hw).le]

@[simp]
/--
theorem `negAt_signSet_apply_isComplex` / 定理 `negAt_signSet_apply_isComplex`

English:
theorem negAt_signSet_apply_isComplex
  given: (x : mixedSpace K) (w : {w // IsComplex w})
  proof: rfl

中文:
定理 negAt_signSet_apply_isComplex
  条件: (x : mixedSpace K) (w : {w // 是复形 w})
  证明: rfl
-/
theorem negAt_signSet_apply_isComplex (x : mixedSpace K) (w : {w // IsComplex w}) :
    (negAt (signSet x) x).2 w = x.2 w := rfl

variable (A : Set (mixedSpace K)) {x : mixedSpace K}

variable (s) in
/--
theorem `negAt_preimage` / 定理 `negAt_preimage`

English:
theorem negAt_preimage
  statement: negAt s ⁻¹' A = negAt s '' A
  proof: by
  rw [ContinuousLinearEquiv.image_eq_preimage_symm]; rw [negAt_symm]

中文:
定理 negAt_preimage
  结论: negAt s ⁻¹' A = negAt s '' A
  证明: by
  rw [ContinuousLinearEquiv.image_eq_preimage_symm]; rw [negAt_symm]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.image_eq_preimage_symm, h.symm, image_eq_preimage_symm, negAt_symm
-/
theorem negAt_preimage : negAt s ⁻¹' A = negAt s '' A := by
  rw [ContinuousLinearEquiv.image_eq_preimage_symm]; rw [negAt_symm]

/--
Definition of `plusPart` / `plusPart` 的定义

English:
abbreviation plusPart
  signature: : Set (mixedSpace K)
  body: A inter {x | forall w, 0 < x.1 w}

中文:
缩写 plusPart
  签名: : 集合 (mixedSpace K)
  定义体: A inter {x | forall w, 0 < x.1 w}

Depends on / 依赖: RelIso, RelIso.refl
-/
abbrev plusPart : Set (mixedSpace K) := A inter {x | forall w, 0 < x.1 w}

/--
theorem `neg_of_mem_negA_plusPart` / 定理 `neg_of_mem_negA_plusPart`

English:
theorem neg_of_mem_negA_plusPart
  statement: (hx : x in negAt s '' (plusPart A)) {w : {w // IsReal w}}
  proof: by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [negAt_apply_isReal_and_mem _ hw]; rw [neg_lt_zero]
  exact hy.2 w

中文:
定理 neg_of_mem_negA_plusPart
  结论: (hx : x in negAt s '' (plusPart A)) {w : {w // Is实数 w}}
  证明: by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [negAt_apply_isReal_and_mem _ hw]; rw [neg_lt_zero]
  exact hy.2 w

Depends on / 依赖: negAt_apply_isReal_and_mem, neg_lt_zero
-/
theorem neg_of_mem_negA_plusPart (hx : x in negAt s '' (plusPart A)) {w : {w // IsReal w}}
    (hw : w in s) : x.1 w < 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [negAt_apply_isReal_and_mem _ hw]; rw [neg_lt_zero]
  exact hy.2 w

/--
theorem `pos_of_notMem_negAt_plusPart` / 定理 `pos_of_notMem_negAt_plusPart`

English:
theorem pos_of_notMem_negAt_plusPart
  statement: (hx : x in negAt s '' (plusPart A)) {w : {w // IsReal w}}
  proof: by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [negAt_apply_isReal_and_notMem _ hw]
  exact hy.2 w

中文:
定理 pos_of_notMem_negAt_plusPart
  结论: (hx : x in negAt s '' (plusPart A)) {w : {w // Is实数 w}}
  证明: by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [negAt_apply_isReal_and_notMem _ hw]
  exact hy.2 w

Depends on / 依赖: negAt_apply_isReal_and_notMem
-/
theorem pos_of_notMem_negAt_plusPart (hx : x in negAt s '' (plusPart A)) {w : {w // IsReal w}}
    (hw : w ∉ s) : 0 < x.1 w := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [negAt_apply_isReal_and_notMem _ hw]
  exact hy.2 w

open scoped Function in -- required for scoped `on` notation
/--
theorem `disjoint_negAt_plusPart` / 定理 `disjoint_negAt_plusPart`

English:
theorem disjoint_negAt_plusPart
  statement: Pairwise (Disjoint on (fun s => negAt s '' (plusPart A)))
  proof: by
  intro s t hst
  refine Set.disjoint_left.mpr fun _ hx hx' => ?_
  obtain ⟨w, hw | hw⟩ : exists w, (w in s ∧ w ∉ t) ∨ (w in t ∧ w ∉ s) := Set.symmDiff_nonempty.mpr hst
· exact lt_irrefl _
      (neg_of_mem_negA_plusPart A hx hw.1).trans (pos_of_notMem_negAt_plusPart A hx' hw.2)
· exact lt_irrefl

中文:
定理 disjoint_negAt_plusPart
  结论: 两两 (Disjoint on (fun s => negAt s '' (plusPart A)))
  证明: by
  intro s t hst
  refine Set.disjoint_left.mpr fun _ hx hx' => ?_
  obtain ⟨w, hw | hw⟩ : exists w, (w in s ∧ w ∉ t) ∨ (w in t ∧ w ∉ s) := Set.symmDiff_nonempty.mpr hst
· exact lt_irrefl _
      (neg_of_mem_negA_plusPart A hx hw.1).trans (pos_of_notMem_negAt_plusPart A hx' hw.2)
· exact lt_irrefl

Depends on / 依赖: Set.disjoint_left.mpr, Set.symmDiff_nonempty.mpr, disjoint_left, lt_irrefl, neg_of_mem_negA_plusPart, pos_of_notMem_negAt_plusPart, symmDiff_nonempty
-/
theorem disjoint_negAt_plusPart : Pairwise (Disjoint on (fun s => negAt s '' (plusPart A))) := by
  intro s t hst
  refine Set.disjoint_left.mpr fun _ hx hx' => ?_
  obtain ⟨w, hw | hw⟩ : exists w, (w in s ∧ w ∉ t) ∨ (w in t ∧ w ∉ s) := Set.symmDiff_nonempty.mpr hst
· exact lt_irrefl _
      (neg_of_mem_negA_plusPart A hx hw.1).trans (pos_of_notMem_negAt_plusPart A hx' hw.2)
· exact lt_irrefl _
      (neg_of_mem_negA_plusPart A hx' hw.1).trans (pos_of_notMem_negAt_plusPart A hx hw.2)

-- We will assume from now that `A` is symmetric at real places
variable (hA : forall x, x in A ↔ (fun w => ‖x.1 w‖, x.2) in A)

include hA in
/--
theorem `mem_negAt_plusPart_of_mem` / 定理 `mem_negAt_plusPart_of_mem`

English:
theorem mem_negAt_plusPart_of_mem
  given: (hx₁ : x in A) (hx₂ : forall w, x.1 w != 0)
  proof: by
  refine ⟨fun hx => ⟨fun _ hw => neg_of_mem_negA_plusPart A hx hw,
      fun _ hw => pos_of_notMem_negAt_plusPart A hx hw⟩,
      fun ⟨h₁, h₂⟩ =>
        ⟨(fun w => ‖x.1 w‖, x.2), ⟨(hA x).mp hx₁, fun w => norm_pos_iff.mpr (hx₂ w)⟩, ?_⟩⟩
  ext w
  · by_cases hw : w in s
    · simp [negAt_apply_isR

中文:
定理 mem_negAt_plusPart_of_mem
  条件: (hx₁ : x in A) (hx₂ : 对任意 w, x.1 w != 0)
  证明: by
  refine ⟨fun hx => ⟨fun _ hw => neg_of_mem_negA_plusPart A hx hw,
      fun _ hw => pos_of_notMem_negAt_plusPart A hx hw⟩,
      fun ⟨h₁, h₂⟩ =>
        ⟨(fun w => ‖x.1 w‖, x.2), ⟨(hA x).mp hx₁, fun w => norm_pos_iff.mpr (hx₂ w)⟩, ?_⟩⟩
  ext w
  · by_cases hw : w in s
    · simp [negAt_apply_isR

Depends on / 依赖: abs_of_neg, abs_of_pos, negAt_apply_isReal_and_mem, negAt_apply_isReal_and_notMem, neg_of_mem_negA_plusPart, norm_pos_iff, norm_pos_iff.mpr, pos_of_notMem_negAt_plusPart
-/
theorem mem_negAt_plusPart_of_mem (hx₁ : x in A) (hx₂ : forall w, x.1 w != 0) :
    x in negAt s '' (plusPart A) ↔ (forall w, w in s -> x.1 w < 0) ∧ (forall w, w ∉ s -> x.1 w > 0) := by
  refine ⟨fun hx => ⟨fun _ hw => neg_of_mem_negA_plusPart A hx hw,
      fun _ hw => pos_of_notMem_negAt_plusPart A hx hw⟩,
      fun ⟨h₁, h₂⟩ =>
        ⟨(fun w => ‖x.1 w‖, x.2), ⟨(hA x).mp hx₁, fun w => norm_pos_iff.mpr (hx₂ w)⟩, ?_⟩⟩
  ext w
  · by_cases hw : w in s
    · simp [negAt_apply_isReal_and_mem _ hw, abs_of_neg (h₁ w hw)]
    · simp [negAt_apply_isReal_and_notMem _ hw, abs_of_pos (h₂ w hw)]
  · rfl

include hA in
/--
theorem `iUnion_negAt_plusPart_union` / 定理 `iUnion_negAt_plusPart_union`

English:
theorem iUnion_negAt_plusPart_union
  proof: by
  ext x
  rw [Set.mem_union]; rw [Set.mem_inter_iff]; rw [Set.mem_iUnion]; rw [Set.mem_iUnion]
  refine ⟨?_, fun h => ?_⟩
  · rintro (⟨s, ⟨x, ⟨hx, _⟩, rfl⟩⟩ | h)
    · simp_rw +singlePass [hA, negAt_apply_norm_isReal, negAt_apply_snd]
      rwa [← hA]
    · exact h.left
  · obtain hx | hx := exis

中文:
定理 iUnion_negAt_plusPart_union
  证明: by
  ext x
  rw [Set.mem_union]; rw [Set.mem_inter_iff]; rw [Set.mem_iUnion]; rw [Set.mem_iUnion]
  refine ⟨?_, fun h => ?_⟩
  · rintro (⟨s, ⟨x, ⟨hx, _⟩, rfl⟩⟩ | h)
    · simp_rw +singlePass [hA, negAt_apply_norm_isReal, negAt_apply_snd]
      rwa [← hA]
    · exact h.left
  · obtain hx | hx := exis

Depends on / 依赖: Or.inl, Or.inr, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_union, exists_or_forall_not, h.left, lt_of_le_of_ne, mem_iUnion, mem_inter_iff, mem_negAt_plusPart_of_mem, mem_union, negAt_apply_norm_isReal, negAt_apply_snd, signSet, simp_rw, singlePass
-/
theorem iUnion_negAt_plusPart_union :
    (⋃ s, negAt s '' (plusPart A)) union (A inter (⋃ w, {x | x.1 w = 0})) = A := by
  ext x
  rw [Set.mem_union]; rw [Set.mem_inter_iff]; rw [Set.mem_iUnion]; rw [Set.mem_iUnion]
  refine ⟨?_, fun h => ?_⟩
  · rintro (⟨s, ⟨x, ⟨hx, _⟩, rfl⟩⟩ | h)
    · simp_rw +singlePass [hA, negAt_apply_norm_isReal, negAt_apply_snd]
      rwa [← hA]
    · exact h.left
  · obtain hx | hx := exists_or_forall_not (fun w => x.1 w = 0)
    · exact Or.inr ⟨h, hx⟩
    · refine Or.inl ⟨signSet x,
        (mem_negAt_plusPart_of_mem A hA h hx).mpr ⟨fun w hw => ?_, fun w hw => ?_⟩⟩
      · exact lt_of_le_of_ne hw (hx w)
      · exact lt_of_le_of_ne (lt_of_not_ge hw).le (Ne.symm (hx w))

open MeasureTheory

variable [NumberField K]

include hA in
open scoped Classical in
/--
theorem `iUnion_negAt_plusPart_ae` / 定理 `iUnion_negAt_plusPart_ae`

English:
theorem iUnion_negAt_plusPart_ae
  proof: by
  nth_rewrite 2 [← iUnion_negAt_plusPart_union A hA]
  refine (MeasureTheory.union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr ?_)).symm
  exact measure_mono_null Set.inter_subset_right
    (measure_iUnion_null_iff.mpr fun _ => volume_eq_zero _)

中文:
定理 iUnion_negAt_plusPart_ae
  证明: by
  nth_rewrite 2 [← iUnion_negAt_plusPart_union A hA]
  refine (MeasureTheory.union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr ?_)).symm
  exact measure_mono_null Set.inter_subset_right
    (measure_iUnion_null_iff.mpr fun _ => volume_eq_zero _)

Depends on / 依赖: MeasureTheory, MeasureTheory.union_ae_eq_left_of_ae_eq_empty, Set.inter_subset_right, ae_eq_empty, ae_eq_empty.mpr, iUnion_negAt_plusPart_union, inter_subset_right, measure_iUnion_null_iff, measure_iUnion_null_iff.mpr, measure_mono_null, nth_rewrite, union_ae_eq_left_of_ae_eq_empty, volume_eq_zero
-/
theorem iUnion_negAt_plusPart_ae :
    ⋃ s, negAt s '' (plusPart A) =ᵐ[volume] A := by
  nth_rewrite 2 [← iUnion_negAt_plusPart_union A hA]
  refine (MeasureTheory.union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr ?_)).symm
  exact measure_mono_null Set.inter_subset_right
    (measure_iUnion_null_iff.mpr fun _ => volume_eq_zero _)

variable {A} in
/--
theorem `measurableSet_plusPart` / 定理 `measurableSet_plusPart`

English:
theorem measurableSet_plusPart
  given: (hm : MeasurableSet A)
  proof: by
  convert_to MeasurableSet (A inter (⋂ w, {x | 0 < x.1 w}))
  · ext; simp
  · refine hm.inter (MeasurableSet.iInter fun _ => ?_)
    exact measurableSet_lt measurable_const (by fun_prop)

中文:
定理 measurableSet_plusPart
  条件: (hm : 可测集 A)
  证明: by
  convert_to MeasurableSet (A inter (⋂ w, {x | 0 < x.1 w}))
  · ext; simp
  · refine hm.inter (MeasurableSet.iInter fun _ => ?_)
    exact measurableSet_lt measurable_const (by fun_prop)

Depends on / 依赖: MeasurableSet, MeasurableSet.iInter, convert_to, fun_prop, hm.inter, iInter, measurableSet_lt, measurable_const
-/
theorem measurableSet_plusPart (hm : MeasurableSet A) :
    MeasurableSet (plusPart A) := by
  convert_to MeasurableSet (A inter (⋂ w, {x | 0 < x.1 w}))
  · ext; simp
  · refine hm.inter (MeasurableSet.iInter fun _ => ?_)
    exact measurableSet_lt measurable_const (by fun_prop)

variable (s) in
/--
theorem `measurableSet_negAt_plusPart` / 定理 `measurableSet_negAt_plusPart`

English:
theorem measurableSet_negAt_plusPart
  given: (hm : MeasurableSet A)
  proof: negAt_preimage s _ ▸ (measurableSet_plusPart hm).preimage (negAt s).continuous.measurable

中文:
定理 measurableSet_negAt_plusPart
  条件: (hm : 可测集 A)
  证明: negAt_preimage s _ ▸ (measurableSet_plusPart hm).preimage (negAt s).continuous.measurable

Depends on / 依赖: continuous, continuous.measurable, measurable, measurableSet_plusPart, negAt_preimage, preimage
-/
theorem measurableSet_negAt_plusPart (hm : MeasurableSet A) :
    MeasurableSet (negAt s '' (plusPart A)) :=
  negAt_preimage s _ ▸ (measurableSet_plusPart hm).preimage (negAt s).continuous.measurable

variable {A}

open scoped Classical in
/--
theorem `volume_negAt_plusPart` / 定理 `volume_negAt_plusPart`

English:
theorem volume_negAt_plusPart
  given: (hm : MeasurableSet A)
  proof: by
  rw [← negAt_symm]; rw [ContinuousLinearEquiv.image_symm_eq_preimage]; rw [volume_preserving_negAt.measure_preimage (measurableSet_plusPart hm).nullMeasurableSet]

include hA in

中文:
定理 volume_negAt_plusPart
  条件: (hm : 可测集 A)
  证明: by
  rw [← negAt_symm]; rw [ContinuousLinearEquiv.image_symm_eq_preimage]; rw [volume_preserving_negAt.measure_preimage (measurableSet_plusPart hm).nullMeasurableSet]

include hA in

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.image_symm_eq_preimage, image_symm_eq_preimage, measurableSet_plusPart, measure_preimage, negAt_symm, nullMeasurableSet, volume_preserving_negAt, volume_preserving_negAt.measure_preimage
-/
theorem volume_negAt_plusPart (hm : MeasurableSet A) :
    volume (negAt s '' (plusPart A)) = volume (plusPart A) := by
  rw [← negAt_symm]; rw [ContinuousLinearEquiv.image_symm_eq_preimage]; rw [volume_preserving_negAt.measure_preimage (measurableSet_plusPart hm).nullMeasurableSet]

include hA in
open scoped Classical in
/--
theorem `volume_eq_two_pow_mul_volume_plusPart` / 定理 `volume_eq_two_pow_mul_volume_plusPart`

English:
theorem volume_eq_two_pow_mul_volume_plusPart
  given: (hm : MeasurableSet A)
  proof: by
  simp only [← measure_congr (iUnion_negAt_plusPart_ae A hA),
    measure_iUnion (disjoint_negAt_plusPart A) (fun _ => measurableSet_negAt_plusPart _ A hm),
    volume_negAt_plusPart hm, tsum_fintype, sum_const, card_univ, Fintype.card_set, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat, nrRealPl

中文:
定理 volume_eq_two_pow_mul_volume_plusPart
  条件: (hm : 可测集 A)
  证明: by
  simp only [← measure_congr (iUnion_negAt_plusPart_ae A hA),
    measure_iUnion (disjoint_negAt_plusPart A) (fun _ => measurableSet_negAt_plusPart _ A hm),
    volume_negAt_plusPart hm, tsum_fintype, sum_const, card_univ, Fintype.card_set, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat, nrRealPl

Depends on / 依赖: Fintype, Fintype.card_set, Nat.cast_ofNat, Nat.cast_pow, card_set, card_univ, cast_ofNat, cast_pow, disjoint_negAt_plusPart, iUnion_negAt_plusPart_ae, measurableSet_negAt_plusPart, measure_congr, measure_iUnion, nrRealPlaces, nsmul_eq_mul, sum_const, tsum_fintype, volume_negAt_plusPart
-/
theorem volume_eq_two_pow_mul_volume_plusPart (hm : MeasurableSet A) :
    volume A = 2 ^ nrRealPlaces K * volume (plusPart A) := by
  simp only [← measure_congr (iUnion_negAt_plusPart_ae A hA),
    measure_iUnion (disjoint_negAt_plusPart A) (fun _ => measurableSet_negAt_plusPart _ A hm),
    volume_negAt_plusPart hm, tsum_fintype, sum_const, card_univ, Fintype.card_set, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat, nrRealPlaces]

end plusPart

noncomputable section realSpace

open MeasureTheory

/--
Definition of `realSpace` / `realSpace` 的定义

English:
abbreviation realSpace
  body: InfinitePlace K -> Real

中文:
缩写 realSpace
  定义体: InfinitePlace K -> Real

Depends on / 依赖: InfinitePlace
-/
abbrev realSpace := InfinitePlace K -> Real

variable {K}

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `realSpace.volume_eq_zero` / 定理 `realSpace.volume_eq_zero`

English:
theorem realSpace.volume_eq_zero
  given: [NumberField K] (w : InfinitePlace K)
  proof: by
  let A : AffineSubspace Real (realSpace K) :=
    Submodule.toAffineSubspace (Submodule.mk ⟨⟨{x | x w = 0}, by simp_all⟩, rfl⟩ (by simp_all))
  convert! Measure.addHaar_affineSubspace volume A fun h => ?_
  simpa [A] using (h ▸ Set.mem_univ _ : 1 in A)

中文:
定理 realSpace.volume_eq_zero
  条件: [数域 K] (w : InfinitePlace K)
  证明: by
  let A : AffineSubspace Real (realSpace K) :=
    Submodule.toAffineSubspace (Submodule.mk ⟨⟨{x | x w = 0}, by simp_all⟩, rfl⟩ (by simp_all))
  convert! Measure.addHaar_affineSubspace volume A fun h => ?_
  simpa [A] using (h ▸ Set.mem_univ _ : 1 in A)

Depends on / 依赖: AffineSubspace, Measure, Measure.addHaar_affineSubspace, Set.mem_univ, Submodule, Submodule.mk, Submodule.toAffineSubspace, addHaar_affineSubspace, convert, mem_univ, realSpace, toAffineSubspace, volume
-/
theorem realSpace.volume_eq_zero [NumberField K] (w : InfinitePlace K) :
    volume ({x : realSpace K | x w = 0}) = 0 := by
  let A : AffineSubspace Real (realSpace K) :=
    Submodule.toAffineSubspace (Submodule.mk ⟨⟨{x | x w = 0}, by simp_all⟩, rfl⟩ (by simp_all))
  convert! Measure.addHaar_affineSubspace volume A fun h => ?_
  simpa [A] using (h ▸ Set.mem_univ _ : 1 in A)

/--
Definition of `mixedSpaceOfRealSpace` / `mixedSpaceOfRealSpace` 的定义

English:
definition mixedSpaceOfRealSpace
  signature: : realSpace K ->L[Real] mixedSpace K
  body: .prod (.pi fun w => .proj w.1) (.pi fun w => Complex.ofRealCLM.comp (.proj w.1))

中文:
定义 mixedSpaceOf实数Space
  签名: : realSpace K ->L[实数] mixedSpace K
  定义体: .prod (.pi fun w => .proj w.1) (.pi fun w => Complex.ofRealCLM.comp (.proj w.1))

Depends on / 依赖: Complex.ofRealCLM.comp, ofRealCLM
-/
def mixedSpaceOfRealSpace : realSpace K ->L[Real] mixedSpace K :=
  .prod (.pi fun w => .proj w.1) (.pi fun w => Complex.ofRealCLM.comp (.proj w.1))

/--
theorem `mixedSpaceOfRealSpace_apply` / 定理 `mixedSpaceOfRealSpace_apply`

English:
theorem mixedSpaceOfRealSpace_apply
  given: (x : realSpace K)
  proof: rfl

中文:
定理 mixedSpaceOf实数Space_apply
  条件: (x : realSpace K)
  证明: rfl
-/
theorem mixedSpaceOfRealSpace_apply (x : realSpace K) :
    mixedSpaceOfRealSpace x = ⟨fun w => x w.1, fun w => x w.1⟩ := rfl

variable (K) in
/--
theorem `injective_mixedSpaceOfRealSpace` / 定理 `injective_mixedSpaceOfRealSpace`

English:
theorem injective_mixedSpaceOfRealSpace
  proof: by
  refine (injective_iff_map_eq_zero mixedSpaceOfRealSpace).mpr fun _ h => ?_
  rw [mixedSpaceOfRealSpace_apply]; rw [Prod.mk_eq_zero]; rw [funext_iff]; rw [funext_iff] at h
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · exact h.1 ⟨w, hw⟩
· exact Complex.ofReal_inj.mp h.2 ⟨w, hw⟩

中文:
定理 injective_mixedSpaceOf实数Space
  证明: by
  refine (injective_iff_map_eq_zero mixedSpaceOfRealSpace).mpr fun _ h => ?_
  rw [mixedSpaceOfRealSpace_apply]; rw [Prod.mk_eq_zero]; rw [funext_iff]; rw [funext_iff] at h
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · exact h.1 ⟨w, hw⟩
· exact Complex.ofReal_inj.mp h.2 ⟨w, hw⟩

Depends on / 依赖: Complex.ofReal_inj.mp, Prod.mk_eq_zero, funext_iff, injective_iff_map_eq_zero, isReal_or_isComplex, mixedSpaceOfRealSpace, mixedSpaceOfRealSpace_apply, mk_eq_zero, ofReal_inj
-/
theorem injective_mixedSpaceOfRealSpace :
    Function.Injective (mixedSpaceOfRealSpace : realSpace K -> mixedSpace K) := by
  refine (injective_iff_map_eq_zero mixedSpaceOfRealSpace).mpr fun _ h => ?_
  rw [mixedSpaceOfRealSpace_apply]; rw [Prod.mk_eq_zero]; rw [funext_iff]; rw [funext_iff] at h
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · exact h.1 ⟨w, hw⟩
· exact Complex.ofReal_inj.mp h.2 ⟨w, hw⟩

/--
theorem `normAtPlace_mixedSpaceOfRealSpace` / 定理 `normAtPlace_mixedSpaceOfRealSpace`

English:
theorem normAtPlace_mixedSpaceOfRealSpace
  given: {x : realSpace K} {w : InfinitePlace K} (hx : 0 <= x w)
  proof: by
  simp only [mixedSpaceOfRealSpace_apply]
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_of_isReal hw, Real.norm_of_nonneg hx]
  · rw [normAtPlace_apply_of_isComplex hw, Complex.norm_of_nonneg hx]

中文:
定理 normAtPlace_mixedSpaceOf实数Space
  条件: {x : realSpace K} {w : InfinitePlace K} (hx : 0 <= x w)
  证明: by
  simp only [mixedSpaceOfRealSpace_apply]
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_of_isReal hw, Real.norm_of_nonneg hx]
  · rw [normAtPlace_apply_of_isComplex hw, Complex.norm_of_nonneg hx]

Depends on / 依赖: Complex.norm_of_nonneg, Real.norm_of_nonneg, isReal_or_isComplex, mixedSpaceOfRealSpace_apply, normAtPlace_apply_of_isComplex, normAtPlace_apply_of_isReal, norm_of_nonneg
-/
theorem normAtPlace_mixedSpaceOfRealSpace {x : realSpace K} {w : InfinitePlace K} (hx : 0 <= x w) :
    normAtPlace w (mixedSpaceOfRealSpace x) = x w := by
  simp only [mixedSpaceOfRealSpace_apply]
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_of_isReal hw, Real.norm_of_nonneg hx]
  · rw [normAtPlace_apply_of_isComplex hw, Complex.norm_of_nonneg hx]

open scoped Classical in
/--
Definition of `normAtComplexPlaces` / `normAtComplexPlaces` 的定义

English:
abbreviation normAtComplexPlaces
  signature: (x : mixedSpace K)
  body: fun w => if hw : w.IsReal then x.1 ⟨w, hw⟩ else normAtPlace w x

@[simp]

中文:
缩写 normAtComplexPlaces
  签名: (x : mixedSpace K)
  定义体: fun w => if hw : w.IsReal then x.1 ⟨w, hw⟩ else normAtPlace w x

@[simp]

Depends on / 依赖: IsReal, normAtPlace, w.IsReal
-/
abbrev normAtComplexPlaces (x : mixedSpace K) : realSpace K :=
    fun w => if hw : w.IsReal then x.1 ⟨w, hw⟩ else normAtPlace w x

@[simp]
/--
theorem `normAtComplexPlaces_apply_isReal` / 定理 `normAtComplexPlaces_apply_isReal`

English:
theorem normAtComplexPlaces_apply_isReal
  given: {x : mixedSpace K} (w : {w // IsReal w})
  proof: by
  rw [normAtComplexPlaces]; rw [dif_pos]

@[simp]

中文:
定理 normAtComplexPlaces_apply_is实数
  条件: {x : mixedSpace K} (w : {w // Is实数 w})
  证明: by
  rw [normAtComplexPlaces]; rw [dif_pos]

@[simp]

Depends on / 依赖: dif_pos, normAtComplexPlaces
-/
theorem normAtComplexPlaces_apply_isReal {x : mixedSpace K} (w : {w // IsReal w}) :
    normAtComplexPlaces x w = x.1 w := by
  rw [normAtComplexPlaces]; rw [dif_pos]

@[simp]
/--
theorem `normAtComplexPlaces_apply_isComplex` / 定理 `normAtComplexPlaces_apply_isComplex`

English:
theorem normAtComplexPlaces_apply_isComplex
  given: {x : mixedSpace K} (w : {w // IsComplex w})
  proof: by
  rw [normAtComplexPlaces]; rw [dif_neg (not_isReal_iff_isComplex.mpr w.prop)]; rw [normAtPlace_apply_of_isComplex]

中文:
定理 normAtComplexPlaces_apply_isComplex
  条件: {x : mixedSpace K} (w : {w // 是复形 w})
  证明: by
  rw [normAtComplexPlaces]; rw [dif_neg (not_isReal_iff_isComplex.mpr w.prop)]; rw [normAtPlace_apply_of_isComplex]

Depends on / 依赖: dif_neg, normAtComplexPlaces, normAtPlace_apply_of_isComplex, not_isReal_iff_isComplex, not_isReal_iff_isComplex.mpr, w.prop
-/
theorem normAtComplexPlaces_apply_isComplex {x : mixedSpace K} (w : {w // IsComplex w}) :
    normAtComplexPlaces x w = ‖x.2 w‖ := by
  rw [normAtComplexPlaces]; rw [dif_neg (not_isReal_iff_isComplex.mpr w.prop)]; rw [normAtPlace_apply_of_isComplex]

/--
theorem `normAtComplexPlaces_mixedSpaceOfRealSpace` / 定理 `normAtComplexPlaces_mixedSpaceOfRealSpace`

English:
theorem normAtComplexPlaces_mixedSpaceOfRealSpace
  statement: {x : realSpace K}
  proof: by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtComplexPlaces_apply_isReal ⟨w, hw⟩, mixedSpaceOfRealSpace_apply]
  · rw [normAtComplexPlaces_apply_isComplex ⟨w, hw⟩, mixedSpaceOfRealSpace_apply,
      Complex.norm_of_nonneg (hx w hw)]

中文:
定理 normAtComplexPlaces_mixedSpaceOf实数Space
  结论: {x : realSpace K}
  证明: by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtComplexPlaces_apply_isReal ⟨w, hw⟩, mixedSpaceOfRealSpace_apply]
  · rw [normAtComplexPlaces_apply_isComplex ⟨w, hw⟩, mixedSpaceOfRealSpace_apply,
      Complex.norm_of_nonneg (hx w hw)]

Depends on / 依赖: Complex.norm_of_nonneg, isReal_or_isComplex, mixedSpaceOfRealSpace_apply, normAtComplexPlaces_apply_isComplex, normAtComplexPlaces_apply_isReal, norm_of_nonneg
-/
theorem normAtComplexPlaces_mixedSpaceOfRealSpace {x : realSpace K}
    (hx : forall w, IsComplex w -> 0 <= x w) :
    normAtComplexPlaces (mixedSpaceOfRealSpace x) = x := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtComplexPlaces_apply_isReal ⟨w, hw⟩, mixedSpaceOfRealSpace_apply]
  · rw [normAtComplexPlaces_apply_isComplex ⟨w, hw⟩, mixedSpaceOfRealSpace_apply,
      Complex.norm_of_nonneg (hx w hw)]

/--
Definition of `normAtAllPlaces` / `normAtAllPlaces` 的定义

English:
abbreviation normAtAllPlaces
  signature: (x : mixedSpace K)
  body: fun w => normAtPlace w x

@[simp]

中文:
缩写 normAtAllPlaces
  签名: (x : mixedSpace K)
  定义体: fun w => normAtPlace w x

@[simp]

Depends on / 依赖: normAtPlace
-/
abbrev normAtAllPlaces (x : mixedSpace K) : realSpace K :=
    fun w => normAtPlace w x

@[simp]
/--
theorem `normAtAllPlaces_apply` / 定理 `normAtAllPlaces_apply`

English:
theorem normAtAllPlaces_apply
  given: (x : mixedSpace K) (w : InfinitePlace K)
  proof: rfl

中文:
定理 normAtAllPlaces_apply
  条件: (x : mixedSpace K) (w : InfinitePlace K)
  证明: rfl
-/
theorem normAtAllPlaces_apply (x : mixedSpace K) (w : InfinitePlace K) :
    normAtAllPlaces x w = normAtPlace w x := rfl

variable (K) in
/--
theorem `continuous_normAtAllPlaces` / 定理 `continuous_normAtAllPlaces`

English:
theorem continuous_normAtAllPlaces
  proof: by fun_prop

中文:
定理 continuous_normAtAllPlaces
  证明: by fun_prop

Depends on / 依赖: fun_prop
-/
theorem continuous_normAtAllPlaces :
    Continuous (normAtAllPlaces : mixedSpace K -> realSpace K) := by fun_prop

/--
theorem `normAtAllPlaces_nonneg` / 定理 `normAtAllPlaces_nonneg`

English:
theorem normAtAllPlaces_nonneg
  given: (x : mixedSpace K) (w : InfinitePlace K)
  proof: normAtPlace_nonneg _ _

中文:
定理 normAtAllPlaces_nonneg
  条件: (x : mixedSpace K) (w : InfinitePlace K)
  证明: normAtPlace_nonneg _ _

Depends on / 依赖: normAtPlace_nonneg
-/
theorem normAtAllPlaces_nonneg (x : mixedSpace K) (w : InfinitePlace K) :
    0 <= normAtAllPlaces x w := normAtPlace_nonneg _ _

/--
theorem `normAtAllPlaces_mixedSpaceOfRealSpace` / 定理 `normAtAllPlaces_mixedSpaceOfRealSpace`

English:
theorem normAtAllPlaces_mixedSpaceOfRealSpace
  given: {x : realSpace K} (hx : forall w, 0 <= x w)
  proof: by
  ext
  rw [normAtAllPlaces_apply]; rw [normAtPlace_mixedSpaceOfRealSpace (hx _)]

中文:
定理 normAtAllPlaces_mixedSpaceOf实数Space
  条件: {x : realSpace K} (hx : 对任意 w, 0 <= x w)
  证明: by
  ext
  rw [normAtAllPlaces_apply]; rw [normAtPlace_mixedSpaceOfRealSpace (hx _)]

Depends on / 依赖: normAtAllPlaces_apply, normAtPlace_mixedSpaceOfRealSpace
-/
theorem normAtAllPlaces_mixedSpaceOfRealSpace {x : realSpace K} (hx : forall w, 0 <= x w) :
    normAtAllPlaces (mixedSpaceOfRealSpace x) = x := by
  ext
  rw [normAtAllPlaces_apply]; rw [normAtPlace_mixedSpaceOfRealSpace (hx _)]

/--
theorem `normAtAllPlaces_mixedEmbedding` / 定理 `normAtAllPlaces_mixedEmbedding`

English:
theorem normAtAllPlaces_mixedEmbedding
  given: (x : K) (w : InfinitePlace K)
  proof: by
  rw [normAtAllPlaces_apply]; rw [normAtPlace_apply]

中文:
定理 normAtAllPlaces_mixedEmbedding
  条件: (x : K) (w : InfinitePlace K)
  证明: by
  rw [normAtAllPlaces_apply]; rw [normAtPlace_apply]

Depends on / 依赖: normAtAllPlaces_apply, normAtPlace_apply
-/
theorem normAtAllPlaces_mixedEmbedding (x : K) (w : InfinitePlace K) :
    normAtAllPlaces (mixedEmbedding K x) w = w x := by
  rw [normAtAllPlaces_apply]; rw [normAtPlace_apply]

/--
theorem `normAtAllPlaces_normAtAllPlaces` / 定理 `normAtAllPlaces_normAtAllPlaces`

English:
theorem normAtAllPlaces_normAtAllPlaces
  given: (x : mixedSpace K)
  proof: normAtAllPlaces_mixedSpaceOfRealSpace fun _ => (normAtAllPlaces_nonneg _ _)

中文:
定理 normAtAllPlaces_normAtAllPlaces
  条件: (x : mixedSpace K)
  证明: normAtAllPlaces_mixedSpaceOfRealSpace fun _ => (normAtAllPlaces_nonneg _ _)

Depends on / 依赖: normAtAllPlaces_mixedSpaceOfRealSpace, normAtAllPlaces_nonneg
-/
theorem normAtAllPlaces_normAtAllPlaces (x : mixedSpace K) :
    normAtAllPlaces (mixedSpaceOfRealSpace (normAtAllPlaces x)) = normAtAllPlaces x :=
  normAtAllPlaces_mixedSpaceOfRealSpace fun _ => (normAtAllPlaces_nonneg _ _)

/--
theorem `normAtAllPlaces_norm_at_real_places` / 定理 `normAtAllPlaces_norm_at_real_places`

English:
theorem normAtAllPlaces_norm_at_real_places
  given: (x : mixedSpace K)
  proof: by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · simp_rw [normAtAllPlaces, normAtPlace_apply_of_isReal hw, norm_norm]
  · simp_rw [normAtAllPlaces, normAtPlace_apply_of_isComplex hw]

中文:
定理 normAtAllPlaces_norm_at_real_places
  条件: (x : mixedSpace K)
  证明: by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · simp_rw [normAtAllPlaces, normAtPlace_apply_of_isReal hw, norm_norm]
  · simp_rw [normAtAllPlaces, normAtPlace_apply_of_isComplex hw]

Depends on / 依赖: isReal_or_isComplex, normAtAllPlaces, normAtPlace_apply_of_isComplex, normAtPlace_apply_of_isReal, norm_norm, simp_rw
-/
theorem normAtAllPlaces_norm_at_real_places (x : mixedSpace K) :
    normAtAllPlaces (fun w => ‖x.1 w‖, x.2) = normAtAllPlaces x := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · simp_rw [normAtAllPlaces, normAtPlace_apply_of_isReal hw, norm_norm]
  · simp_rw [normAtAllPlaces, normAtPlace_apply_of_isComplex hw]

/--
theorem `normAtComplexPlaces_normAtAllPlaces` / 定理 `normAtComplexPlaces_normAtAllPlaces`

English:
theorem normAtComplexPlaces_normAtAllPlaces
  given: (x : mixedSpace K)
  proof: normAtComplexPlaces_mixedSpaceOfRealSpace fun _ _ => (normAtAllPlaces_nonneg _ _)

中文:
定理 normAtComplexPlaces_normAtAllPlaces
  条件: (x : mixedSpace K)
  证明: normAtComplexPlaces_mixedSpaceOfRealSpace fun _ _ => (normAtAllPlaces_nonneg _ _)

Depends on / 依赖: normAtAllPlaces_nonneg, normAtComplexPlaces_mixedSpaceOfRealSpace
-/
theorem normAtComplexPlaces_normAtAllPlaces (x : mixedSpace K) :
    normAtComplexPlaces (mixedSpaceOfRealSpace (normAtAllPlaces x)) = normAtAllPlaces x :=
  normAtComplexPlaces_mixedSpaceOfRealSpace fun _ _ => (normAtAllPlaces_nonneg _ _)

/--
theorem `normAtAllPlaces_eq_of_normAtComplexPlaces_eq` / 定理 `normAtAllPlaces_eq_of_normAtComplexPlaces_eq`

English:
theorem normAtAllPlaces_eq_of_normAtComplexPlaces_eq
  statement: {x y : mixedSpace K}
  proof: by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · simpa [normAtAllPlaces_apply, normAtPlace_apply_of_isReal hw,
      normAtComplexPlaces_apply_isReal ⟨w, hw⟩] using congr_arg (|·|) (congr_fun h w)
  · simpa [normAtAllPlaces_apply, normAtPlace_apply_of_isComplex hw,
      normAtComplexPlaces_

中文:
定理 normAtAllPlaces_eq_of_normAtComplexPlaces_eq
  结论: {x y : mixedSpace K}
  证明: by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · simpa [normAtAllPlaces_apply, normAtPlace_apply_of_isReal hw,
      normAtComplexPlaces_apply_isReal ⟨w, hw⟩] using congr_arg (|·|) (congr_fun h w)
  · simpa [normAtAllPlaces_apply, normAtPlace_apply_of_isComplex hw,
      normAtComplexPlaces_

Depends on / 依赖: congr_arg, congr_fun, isReal_or_isComplex, normAtAllPlaces_apply, normAtComplexPlaces_apply_isComplex, normAtComplexPlaces_apply_isReal, normAtPlace_apply_of_isComplex, normAtPlace_apply_of_isReal
-/
theorem normAtAllPlaces_eq_of_normAtComplexPlaces_eq {x y : mixedSpace K}
    (h : normAtComplexPlaces x = normAtComplexPlaces y) :
    normAtAllPlaces x = normAtAllPlaces y := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · simpa [normAtAllPlaces_apply, normAtPlace_apply_of_isReal hw,
      normAtComplexPlaces_apply_isReal ⟨w, hw⟩] using congr_arg (|·|) (congr_fun h w)
  · simpa [normAtAllPlaces_apply, normAtPlace_apply_of_isComplex hw,
      normAtComplexPlaces_apply_isComplex ⟨w, hw⟩] using congr_fun h w

/--
theorem `normAtAllPlaces_image_preimage_of_nonneg` / 定理 `normAtAllPlaces_image_preimage_of_nonneg`

English:
theorem normAtAllPlaces_image_preimage_of_nonneg
  statement: {s : Set (realSpace K)}
  proof: by
  rw [Set.image_preimage_eq_iff]
  rintro x hx
  refine ⟨mixedSpaceOfRealSpace x, funext fun w => ?_⟩
  rw [normAtAllPlaces_apply]; rw [normAtPlace_mixedSpaceOfRealSpace (hs x hx w)]

中文:
定理 normAtAllPlaces_image_preimage_of_nonneg
  结论: {s : 集合 (realSpace K)}
  证明: by
  rw [Set.image_preimage_eq_iff]
  rintro x hx
  refine ⟨mixedSpaceOfRealSpace x, funext fun w => ?_⟩
  rw [normAtAllPlaces_apply]; rw [normAtPlace_mixedSpaceOfRealSpace (hs x hx w)]

Depends on / 依赖: Set.image_preimage_eq_iff, image_preimage_eq_iff, mixedSpaceOfRealSpace, normAtAllPlaces_apply, normAtPlace_mixedSpaceOfRealSpace
-/
theorem normAtAllPlaces_image_preimage_of_nonneg {s : Set (realSpace K)}
    (hs : forall x in s, forall w, 0 <= x w) :
    normAtAllPlaces '' normAtAllPlaces ⁻¹' s = s := by
  rw [Set.image_preimage_eq_iff]
  rintro x hx
  refine ⟨mixedSpaceOfRealSpace x, funext fun w => ?_⟩
  rw [normAtAllPlaces_apply]; rw [normAtPlace_mixedSpaceOfRealSpace (hs x hx w)]

end realSpace

end NumberField.mixedEmbedding
