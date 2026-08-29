/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Multivariate Fourier series

In this file we define the Fourier series of an L² function on the `d`-dimensional unit circle, and
show that it converges to the function in the L² norm. We also prove uniform convergence of the
Fourier series if `f` is continuous and the sequence of its Fourier coefficients is summable.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate ENNReal

open Set Algebra Submodule MeasureTheory

-- some instances for unit circle

/-- In this file we normalise the measure on `ℝ / ℤ` to have total volume 1. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The measure on `ℝ / ℤ` is a Haar measure. -/
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The measure on `ℝ / ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace UnitAddTorus

variable {d : Type*} [Fintype d]

section Monomials

variable (n : d -> Int)

/--
Definition of `mFourier` / `mFourier` 的定义

English:
definition mFourier
  signature: : C(UnitAddTorus d, Complex) where
  body: ∏ i : d, fourier (n i) (x i)
  continuous_toFun := by fun_prop

中文:
定义 mFourier
  签名: : C(UnitAddTorus d, 复形) where
  定义体: ∏ i : d, fourier (n i) (x i)
  continuous_toFun := by fun_prop

Depends on / 依赖: fourier
-/
def mFourier : C(UnitAddTorus d, Complex) where
  toFun x := ∏ i : d, fourier (n i) (x i)
  continuous_toFun := by fun_prop

variable {n} {x : UnitAddTorus d}

/--
lemma `mFourier_neg` / 引理 `mFourier_neg`

English:
lemma mFourier_neg
  statement: mFourier (-n) x = conj (mFourier n x)
  proof: by
  simp only [mFourier, Pi.neg_apply, fourier_neg, ContinuousMap.coe_mk, map_prod]

中文:
引理 mFourier_neg
  结论: mFourier (-n) x = conj (mFourier n x)
  证明: by
  simp only [mFourier, Pi.neg_apply, fourier_neg, ContinuousMap.coe_mk, map_prod]

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, Pi.neg_apply, coe_mk, fourier_neg, mFourier, map_prod, neg_apply
-/
lemma mFourier_neg : mFourier (-n) x = conj (mFourier n x) := by
  simp only [mFourier, Pi.neg_apply, fourier_neg, ContinuousMap.coe_mk, map_prod]

/--
lemma `mFourier_add` / 引理 `mFourier_add`

English:
lemma mFourier_add
  given: {m : d -> Int}
  statement: mFourier (m + n) x = mFourier m x * mFourier n x
  proof: by
  simp only [mFourier, Pi.add_apply, fourier_add, ContinuousMap.coe_mk, ← Finset.prod_mul_distrib]

中文:
引理 mFourier_add
  条件: {m : d -> 整数}
  结论: mFourier (m + n) x = mFourier m x * mFourier n x
  证明: by
  simp only [mFourier, Pi.add_apply, fourier_add, ContinuousMap.coe_mk, ← Finset.prod_mul_distrib]

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, Finset, Finset.prod_mul_distrib, Pi.add_apply, add_apply, coe_mk, fourier_add, mFourier, prod_mul_distrib
-/
lemma mFourier_add {m : d -> Int} : mFourier (m + n) x = mFourier m x * mFourier n x := by
  simp only [mFourier, Pi.add_apply, fourier_add, ContinuousMap.coe_mk, ← Finset.prod_mul_distrib]

/--
lemma `mFourier_zero` / 引理 `mFourier_zero`

English:
lemma mFourier_zero
  statement: mFourier (0 : d -> Int) = 1
  proof: by
  ext x
  simp only [mFourier, Pi.zero_apply, fourier_zero, Finset.prod_const_one, ContinuousMap.coe_mk,
    ContinuousMap.one_apply]

中文:
引理 mFourier_zero
  结论: mFourier (0 : d -> 整数) = 1
  证明: by
  ext x
  simp only [mFourier, Pi.zero_apply, fourier_zero, Finset.prod_const_one, ContinuousMap.coe_mk,
    ContinuousMap.one_apply]

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, ContinuousMap.one_apply, Finset, Finset.prod_const_one, Pi.zero_apply, coe_mk, fourier_zero, mFourier, one_apply, prod_const_one, zero_apply
-/
lemma mFourier_zero : mFourier (0 : d -> Int) = 1 := by
  ext x
  simp only [mFourier, Pi.zero_apply, fourier_zero, Finset.prod_const_one, ContinuousMap.coe_mk,
    ContinuousMap.one_apply]

/--
lemma `mFourier_norm` / 引理 `mFourier_norm`

English:
lemma mFourier_norm
  statement: ‖mFourier n‖ = 1
  proof: by
  apply le_antisymm
  · refine (ContinuousMap.norm_le _ zero_le_one).mpr fun i => ?_
    simp only [mFourier, fourier_apply, ContinuousMap.coe_mk, norm_prod, Circle.norm_coe,
      Finset.prod_const_one, le_rfl]
  · refine (le_of_eq ?_).trans ((mFourier n).norm_coe_le_norm fun _ => 0)
    simp only [mFourier, ContinuousMap.coe_mk, fourier_eval_zero, Finset.prod_const_one,
      CStarRing.norm_one]

中文:
引理 mFourier_norm
  结论: ‖mFourier n‖ = 1
  证明: by
  apply le_antisymm
  · refine (ContinuousMap.norm_le _ zero_le_one).mpr fun i => ?_
    simp only [mFourier, fourier_apply, ContinuousMap.coe_mk, norm_prod, Circle.norm_coe,
      Finset.prod_const_one, le_rfl]
  · refine (le_of_eq ?_).trans ((mFourier n).norm_coe_le_norm fun _ => 0)
    simp only [mFourier, ContinuousMap.coe_mk, fourier_eval_zero, Finset.prod_const_one,
      CStarRing.norm_one]

Depends on / 依赖: CStarRing, CStarRing.norm_one, Circle, Circle.norm_coe, ContinuousMap, ContinuousMap.coe_mk, ContinuousMap.norm_le, Finset, Finset.prod_const_one, coe_mk, fourier_apply, fourier_eval_zero, le_antisymm, le_of_eq, le_rfl, mFourier, norm_coe, norm_coe_le_norm, norm_le, norm_one
-/
lemma mFourier_norm : ‖mFourier n‖ = 1 := by
  apply le_antisymm
  · refine (ContinuousMap.norm_le _ zero_le_one).mpr fun i => ?_
    simp only [mFourier, fourier_apply, ContinuousMap.coe_mk, norm_prod, Circle.norm_coe,
      Finset.prod_const_one, le_rfl]
  · refine (le_of_eq ?_).trans ((mFourier n).norm_coe_le_norm fun _ => 0)
    simp only [mFourier, ContinuousMap.coe_mk, fourier_eval_zero, Finset.prod_const_one,
      CStarRing.norm_one]

/--
lemma `mFourier_single` / 引理 `mFourier_single`

English:
lemma mFourier_single
  given: [DecidableEq d] (z : d -> AddCircle (1 : Real)) (i : d)
  proof: by
  simp_rw [mFourier, ContinuousMap.coe_mk]
  have := Finset.prod_mul_prod_compl {i} (fun j => fourier ((Pi.single i (1 : Int) : d -> Int) j) (z j))
  rw [Finset.prod_singleton]; rw [Finset.prod_congr rfl (fun j hj => ?_)] at this
  · rw [← this, Finset.prod_const_one, mul_one, Pi.single_eq_same]
  · rw [Finset.mem_compl, Finset.mem_singleton] at hj
    simp only [Pi.single_eq_of_ne hj, fourier_zero]

中文:
引理 mFourier_single
  条件: [DecidableEq d] (z : d -> AddCircle (1 : 实数)) (i : d)
  证明: by
  simp_rw [mFourier, ContinuousMap.coe_mk]
  have := Finset.prod_mul_prod_compl {i} (fun j => fourier ((Pi.single i (1 : Int) : d -> Int) j) (z j))
  rw [Finset.prod_singleton]; rw [Finset.prod_congr rfl (fun j hj => ?_)] at this
  · rw [← this, Finset.prod_const_one, mul_one, Pi.single_eq_same]
  · rw [Finset.mem_compl, Finset.mem_singleton] at hj
    simp only [Pi.single_eq_of_ne hj, fourier_zero]

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, Finset, Finset.mem_compl, Finset.mem_singleton, Finset.prod_congr, Finset.prod_const_one, Finset.prod_mul_prod_compl, Finset.prod_singleton, Pi.single, Pi.single_eq_of_ne, Pi.single_eq_same, coe_mk, fourier, fourier_zero, mFourier, mem_compl, mem_singleton, mul_one, prod_congr
-/
lemma mFourier_single [DecidableEq d] (z : d -> AddCircle (1 : Real)) (i : d) :
    mFourier (Pi.single i 1) z = fourier 1 (z i) := by
  simp_rw [mFourier, ContinuousMap.coe_mk]
  have := Finset.prod_mul_prod_compl {i} (fun j => fourier ((Pi.single i (1 : Int) : d -> Int) j) (z j))
  rw [Finset.prod_singleton]; rw [Finset.prod_congr rfl (fun j hj => ?_)] at this
  · rw [← this, Finset.prod_const_one, mul_one, Pi.single_eq_same]
  · rw [Finset.mem_compl, Finset.mem_singleton] at hj
    simp only [Pi.single_eq_of_ne hj, fourier_zero]

end Monomials

section Algebra

/--
Definition of `mFourierSubalgebra` / `mFourierSubalgebra` 的定义

English:
definition mFourierSubalgebra
  signature: (d : Type*) [Fintype d]
  body: Algebra.adjoin Complex (range mFourier)
  star_mem' := by
    change Algebra.adjoin Complex (range mFourier) <= star (Algebra.adjoin Complex (range mFourier))
    refine adjoin_le ?_
    rintro _ ⟨n, rfl⟩
    refine subset_adjoin ⟨-n, ?_⟩
    ext1 x
    simp only [mFourier_neg, starRingEnd_apply, ContinuousMap.star_apply]

中文:
定义 mFourierSubalgebra
  签名: (d : 类型) [有限类型 d]
  定义体: Algebra.adjoin Complex (range mFourier)
  star_mem' := by
    change Algebra.adjoin Complex (range mFourier) <= star (Algebra.adjoin Complex (range mFourier))
    refine adjoin_le ?_
    rintro _ ⟨n, rfl⟩
    refine subset_adjoin ⟨-n, ?_⟩
    ext1 x
    simp only [mFourier_neg, starRingEnd_apply, ContinuousMap.star_apply]

Depends on / 依赖: Algebra, Algebra.adjoin, adjoin, mFourier
-/
def mFourierSubalgebra (d : Type*) [Fintype d] : StarSubalgebra Complex C(UnitAddTorus d, Complex) where
  toSubalgebra := Algebra.adjoin Complex (range mFourier)
  star_mem' := by
    change Algebra.adjoin Complex (range mFourier) <= star (Algebra.adjoin Complex (range mFourier))
    refine adjoin_le ?_
    rintro _ ⟨n, rfl⟩
    refine subset_adjoin ⟨-n, ?_⟩
    ext1 x
    simp only [mFourier_neg, starRingEnd_apply, ContinuousMap.star_apply]

/--
theorem `mFourierSubalgebra_coe` / 定理 `mFourierSubalgebra_coe`

English:
theorem mFourierSubalgebra_coe
  proof: by
  apply adjoin_eq_span_of_subset
  refine .trans (fun x => Submonoid.closure_induction (fun _ => id) ⟨0, ?_⟩ ?_) subset_span
  · ext z
    simp only [mFourier, Pi.zero_apply, fourier_zero, Finset.prod_const, one_pow,
      ContinuousMap.coe_mk, ContinuousMap.one_apply]
  · rintro _ _ _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    refine ⟨m + n, ?_⟩
    ext z
    simp only [mFourier, Pi.add_apply, fourier_apply, fourier_add', Finset.prod_mul_distrib,
      ContinuousMap.coe_mk, ContinuousMap.mul_apply]

中文:
定理 mFourierSubalgebra_coe
  证明: by
  apply adjoin_eq_span_of_subset
  refine .trans (fun x => Submonoid.closure_induction (fun _ => id) ⟨0, ?_⟩ ?_) subset_span
  · ext z
    simp only [mFourier, Pi.zero_apply, fourier_zero, Finset.prod_const, one_pow,
      ContinuousMap.coe_mk, ContinuousMap.one_apply]
  · rintro _ _ _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    refine ⟨m + n, ?_⟩
    ext z
    simp only [mFourier, Pi.add_apply, fourier_apply, fourier_add', Finset.prod_mul_distrib,
      ContinuousMap.coe_mk, ContinuousMap.mul_apply]

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, ContinuousMap.mul_apply, ContinuousMap.one_apply, Finset, Finset.prod_const, Finset.prod_mul_distrib, Pi.add_apply, Pi.zero_apply, Submonoid, Submonoid.closure_induction, add_apply, adjoin_eq_span_of_subset, closure_induction, coe_mk, fourier_add, fourier_apply, fourier_zero, mFourier, mul_apply
-/
theorem mFourierSubalgebra_coe :
    (mFourierSubalgebra d).toSubalgebra.toSubmodule = span Complex (range mFourier) := by
  apply adjoin_eq_span_of_subset
  refine .trans (fun x => Submonoid.closure_induction (fun _ => id) ⟨0, ?_⟩ ?_) subset_span
  · ext z
    simp only [mFourier, Pi.zero_apply, fourier_zero, Finset.prod_const, one_pow,
      ContinuousMap.coe_mk, ContinuousMap.one_apply]
  · rintro _ _ _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    refine ⟨m + n, ?_⟩
    ext z
    simp only [mFourier, Pi.add_apply, fourier_apply, fourier_add', Finset.prod_mul_distrib,
      ContinuousMap.coe_mk, ContinuousMap.mul_apply]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mFourierSubalgebra_separatesPoints` / 定理 `mFourierSubalgebra_separatesPoints`

English:
theorem mFourierSubalgebra_separatesPoints
  statement: (mFourierSubalgebra d).SeparatesPoints
  proof: by
  classical
  intro x y hxy
  rw [Ne]; rw [funext_iff]; rw [not_forall] at hxy
  obtain ⟨i, hi⟩ := hxy
  refine ⟨_, ⟨mFourier (Pi.single i 1), subset_adjoin ⟨Pi.single i 1, rfl⟩, rfl⟩, ?_⟩
  dsimp only
  rw [mFourier_single]; rw [mFourier_single]; rw [fourier_one]; rw [fourier_one]; rw [Ne]; rw [Subtype.coe_inj]
  contrapose hi
  exact AddCircle.injective_toCircle one_ne_zero hi

中文:
定理 mFourierSubalgebra_separatesPoints
  结论: (mFourierSubalgebra d).SeparatesPoints
  证明: by
  classical
  intro x y hxy
  rw [Ne]; rw [funext_iff]; rw [not_forall] at hxy
  obtain ⟨i, hi⟩ := hxy
  refine ⟨_, ⟨mFourier (Pi.single i 1), subset_adjoin ⟨Pi.single i 1, rfl⟩, rfl⟩, ?_⟩
  dsimp only
  rw [mFourier_single]; rw [mFourier_single]; rw [fourier_one]; rw [fourier_one]; rw [Ne]; rw [Subtype.coe_inj]
  contrapose hi
  exact AddCircle.injective_toCircle one_ne_zero hi

Depends on / 依赖: AddCircle, AddCircle.injective_toCircle, Pi.single, Subtype, Subtype.coe_inj, classical, coe_inj, contrapose, fourier_one, funext_iff, injective_toCircle, mFourier, mFourier_single, not_forall, one_ne_zero, single, subset_adjoin
-/
theorem mFourierSubalgebra_separatesPoints : (mFourierSubalgebra d).SeparatesPoints := by
  classical
  intro x y hxy
  rw [Ne]; rw [funext_iff]; rw [not_forall] at hxy
  obtain ⟨i, hi⟩ := hxy
  refine ⟨_, ⟨mFourier (Pi.single i 1), subset_adjoin ⟨Pi.single i 1, rfl⟩, rfl⟩, ?_⟩
  dsimp only
  rw [mFourier_single]; rw [mFourier_single]; rw [fourier_one]; rw [fourier_one]; rw [Ne]; rw [Subtype.coe_inj]
  contrapose hi
  exact AddCircle.injective_toCircle one_ne_zero hi

/--
theorem `mFourierSubalgebra_closure_eq_top` / 定理 `mFourierSubalgebra_closure_eq_top`

English:
theorem mFourierSubalgebra_closure_eq_top
  statement: (mFourierSubalgebra d).topologicalClosure = ⊤
  proof: ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    mFourierSubalgebra_separatesPoints

中文:
定理 mFourierSubalgebra_closure_eq_top
  结论: (mFourierSubalgebra d).topologicalClosure = ⊤
  证明: ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    mFourierSubalgebra_separatesPoints

Depends on / 依赖: ContinuousMap, ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints, mFourierSubalgebra_separatesPoints, starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
-/
theorem mFourierSubalgebra_closure_eq_top : (mFourierSubalgebra d).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    mFourierSubalgebra_separatesPoints

/--
theorem `span_mFourier_closure_eq_top` / 定理 `span_mFourier_closure_eq_top`

English:
theorem span_mFourier_closure_eq_top
  proof: by
  rw [← mFourierSubalgebra_coe]
  exact congr_arg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    mFourierSubalgebra_closure_eq_top

中文:
定理 span_mFourier_closure_eq_top
  证明: by
  rw [← mFourierSubalgebra_coe]
  exact congr_arg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    mFourierSubalgebra_closure_eq_top

Depends on / 依赖: StarSubalgebra, StarSubalgebra.toSubalgebra, Subalgebra, Subalgebra.toSubmodule, congr_arg, mFourierSubalgebra_closure_eq_top, mFourierSubalgebra_coe, toSubalgebra, toSubmodule, topologicalClosure
-/
theorem span_mFourier_closure_eq_top :
    (span Complex (range <| mFourier (d := d))).topologicalClosure = ⊤ := by
  rw [← mFourierSubalgebra_coe]
  exact congr_arg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    mFourierSubalgebra_closure_eq_top

end Algebra

section Integral

variable (a : d -> Real) {ι : Type*} (b : ι -> Real)

/--
Definition of `measurableEquivPiIoc` / `measurableEquivPiIoc` 的定义

English:
definition measurableEquivPiIoc
  signature: : UnitAddTorus ι ≃ᵐ {x : ι -> Real // forall i, x i in Ioc (b i) (b i + 1)}
  body: (MeasurableEquiv.piCongrRight fun i => AddCircle.measurableEquivIoc 1 (b i)).trans
  MeasurableEquiv.subtypePiEquivPi.symm

中文:
定义 measurableEquivPiIoc
  签名: : UnitAddTorus ι ≃ᵐ {x : ι -> 实数 // 对任意 i, x i in 左开右闭区间 (b i) (b i + 1)}
  定义体: (MeasurableEquiv.piCongrRight fun i => AddCircle.measurableEquivIoc 1 (b i)).trans
  MeasurableEquiv.subtypePiEquivPi.symm

Depends on / 依赖: AddCircle, AddCircle.measurableEquivIoc, MeasurableEquiv, MeasurableEquiv.piCongrRight, MeasurableEquiv.subtypePiEquivPi.symm, measurableEquivIoc, piCongrRight, subtypePiEquivPi
-/
def measurableEquivPiIoc : UnitAddTorus ι ≃ᵐ {x : ι -> Real // forall i, x i in Ioc (b i) (b i + 1)} :=
(MeasurableEquiv.piCongrRight fun i => AddCircle.measurableEquivIoc 1 (b i)).trans
  MeasurableEquiv.subtypePiEquivPi.symm

/--
theorem `coe_measurableEquivPiIoc` / 定理 `coe_measurableEquivPiIoc`

English:
theorem coe_measurableEquivPiIoc
  proof: rfl

@[simp]

中文:
定理 coe_measurableEquivPiIoc
  证明: rfl

@[simp]
-/
theorem coe_measurableEquivPiIoc :
    ⇑(measurableEquivPiIoc b) = fun x =>
      ⟨fun i => (AddCircle.equivIoc 1 (b i) (x i)).1,
      fun i => (AddCircle.equivIoc 1 (b i) (x i)).2⟩ := rfl

@[simp]
/--
theorem `coe_measurableEquivPiIoc_apply` / 定理 `coe_measurableEquivPiIoc_apply`

English:
theorem coe_measurableEquivPiIoc_apply
  given: (x : UnitAddTorus ι)
  proof: rfl

中文:
定理 coe_measurableEquivPiIoc_apply
  条件: (x : UnitAddTorus ι)
  证明: rfl
-/
theorem coe_measurableEquivPiIoc_apply (x : UnitAddTorus ι) :
    (measurableEquivPiIoc b) x = ⟨fun i => (AddCircle.equivIoc 1 (b i) (x i)).1,
      fun i => (AddCircle.equivIoc 1 (b i) (x i)).2⟩ := rfl

/--
theorem `coe_symm_measurableEquivPiIoc` / 定理 `coe_symm_measurableEquivPiIoc`

English:
theorem coe_symm_measurableEquivPiIoc
  proof: rfl

@[simp]

中文:
定理 coe_symm_measurableEquivPiIoc
  证明: rfl

@[simp]
-/
theorem coe_symm_measurableEquivPiIoc :
    ⇑(measurableEquivPiIoc b).symm = fun x i => x.1 i := rfl

@[simp]
/--
theorem `coe_symm_measurableEquivPiIoc_apply` / 定理 `coe_symm_measurableEquivPiIoc_apply`

English:
theorem coe_symm_measurableEquivPiIoc_apply
  given: (y : {x : ι -> Real // forall i, x i in Ioc (b i) (b i + 1)})
  proof: rfl

中文:
定理 coe_symm_measurableEquivPiIoc_apply
  条件: (y : {x : ι -> 实数 // 对任意 i, x i in 左开右闭区间 (b i) (b i + 1)})
  证明: rfl
-/
theorem coe_symm_measurableEquivPiIoc_apply (y : {x : ι -> Real // forall i, x i in Ioc (b i) (b i + 1)}) :
    (measurableEquivPiIoc b).symm y = fun i => (y.1 i : UnitAddCircle) := rfl

/--
lemma `measurePreserving_equivPiIoc` / 引理 `measurePreserving_equivPiIoc`

English:
lemma measurePreserving_equivPiIoc
  proof: by
  refine (⟨(measurableEquivPiIoc a).symm.measurable, symm ?_⟩ :
    MeasurePreserving (measurableEquivPiIoc a).symm _ _).symm
  have := Measure.map_map (μ := volume.comap Subtype.val) (measurable_pi_lambda
    (fun (x : d -> Real) => (fun i => x i : UnitAddTorus d))
    (fun i => AddCircle.measurable_mk'.comp (measurable_pi_apply i)))
    measurable_subtype_coe (α := {x : d -> Real // forall i, x i in Ioc (a i) (a i + 1)})
  simp only [Function.comp_def] at this
  simp_rw [coe_symm_measurableEquivPiIoc, ← this]
  convert! (measurePreserving_pi _ _ (fun i => AddCircle.measurePreserving_mk 1 (a i))).map_eq.symm
  · simp [volume, AddCircle.haarAddCircle]
  · convert!
    (map_comap_subtype_coe (MeasurableSet.univ_pi' (fun i => measurableSet_Ioc (a := a i))) volume)
    convert! (Measure.restrict_pi_pi (fun i => volume) (fun i => Ioc (a i) (a i + 1))).symm
    grind

中文:
引理 measurePreserving_equivPiIoc
  证明: by
  refine (⟨(measurableEquivPiIoc a).symm.measurable, symm ?_⟩ :
    MeasurePreserving (measurableEquivPiIoc a).symm _ _).symm
  have := Measure.map_map (μ := volume.comap Subtype.val) (measurable_pi_lambda
    (fun (x : d -> Real) => (fun i => x i : UnitAddTorus d))
    (fun i => AddCircle.measurable_mk'.comp (measurable_pi_apply i)))
    measurable_subtype_coe (α := {x : d -> Real // forall i, x i in Ioc (a i) (a i + 1)})
  simp only [Function.comp_def] at this
  simp_rw [coe_symm_measurableEquivPiIoc, ← this]
  convert! (measurePreserving_pi _ _ (fun i => AddCircle.measurePreserving_mk 1 (a i))).map_eq.symm
  · simp [volume, AddCircle.haarAddCircle]
  · convert!
    (map_comap_subtype_coe (MeasurableSet.univ_pi' (fun i => measurableSet_Ioc (a := a i))) volume)
    convert! (Measure.restrict_pi_pi (fun i => volume) (fun i => Ioc (a i) (a i + 1))).symm
    grind

Depends on / 依赖: AddCircle, AddCircle.measurable_mk, Function, Function.comp_def, Measure, Measure.map_map, MeasurePreserving, Subtype, Subtype.val, UnitAddTorus, coe_symm_measurableEquivPiIoc, comp_def, map_map, measurable, measurableEquivPiIoc, measurable_mk, measurable_pi_apply, measurable_pi_lambda, measurable_subtype_coe, simp_rw
-/
lemma measurePreserving_equivPiIoc :
    MeasurePreserving (measurableEquivPiIoc a) volume (Measure.comap Subtype.val volume) := by
  refine (⟨(measurableEquivPiIoc a).symm.measurable, symm ?_⟩ :
    MeasurePreserving (measurableEquivPiIoc a).symm _ _).symm
  have := Measure.map_map (μ := volume.comap Subtype.val) (measurable_pi_lambda
    (fun (x : d -> Real) => (fun i => x i : UnitAddTorus d))
    (fun i => AddCircle.measurable_mk'.comp (measurable_pi_apply i)))
    measurable_subtype_coe (α := {x : d -> Real // forall i, x i in Ioc (a i) (a i + 1)})
  simp only [Function.comp_def] at this
  simp_rw [coe_symm_measurableEquivPiIoc, ← this]
  convert! (measurePreserving_pi _ _ (fun i => AddCircle.measurePreserving_mk 1 (a i))).map_eq.symm
  · simp [volume, AddCircle.haarAddCircle]
  · convert!
    (map_comap_subtype_coe (MeasurableSet.univ_pi' (fun i => measurableSet_Ioc (a := a i))) volume)
    convert! (Measure.restrict_pi_pi (fun i => volume) (fun i => Ioc (a i) (a i + 1))).symm
    grind

/--
theorem `lintegral_preimage` / 定理 `lintegral_preimage`

English:
theorem lintegral_preimage
  given: (f : UnitAddTorus d -> Real>=0∞) (a : d -> Real)
  proof: by
  convert! lintegral_map_equiv (μ := volume.comap Subtype.val) f (measurableEquivPiIoc a).symm
  · exact (measurePreserving_equivPiIoc a).symm.map_eq.symm
  · rw [← lintegral_subtype_comap (MeasurableSet.univ_pi' (fun i => measurableSet_Ioc))]
    rfl

中文:
定理 lintegral_preimage
  条件: (f : UnitAddTorus d -> 实数>=0∞) (a : d -> 实数)
  证明: by
  convert! lintegral_map_equiv (μ := volume.comap Subtype.val) f (measurableEquivPiIoc a).symm
  · exact (measurePreserving_equivPiIoc a).symm.map_eq.symm
  · rw [← lintegral_subtype_comap (MeasurableSet.univ_pi' (fun i => measurableSet_Ioc))]
    rfl

Depends on / 依赖: MeasurableSet, MeasurableSet.univ_pi, Subtype, Subtype.val, convert, lintegral_map_equiv, lintegral_subtype_comap, map_eq, measurableEquivPiIoc, measurableSet_Ioc, measurePreserving_equivPiIoc, symm.map_eq.symm, univ_pi, volume, volume.comap
-/
theorem lintegral_preimage (f : UnitAddTorus d -> Real>=0∞) (a : d -> Real) :
    ∫⁻ x : UnitAddTorus d, f x =
    ∫⁻ (x : d -> Real) in {x : d -> Real | forall i, x i in Ioc (a i) (a i + 1)}, f (fun i => x i) := by
  convert! lintegral_map_equiv (μ := volume.comap Subtype.val) f (measurableEquivPiIoc a).symm
  · exact (measurePreserving_equivPiIoc a).symm.map_eq.symm
  · rw [← lintegral_subtype_comap (MeasurableSet.univ_pi' (fun i => measurableSet_Ioc))]
    rfl

/--
theorem `integral_preimage` / 定理 `integral_preimage`

English:
theorem integral_preimage
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  convert! integral_map_equiv (μ := volume.comap Subtype.val) (measurableEquivPiIoc a).symm f
  · exact (measurePreserving_equivPiIoc a).symm.map_eq.symm
  · rw [← integral_subtype_comap (MeasurableSet.univ_pi' (fun i => measurableSet_Ioc))]
    rfl

中文:
定理 integral_preimage
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: by
  convert! integral_map_equiv (μ := volume.comap Subtype.val) (measurableEquivPiIoc a).symm f
  · exact (measurePreserving_equivPiIoc a).symm.map_eq.symm
  · rw [← integral_subtype_comap (MeasurableSet.univ_pi' (fun i => measurableSet_Ioc))]
    rfl

Depends on / 依赖: MeasurableSet, MeasurableSet.univ_pi, Subtype, Subtype.val, convert, integral_map_equiv, integral_subtype_comap, map_eq, measurableEquivPiIoc, measurableSet_Ioc, measurePreserving_equivPiIoc, symm.map_eq.symm, univ_pi, volume, volume.comap
-/
theorem integral_preimage {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (f : UnitAddTorus d -> E) (a : d -> Real) :
    ∫ x : UnitAddTorus d, f x =
    ∫ (x : d -> Real) in {x : d -> Real | forall i, x i in Ioc (a i) (a i + 1)}, f (fun i => x i) := by
  convert! integral_map_equiv (μ := volume.comap Subtype.val) (measurableEquivPiIoc a).symm f
  · exact (measurePreserving_equivPiIoc a).symm.map_eq.symm
  · rw [← integral_subtype_comap (MeasurableSet.univ_pi' (fun i => measurableSet_Ioc))]
    rfl

end Integral

section Lp

/--
Definition of `mFourierLp` / `mFourierLp` 的定义

English:
abbreviation mFourierLp
  signature: (p : Real>=0∞) [Fact (1 <= p)] (n : d -> Int)
  body: ContinuousMap.toLp (E := Complex) p volume Complex (mFourier n)

中文:
缩写 mFourierLp
  签名: (p : 实数>=0∞) [Fact (1 <= p)] (n : d -> 整数)
  定义体: ContinuousMap.toLp (E := Complex) p volume Complex (mFourier n)

Depends on / 依赖: ContinuousMap, ContinuousMap.toLp, mFourier, volume
-/
abbrev mFourierLp (p : Real>=0∞) [Fact (1 <= p)] (n : d -> Int) :
    Lp Complex p (volume : Measure (UnitAddTorus d)) :=
  ContinuousMap.toLp (E := Complex) p volume Complex (mFourier n)

/--
theorem `coeFn_mFourierLp` / 定理 `coeFn_mFourierLp`

English:
theorem coeFn_mFourierLp
  given: (p : Real>=0∞) [Fact (1 <= p)] (n : d -> Int)
  proof: ContinuousMap.coeFn_toLp volume (mFourier n)

中文:
定理 coeFn_mFourierLp
  条件: (p : 实数>=0∞) [Fact (1 <= p)] (n : d -> 整数)
  证明: ContinuousMap.coeFn_toLp volume (mFourier n)

Depends on / 依赖: ContinuousMap, ContinuousMap.coeFn_toLp, coeFn_toLp, mFourier, volume
-/
theorem coeFn_mFourierLp (p : Real>=0∞) [Fact (1 <= p)] (n : d -> Int) :
    mFourierLp p n =ᵐ[volume] mFourier n :=
  ContinuousMap.coeFn_toLp volume (mFourier n)

/--
theorem `span_mFourierLp_closure_eq_top` / 定理 `span_mFourierLp_closure_eq_top`

English:
theorem span_mFourierLp_closure_eq_top
  given: {p : Real>=0∞} [Fact (1 <= p)] (hp : p != ∞)
  proof: by
  simpa only [map_span, ContinuousLinearMap.coe_coe, ← range_comp, Function.comp_def] using
    (ContinuousMap.toLp_denseRange Complex volume Complex hp).topologicalClosure_map_submodule
      span_mFourier_closure_eq_top

中文:
定理 span_mFourierLp_closure_eq_top
  条件: {p : 实数>=0∞} [Fact (1 <= p)] (hp : p != ∞)
  证明: by
  simpa only [map_span, ContinuousLinearMap.coe_coe, ← range_comp, Function.comp_def] using
    (ContinuousMap.toLp_denseRange Complex volume Complex hp).topologicalClosure_map_submodule
      span_mFourier_closure_eq_top

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_coe, ContinuousMap, ContinuousMap.toLp_denseRange, Function, Function.comp_def, coe_coe, comp_def, map_span, range_comp, span_mFourier_closure_eq_top, toLp_denseRange, topologicalClosure_map_submodule, volume
-/
theorem span_mFourierLp_closure_eq_top {p : Real>=0∞} [Fact (1 <= p)] (hp : p != ∞) :
    (span Complex (range (@mFourierLp d _ p _))).topologicalClosure = ⊤ := by
  simpa only [map_span, ContinuousLinearMap.coe_coe, ← range_comp, Function.comp_def] using
    (ContinuousMap.toLp_denseRange Complex volume Complex hp).topologicalClosure_map_submodule
      span_mFourier_closure_eq_top

/--
theorem `orthonormal_mFourier` / 定理 `orthonormal_mFourier`

English:
theorem orthonormal_mFourier
  statement: Orthonormal Complex (mFourierLp (d := d) 2)
  proof: by
  rw [orthonormal_iff_ite]
  intro m n
  simp only [ContinuousMap.inner_toLp, ← mFourier_neg, ← mFourier_add]
  split_ifs with h
  · simpa only [h, add_neg_cancel, mFourier_zero, probReal_univ, one_smul] using!
      integral_const (α := UnitAddTorus d) (μ := volume) (1 : Complex)
  rw [mFourier]; rw [ContinuousMap.coe_mk]; rw [MeasureTheory.integral_fintype_prod_volume_eq_prod]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa only [eq_false_intro hi, if_false, ContinuousMap.inner_toLp, ← fourier_neg,
← fourier_add] using! (orthonormal_iff_ite.mp orthonormal_fourier) (m i) (n i)

中文:
定理 orthonormal_mFourier
  结论: Orthonormal 复形 (mFourierLp (d := d) 2)
  证明: by
  rw [orthonormal_iff_ite]
  intro m n
  simp only [ContinuousMap.inner_toLp, ← mFourier_neg, ← mFourier_add]
  split_ifs with h
  · simpa only [h, add_neg_cancel, mFourier_zero, probReal_univ, one_smul] using!
      integral_const (α := UnitAddTorus d) (μ := volume) (1 : Complex)
  rw [mFourier]; rw [ContinuousMap.coe_mk]; rw [MeasureTheory.integral_fintype_prod_volume_eq_prod]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa only [eq_false_intro hi, if_false, ContinuousMap.inner_toLp, ← fourier_neg,
← fourier_add] using! (orthonormal_iff_ite.mp orthonormal_fourier) (m i) (n i)

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, ContinuousMap.inner_toLp, Finset, Finset.mem_univ, Finset.prod_eq_zero, Function, Function.ne_iff.mp, MeasureTheory, MeasureTheory.integral_fintype_prod_volume_eq_prod, UnitAddTorus, add_neg_cancel, coe_mk, eq_false_intro, if_false, inner_toLp, integral_const, integral_fintype_prod_volume_eq_prod, mFourier, mFourier_add
-/
theorem orthonormal_mFourier : Orthonormal Complex (mFourierLp (d := d) 2) := by
  rw [orthonormal_iff_ite]
  intro m n
  simp only [ContinuousMap.inner_toLp, ← mFourier_neg, ← mFourier_add]
  split_ifs with h
  · simpa only [h, add_neg_cancel, mFourier_zero, probReal_univ, one_smul] using!
      integral_const (α := UnitAddTorus d) (μ := volume) (1 : Complex)
  rw [mFourier]; rw [ContinuousMap.coe_mk]; rw [MeasureTheory.integral_fintype_prod_volume_eq_prod]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa only [eq_false_intro hi, if_false, ContinuousMap.inner_toLp, ← fourier_neg,
← fourier_add] using! (orthonormal_iff_ite.mp orthonormal_fourier) (m i) (n i)

end Lp

section fourierCoeff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]

/--
Definition of `mFourierCoeff` / `mFourierCoeff` 的定义

English:
definition mFourierCoeff
  signature: (f : UnitAddTorus d -> E) (n : d -> Int)
  body: ∫ t, mFourier (-n) t • f t

中文:
定义 mFourierCoeff
  签名: (f : UnitAddTorus d -> E) (n : d -> 整数)
  定义体: ∫ t, mFourier (-n) t • f t

Depends on / 依赖: mFourier
-/
def mFourierCoeff (f : UnitAddTorus d -> E) (n : d -> Int) : E := ∫ t, mFourier (-n) t • f t

/--
theorem `mFourierCoeff_eq_integral` / 定理 `mFourierCoeff_eq_integral`

English:
theorem mFourierCoeff_eq_integral
  given: (f : UnitAddTorus d -> E) (n : d -> Int) (a : d -> Real)
  proof: integral_preimage (fun x => (mFourier (-n)) x • f x) a

中文:
定理 mFourierCoeff_eq_integral
  条件: (f : UnitAddTorus d -> E) (n : d -> 整数) (a : d -> 实数)
  证明: integral_preimage (fun x => (mFourier (-n)) x • f x) a

Depends on / 依赖: integral_preimage, mFourier
-/
theorem mFourierCoeff_eq_integral (f : UnitAddTorus d -> E) (n : d -> Int) (a : d -> Real) :
    mFourierCoeff f n =
    ∫ (x : d -> Real) in {x : d -> Real | forall i, x i in Ioc (a i) (a i + 1)},
    mFourier (-n) (fun i => x i) • f (fun i => x i) :=
  integral_preimage (fun x => (mFourier (-n)) x • f x) a

end fourierCoeff

section FourierL2

local notation "L²(" α ")" => Lp Complex 2 (volume : Measure α)

/--
Definition of `mFourierBasis` / `mFourierBasis` 的定义

English:
definition mFourierBasis
  signature: : HilbertBasis (d -> Int) Complex L²(UnitAddTorus d)
  body: HilbertBasis.mk orthonormal_mFourier (span_mFourierLp_closure_eq_top (by simp)).ge

中文:
定义 mFourierBasis
  签名: : Hilbert基 (d -> 整数) 复形 L²(UnitAddTorus d)
  定义体: HilbertBasis.mk orthonormal_mFourier (span_mFourierLp_closure_eq_top (by simp)).ge

Depends on / 依赖: HilbertBasis, HilbertBasis.mk, orthonormal_mFourier, span_mFourierLp_closure_eq_top
-/
def mFourierBasis : HilbertBasis (d -> Int) Complex L²(UnitAddTorus d) :=
  HilbertBasis.mk orthonormal_mFourier (span_mFourierLp_closure_eq_top (by simp)).ge

/-- The elements of the Hilbert basis `mFourierBasis` are the functions `mFourierLp 2`, i.e. the
monomials `mFourier n` on `UnitAddTorus d` considered as elements of `L²`. -/
@[simp]
/--
theorem `coe_mFourierBasis` / 定理 `coe_mFourierBasis`

English:
theorem coe_mFourierBasis
  statement: ⇑(mFourierBasis (d := d)) = mFourierLp 2
  proof: HilbertBasis.coe_mk _ _

中文:
定理 coe_mFourierBasis
  结论: ⇑(mFourierBasis (d := d)) = mFourierLp 2
  证明: HilbertBasis.coe_mk _ _

Depends on / 依赖: HilbertBasis, HilbertBasis.coe_mk, coe_mk, mFourierLp
-/
theorem coe_mFourierBasis : ⇑(mFourierBasis (d := d)) = mFourierLp 2 := HilbertBasis.coe_mk _ _

/--
theorem `mFourierBasis_repr` / 定理 `mFourierBasis_repr`

English:
theorem mFourierBasis_repr
  given: (f : L²(UnitAddTorus d)) (i : d -> Int)
  proof: by
  trans ∫ t, conj (mFourierLp 2 i t) * f t
  · rw [mFourierBasis.repr_apply_apply f i, MeasureTheory.L2.inner_def, coe_mFourierBasis]
    simp only [RCLike.inner_apply, mul_comm]
  · apply integral_congr_ae
    filter_upwards [coeFn_mFourierLp 2 i] with _ ht
    rw [ht]; rw [← mFourier_neg]; rw [smul_eq_mul]

中文:
定理 mFourierBasis_repr
  条件: (f : L²(UnitAddTorus d)) (i : d -> 整数)
  证明: by
  trans ∫ t, conj (mFourierLp 2 i t) * f t
  · rw [mFourierBasis.repr_apply_apply f i, MeasureTheory.L2.inner_def, coe_mFourierBasis]
    simp only [RCLike.inner_apply, mul_comm]
  · apply integral_congr_ae
    filter_upwards [coeFn_mFourierLp 2 i] with _ ht
    rw [ht]; rw [← mFourier_neg]; rw [smul_eq_mul]

Depends on / 依赖: MeasureTheory, MeasureTheory.L2.inner_def, RCLike, RCLike.inner_apply, coeFn_mFourierLp, coe_mFourierBasis, filter_upwards, inner_apply, inner_def, integral_congr_ae, mFourierBasis, mFourierBasis.repr_apply_apply, mFourierLp, mFourier_neg, mul_comm, repr_apply_apply, smul_eq_mul
-/
theorem mFourierBasis_repr (f : L²(UnitAddTorus d)) (i : d -> Int) :
    mFourierBasis.repr f i = mFourierCoeff f i := by
  trans ∫ t, conj (mFourierLp 2 i t) * f t
  · rw [mFourierBasis.repr_apply_apply f i, MeasureTheory.L2.inner_def, coe_mFourierBasis]
    simp only [RCLike.inner_apply, mul_comm]
  · apply integral_congr_ae
    filter_upwards [coeFn_mFourierLp 2 i] with _ ht
    rw [ht]; rw [← mFourier_neg]; rw [smul_eq_mul]

/--
theorem `hasSum_mFourier_series_L2` / 定理 `hasSum_mFourier_series_L2`

English:
theorem hasSum_mFourier_series_L2
  given: (f : L²(UnitAddTorus d))
  proof: by
  simpa [← coe_mFourierBasis, mFourierBasis_repr] using mFourierBasis.hasSum_repr f

中文:
定理 hasSum_mFourier_series_L2
  条件: (f : L²(UnitAddTorus d))
  证明: by
  simpa [← coe_mFourierBasis, mFourierBasis_repr] using mFourierBasis.hasSum_repr f

Depends on / 依赖: coe_mFourierBasis, hasSum_repr, mFourierBasis, mFourierBasis.hasSum_repr, mFourierBasis_repr
-/
theorem hasSum_mFourier_series_L2 (f : L²(UnitAddTorus d)) :
    HasSum (fun i => mFourierCoeff f i • mFourierLp 2 i) f := by
  simpa [← coe_mFourierBasis, mFourierBasis_repr] using mFourierBasis.hasSum_repr f

/--
theorem `hasSum_prod_mFourierCoeff` / 定理 `hasSum_prod_mFourierCoeff`

English:
theorem hasSum_prod_mFourierCoeff
  given: (f g : L²(UnitAddTorus d))
  proof: by
  simp_rw [mul_comm (conj _)]
  refine HasSum.congr_fun (mFourierBasis.hasSum_inner_mul_inner f g) (fun n => ?_)
  simp only [← mFourierBasis_repr, HilbertBasis.repr_apply_apply, inner_conj_symm,
    mul_comm (inner Complex f _)]

中文:
定理 hasSum_prod_mFourierCoeff
  条件: (f g : L²(UnitAddTorus d))
  证明: by
  simp_rw [mul_comm (conj _)]
  refine HasSum.congr_fun (mFourierBasis.hasSum_inner_mul_inner f g) (fun n => ?_)
  simp only [← mFourierBasis_repr, HilbertBasis.repr_apply_apply, inner_conj_symm,
    mul_comm (inner Complex f _)]

Depends on / 依赖: HasSum, HasSum.congr_fun, HilbertBasis, HilbertBasis.repr_apply_apply, congr_fun, hasSum_inner_mul_inner, inner_conj_symm, mFourierBasis, mFourierBasis.hasSum_inner_mul_inner, mFourierBasis_repr, mul_comm, repr_apply_apply, simp_rw
-/
theorem hasSum_prod_mFourierCoeff (f g : L²(UnitAddTorus d)) :
    HasSum (fun i => conj (mFourierCoeff f i) * (mFourierCoeff g i)) (∫ t, conj (f t) * g t) := by
  simp_rw [mul_comm (conj _)]
  refine HasSum.congr_fun (mFourierBasis.hasSum_inner_mul_inner f g) (fun n => ?_)
  simp only [← mFourierBasis_repr, HilbertBasis.repr_apply_apply, inner_conj_symm,
    mul_comm (inner Complex f _)]

/--
theorem `hasSum_sq_mFourierCoeff` / 定理 `hasSum_sq_mFourierCoeff`

English:
theorem hasSum_sq_mFourierCoeff
  given: (f : L²(UnitAddTorus d))
  proof: by
  simpa only [← RCLike.inner_apply', inner_self_eq_norm_sq, ← integral_re
    (L2.integrable_inner f f)] using RCLike.hasSum_re Complex (hasSum_prod_mFourierCoeff f f)

中文:
定理 hasSum_sq_mFourierCoeff
  条件: (f : L²(UnitAddTorus d))
  证明: by
  simpa only [← RCLike.inner_apply', inner_self_eq_norm_sq, ← integral_re
    (L2.integrable_inner f f)] using RCLike.hasSum_re Complex (hasSum_prod_mFourierCoeff f f)

Depends on / 依赖: L2.integrable_inner, RCLike, RCLike.hasSum_re, RCLike.inner_apply, hasSum_prod_mFourierCoeff, hasSum_re, inner_apply, inner_self_eq_norm_sq, integrable_inner, integral_re
-/
theorem hasSum_sq_mFourierCoeff (f : L²(UnitAddTorus d)) :
    HasSum (fun i => ‖mFourierCoeff f i‖ ^ 2) (∫ t, ‖f t‖ ^ 2) := by
  simpa only [← RCLike.inner_apply', inner_self_eq_norm_sq, ← integral_re
    (L2.integrable_inner f f)] using RCLike.hasSum_re Complex (hasSum_prod_mFourierCoeff f f)

end FourierL2

section Convergence

variable (f : C(UnitAddTorus d, Complex))

/--
theorem `mFourierCoeff_toLp` / 定理 `mFourierCoeff_toLp`

English:
theorem mFourierCoeff_toLp
  given: (n : d -> Int)
  proof: integral_congr_ae (ae_eq_rfl.mul <| f.coeFn_toAEEqFun _)

中文:
定理 mFourierCoeff_toLp
  条件: (n : d -> 整数)
  证明: integral_congr_ae (ae_eq_rfl.mul <| f.coeFn_toAEEqFun _)

Depends on / 依赖: ae_eq_rfl, ae_eq_rfl.mul, coeFn_toAEEqFun, f.coeFn_toAEEqFun, integral_congr_ae
-/
theorem mFourierCoeff_toLp (n : d -> Int) :
    mFourierCoeff (f.toLp 2 volume Complex) n = mFourierCoeff f n :=
  integral_congr_ae (ae_eq_rfl.mul <| f.coeFn_toAEEqFun _)

variable {f}

/--
theorem `hasSum_mFourier_series_of_summable` / 定理 `hasSum_mFourier_series_of_summable`

English:
theorem hasSum_mFourier_series_of_summable
  given: (h : Summable (mFourierCoeff f))
  proof: by
  have sum_L2 := hasSum_mFourier_series_L2 (ContinuousMap.toLp 2 volume Complex f)
  simp only [mFourierCoeff_toLp] at sum_L2
  refine ContinuousMap.hasSum_of_hasSum_Lp (.of_norm ?_) sum_L2
  simpa only [norm_smul, mFourier_norm, mul_one] using h.norm

中文:
定理 hasSum_mFourier_series_of_summable
  条件: (h : Summable (mFourierCoeff f))
  证明: by
  have sum_L2 := hasSum_mFourier_series_L2 (ContinuousMap.toLp 2 volume Complex f)
  simp only [mFourierCoeff_toLp] at sum_L2
  refine ContinuousMap.hasSum_of_hasSum_Lp (.of_norm ?_) sum_L2
  simpa only [norm_smul, mFourier_norm, mul_one] using h.norm

Depends on / 依赖: ContinuousMap, ContinuousMap.hasSum_of_hasSum_Lp, ContinuousMap.toLp, h.norm, hasSum_mFourier_series_L2, hasSum_of_hasSum_Lp, mFourierCoeff_toLp, mFourier_norm, mul_one, norm_smul, of_norm, sum_L2, volume
-/
theorem hasSum_mFourier_series_of_summable (h : Summable (mFourierCoeff f)) :
    HasSum (fun i => mFourierCoeff f i • mFourier i) f := by
  have sum_L2 := hasSum_mFourier_series_L2 (ContinuousMap.toLp 2 volume Complex f)
  simp only [mFourierCoeff_toLp] at sum_L2
  refine ContinuousMap.hasSum_of_hasSum_Lp (.of_norm ?_) sum_L2
  simpa only [norm_smul, mFourier_norm, mul_one] using h.norm

/--
theorem `hasSum_mFourier_series_apply_of_summable` / 定理 `hasSum_mFourier_series_apply_of_summable`

English:
theorem hasSum_mFourier_series_apply_of_summable
  statement: (h : Summable (mFourierCoeff f))
  proof: by
  simpa only [map_smul] using! (ContinuousMap.evalCLM Complex x).hasSum
    (hasSum_mFourier_series_of_summable h)

中文:
定理 hasSum_mFourier_series_apply_of_summable
  结论: (h : Summable (mFourierCoeff f))
  证明: by
  simpa only [map_smul] using! (ContinuousMap.evalCLM Complex x).hasSum
    (hasSum_mFourier_series_of_summable h)

Depends on / 依赖: ContinuousMap, ContinuousMap.evalCLM, evalCLM, hasSum, hasSum_mFourier_series_of_summable, map_smul
-/
theorem hasSum_mFourier_series_apply_of_summable (h : Summable (mFourierCoeff f))
    (x : UnitAddTorus d) : HasSum (fun i => mFourierCoeff f i • mFourier i x) (f x) := by
  simpa only [map_smul] using! (ContinuousMap.evalCLM Complex x).hasSum
    (hasSum_mFourier_series_of_summable h)

end Convergence

end UnitAddTorus
