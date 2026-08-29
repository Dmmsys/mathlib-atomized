/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Ideal.IdempotentFG

/-!

# Standard etale maps

## Main definitions
- `StandardEtalePair`:
  A pair `f g : R[X]` such that `f` is monic and `f'` is invertible in `R[X][1/g]`.
- `StandardEtalePair`: The standard etale algebra corresponding to a `StandardEtalePair`.
- `StandardEtalePair.equivPolynomialQuotient` : `P.Ring ≃ R[X][Y]/⟨f, Yg-1⟩`
- `StandardEtalePair.equivAwayAdjoinRoot` : `P.Ring ≃ (R[X]/f)[1/g]`
- `StandardEtalePair.equivAwayQuotient` : `P.Ring ≃ R[X][1/g]/f`
- `StandardEtalePair.equivMvPolynomialQuotient` : `P.Ring ≃ R[X, Y]/⟨f, Yg-1⟩`
- `StandardEtalePair.homEquiv`:
  Maps out of `P.Ring` corresponds to `x` such that `f(x) = 0` and `g(x)` is invertible.
- We also provide the instance that `P.Ring` is etale over `R`.

- `Algebra.IsStandardEtale`: The class of standard etale algebras.

-/

@[expose] public section

universe u

open Polynomial

open scoped Bivariate

noncomputable section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

variable (R) in
/--
Definition of `StandardEtalePair` / `StandardEtalePair` 的定义

English:
structure StandardEtalePair
  parameters: : Type _ where
  axioms and operations (4):
    - f : R[X]
    - monic_f : f.Monic
    - g : R[X]
    - cond : exists p₁ p₂ n, derivative f * p₁ + f * p₂ = g ^ n

中文:
结构 StandardEtalePair
  参数: : 类型 _ where
  公理与运算 (4 个):
    - f : R[X]
    - monic_f : f.Monic
    - g : R[X]
    - cond : 存在 p₁ p₂ n, derivative f * p₁ + f * p₂ = g ^ n

Depends on / 依赖: Ideal.span
-/
structure StandardEtalePair : Type _ where
  /-- The monic polynomial to be quotiented out in a standard etale algebra. -/
  f : R[X]
  monic_f : f.Monic
  /-- The polynomial to be localized away from in a standard etale algebra. -/
  g : R[X]
  cond : exists p₁ p₂ n, derivative f * p₁ + f * p₂ = g ^ n

variable (P : StandardEtalePair R)

/--
Definition of `StandardEtalePair.Ring` / `StandardEtalePair.Ring` 的定义

English:
definition StandardEtalePair.Ring
  body: R[X][Y] ⧸ Ideal.span {C P.f, Y * C P.g - 1}
  deriving CommRing, Algebra R

中文:
定义 StandardEtalePair.环
  定义体: R[X][Y] ⧸ Ideal.span {C P.f, Y * C P.g - 1}
  deriving CommRing, Algebra R
-/
protected def StandardEtalePair.Ring := R[X][Y] ⧸ Ideal.span {C P.f, Y * C P.g - 1}
  deriving CommRing, Algebra R

namespace StandardEtalePair

/--
Definition of `X` / `X` 的定义

English:
definition X
  signature: : P.Ring
  body: Ideal.Quotient.mk _ (C .X)

中文:
定义 X
  签名: : P.环
  定义体: Ideal.Quotient.mk _ (C .X)
-/
protected def X : P.Ring := Ideal.Quotient.mk _ (C .X)

/--
Definition of `HasMap` / `HasMap` 的定义

English:
definition HasMap
  signature: (x : S)
  body: aeval x P.f = 0 ∧ IsUnit (aeval x P.g)

中文:
定义 HasMap
  签名: (x : S)
  定义体: aeval x P.f = 0 ∧ IsUnit (aeval x P.g)

Depends on / 依赖: IsUnit
-/
def HasMap (x : S) : Prop :=
  aeval x P.f = 0 ∧ IsUnit (aeval x P.g)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (x : S) (h : P.HasMap x)
  body: Ideal.Quotient.liftₐ _ (aevalAeval x ↑(h.2.unit⁻¹))
    (Ideal.span_le (I := RingHom.ker _).mpr (by simp [Set.pair_subset_iff, h.1]))

中文:
定义 lift
  签名: (x : S) (h : P.HasMap x)
  定义体: Ideal.Quotient.liftₐ _ (aevalAeval x ↑(h.2.unit⁻¹))
    (Ideal.span_le (I := RingHom.ker _).mpr (by simp [Set.pair_subset_iff, h.1]))

Depends on / 依赖: Ideal.Quotient.lift, Ideal.span_le, Quotient, RingHom, RingHom.ker, Set.pair_subset_iff, aevalAeval, pair_subset_iff, span_le
-/
def lift (x : S) (h : P.HasMap x) : P.Ring ->ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aevalAeval x ↑(h.2.unit⁻¹))
    (Ideal.span_le (I := RingHom.ker _).mpr (by simp [Set.pair_subset_iff, h.1]))

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `lift_X` / 引理 `lift_X`

English:
lemma lift_X
  given: (x : S) (h : P.HasMap x)
  statement: P.lift x h P.X = x
  proof: by
  simp [lift, StandardEtalePair.Ring, StandardEtalePair.X]

中文:
引理 lift_X
  条件: (x : S) (h : P.HasMap x)
  结论: P.lift x h P.X = x
  证明: by
  simp [lift, StandardEtalePair.Ring, StandardEtalePair.X]

Depends on / 依赖: StandardEtalePair, StandardEtalePair.Ring, StandardEtalePair.X
-/
lemma lift_X (x : S) (h : P.HasMap x) : P.lift x h P.X = x := by
  simp [lift, StandardEtalePair.Ring, StandardEtalePair.X]

variable {P} in
/--
lemma `HasMap.map` / 引理 `HasMap.map`

English:
lemma HasMap.map
  given: {x : S} (h : P.HasMap x) (f : S ->ₐ[R] T)
  statement: P.HasMap (f x)
  proof: ⟨by simp [aeval_algHom, h.1], by simpa [aeval_algHom] using h.2.map f⟩

中文:
引理 HasMap.map
  条件: {x : S} (h : P.HasMap x) (f : S ->ₐ[R] T)
  结论: P.HasMap (f x)
  证明: ⟨by simp [aeval_algHom, h.1], by simpa [aeval_algHom] using h.2.map f⟩

Depends on / 依赖: aeval_algHom
-/
lemma HasMap.map {x : S} (h : P.HasMap x) (f : S ->ₐ[R] T) : P.HasMap (f x) :=
  ⟨by simp [aeval_algHom, h.1], by simpa [aeval_algHom] using h.2.map f⟩

/--
lemma `HasMap.isUnit_derivative_f` / 引理 `HasMap.isUnit_derivative_f`

English:
lemma HasMap.isUnit_derivative_f
  given: {x : S} (h : P.HasMap x)
  proof: by
  obtain ⟨p₁, p₂, n, e⟩ := P.cond
  have : aeval x P.f.derivative ∣ aeval x P.g ^ n :=
    ⟨_, by simpa [h.1] using congr(aeval x $e.symm)⟩
  exact isUnit_of_dvd_unit this (.pow _ h.2)

中文:
引理 HasMap.isUnit_derivative_f
  条件: {x : S} (h : P.HasMap x)
  证明: by
  obtain ⟨p₁, p₂, n, e⟩ := P.cond
  have : aeval x P.f.derivative ∣ aeval x P.g ^ n :=
    ⟨_, by simpa [h.1] using congr(aeval x $e.symm)⟩
  exact isUnit_of_dvd_unit this (.pow _ h.2)

Depends on / 依赖: P.cond, P.f.derivative, derivative, e.symm, isUnit_of_dvd_unit
-/
lemma HasMap.isUnit_derivative_f {x : S} (h : P.HasMap x) :
    IsUnit (P.f.derivative.aeval x) := by
  obtain ⟨p₁, p₂, n, e⟩ := P.cond
  have : aeval x P.f.derivative ∣ aeval x P.g ^ n :=
    ⟨_, by simpa [h.1] using congr(aeval x $e.symm)⟩
  exact isUnit_of_dvd_unit this (.pow _ h.2)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `aeval_X_g_mul_mk_X` / 引理 `aeval_X_g_mul_mk_X`

English:
lemma aeval_X_g_mul_mk_X
  statement: aeval P.X P.g * Ideal.Quotient.mk _ .X = 1
  proof: by
  have : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext; simp [StandardEtalePair.Ring, StandardEtalePair.X]
  rw [this]
  dsimp [StandardEtalePair.Ring]
  rw [← map_mul]; rw [← map_one (Ideal.Quotient.mk _)]; rw [← sub_eq_zero]; rw [← map_sub]; rw [mul_comm]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))

中文:
引理 aeval_X_g_mul_mk_X
  结论: aeval P.X P.g * 理想.商.mk _ .X = 1
  证明: by
  have : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext; simp [StandardEtalePair.Ring, StandardEtalePair.X]
  rw [this]
  dsimp [StandardEtalePair.Ring]
  rw [← map_mul]; rw [← map_one (Ideal.Quotient.mk _)]; rw [← sub_eq_zero]; rw [← map_sub]; rw [mul_comm]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))

Depends on / 依赖: CAlgHom, Ideal.Quotient.eq_zero_iff_mem.mpr, Ideal.Quotient.mk, Ideal.subset_span, Polynomial, Polynomial.CAlgHom, Quotient, Set.mem_insert_of_mem, StandardEtalePair, StandardEtalePair.Ring, StandardEtalePair.X, eq_zero_iff_mem, map_mul, map_one, map_sub, mem_insert_of_mem, mul_comm, sub_eq_zero, subset_span
-/
lemma aeval_X_g_mul_mk_X : aeval P.X P.g * Ideal.Quotient.mk _ .X = 1 := by
  have : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext; simp [StandardEtalePair.Ring, StandardEtalePair.X]
  rw [this]
  dsimp [StandardEtalePair.Ring]
  rw [← map_mul]; rw [← map_one (Ideal.Quotient.mk _)]; rw [← sub_eq_zero]; rw [← map_sub]; rw [mul_comm]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))

set_option backward.isDefEq.respectTransparency false in
variable {P} in
/--
lemma `hasMap_X` / 引理 `hasMap_X`

English:
lemma hasMap_X
  statement: P.HasMap P.X
  proof: have : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext; simp [StandardEtalePair.Ring, StandardEtalePair.X]
  ⟨this ▸ Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _)),
    IsUnit.of_mul_eq_one _ P.aeval_X_g_mul_mk_X⟩

中文:
引理 hasMap_X
  结论: P.HasMap P.X
  证明: have : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext; simp [StandardEtalePair.Ring, StandardEtalePair.X]
  ⟨this ▸ Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _)),
    IsUnit.of_mul_eq_one _ P.aeval_X_g_mul_mk_X⟩

Depends on / 依赖: CAlgHom, Ideal.Quotient.eq_zero_iff_mem.mpr, Ideal.Quotient.mk, Ideal.subset_span, IsUnit, IsUnit.of_mul_eq_one, P.aeval_X_g_mul_mk_X, Polynomial, Polynomial.CAlgHom, Quotient, Set.mem_insert, StandardEtalePair, StandardEtalePair.Ring, StandardEtalePair.X, aeval_X_g_mul_mk_X, eq_zero_iff_mem, mem_insert, of_mul_eq_one, subset_span
-/
lemma hasMap_X : P.HasMap P.X :=
  have : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext; simp [StandardEtalePair.Ring, StandardEtalePair.X]
  ⟨this ▸ Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _)),
    IsUnit.of_mul_eq_one _ P.aeval_X_g_mul_mk_X⟩

set_option backward.isDefEq.respectTransparency false in
variable {P} in
@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {f g : P.Ring ->ₐ[R] S} (H : f P.X = g P.X)
  statement: f = g
  proof: by
  have H : (f.comp (Ideal.Quotient.mkₐ R _)).comp CAlgHom =
    (g.comp (Ideal.Quotient.mkₐ R _)).comp CAlgHom := Polynomial.algHom_ext (by simpa)
  have H' : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext; simp [StandardEtalePair.Ring, StandardEtalePair.X]
  refine Ideal.Quotient.algHom_ext _ (Polynomial.algHom_ext' H ?_)
  change f.toMonoidHom (Ideal.Quotient.mk _ .X) = g.toMonoidHom (Ideal.Quotient.mk _ .X)
  rw [← show (↑P.hasMap_X.2.unit⁻¹ : P.Ring) = Ideal.Quotient.mk _ .X from
    Units.mul_eq_one_iff_inv_eq.mp P.aeval_X_g_mul_mk_X]; rw [← Units.coe_map_inv]; rw [← Units.coe_map_inv]
  congr 2
  ext
  simpa [H'] using! congr($H _)

@[simp]

中文:
引理 hom_ext
  条件: {f g : P.环 ->ₐ[R] S} (H : f P.X = g P.X)
  结论: f = g
  证明: by
  have H : (f.comp (Ideal.Quotient.mkₐ R _)).comp CAlgHom =
    (g.comp (Ideal.Quotient.mkₐ R _)).comp CAlgHom := Polynomial.algHom_ext (by simpa)
  have H' : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext; simp [StandardEtalePair.Ring, StandardEtalePair.X]
  refine Ideal.Quotient.algHom_ext _ (Polynomial.algHom_ext' H ?_)
  change f.toMonoidHom (Ideal.Quotient.mk _ .X) = g.toMonoidHom (Ideal.Quotient.mk _ .X)
  rw [← show (↑P.hasMap_X.2.unit⁻¹ : P.Ring) = Ideal.Quotient.mk _ .X from
    Units.mul_eq_one_iff_inv_eq.mp P.aeval_X_g_mul_mk_X]; rw [← Units.coe_map_inv]; rw [← Units.coe_map_inv]
  congr 2
  ext
  simpa [H'] using! congr($H _)

@[simp]

Depends on / 依赖: CAlgHom, Ideal.Quotient.algHom_ext, Ideal.Quotient.mk, P.Ring, P.hasMap_X, Polynomial, Polynomial.CAlgHom, Polynomial.algHom_ext, Quotient, StandardEtalePair, StandardEtalePair.Ring, StandardEtalePair.X, algHom_ext, f.comp, f.toMonoidHom, g.comp, g.toMonoidHom, hasMap_X, toMonoidHom
-/
lemma hom_ext {f g : P.Ring ->ₐ[R] S} (H : f P.X = g P.X) : f = g := by
  have H : (f.comp (Ideal.Quotient.mkₐ R _)).comp CAlgHom =
    (g.comp (Ideal.Quotient.mkₐ R _)).comp CAlgHom := Polynomial.algHom_ext (by simpa)
  have H' : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext; simp [StandardEtalePair.Ring, StandardEtalePair.X]
  refine Ideal.Quotient.algHom_ext _ (Polynomial.algHom_ext' H ?_)
  change f.toMonoidHom (Ideal.Quotient.mk _ .X) = g.toMonoidHom (Ideal.Quotient.mk _ .X)
  rw [← show (↑P.hasMap_X.2.unit⁻¹ : P.Ring) = Ideal.Quotient.mk _ .X from
    Units.mul_eq_one_iff_inv_eq.mp P.aeval_X_g_mul_mk_X]; rw [← Units.coe_map_inv]; rw [← Units.coe_map_inv]
  congr 2
  ext
  simpa [H'] using! congr($H _)

@[simp]
/--
lemma `lift_X_left` / 引理 `lift_X_left`

English:
lemma lift_X_left
  statement: P.lift P.X P.hasMap_X = .id _ _
  proof: P.hom_ext (by simp)

中文:
引理 lift_X_left
  结论: P.lift P.X P.hasMap_X = .id _ _
  证明: P.hom_ext (by simp)

Depends on / 依赖: P.hom_ext, hom_ext
-/
lemma lift_X_left : P.lift P.X P.hasMap_X = .id _ _ :=
  P.hom_ext (by simp)

/--
lemma `inv_aeval_X_g` / 引理 `inv_aeval_X_g`

English:
lemma inv_aeval_X_g
  proof: Units.mul_eq_one_iff_inv_eq.mp P.aeval_X_g_mul_mk_X

中文:
引理 inv_aeval_X_g
  证明: Units.mul_eq_one_iff_inv_eq.mp P.aeval_X_g_mul_mk_X

Depends on / 依赖: P.aeval_X_g_mul_mk_X, Units.mul_eq_one_iff_inv_eq.mp, aeval_X_g_mul_mk_X, mul_eq_one_iff_inv_eq
-/
lemma inv_aeval_X_g :
    (↑P.hasMap_X.2.unit⁻¹ : P.Ring) = Ideal.Quotient.mk _ .X :=
  Units.mul_eq_one_iff_inv_eq.mp P.aeval_X_g_mul_mk_X

/-- Maps out of `R[X][Y]/⟨f, Yg-1⟩` corresponds bijectively with
`x` such that `f(x) = 0` and `g(x)` is invertible. -/
@[simps]
/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: : (P.Ring ->ₐ[R] S) ≃ { x : S // P.HasMap x } where
  body: ⟨f P.X, hasMap_X.map f⟩
  invFun x := P.lift x.1 x.2
  left_inv f := P.hom_ext (by simp)
  right_inv x := by simp

中文:
定义 homEquiv
  签名: : (P.环 ->ₐ[R] S) ≃ { x : S // P.HasMap x } where
  定义体: ⟨f P.X, hasMap_X.map f⟩
  invFun x := P.lift x.1 x.2
  left_inv f := P.hom_ext (by simp)
  right_inv x := by simp

Depends on / 依赖: hasMap_X, hasMap_X.map
-/
def homEquiv : (P.Ring ->ₐ[R] S) ≃ { x : S // P.HasMap x } where
  toFun f := ⟨f P.X, hasMap_X.map f⟩
  invFun x := P.lift x.1 x.2
  left_inv f := P.hom_ext (by simp)
  right_inv x := by simp

/--
lemma `existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot` / 引理 `existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot`

English:
lemma existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot
  proof: by
  have hf := Ideal.Quotient.eq_zero_iff_mem.mp
    ((aeval_algHom_apply (Ideal.Quotient.mkₐ R I) _ _).symm.trans hx.1)
  obtain ⟨⟨_, a, ha, -⟩, rfl⟩ := hx.2
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp_rw [← Ideal.Quotient.mkₐ_eq_mk R, aeval_algHom_apply, ← map_mul, ← map_one
    (Ideal.Quotient.mkₐ R I), Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ha
  obtain ⟨p₁, p₂, n, e⟩ := P.cond
  apply_fun aeval x at e
  simp only [map_add, map_mul, map_pow] at e
  obtain ⟨ε, hεI, b, hb⟩ : exists ε in I, exists b, aeval x (derivative P.f) * b = 1 + ε := by
    refine ⟨_, ?_, (a ^ n * aeval x p₁), sub_eq_iff_eq_add'.mp rfl⟩
    convert_to (aeval x P.g * a) ^ n - 1 - aeval x P.f * (a ^ n * aeval x p₂) in I
    · linear_combination a ^ n * e
    · exact sub_mem (Ideal.mem_of_dvd _ (sub_one_dvd_pow_sub_one _ _) ha) (I.mul_mem_right _ hf)
  have : aeval x P.f ^ 2 = 0 := hI.le (Ideal.pow_mem_pow hf 2)
  have : aeval x P.f * ε = 0 := ((pow_two _).symm.trans hI).le (Ideal.mul_mem_mul hf hεI)
  refine ⟨aeval x P.f * -b, ⟨I.mul_mem_right _ hf, ?_, ?_⟩, ?_⟩
  · rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ (by grind)]; grind
  · rw [← IsNilpotent.isUnit_quotient_mk_iff (I := I) ⟨2, hI⟩, ← Ideal.Quotient.mkₐ_eq_mk R,
      ← aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, map_add,
      Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right _ hf), add_zero]
    exact hx.2
  · rintro ε' ⟨hε'I, hε', hε''⟩
    rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ (hI.le (Ideal.pow_mem_pow hε'I 2))] at hε'
    have : ε * ε' = 0 := ((pow_two _).symm.trans hI).le (Ideal.mul_mem_mul hεI hε'I)
    grind

中文:
引理 存在Unique_hasMap_of_hasMap_quotient_of_sq_eq_bot
  证明: by
  have hf := Ideal.Quotient.eq_zero_iff_mem.mp
    ((aeval_algHom_apply (Ideal.Quotient.mkₐ R I) _ _).symm.trans hx.1)
  obtain ⟨⟨_, a, ha, -⟩, rfl⟩ := hx.2
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp_rw [← Ideal.Quotient.mkₐ_eq_mk R, aeval_algHom_apply, ← map_mul, ← map_one
    (Ideal.Quotient.mkₐ R I), Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ha
  obtain ⟨p₁, p₂, n, e⟩ := P.cond
  apply_fun aeval x at e
  simp only [map_add, map_mul, map_pow] at e
  obtain ⟨ε, hεI, b, hb⟩ : exists ε in I, exists b, aeval x (derivative P.f) * b = 1 + ε := by
    refine ⟨_, ?_, (a ^ n * aeval x p₁), sub_eq_iff_eq_add'.mp rfl⟩
    convert_to (aeval x P.g * a) ^ n - 1 - aeval x P.f * (a ^ n * aeval x p₂) in I
    · linear_combination a ^ n * e
    · exact sub_mem (Ideal.mem_of_dvd _ (sub_one_dvd_pow_sub_one _ _) ha) (I.mul_mem_right _ hf)
  have : aeval x P.f ^ 2 = 0 := hI.le (Ideal.pow_mem_pow hf 2)
  have : aeval x P.f * ε = 0 := ((pow_two _).symm.trans hI).le (Ideal.mul_mem_mul hf hεI)
  refine ⟨aeval x P.f * -b, ⟨I.mul_mem_right _ hf, ?_, ?_⟩, ?_⟩
  · rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ (by grind)]; grind
  · rw [← IsNilpotent.isUnit_quotient_mk_iff (I := I) ⟨2, hI⟩, ← Ideal.Quotient.mkₐ_eq_mk R,
      ← aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, map_add,
      Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right _ hf), add_zero]
    exact hx.2
  · rintro ε' ⟨hε'I, hε', hε''⟩
    rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ (hI.le (Ideal.pow_mem_pow hε'I 2))] at hε'
    have : ε * ε' = 0 := ((pow_two _).symm.trans hI).le (Ideal.mul_mem_mul hεI hε'I)
    grind

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem.mp, Ideal.Quotient.mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.Quotient.mk_surjective, P.cond, Quotient, aeval_algHom_apply, apply_fun, eq_zero_iff_mem, map_add, map_mul, map_one, map_pow, mk_eq_mk_iff_sub_mem, mk_surjective, simp_rw, symm.trans
-/
lemma existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot
    (I : Ideal S) (hI : I ^ 2 = ⊥) (x : S) (hx : P.HasMap (Ideal.Quotient.mk I x)) :
    exists! ε, ε in I ∧ P.HasMap (x + ε) := by
  have hf := Ideal.Quotient.eq_zero_iff_mem.mp
    ((aeval_algHom_apply (Ideal.Quotient.mkₐ R I) _ _).symm.trans hx.1)
  obtain ⟨⟨_, a, ha, -⟩, rfl⟩ := hx.2
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp_rw [← Ideal.Quotient.mkₐ_eq_mk R, aeval_algHom_apply, ← map_mul, ← map_one
    (Ideal.Quotient.mkₐ R I), Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ha
  obtain ⟨p₁, p₂, n, e⟩ := P.cond
  apply_fun aeval x at e
  simp only [map_add, map_mul, map_pow] at e
  obtain ⟨ε, hεI, b, hb⟩ : exists ε in I, exists b, aeval x (derivative P.f) * b = 1 + ε := by
    refine ⟨_, ?_, (a ^ n * aeval x p₁), sub_eq_iff_eq_add'.mp rfl⟩
    convert_to (aeval x P.g * a) ^ n - 1 - aeval x P.f * (a ^ n * aeval x p₂) in I
    · linear_combination a ^ n * e
    · exact sub_mem (Ideal.mem_of_dvd _ (sub_one_dvd_pow_sub_one _ _) ha) (I.mul_mem_right _ hf)
  have : aeval x P.f ^ 2 = 0 := hI.le (Ideal.pow_mem_pow hf 2)
  have : aeval x P.f * ε = 0 := ((pow_two _).symm.trans hI).le (Ideal.mul_mem_mul hf hεI)
  refine ⟨aeval x P.f * -b, ⟨I.mul_mem_right _ hf, ?_, ?_⟩, ?_⟩
  · rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ (by grind)]; grind
  · rw [← IsNilpotent.isUnit_quotient_mk_iff (I := I) ⟨2, hI⟩, ← Ideal.Quotient.mkₐ_eq_mk R,
      ← aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, map_add,
      Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right _ hf), add_zero]
    exact hx.2
  · rintro ε' ⟨hε'I, hε', hε''⟩
    rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ (hI.le (Ideal.pow_mem_pow hε'I 2))] at hε'
    have : ε * ε' = 0 := ((pow_two _).symm.trans hI).le (Ideal.mul_mem_mul hεI hε'I)
    grind

-- This works even if `f` is not monic. Generalize if we care.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra.FormallyEtale R P.Ring
  body: by
  refine Algebra.FormallyEtale.iff_comp_bijective.mpr fun S _ _ I hI => ?_
  rw [← P.homEquiv.symm.bijective.of_comp_iff]; rw [← P.homEquiv.bijective.of_comp_iff']
  suffices forall x, P.HasMap (Ideal.Quotient.mk I x) -> exists! a : { x : S // P.HasMap x }, a - x in I by
    simpa [Function.bijective_iff_existsUnique, Ideal.Quotient.mk_surjective.forall,
      Subtype.ext_iff, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  intro x hx
  obtain ⟨ε, ⟨hεI, hε⟩, H⟩ := P.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot I hI _ hx
  exact ⟨⟨x + ε, hε⟩, by simpa, fun y hy =>
    Subtype.ext (sub_eq_iff_eq_add'.mp (H _ ⟨hy, by simpa using y.2⟩))⟩

中文:
实例 :
  签名: 代数.形式平展 R P.环
  定义体: by
  refine Algebra.FormallyEtale.iff_comp_bijective.mpr fun S _ _ I hI => ?_
  rw [← P.homEquiv.symm.bijective.of_comp_iff]; rw [← P.homEquiv.bijective.of_comp_iff']
  suffices forall x, P.HasMap (Ideal.Quotient.mk I x) -> exists! a : { x : S // P.HasMap x }, a - x in I by
    simpa [Function.bijective_iff_existsUnique, Ideal.Quotient.mk_surjective.forall,
      Subtype.ext_iff, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  intro x hx
  obtain ⟨ε, ⟨hεI, hε⟩, H⟩ := P.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot I hI _ hx
  exact ⟨⟨x + ε, hε⟩, by simpa, fun y hy =>
    Subtype.ext (sub_eq_iff_eq_add'.mp (H _ ⟨hy, by simpa using y.2⟩))⟩

Depends on / 依赖: Algebra, Algebra.FormallyEtale.iff_comp_bijective.mpr, FormallyEtale, Function, Function.bijective_iff_existsUnique, HasMap, Ideal.Quotient.mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.Quotient.mk_surjective.forall, P.HasMap, P.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot, P.homEquiv.bijective.of_comp_iff, P.homEquiv.symm.bijective.of_comp_iff, Quotient, Subtype, Subtype.ext_iff, bijective, bijective_iff_existsUnique, existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot, ext_iff
-/
instance : Algebra.FormallyEtale R P.Ring := by
  refine Algebra.FormallyEtale.iff_comp_bijective.mpr fun S _ _ I hI => ?_
  rw [← P.homEquiv.symm.bijective.of_comp_iff]; rw [← P.homEquiv.bijective.of_comp_iff']
  suffices forall x, P.HasMap (Ideal.Quotient.mk I x) -> exists! a : { x : S // P.HasMap x }, a - x in I by
    simpa [Function.bijective_iff_existsUnique, Ideal.Quotient.mk_surjective.forall,
      Subtype.ext_iff, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  intro x hx
  obtain ⟨ε, ⟨hεI, hε⟩, H⟩ := P.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot I hI _ hx
  exact ⟨⟨x + ε, hε⟩, by simpa, fun y hy =>
    Subtype.ext (sub_eq_iff_eq_add'.mp (H _ ⟨hy, by simpa using y.2⟩))⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra.Etale R P.Ring
  body: .quotient (Submodule.fg_span (by simp))

中文:
实例 :
  签名: 代数.平展 R P.环
  定义体: .quotient (Submodule.fg_span (by simp))

Depends on / 依赖: Submodule, Submodule.fg_span, fg_span, quotient
-/
instance : Algebra.Etale R P.Ring where
  finitePresentation := .quotient (Submodule.fg_span (by simp))

/--
Definition of `equivPolynomialQuotient` / `equivPolynomialQuotient` 的定义

English:
definition equivPolynomialQuotient
  signature: :
  body: .refl ..

中文:
定义 equivPolynomialQuotient
  签名: :
  定义体: .refl ..
-/
def equivPolynomialQuotient :
    P.Ring ≃ₐ[R] R[X][Y] ⧸ Ideal.span {C P.f, Y * C P.g - 1} := .refl ..

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `equivAwayAdjoinRoot` / `equivAwayAdjoinRoot` 的定义

English:
definition equivAwayAdjoinRoot
  signature: :
  body: by
  refine .ofAlgHom (P.lift (algebraMap (AdjoinRoot P.f) _ (.root P.f)) ⟨?_, ?_⟩)
    (IsLocalization.Away.liftAlgHom (AdjoinRoot.mk P.f P.g)
      (f := AdjoinRoot.liftAlgHom _ _ P.X P.hasMap_X.1) P.hasMap_X.2) ?_ ?_
  · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq]
    exact IsLocalization.Away.algebraMap_isUnit ..
  · ext; simp [Algebra.algHom]
  · ext; simp

中文:
定义 equivAwayAdjoinRoot
  签名: :
  定义体: by
  refine .ofAlgHom (P.lift (algebraMap (AdjoinRoot P.f) _ (.root P.f)) ⟨?_, ?_⟩)
    (IsLocalization.Away.liftAlgHom (AdjoinRoot.mk P.f P.g)
      (f := AdjoinRoot.liftAlgHom _ _ P.X P.hasMap_X.1) P.hasMap_X.2) ?_ ?_
  · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq]
    exact IsLocalization.Away.algebraMap_isUnit ..
  · ext; simp [Algebra.algHom]
  · ext; simp

Depends on / 依赖: AdjoinRoot, AdjoinRoot.aeval_eq, AdjoinRoot.liftAlgHom, AdjoinRoot.mk, AdjoinRoot.mk_self, Algebra, Algebra.algHom, IsLocalization, IsLocalization.Away.algebraMap_isUnit, IsLocalization.Away.liftAlgHom, P.hasMap_X, P.lift, aeval_algebraMap_apply, aeval_eq, algHom, algebraMap, algebraMap_isUnit, hasMap_X, liftAlgHom, map_zero
-/
def equivAwayAdjoinRoot :
    P.Ring ≃ₐ[R] Localization.Away (AdjoinRoot.mk P.f P.g) := by
  refine .ofAlgHom (P.lift (algebraMap (AdjoinRoot P.f) _ (.root P.f)) ⟨?_, ?_⟩)
    (IsLocalization.Away.liftAlgHom (AdjoinRoot.mk P.f P.g)
      (f := AdjoinRoot.liftAlgHom _ _ P.X P.hasMap_X.1) P.hasMap_X.2) ?_ ?_
  · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq]
    exact IsLocalization.Away.algebraMap_isUnit ..
  · ext; simp [Algebra.algHom]
  · ext; simp

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `equivAwayQuotient` / `equivAwayQuotient` 的定义

English:
definition equivAwayQuotient
  signature: :
  body: by
  refine .ofAlgHom (P.lift (algebraMap R[X] _ .X) ⟨?_, ?_⟩)
    (Ideal.Quotient.liftₐ _ (IsLocalization.Away.liftAlgHom (P.g) P.hasMap_X.2) ?_) ?_ ?_
  · rw [aeval_algebraMap_apply, IsScalarTower.algebraMap_apply _ (Localization.Away P.g) (_ ⧸ _),
      Ideal.Quotient.algebraMap_eq, aeval_X_left_apply, Ideal.Quotient.mk_singleton_self]
  · rw [aeval_algebraMap_apply, IsScalarTower.algebraMap_apply _ (Localization.Away P.g) (_ ⧸ _),
      aeval_X_left_apply]
    exact (IsLocalization.Away.algebraMap_isUnit ..).map _
  · change Ideal.span _ <= RingHom.ker _
    simpa [Ideal.span_le] using P.hasMap_X.1
  · apply Ideal.Quotient.algHom_ext
    ext
    simp [Algebra.algHom, IsScalarTower.algebraMap_apply R[X] (Localization.Away P.g) (_ ⧸ _),
      -Ideal.Quotient.mk_algebraMap]
  · ext; simp [IsScalarTower.algebraMap_apply R[X] (Localization.Away P.g) (_ ⧸ _),
      -Ideal.Quotient.mk_algebraMap]

中文:
定义 equivAwayQuotient
  签名: :
  定义体: by
  refine .ofAlgHom (P.lift (algebraMap R[X] _ .X) ⟨?_, ?_⟩)
    (Ideal.Quotient.liftₐ _ (IsLocalization.Away.liftAlgHom (P.g) P.hasMap_X.2) ?_) ?_ ?_
  · rw [aeval_algebraMap_apply, IsScalarTower.algebraMap_apply _ (Localization.Away P.g) (_ ⧸ _),
      Ideal.Quotient.algebraMap_eq, aeval_X_left_apply, Ideal.Quotient.mk_singleton_self]
  · rw [aeval_algebraMap_apply, IsScalarTower.algebraMap_apply _ (Localization.Away P.g) (_ ⧸ _),
      aeval_X_left_apply]
    exact (IsLocalization.Away.algebraMap_isUnit ..).map _
  · change Ideal.span _ <= RingHom.ker _
    simpa [Ideal.span_le] using P.hasMap_X.1
  · apply Ideal.Quotient.algHom_ext
    ext
    simp [Algebra.algHom, IsScalarTower.algebraMap_apply R[X] (Localization.Away P.g) (_ ⧸ _),
      -Ideal.Quotient.mk_algebraMap]
  · ext; simp [IsScalarTower.algebraMap_apply R[X] (Localization.Away P.g) (_ ⧸ _),
      -Ideal.Quotient.mk_algebraMap]

Depends on / 依赖: Ideal.Quotient.algebraMap_eq, Ideal.Quotient.lift, Ideal.Quotient.mk_singleton_self, IsLocalization, IsLocalization.Away.algebraMap_isUnit, IsLocalization.Away.liftAlgHom, IsScalarTower, IsScalarTower.algebraMap_apply, Localization, Localization.Away, P.hasMap_X, P.lift, Quotient, aeval_X_left_apply, aeval_algebraMap_apply, algebraMap, algebraMap_apply, algebraMap_eq, algebraMap_isUnit, hasMap_X
-/
def equivAwayQuotient :
    P.Ring ≃ₐ[R] Localization.Away P.g ⧸ Ideal.span {algebraMap _ (Localization.Away P.g) P.f} := by
  refine .ofAlgHom (P.lift (algebraMap R[X] _ .X) ⟨?_, ?_⟩)
    (Ideal.Quotient.liftₐ _ (IsLocalization.Away.liftAlgHom (P.g) P.hasMap_X.2) ?_) ?_ ?_
  · rw [aeval_algebraMap_apply, IsScalarTower.algebraMap_apply _ (Localization.Away P.g) (_ ⧸ _),
      Ideal.Quotient.algebraMap_eq, aeval_X_left_apply, Ideal.Quotient.mk_singleton_self]
  · rw [aeval_algebraMap_apply, IsScalarTower.algebraMap_apply _ (Localization.Away P.g) (_ ⧸ _),
      aeval_X_left_apply]
    exact (IsLocalization.Away.algebraMap_isUnit ..).map _
  · change Ideal.span _ <= RingHom.ker _
    simpa [Ideal.span_le] using P.hasMap_X.1
  · apply Ideal.Quotient.algHom_ext
    ext
    simp [Algebra.algHom, IsScalarTower.algebraMap_apply R[X] (Localization.Away P.g) (_ ⧸ _),
      -Ideal.Quotient.mk_algebraMap]
  · ext; simp [IsScalarTower.algebraMap_apply R[X] (Localization.Away P.g) (_ ⧸ _),
      -Ideal.Quotient.mk_algebraMap]

/--
Definition of `equivMvPolynomialQuotient` / `equivMvPolynomialQuotient` 的定义

English:
definition equivMvPolynomialQuotient
  signature: :
  body: Ideal.quotientEquivAlg _ _ (Bivariate.equivMvPolynomial R)
    (by simp only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]; rfl)

中文:
定义 equivMvPolynomialQuotient
  签名: :
  定义体: Ideal.quotientEquivAlg _ _ (Bivariate.equivMvPolynomial R)
    (by simp only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]; rfl)

Depends on / 依赖: Bivariate, Bivariate.equivMvPolynomial, Ideal.map_span, Ideal.quotientEquivAlg, Set.image_insert_eq, Set.image_singleton, equivMvPolynomial, image_insert_eq, image_singleton, map_span, quotientEquivAlg
-/
def equivMvPolynomialQuotient :
    P.Ring ≃ₐ[R] MvPolynomial (Fin 2) R ⧸ Ideal.span
      {Bivariate.equivMvPolynomial R (C P.f), Bivariate.equivMvPolynomial R (.X * C P.g - 1)} :=
  Ideal.quotientEquivAlg _ _ (Bivariate.equivMvPolynomial R)
    (by simp only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]; rfl)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `equivMvPolynomialQuotient_symm_apply` / 引理 `equivMvPolynomialQuotient_symm_apply`

English:
lemma equivMvPolynomialQuotient_symm_apply
  proof: by
  simp [equivMvPolynomialQuotient, StandardEtalePair.Ring]; rfl

中文:
引理 equivMvPolynomialQuotient_symm_apply
  证明: by
  simp [equivMvPolynomialQuotient, StandardEtalePair.Ring]; rfl

Depends on / 依赖: StandardEtalePair, StandardEtalePair.Ring, equivMvPolynomialQuotient
-/
lemma equivMvPolynomialQuotient_symm_apply :
    P.equivMvPolynomialQuotient.symm (Ideal.Quotient.mk _ (.X 0)) = P.X := by
  simp [equivMvPolynomialQuotient, StandardEtalePair.Ring]; rfl

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def map (f : R ->+* S)
  body: P.f.map f
  monic_f := P.monic_f.map _
  g := P.g.map f
  cond := by
    obtain ⟨p₁, p₂, n, e⟩ := P.cond
    refine ⟨p₁.map f, p₂.map f, n, ?_⟩
    simp [← Polynomial.map_mul, ← Polynomial.map_add, e]

中文:
定义 noncomputable
  签名: def map (f : R ->+* S)
  定义体: P.f.map f
  monic_f := P.monic_f.map _
  g := P.g.map f
  cond := by
    obtain ⟨p₁, p₂, n, e⟩ := P.cond
    refine ⟨p₁.map f, p₂.map f, n, ?_⟩
    simp [← Polynomial.map_mul, ← Polynomial.map_add, e]
-/
@[simps] protected noncomputable def map (f : R ->+* S) : StandardEtalePair S where
  f := P.f.map f
  monic_f := P.monic_f.map _
  g := P.g.map f
  cond := by
    obtain ⟨p₁, p₂, n, e⟩ := P.cond
    refine ⟨p₁.map f, p₂.map f, n, ?_⟩
    simp [← Polynomial.map_mul, ← Polynomial.map_add, e]

/--
lemma `HasMap.map_algebraMap` / 引理 `HasMap.map_algebraMap`

English:
lemma HasMap.map_algebraMap
  given: [Algebra S T] [IsScalarTower R S T] {x : T} (H : P.HasMap x)
  proof: by
  simpa [HasMap]

中文:
引理 HasMap.map_algebraMap
  条件: [代数 S T] [标量塔 R S T] {x : T} (H : P.HasMap x)
  证明: by
  simpa [HasMap]

Depends on / 依赖: HasMap
-/
lemma HasMap.map_algebraMap [Algebra S T] [IsScalarTower R S T] {x : T} (H : P.HasMap x) :
    (P.map (algebraMap R S)).HasMap x := by
  simpa [HasMap]

end StandardEtalePair

/--
Definition of `StandardEtalePresentation` / `StandardEtalePresentation` 的定义

English:
structure StandardEtalePresentation
  parameters: (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  axioms and operations (3):
    - x : S
    - hasMap : P.HasMap x
    - lift_bijective : Function.Bijective (P.lift x hasMap)

中文:
结构 StandardEtalePresentation
  参数: (R S : 类型) [交换环 R] [交换环 S] [代数 R S]
  公理与运算 (3 个):
    - x : S
    - hasMap : P.HasMap x
    - lift_bijective : 函数.双射 (P.lift x hasMap)
-/
structure StandardEtalePresentation (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] extends
    P : StandardEtalePair R where
  /-- The image of X in a `StandardEtalePresentation`. -/
  x : S
  hasMap : P.HasMap x
  lift_bijective : Function.Bijective (P.lift x hasMap)

variable (P : StandardEtalePresentation R S)

/--
Definition of `StandardEtalePresentation.equivRing` / `StandardEtalePresentation.equivRing` 的定义

English:
definition StandardEtalePresentation.equivRing
  signature: : S ≃ₐ[R] P.Ring
  body: .symm .ofBijective _ P.lift_bijective

@[simp]

中文:
定义 StandardEtalePresentation.equivRing
  签名: : S ≃ₐ[R] P.环
  定义体: .symm .ofBijective _ P.lift_bijective

@[simp]

Depends on / 依赖: P.lift_bijective, lift_bijective, ofBijective
-/
def StandardEtalePresentation.equivRing : S ≃ₐ[R] P.Ring :=
.symm .ofBijective _ P.lift_bijective

@[simp]
/--
lemma `StandardEtalePresentation.equivRing_symm_X` / 引理 `StandardEtalePresentation.equivRing_symm_X`

English:
lemma StandardEtalePresentation.equivRing_symm_X
  statement: P.equivRing.symm P.X = P.x
  proof: P.lift_X _ P.hasMap

@[simp]

中文:
引理 StandardEtalePresentation.equivRing_symm_X
  结论: P.equivRing.symm P.X = P.x
  证明: P.lift_X _ P.hasMap

@[simp]

Depends on / 依赖: P.hasMap, P.lift_X, hasMap, lift_X
-/
lemma StandardEtalePresentation.equivRing_symm_X : P.equivRing.symm P.X = P.x :=
  P.lift_X _ P.hasMap

@[simp]
/--
lemma `StandardEtalePresentation.equivRing_x` / 引理 `StandardEtalePresentation.equivRing_x`

English:
lemma StandardEtalePresentation.equivRing_x
  statement: P.equivRing P.x = P.X
  proof: (P.equivRing.symm_apply_eq.mp P.equivRing_symm_X).symm

中文:
引理 StandardEtalePresentation.equivRing_x
  结论: P.equivRing P.x = P.X
  证明: (P.equivRing.symm_apply_eq.mp P.equivRing_symm_X).symm

Depends on / 依赖: P.equivRing.symm_apply_eq.mp, P.equivRing_symm_X, equivRing, equivRing_symm_X, symm_apply_eq
-/
lemma StandardEtalePresentation.equivRing_x : P.equivRing P.x = P.X :=
  (P.equivRing.symm_apply_eq.mp P.equivRing_symm_X).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The `Algebra.Presentation` associated to a standard etale presentation. -/
@[simps! relation val]
/--
Definition of `StandardEtalePresentation.toPresentation` / `StandardEtalePresentation.toPresentation` 的定义

English:
definition StandardEtalePresentation.toPresentation
  signature: : Algebra.Presentation R S (Fin 2) (Fin 2) where
  body: Algebra.Generators.ofAlgHom ((P.lift _ P.hasMap).comp
      (P.equivMvPolynomialQuotient.symm.toAlgHom.comp (Ideal.Quotient.mkₐ _ _)))
    (P.lift_bijective.surjective.comp
      (P.equivMvPolynomialQuotient.symm.surjective.comp Ideal.Quotient.mk_surjective))
  relation := ![Bivariate.equivMvPolynomial R (C P.f),
    Bivariate.equivMvPolynomial R (.X * C P.g - 1)]
  span_range_relation_eq_ker := by
    rw [Algebra.Generators.ker_ofAlgHom]; rw [AlgHom.toRingHom_eq_coe]; rw [AlgHom.comp_toRingHom]; rw [AlgHom.comp_toRingHom]; rw [RingHom.ker_comp_of_injective _ (by exact P.lift_bijective.injective)]; rw [RingHom.ker_comp_of_injective _ (by exact P.equivMvPolynomialQuotient.symm.injective)]
    simp [Set.pair_comm]

中文:
定义 StandardEtalePresentation.toPresentation
  签名: : 代数.呈现 R S (有限集 2) (有限集 2) where
  定义体: Algebra.Generators.ofAlgHom ((P.lift _ P.hasMap).comp
      (P.equivMvPolynomialQuotient.symm.toAlgHom.comp (Ideal.Quotient.mkₐ _ _)))
    (P.lift_bijective.surjective.comp
      (P.equivMvPolynomialQuotient.symm.surjective.comp Ideal.Quotient.mk_surjective))
  relation := ![Bivariate.equivMvPolynomial R (C P.f),
    Bivariate.equivMvPolynomial R (.X * C P.g - 1)]
  span_range_relation_eq_ker := by
    rw [Algebra.Generators.ker_ofAlgHom]; rw [AlgHom.toRingHom_eq_coe]; rw [AlgHom.comp_toRingHom]; rw [AlgHom.comp_toRingHom]; rw [RingHom.ker_comp_of_injective _ (by exact P.lift_bijective.injective)]; rw [RingHom.ker_comp_of_injective _ (by exact P.equivMvPolynomialQuotient.symm.injective)]
    simp [Set.pair_comm]

Depends on / 依赖: Algebra, Algebra.Generators.ofAlgHom, Generators, P.hasMap, P.lift, hasMap, ofAlgHom
-/
def StandardEtalePresentation.toPresentation : Algebra.Presentation R S (Fin 2) (Fin 2) where
  __ := Algebra.Generators.ofAlgHom ((P.lift _ P.hasMap).comp
      (P.equivMvPolynomialQuotient.symm.toAlgHom.comp (Ideal.Quotient.mkₐ _ _)))
    (P.lift_bijective.surjective.comp
      (P.equivMvPolynomialQuotient.symm.surjective.comp Ideal.Quotient.mk_surjective))
  relation := ![Bivariate.equivMvPolynomial R (C P.f),
    Bivariate.equivMvPolynomial R (.X * C P.g - 1)]
  span_range_relation_eq_ker := by
    rw [Algebra.Generators.ker_ofAlgHom]; rw [AlgHom.toRingHom_eq_coe]; rw [AlgHom.comp_toRingHom]; rw [AlgHom.comp_toRingHom]; rw [RingHom.ker_comp_of_injective _ (by exact P.lift_bijective.injective)]; rw [RingHom.ker_comp_of_injective _ (by exact P.equivMvPolynomialQuotient.symm.injective)]
    simp [Set.pair_comm]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `StandardEtalePresentation.aeval_val_equivMvPolynomial` / 引理 `StandardEtalePresentation.aeval_val_equivMvPolynomial`

English:
lemma StandardEtalePresentation.aeval_val_equivMvPolynomial
  given: (p : R[X])
  proof: by
  change (((MvPolynomial.aeval _).comp (Bivariate.equivMvPolynomial R).toAlgHom).comp CAlgHom) _ = _
  congr 1
  ext
  simp

中文:
引理 StandardEtalePresentation.aeval_val_equivMvPolynomial
  条件: (p : R[X])
  证明: by
  change (((MvPolynomial.aeval _).comp (Bivariate.equivMvPolynomial R).toAlgHom).comp CAlgHom) _ = _
  congr 1
  ext
  simp
-/
@[simp] lemma StandardEtalePresentation.aeval_val_equivMvPolynomial (p : R[X]) :
    MvPolynomial.aeval P.toPresentation.val
    (Bivariate.equivMvPolynomial R (.C p)) = p.aeval P.x := by
  change (((MvPolynomial.aeval _).comp (Bivariate.equivMvPolynomial R).toAlgHom).comp CAlgHom) _ = _
  congr 1
  ext
  simp

attribute [local simp] Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det
  Matrix.det_fin_two Algebra.PreSubmersivePresentation.jacobiMatrix_apply
  Polynomial.Bivariate.pderiv_zero_equivMvPolynomial
  Polynomial.Bivariate.pderiv_one_equivMvPolynomial

set_option backward.isDefEq.respectTransparency.types false in
/-- The `Algebra.SubmersivePresentation` associated to a standard etale presentation. -/
@[simps map toPreSubmersivePresentation_toPresentation]
/--
Definition of `StandardEtalePresentation.toSubmersivePresentation` / `StandardEtalePresentation.toSubmersivePresentation` 的定义

English:
definition StandardEtalePresentation.toSubmersivePresentation
  signature: :
  body: P.toPresentation
  map := id
  map_inj := Function.injective_id
  jacobian_isUnit := by simp [P.hasMap.2, P.hasMap.isUnit_derivative_f]

中文:
定义 StandardEtalePresentation.toSubmersivePresentation
  签名: :
  定义体: P.toPresentation
  map := id
  map_inj := Function.injective_id
  jacobian_isUnit := by simp [P.hasMap.2, P.hasMap.isUnit_derivative_f]

Depends on / 依赖: P.toPresentation, toPresentation
-/
def StandardEtalePresentation.toSubmersivePresentation :
    Algebra.SubmersivePresentation R S (Fin 2) (Fin 2) where
  __ := P.toPresentation
  map := id
  map_inj := Function.injective_id
  jacobian_isUnit := by simp [P.hasMap.2, P.hasMap.isUnit_derivative_f]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `StandardEtalePresentation.toSubmersivePresentation_jacobian` / 引理 `StandardEtalePresentation.toSubmersivePresentation_jacobian`

English:
lemma StandardEtalePresentation.toSubmersivePresentation_jacobian
  proof: by
  simp [StandardEtalePresentation.toSubmersivePresentation]

中文:
引理 StandardEtalePresentation.toSubmersivePresentation_jacobian
  证明: by
  simp [StandardEtalePresentation.toSubmersivePresentation]

Depends on / 依赖: StandardEtalePresentation, StandardEtalePresentation.toSubmersivePresentation, toSubmersivePresentation
-/
lemma StandardEtalePresentation.toSubmersivePresentation_jacobian :
    P.toSubmersivePresentation.jacobian = aeval P.x P.f.derivative * aeval P.x P.g := by
  simp [StandardEtalePresentation.toSubmersivePresentation]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `StandardEtalePresentation.exists_mul_aeval_x_g_pow_eq_aeval_x` / 引理 `StandardEtalePresentation.exists_mul_aeval_x_g_pow_eq_aeval_x`

English:
lemma StandardEtalePresentation.exists_mul_aeval_x_g_pow_eq_aeval_x
  given: (x : S)
  proof: by
  obtain ⟨x, rfl⟩ := (P.equivRing.trans P.P.equivAwayAdjoinRoot).symm.surjective x
  obtain ⟨⟨p, ⟨_, n, rfl⟩⟩, e⟩ := IsLocalization.surj (.powers (AdjoinRoot.mk P.f P.g)) x
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective p
  refine ⟨p, n, P.equivRing.injective ?_⟩
  simpa [← aeval_algHom_apply, StandardEtalePair.equivAwayAdjoinRoot, ← aeval_def] using
    congr(P.equivAwayAdjoinRoot.symm $e)

中文:
引理 StandardEtalePresentation.存在_mul_aeval_x_g_pow_eq_aeval_x
  条件: (x : S)
  证明: by
  obtain ⟨x, rfl⟩ := (P.equivRing.trans P.P.equivAwayAdjoinRoot).symm.surjective x
  obtain ⟨⟨p, ⟨_, n, rfl⟩⟩, e⟩ := IsLocalization.surj (.powers (AdjoinRoot.mk P.f P.g)) x
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective p
  refine ⟨p, n, P.equivRing.injective ?_⟩
  simpa [← aeval_algHom_apply, StandardEtalePair.equivAwayAdjoinRoot, ← aeval_def] using
    congr(P.equivAwayAdjoinRoot.symm $e)

Depends on / 依赖: AdjoinRoot, AdjoinRoot.mk, AdjoinRoot.mk_surjective, IsLocalization, IsLocalization.surj, P.P.equivAwayAdjoinRoot, P.equivAwayAdjoinRoot.symm, P.equivRing.injective, P.equivRing.trans, StandardEtalePair, StandardEtalePair.equivAwayAdjoinRoot, aeval_algHom_apply, aeval_def, equivAwayAdjoinRoot, equivRing, injective, mk_surjective, powers, surjective, symm.surjective
-/
lemma StandardEtalePresentation.exists_mul_aeval_x_g_pow_eq_aeval_x (x : S) :
    exists p : R[X], exists n, x * P.g.aeval P.x ^ n = p.aeval P.x := by
  obtain ⟨x, rfl⟩ := (P.equivRing.trans P.P.equivAwayAdjoinRoot).symm.surjective x
  obtain ⟨⟨p, ⟨_, n, rfl⟩⟩, e⟩ := IsLocalization.surj (.powers (AdjoinRoot.mk P.f P.g)) x
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective p
  refine ⟨p, n, P.equivRing.injective ?_⟩
  simpa [← aeval_algHom_apply, StandardEtalePair.equivAwayAdjoinRoot, ← aeval_def] using
    congr(P.equivAwayAdjoinRoot.symm $e)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `StandardEtalePresentation.mapEquiv` / `StandardEtalePresentation.mapEquiv` 的定义

English:
definition StandardEtalePresentation.mapEquiv
  signature: (e : S ≃ₐ[R] T)
  body: P.P
  x := e P.x
  hasMap := P.hasMap.map e.toAlgHom
  lift_bijective := (show P.lift (e P.x) (P.hasMap.map e.toAlgHom) = e.toAlgHom.comp
    (P.lift _ P.hasMap) from P.hom_ext (by simp)) ▸ e.bijective.comp P.lift_bijective

中文:
定义 StandardEtalePresentation.mapEquiv
  签名: (e : S ≃ₐ[R] T)
  定义体: P.P
  x := e P.x
  hasMap := P.hasMap.map e.toAlgHom
  lift_bijective := (show P.lift (e P.x) (P.hasMap.map e.toAlgHom) = e.toAlgHom.comp
    (P.lift _ P.hasMap) from P.hom_ext (by simp)) ▸ e.bijective.comp P.lift_bijective
-/
def StandardEtalePresentation.mapEquiv (e : S ≃ₐ[R] T) : StandardEtalePresentation R T where
  P := P.P
  x := e P.x
  hasMap := P.hasMap.map e.toAlgHom
  lift_bijective := (show P.lift (e P.x) (P.hasMap.map e.toAlgHom) = e.toAlgHom.comp
    (P.lift _ P.hasMap) from P.hom_ext (by simp)) ▸ e.bijective.comp P.lift_bijective

/--
lemma `StandardEtalePresentation.hom_ext` / 引理 `StandardEtalePresentation.hom_ext`

English:
lemma StandardEtalePresentation.hom_ext
  given: {f₁ f₂ : S ->ₐ[R] T} (h : f₁ P.x = f₂ P.x)
  statement: f₁ = f₂
  proof: by
  have : f₁.comp P.equivRing.symm.toAlgHom = f₂.comp P.equivRing.symm.toAlgHom :=
    P.P.hom_ext (by simpa)
  ext x
  obtain ⟨x, rfl⟩ := P.equivRing.symm.surjective x
  exact congr($this x)

中文:
引理 StandardEtalePresentation.hom_ext
  条件: {f₁ f₂ : S ->ₐ[R] T} (h : f₁ P.x = f₂ P.x)
  结论: f₁ = f₂
  证明: by
  have : f₁.comp P.equivRing.symm.toAlgHom = f₂.comp P.equivRing.symm.toAlgHom :=
    P.P.hom_ext (by simpa)
  ext x
  obtain ⟨x, rfl⟩ := P.equivRing.symm.surjective x
  exact congr($this x)

Depends on / 依赖: P.P.hom_ext, P.equivRing.symm.surjective, P.equivRing.symm.toAlgHom, equivRing, hom_ext, surjective, toAlgHom
-/
lemma StandardEtalePresentation.hom_ext {f₁ f₂ : S ->ₐ[R] T} (h : f₁ P.x = f₂ P.x) : f₁ = f₂ := by
  have : f₁.comp P.equivRing.symm.toAlgHom = f₂.comp P.equivRing.symm.toAlgHom :=
    P.P.hom_ext (by simpa)
  ext x
  obtain ⟨x, rfl⟩ := P.equivRing.symm.surjective x
  exact congr($this x)

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency.types false in
/-- The base change of a standard etale algebra is standard etale. -/
noncomputable
/--
Definition of `StandardEtalePresentation.baseChange` / `StandardEtalePresentation.baseChange` 的定义

English:
definition StandardEtalePresentation.baseChange
  signature: :
  body: P.map (algebraMap R T)
  x := 1 otimesₜ P.x
  hasMap := (P.hasMap.map (Algebra.TensorProduct.includeRight (R := R) (A := T))).map_algebraMap
  lift_bijective := by
    algebraize [(algebraMap T (P.map (algebraMap R T)).Ring).comp (algebraMap R T)]
    have H : P.HasMap (P.map (algebraMap R T)).X := by
      simpa [StandardEtalePair.HasMap] using (P.map (algebraMap R T)).hasMap_X
    let f : T otimes[R] S ->ₐ[T] (P.map (algebraMap R T)).Ring :=
      Algebra.TensorProduct.lift (Algebra.ofId _ _) ((P.lift (P.map _).X H).comp P.equivRing)
        fun _ _ => .all _ _
    let α : T otimes[R] S ≃ₐ[T] (P.map (algebraMap R T)).Ring :=
      .ofAlgHom f ((P.map (algebraMap R T)).lift (1 otimesₜ[R] P.x)
        (P.hasMap.map (Algebra.TensorProduct.includeRight (R := R) (A := T))).map_algebraMap) (by
        ext; simp [f]) (by ext1; apply P.hom_ext; simp [f])
    exact α.symm.bijective

中文:
定义 StandardEtalePresentation.baseChange
  签名: :
  定义体: P.map (algebraMap R T)
  x := 1 otimesₜ P.x
  hasMap := (P.hasMap.map (Algebra.TensorProduct.includeRight (R := R) (A := T))).map_algebraMap
  lift_bijective := by
    algebraize [(algebraMap T (P.map (algebraMap R T)).Ring).comp (algebraMap R T)]
    have H : P.HasMap (P.map (algebraMap R T)).X := by
      simpa [StandardEtalePair.HasMap] using (P.map (algebraMap R T)).hasMap_X
    let f : T otimes[R] S ->ₐ[T] (P.map (algebraMap R T)).Ring :=
      Algebra.TensorProduct.lift (Algebra.ofId _ _) ((P.lift (P.map _).X H).comp P.equivRing)
        fun _ _ => .all _ _
    let α : T otimes[R] S ≃ₐ[T] (P.map (algebraMap R T)).Ring :=
      .ofAlgHom f ((P.map (algebraMap R T)).lift (1 otimesₜ[R] P.x)
        (P.hasMap.map (Algebra.TensorProduct.includeRight (R := R) (A := T))).map_algebraMap) (by
        ext; simp [f]) (by ext1; apply P.hom_ext; simp [f])
    exact α.symm.bijective

Depends on / 依赖: P.map, algebraMap
-/
def StandardEtalePresentation.baseChange :
    StandardEtalePresentation T (T otimes[R] S) where
  __ := P.map (algebraMap R T)
  x := 1 otimesₜ P.x
  hasMap := (P.hasMap.map (Algebra.TensorProduct.includeRight (R := R) (A := T))).map_algebraMap
  lift_bijective := by
    algebraize [(algebraMap T (P.map (algebraMap R T)).Ring).comp (algebraMap R T)]
    have H : P.HasMap (P.map (algebraMap R T)).X := by
      simpa [StandardEtalePair.HasMap] using (P.map (algebraMap R T)).hasMap_X
    let f : T otimes[R] S ->ₐ[T] (P.map (algebraMap R T)).Ring :=
      Algebra.TensorProduct.lift (Algebra.ofId _ _) ((P.lift (P.map _).X H).comp P.equivRing)
        fun _ _ => .all _ _
    let α : T otimes[R] S ≃ₐ[T] (P.map (algebraMap R T)).Ring :=
      .ofAlgHom f ((P.map (algebraMap R T)).lift (1 otimesₜ[R] P.x)
        (P.hasMap.map (Algebra.TensorProduct.includeRight (R := R) (A := T))).map_algebraMap) (by
        ext; simp [f]) (by ext1; apply P.hom_ext; simp [f])
    exact α.symm.bijective

namespace Algebra

/--
Definition of `IsStandardEtale` / `IsStandardEtale` 的定义

English:
class IsStandardEtale
  parameters: (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  axioms and operations (1):
    - nonempty_standardEtalePresentation : Nonempty (StandardEtalePresentation R S)

中文:
类 是StandardEtale
  参数: (R S : 类型) [交换环 R] [交换环 S] [代数 R S]
  公理与运算 (1 个):
    - nonempty_standardEtalePresentation : 非空 (StandardEtalePresentation R S)
-/
class IsStandardEtale (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] where
  nonempty_standardEtalePresentation : Nonempty (StandardEtalePresentation R S)

attribute [instance] IsStandardEtale.nonempty_standardEtalePresentation

instance (P : StandardEtalePair R) : IsStandardEtale R P.Ring :=
  ⟨⟨P, P.X, P.hasMap_X, by simpa [StandardEtalePair.lift_X_left] using Function.bijective_id⟩⟩

instance (priority := low) [IsStandardEtale R S] : Algebra.Etale R S :=
  .of_equiv IsStandardEtale.nonempty_standardEtalePresentation.some.equivRing.symm

/--
lemma `IsStandardEtale.of_equiv` / 引理 `IsStandardEtale.of_equiv`

English:
lemma IsStandardEtale.of_equiv
  given: (e : S ≃ₐ[R] T) [IsStandardEtale R S]
  statement: IsStandardEtale R T
  proof: ⟨⟨IsStandardEtale.nonempty_standardEtalePresentation.some.mapEquiv e⟩⟩

中文:
引理 是StandardEtale.of_equiv
  条件: (e : S ≃ₐ[R] T) [是StandardEtale R S]
  结论: 是StandardEtale R T
  证明: ⟨⟨IsStandardEtale.nonempty_standardEtalePresentation.some.mapEquiv e⟩⟩

Depends on / 依赖: IsStandardEtale, IsStandardEtale.nonempty_standardEtalePresentation.some.mapEquiv, mapEquiv, nonempty_standardEtalePresentation
-/
lemma IsStandardEtale.of_equiv (e : S ≃ₐ[R] T) [IsStandardEtale R S] : IsStandardEtale R T :=
  ⟨⟨IsStandardEtale.nonempty_standardEtalePresentation.some.mapEquiv e⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStandardEtale R R
  body: ⟨⟨⟨⟨.X, by simp, 1, 1, 0, 0, by simp⟩, 0, ⟨by simp, by simp⟩, by
    set P : StandardEtalePair R := ⟨.X, by simp, 1, 1, 0, 0, by simp⟩
    have : P.X = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
    let e := AlgEquiv.ofAlgHom (P.lift (0 : R) ⟨by simp [P], by simp [P]⟩) (Algebra.ofId _ _)
      (by ext) (by ext; simp [this])
    exact e.bijective⟩⟩⟩

中文:
实例 :
  签名: 是StandardEtale R R
  定义体: ⟨⟨⟨⟨.X, by simp, 1, 1, 0, 0, by simp⟩, 0, ⟨by simp, by simp⟩, by
    set P : StandardEtalePair R := ⟨.X, by simp, 1, 1, 0, 0, by simp⟩
    have : P.X = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
    let e := AlgEquiv.ofAlgHom (P.lift (0 : R) ⟨by simp [P], by simp [P]⟩) (Algebra.ofId _ _)
      (by ext) (by ext; simp [this])
    exact e.bijective⟩⟩⟩

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, Algebra, Algebra.ofId, Ideal.Quotient.eq_zero_iff_mem.mpr, Ideal.subset_span, P.lift, Quotient, Set.mem_insert, StandardEtalePair, bijective, e.bijective, eq_zero_iff_mem, mem_insert, ofAlgHom, subset_span
-/
instance : IsStandardEtale R R :=
  ⟨⟨⟨⟨.X, by simp, 1, 1, 0, 0, by simp⟩, 0, ⟨by simp, by simp⟩, by
    set P : StandardEtalePair R := ⟨.X, by simp, 1, 1, 0, 0, by simp⟩
    have : P.X = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
    let e := AlgEquiv.ofAlgHom (P.lift (0 : R) ⟨by simp [P], by simp [P]⟩) (Algebra.ofId _ _)
      (by ext) (by ext; simp [this])
    exact e.bijective⟩⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `IsStandardEtale.of_isLocalizationAway` / 引理 `IsStandardEtale.of_isLocalizationAway`

English:
lemma IsStandardEtale.of_isLocalizationAway
  statement: [IsStandardEtale R S]
  proof: by
  have P : StandardEtalePresentation R S := IsStandardEtale.nonempty_standardEtalePresentation.some
  obtain ⟨p, n, hp⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x s
  let P' : StandardEtalePair R := ⟨P.f, P.monic_f, p * P.g, have ⟨p₁, p₂, m, e⟩ := P.cond;
    ⟨p₁ * p ^ m, p₂ * p ^ m, m, by linear_combination e * p ^ m⟩⟩
  let S' := Localization.Away (AdjoinRoot.mk P.f P.g)
  let e : S ≃ₐ[R] S' := P.equivRing.trans P.P.equivAwayAdjoinRoot
  have := IsLocalization.Away.mul S' (Localization.Away (algebraMap _ S' (AdjoinRoot.mk P.f p)))
    (AdjoinRoot.mk P.f P.g) (.mk _ p)
  rw [← map_mul] at this
  have H : Submonoid.map e.symm.toRingEquiv.toMonoidHom (.powers
      (algebraMap _ S' (AdjoinRoot.mk P.f p))) = .powers (aeval P.x p) := by
    have : ((e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R _ S')).comp (AdjoinRoot.mkₐ P.f)) =
      aeval P.x := by ext; simp [e, StandardEtalePair.equivAwayAdjoinRoot]
    rw [Submonoid.map_powers]
    exact congr(Submonoid.powers ($this p))
  have : IsLocalization.Away (aeval P.x p) Sₛ :=
    IsLocalization.Away.of_associated (r := s) ⟨(P.hasMap.2.pow n).unit, hp⟩
  let e₁ : P'.Ring ≃ₐ[R]
      Localization.Away (algebraMap _ S' (AdjoinRoot.mk P.f p)) :=
    P'.equivAwayAdjoinRoot.trans ((IsLocalization.algEquiv (.powers (AdjoinRoot.mk P.f (p * P.g)))
      (Localization.Away (AdjoinRoot.mk P.f (p * P.g))) _).restrictScalars R)
  let e₂ : Localization.Away (algebraMap _ S' (AdjoinRoot.mk P.f p)) ≃ₐ[R] Sₛ :=
    { __ := IsLocalization.ringEquivOfRingEquiv _ _ _ H,
      commutes' r := by
        simp [IsScalarTower.algebraMap_apply R S' (Localization.Away _),
          - AlgEquiv.symm_toRingEquiv, IsScalarTower.algebraMap_eq R S Sₛ] }
  exact .of_equiv (e₁.trans e₂)

中文:
引理 是StandardEtale.of_isLocalizationAway
  结论: [是StandardEtale R S]
  证明: by
  have P : StandardEtalePresentation R S := IsStandardEtale.nonempty_standardEtalePresentation.some
  obtain ⟨p, n, hp⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x s
  let P' : StandardEtalePair R := ⟨P.f, P.monic_f, p * P.g, have ⟨p₁, p₂, m, e⟩ := P.cond;
    ⟨p₁ * p ^ m, p₂ * p ^ m, m, by linear_combination e * p ^ m⟩⟩
  let S' := Localization.Away (AdjoinRoot.mk P.f P.g)
  let e : S ≃ₐ[R] S' := P.equivRing.trans P.P.equivAwayAdjoinRoot
  have := IsLocalization.Away.mul S' (Localization.Away (algebraMap _ S' (AdjoinRoot.mk P.f p)))
    (AdjoinRoot.mk P.f P.g) (.mk _ p)
  rw [← map_mul] at this
  have H : Submonoid.map e.symm.toRingEquiv.toMonoidHom (.powers
      (algebraMap _ S' (AdjoinRoot.mk P.f p))) = .powers (aeval P.x p) := by
    have : ((e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R _ S')).comp (AdjoinRoot.mkₐ P.f)) =
      aeval P.x := by ext; simp [e, StandardEtalePair.equivAwayAdjoinRoot]
    rw [Submonoid.map_powers]
    exact congr(Submonoid.powers ($this p))
  have : IsLocalization.Away (aeval P.x p) Sₛ :=
    IsLocalization.Away.of_associated (r := s) ⟨(P.hasMap.2.pow n).unit, hp⟩
  let e₁ : P'.Ring ≃ₐ[R]
      Localization.Away (algebraMap _ S' (AdjoinRoot.mk P.f p)) :=
    P'.equivAwayAdjoinRoot.trans ((IsLocalization.algEquiv (.powers (AdjoinRoot.mk P.f (p * P.g)))
      (Localization.Away (AdjoinRoot.mk P.f (p * P.g))) _).restrictScalars R)
  let e₂ : Localization.Away (algebraMap _ S' (AdjoinRoot.mk P.f p)) ≃ₐ[R] Sₛ :=
    { __ := IsLocalization.ringEquivOfRingEquiv _ _ _ H,
      commutes' r := by
        simp [IsScalarTower.algebraMap_apply R S' (Localization.Away _),
          - AlgEquiv.symm_toRingEquiv, IsScalarTower.algebraMap_eq R S Sₛ] }
  exact .of_equiv (e₁.trans e₂)

Depends on / 依赖: AdjoinRoot, AdjoinRoot.mk, IsLocalization, IsLocalization.Away.mul, IsStandardEtale, IsStandardEtale.nonempty_standardEtalePresentation.some, Localization, Localization.Away, P.P.equivAwayAdjoinRoot, P.cond, P.equivRing.trans, P.exists_mul_aeval_x_g_pow_eq_aeval_x, P.monic_f, StandardEtalePair, StandardEtalePresentation, algebraMap, equivAwayAdjoinRoot, equivRing, exists_mul_aeval_x_g_pow_eq_aeval_x, linear_combination
-/
lemma IsStandardEtale.of_isLocalizationAway [IsStandardEtale R S]
    {Sₛ : Type*} [CommRing Sₛ] [Algebra S Sₛ]
    [Algebra R Sₛ] [IsScalarTower R S Sₛ] (s : S) [IsLocalization.Away s Sₛ] :
    IsStandardEtale R Sₛ := by
  have P : StandardEtalePresentation R S := IsStandardEtale.nonempty_standardEtalePresentation.some
  obtain ⟨p, n, hp⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x s
  let P' : StandardEtalePair R := ⟨P.f, P.monic_f, p * P.g, have ⟨p₁, p₂, m, e⟩ := P.cond;
    ⟨p₁ * p ^ m, p₂ * p ^ m, m, by linear_combination e * p ^ m⟩⟩
  let S' := Localization.Away (AdjoinRoot.mk P.f P.g)
  let e : S ≃ₐ[R] S' := P.equivRing.trans P.P.equivAwayAdjoinRoot
  have := IsLocalization.Away.mul S' (Localization.Away (algebraMap _ S' (AdjoinRoot.mk P.f p)))
    (AdjoinRoot.mk P.f P.g) (.mk _ p)
  rw [← map_mul] at this
  have H : Submonoid.map e.symm.toRingEquiv.toMonoidHom (.powers
      (algebraMap _ S' (AdjoinRoot.mk P.f p))) = .powers (aeval P.x p) := by
    have : ((e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R _ S')).comp (AdjoinRoot.mkₐ P.f)) =
      aeval P.x := by ext; simp [e, StandardEtalePair.equivAwayAdjoinRoot]
    rw [Submonoid.map_powers]
    exact congr(Submonoid.powers ($this p))
  have : IsLocalization.Away (aeval P.x p) Sₛ :=
    IsLocalization.Away.of_associated (r := s) ⟨(P.hasMap.2.pow n).unit, hp⟩
  let e₁ : P'.Ring ≃ₐ[R]
      Localization.Away (algebraMap _ S' (AdjoinRoot.mk P.f p)) :=
    P'.equivAwayAdjoinRoot.trans ((IsLocalization.algEquiv (.powers (AdjoinRoot.mk P.f (p * P.g)))
      (Localization.Away (AdjoinRoot.mk P.f (p * P.g))) _).restrictScalars R)
  let e₂ : Localization.Away (algebraMap _ S' (AdjoinRoot.mk P.f p)) ≃ₐ[R] Sₛ :=
    { __ := IsLocalization.ringEquivOfRingEquiv _ _ _ H,
      commutes' r := by
        simp [IsScalarTower.algebraMap_apply R S' (Localization.Away _),
          - AlgEquiv.symm_toRingEquiv, IsScalarTower.algebraMap_eq R S Sₛ] }
  exact .of_equiv (e₁.trans e₂)

/--
lemma `IsStandardEtale.of_surjective` / 引理 `IsStandardEtale.of_surjective`

English:
lemma IsStandardEtale.of_surjective
  proof: by
  let := f.toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq' f.comp_algebraMap.symm
  obtain ⟨e, he, hfe⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _ (Algebra.FinitePresentation.ker_fG_of_surjective f hf)).mp
      ((Algebra.FormallyEtale.iff_of_surjective hf).mp (.of_restrictScalars (R := R)))
  have := IsLocalization.away_of_isIdempotentElem he.one_sub (hfe.trans (by simp)) hf
  exact .of_isLocalizationAway (1 - e)

中文:
引理 是StandardEtale.of_surjective
  证明: by
  let := f.toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq' f.comp_algebraMap.symm
  obtain ⟨e, he, hfe⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _ (Algebra.FinitePresentation.ker_fG_of_surjective f hf)).mp
      ((Algebra.FormallyEtale.iff_of_surjective hf).mp (.of_restrictScalars (R := R)))
  have := IsLocalization.away_of_isIdempotentElem he.one_sub (hfe.trans (by simp)) hf
  exact .of_isLocalizationAway (1 - e)

Depends on / 依赖: Algebra, Algebra.FinitePresentation.ker_fG_of_surjective, Algebra.FormallyEtale.iff_of_surjective, FinitePresentation, FormallyEtale, Ideal.isIdempotentElem_iff_of_fg, IsLocalization, IsLocalization.away_of_isIdempotentElem, IsScalarTower, away_of_isIdempotentElem, comp_algebraMap, f.comp_algebraMap.symm, f.toAlgebra, he.one_sub, hfe.trans, iff_of_surjective, isIdempotentElem_iff_of_fg, ker_fG_of_surjective, of_algebraMap_eq, of_isLocalizationAway
-/
lemma IsStandardEtale.of_surjective
    [IsStandardEtale R S] [Algebra.Etale R T] (f : S ->ₐ[R] T) (hf : Function.Surjective f) :
    IsStandardEtale R T := by
  let := f.toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq' f.comp_algebraMap.symm
  obtain ⟨e, he, hfe⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _ (Algebra.FinitePresentation.ker_fG_of_surjective f hf)).mp
      ((Algebra.FormallyEtale.iff_of_surjective hf).mp (.of_restrictScalars (R := R)))
  have := IsLocalization.away_of_isIdempotentElem he.one_sub (hfe.trans (by simp)) hf
  exact .of_isLocalizationAway (1 - e)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra.IsStandardEtale
  signature: R S] :
  body: ⟨⟨Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some.baseChange⟩⟩

中文:
实例 [代数.是StandardEtale
  签名: R S] :
  定义体: ⟨⟨Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some.baseChange⟩⟩

Depends on / 依赖: Algebra, Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some.baseChange, IsStandardEtale, baseChange, nonempty_standardEtalePresentation
-/
instance [Algebra.IsStandardEtale R S] :
    Algebra.IsStandardEtale T (T otimes[R] S) :=
  ⟨⟨Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some.baseChange⟩⟩

end Algebra
