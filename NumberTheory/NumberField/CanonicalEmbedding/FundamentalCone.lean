/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.RingTheory.Ideal.IsPrincipal
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Fundamental Cone

Let `K` be a number field of signature `(r₁, r₂)`. We define an action of the units `(𝓞 K)ˣ` on
the mixed space `ℝ^r₁ × ℂ^r₂` via the `mixedEmbedding`. The fundamental cone is a cone in the
mixed space that is a fundamental domain for the action of `(𝓞 K)ˣ` modulo torsion.

## Main definitions and results

* `NumberField.mixedEmbedding.unitSMul`: the action of `(𝓞 K)ˣ` on the mixed space defined, for
  `u : (𝓞 K)ˣ`, by multiplication component by component with `mixedEmbedding K u`.

* `NumberField.mixedEmbedding.fundamentalCone`: a cone in the mixed space, i.e. a subset stable
  by multiplication by a nonzero real number, see `smul_mem_of_mem`, that is also a fundamental
  domain for the action of `(𝓞 K)ˣ` modulo torsion, see `exists_unit_smul_mem` and
  `torsion_unit_smul_mem_of_mem`.

* `NumberField.mixedEmbedding.fundamentalCone.idealSet`: for `J` an integral ideal, the intersection
  between the fundamental cone and the `idealLattice` defined by the image of `J`.

* `NumberField.mixedEmbedding.fundamentalCone.idealSetEquivNorm`: for `J` an integral ideal and `n`
  a natural integer, the equivalence between the elements of `idealSet K` of norm `n` and the
  product of the set of nonzero principal ideals of `K` divisible by `J` of norm `n` and the
  torsion of `K`.

## Tags

number field, canonical embedding, units, principal ideals
-/

@[expose] public section

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace

noncomputable section UnitSMul

/-- The action of `(𝓞 K)ˣ` on the mixed space `ℝ^r₁ × ℂ^r₂` defined, for `u : (𝓞 K)ˣ`, by
multiplication component by component with `mixedEmbedding K u`. -/
@[simps]
/--
Instance `unitSMul` / 实例 `unitSMul`

English:
instance unitSMul
  signature: : SMul (𝓞 K)ˣ (mixedSpace K) where
  body: mixedEmbedding K u * x

中文:
实例 unitSMul
  签名: : 标量乘法 (𝓞 K)ˣ (mixedSpace K) where
  定义体: mixedEmbedding K u * x

Depends on / 依赖: mixedEmbedding
-/
instance unitSMul : SMul (𝓞 K)ˣ (mixedSpace K) where
  smul u x := mixedEmbedding K u * x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction (𝓞 K)ˣ (mixedSpace K)
  body: fun _ => by simp_rw [unitSMul_smul, Units.coe_one, map_one, one_mul]
  mul_smul := fun _ _ _ => by simp_rw [unitSMul_smul, Units.coe_mul, map_mul, mul_assoc]

中文:
实例 :
  签名: 乘法作用 (𝓞 K)ˣ (mixedSpace K)
  定义体: fun _ => by simp_rw [unitSMul_smul, Units.coe_one, map_one, one_mul]
  mul_smul := fun _ _ _ => by simp_rw [unitSMul_smul, Units.coe_mul, map_mul, mul_assoc]

Depends on / 依赖: Units.coe_one, coe_one, map_one, one_mul, simp_rw, unitSMul_smul
-/
instance : MulAction (𝓞 K)ˣ (mixedSpace K) where
  one_smul := fun _ => by simp_rw [unitSMul_smul, Units.coe_one, map_one, one_mul]
  mul_smul := fun _ _ _ => by simp_rw [unitSMul_smul, Units.coe_mul, map_mul, mul_assoc]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulZeroClass (𝓞 K)ˣ (mixedSpace K)
  body: fun _ => by simp_rw [unitSMul_smul, mul_zero]

中文:
实例 :
  签名: SMulZero类 (𝓞 K)ˣ (mixedSpace K)
  定义体: fun _ => by simp_rw [unitSMul_smul, mul_zero]

Depends on / 依赖: mul_zero, simp_rw, unitSMul_smul
-/
instance : SMulZeroClass (𝓞 K)ˣ (mixedSpace K) where
  smul_zero := fun _ => by simp_rw [unitSMul_smul, mul_zero]

variable {K}

/--
theorem `unit_smul_eq_zero` / 定理 `unit_smul_eq_zero`

English:
theorem unit_smul_eq_zero
  given: (u : (𝓞 K)ˣ) (x : mixedSpace K)
  proof: by
  refine ⟨fun h => ?_, fun h => by rw [h, smul_zero]⟩
  contrapose! h
  obtain ⟨w, h⟩ := exists_normAtPlace_ne_zero_iff.mpr h
  refine exists_normAtPlace_ne_zero_iff.mp ⟨w, ?_⟩
  rw [unitSMul_smul]; rw [map_mul]
  exact mul_ne_zero (by simp) h

中文:
定理 unit_smul_eq_zero
  条件: (u : (𝓞 K)ˣ) (x : mixedSpace K)
  证明: by
  refine ⟨fun h => ?_, fun h => by rw [h, smul_zero]⟩
  contrapose! h
  obtain ⟨w, h⟩ := exists_normAtPlace_ne_zero_iff.mpr h
  refine exists_normAtPlace_ne_zero_iff.mp ⟨w, ?_⟩
  rw [unitSMul_smul]; rw [map_mul]
  exact mul_ne_zero (by simp) h

Depends on / 依赖: contrapose, exists_normAtPlace_ne_zero_iff, exists_normAtPlace_ne_zero_iff.mp, exists_normAtPlace_ne_zero_iff.mpr, map_mul, mul_ne_zero, smul_zero, unitSMul_smul
-/
theorem unit_smul_eq_zero (u : (𝓞 K)ˣ) (x : mixedSpace K) :
    u • x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, smul_zero]⟩
  contrapose! h
  obtain ⟨w, h⟩ := exists_normAtPlace_ne_zero_iff.mpr h
  refine exists_normAtPlace_ne_zero_iff.mp ⟨w, ?_⟩
  rw [unitSMul_smul]; rw [map_mul]
  exact mul_ne_zero (by simp) h

variable [NumberField K]

/--
theorem `unit_smul_eq_iff_mul_eq` / 定理 `unit_smul_eq_iff_mul_eq`

English:
theorem unit_smul_eq_iff_mul_eq
  given: {x y : 𝓞 K} {u : (𝓞 K)ˣ}
  proof: by
  rw [unitSMul_smul]; rw [← map_mul]; rw [Function.Injective.eq_iff]; rw [← RingOfIntegers.coe_eq_algebraMap]; rw [← map_mul]; rw [← RingOfIntegers.ext_iff]
  exact mixedEmbedding_injective K

中文:
定理 unit_smul_eq_iff_mul_eq
  条件: {x y : 𝓞 K} {u : (𝓞 K)ˣ}
  证明: by
  rw [unitSMul_smul]; rw [← map_mul]; rw [Function.Injective.eq_iff]; rw [← RingOfIntegers.coe_eq_algebraMap]; rw [← map_mul]; rw [← RingOfIntegers.ext_iff]
  exact mixedEmbedding_injective K

Depends on / 依赖: Function, Function.Injective.eq_iff, Injective, RingOfIntegers, RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.ext_iff, coe_eq_algebraMap, eq_iff, ext_iff, map_mul, mixedEmbedding_injective, unitSMul_smul
-/
theorem unit_smul_eq_iff_mul_eq {x y : 𝓞 K} {u : (𝓞 K)ˣ} :
    u • mixedEmbedding K x = mixedEmbedding K y ↔ u * x = y := by
  rw [unitSMul_smul]; rw [← map_mul]; rw [Function.Injective.eq_iff]; rw [← RingOfIntegers.coe_eq_algebraMap]; rw [← map_mul]; rw [← RingOfIntegers.ext_iff]
  exact mixedEmbedding_injective K

/--
theorem `norm_unit_smul` / 定理 `norm_unit_smul`

English:
theorem norm_unit_smul
  given: (u : (𝓞 K)ˣ) (x : mixedSpace K)
  proof: by
  rw [unitSMul_smul]; rw [map_mul]; rw [norm_unit]; rw [one_mul]

中文:
定理 norm_unit_smul
  条件: (u : (𝓞 K)ˣ) (x : mixedSpace K)
  证明: by
  rw [unitSMul_smul]; rw [map_mul]; rw [norm_unit]; rw [one_mul]

Depends on / 依赖: map_mul, norm_unit, one_mul, unitSMul_smul
-/
theorem norm_unit_smul (u : (𝓞 K)ˣ) (x : mixedSpace K) :
    mixedEmbedding.norm (u • x) = mixedEmbedding.norm x := by
  rw [unitSMul_smul]; rw [map_mul]; rw [norm_unit]; rw [one_mul]

end UnitSMul

noncomputable section logMap

open NumberField.Units NumberField.Units.dirichletUnitTheorem Module

variable [NumberField K] {K}

/--
Definition of `logMap` / `logMap` 的定义

English:
definition logMap
  signature: (x : mixedSpace K)
  body: fun w =>
  mult w.val * (Real.log (normAtPlace w.val x) -
    Real.log (mixedEmbedding.norm x) * (finrank Rat K : Real)⁻¹)

@[simp]

中文:
定义 logMap
  签名: (x : mixedSpace K)
  定义体: fun w =>
  mult w.val * (Real.log (normAtPlace w.val x) -
    Real.log (mixedEmbedding.norm x) * (finrank Rat K : Real)⁻¹)

@[simp]
-/
def logMap (x : mixedSpace K) : logSpace K := fun w =>
  mult w.val * (Real.log (normAtPlace w.val x) -
    Real.log (mixedEmbedding.norm x) * (finrank Rat K : Real)⁻¹)

@[simp]
/--
theorem `logMap_apply` / 定理 `logMap_apply`

English:
theorem logMap_apply
  given: (x : mixedSpace K) (w : {w : InfinitePlace K // w != w₀})
  proof: rfl

@[simp]

中文:
定理 logMap_apply
  条件: (x : mixedSpace K) (w : {w : InfinitePlace K // w != w₀})
  证明: rfl

@[simp]
-/
theorem logMap_apply (x : mixedSpace K) (w : {w : InfinitePlace K // w != w₀}) :
    logMap x w = mult w.val * (Real.log (normAtPlace w.val x) -
      Real.log (mixedEmbedding.norm x) * (finrank Rat K : Real)⁻¹) := rfl

@[simp]
/--
theorem `logMap_zero` / 定理 `logMap_zero`

English:
theorem logMap_zero
  statement: logMap (0 : mixedSpace K) = 0
  proof: by
  ext; simp

@[simp]

中文:
定理 logMap_zero
  结论: logMap (0 : mixedSpace K) = 0
  证明: by
  ext; simp

@[simp]
-/
theorem logMap_zero : logMap (0 : mixedSpace K) = 0 := by
  ext; simp

@[simp]
/--
theorem `logMap_one` / 定理 `logMap_one`

English:
theorem logMap_one
  statement: logMap (1 : mixedSpace K) = 0
  proof: by
  ext; simp

中文:
定理 logMap_one
  结论: logMap (1 : mixedSpace K) = 0
  证明: by
  ext; simp
-/
theorem logMap_one : logMap (1 : mixedSpace K) = 0 := by
  ext; simp

variable {x y : mixedSpace K}

/--
theorem `logMap_mul` / 定理 `logMap_mul`

English:
theorem logMap_mul
  given: (hx : mixedEmbedding.norm x != 0) (hy : mixedEmbedding.norm y != 0)
  proof: by
  ext w
  simp_rw [Pi.add_apply, logMap_apply]
  rw [map_mul]; rw [map_mul]; rw [Real.log_mul]; rw [Real.log_mul hx hy]; rw [add_mul]
  · ring
  · exact mixedEmbedding.norm_ne_zero_iff.mp hx w
  · exact mixedEmbedding.norm_ne_zero_iff.mp hy w

中文:
定理 logMap_mul
  条件: (hx : mixedEmbedding.norm x != 0) (hy : mixedEmbedding.norm y != 0)
  证明: by
  ext w
  simp_rw [Pi.add_apply, logMap_apply]
  rw [map_mul]; rw [map_mul]; rw [Real.log_mul]; rw [Real.log_mul hx hy]; rw [add_mul]
  · ring
  · exact mixedEmbedding.norm_ne_zero_iff.mp hx w
  · exact mixedEmbedding.norm_ne_zero_iff.mp hy w

Depends on / 依赖: Pi.add_apply, Real.log_mul, add_apply, add_mul, logMap_apply, log_mul, map_mul, mixedEmbedding, mixedEmbedding.norm_ne_zero_iff.mp, norm_ne_zero_iff, simp_rw
-/
theorem logMap_mul (hx : mixedEmbedding.norm x != 0) (hy : mixedEmbedding.norm y != 0) :
    logMap (x * y) = logMap x + logMap y := by
  ext w
  simp_rw [Pi.add_apply, logMap_apply]
  rw [map_mul]; rw [map_mul]; rw [Real.log_mul]; rw [Real.log_mul hx hy]; rw [add_mul]
  · ring
  · exact mixedEmbedding.norm_ne_zero_iff.mp hx w
  · exact mixedEmbedding.norm_ne_zero_iff.mp hy w

/--
theorem `logMap_apply_of_norm_eq_one` / 定理 `logMap_apply_of_norm_eq_one`

English:
theorem logMap_apply_of_norm_eq_one
  statement: (hx : mixedEmbedding.norm x = 1)
  proof: by
  rw [logMap_apply]; rw [hx]; rw [Real.log_one]; rw [zero_mul]; rw [sub_zero]

@[simp]

中文:
定理 logMap_apply_of_norm_eq_one
  结论: (hx : mixedEmbedding.norm x = 1)
  证明: by
  rw [logMap_apply]; rw [hx]; rw [Real.log_one]; rw [zero_mul]; rw [sub_zero]

@[simp]

Depends on / 依赖: Real.log_one, logMap_apply, log_one, sub_zero, zero_mul
-/
theorem logMap_apply_of_norm_eq_one (hx : mixedEmbedding.norm x = 1)
    (w : {w : InfinitePlace K // w != w₀}) :
    logMap x w = mult w.val * Real.log (normAtPlace w x) := by
  rw [logMap_apply]; rw [hx]; rw [Real.log_one]; rw [zero_mul]; rw [sub_zero]

@[simp]
/--
theorem `logMap_eq_logEmbedding` / 定理 `logMap_eq_logEmbedding`

English:
theorem logMap_eq_logEmbedding
  given: (u : (𝓞 K)ˣ)
  proof: by
  ext; simp

中文:
定理 logMap_eq_logEmbedding
  条件: (u : (𝓞 K)ˣ)
  证明: by
  ext; simp
-/
theorem logMap_eq_logEmbedding (u : (𝓞 K)ˣ) :
    logMap (mixedEmbedding K u) = logEmbedding K (Additive.ofMul u) := by
  ext; simp

/--
theorem `logMap_unit_smul` / 定理 `logMap_unit_smul`

English:
theorem logMap_unit_smul
  given: (u : (𝓞 K)ˣ) (hx : mixedEmbedding.norm x != 0)
  proof: by
  rw [unitSMul_smul]; rw [logMap_mul (by rw [norm_unit]; norm_num) hx, logMap_eq_logEmbedding]

中文:
定理 logMap_unit_smul
  条件: (u : (𝓞 K)ˣ) (hx : mixedEmbedding.norm x != 0)
  证明: by
  rw [unitSMul_smul]; rw [logMap_mul (by rw [norm_unit]; norm_num) hx, logMap_eq_logEmbedding]

Depends on / 依赖: WellFoundedLT, WellFoundedLT.toIsPredArchimedean, logMap_eq_logEmbedding, logMap_mul, norm_unit, toIsPredArchimedean, unitSMul_smul
-/
theorem logMap_unit_smul (u : (𝓞 K)ˣ) (hx : mixedEmbedding.norm x != 0) :
    logMap (u • x) = logEmbedding K (Additive.ofMul u) + logMap x := by
  rw [unitSMul_smul]; rw [logMap_mul (by rw [norm_unit]; norm_num) hx, logMap_eq_logEmbedding]

variable (x) in
/--
theorem `logMap_torsion_smul` / 定理 `logMap_torsion_smul`

English:
theorem logMap_torsion_smul
  given: {ζ : (𝓞 K)ˣ} (hζ : ζ in torsion K)
  proof: by
  ext
  simp_rw [logMap_apply, unitSMul_smul, map_mul, norm_eq_norm, Units.norm, Rat.cast_one, one_mul,
    normAtPlace_apply, (mem_torsion K).mp hζ, one_mul]

中文:
定理 logMap_torsion_smul
  条件: {ζ : (𝓞 K)ˣ} (hζ : ζ in torsion K)
  证明: by
  ext
  simp_rw [logMap_apply, unitSMul_smul, map_mul, norm_eq_norm, Units.norm, Rat.cast_one, one_mul,
    normAtPlace_apply, (mem_torsion K).mp hζ, one_mul]

Depends on / 依赖: Rat.cast_one, Units.norm, WellFoundedGT, WellFoundedGT.toIsSuccArchimedean, cast_one, logMap_apply, map_mul, mem_torsion, normAtPlace_apply, norm_eq_norm, one_mul, simp_rw, toIsSuccArchimedean, unitSMul_smul
-/
theorem logMap_torsion_smul {ζ : (𝓞 K)ˣ} (hζ : ζ in torsion K) :
    logMap (ζ • x) = logMap x := by
  ext
  simp_rw [logMap_apply, unitSMul_smul, map_mul, norm_eq_norm, Units.norm, Rat.cast_one, one_mul,
    normAtPlace_apply, (mem_torsion K).mp hζ, one_mul]

/--
theorem `logMap_real` / 定理 `logMap_real`

English:
theorem logMap_real
  given: (c : Real)
  proof: by
  ext
  rw [logMap_apply]; rw [normAtPlace_smul]; rw [norm_smul]; rw [map_one]; rw [map_one]; rw [mul_one]; rw [mul_one]; rw [Real.log_pow]; rw [mul_comm (finrank Rat K : Real) _]; rw [mul_assoc]; rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr finrank_pos.ne')]; rw [mul_one]; rw [sub_self]; rw [mul_zero]; rw [Pi.zero_apply]

中文:
定理 logMap_real
  条件: (c : 实数)
  证明: by
  ext
  rw [logMap_apply]; rw [normAtPlace_smul]; rw [norm_smul]; rw [map_one]; rw [map_one]; rw [mul_one]; rw [mul_one]; rw [Real.log_pow]; rw [mul_comm (finrank Rat K : Real) _]; rw [mul_assoc]; rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr finrank_pos.ne')]; rw [mul_one]; rw [sub_self]; rw [mul_zero]; rw [Pi.zero_apply]

Depends on / 依赖: Nat.cast_ne_zero.mpr, Pi.zero_apply, Real.log_pow, cast_ne_zero, finrank, finrank_pos, finrank_pos.ne, logMap_apply, log_pow, map_one, mul_assoc, mul_comm, mul_one, mul_zero, normAtPlace_smul, norm_smul, sub_self, zero_apply
-/
theorem logMap_real (c : Real) :
    logMap (c • (1 : mixedSpace K)) = 0 := by
  ext
  rw [logMap_apply]; rw [normAtPlace_smul]; rw [norm_smul]; rw [map_one]; rw [map_one]; rw [mul_one]; rw [mul_one]; rw [Real.log_pow]; rw [mul_comm (finrank Rat K : Real) _]; rw [mul_assoc]; rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr finrank_pos.ne')]; rw [mul_one]; rw [sub_self]; rw [mul_zero]; rw [Pi.zero_apply]

/--
theorem `logMap_real_smul` / 定理 `logMap_real_smul`

English:
theorem logMap_real_smul
  given: (hx : mixedEmbedding.norm x != 0) {c : Real} (hc : c != 0)
  proof: by
  have : mixedEmbedding.norm (c • (1 : mixedSpace K)) != 0 := by
    rw [norm_smul]; rw [map_one]; rw [mul_one]
    exact pow_ne_zero _ (abs_ne_zero.mpr hc)
  rw [← smul_one_mul]; rw [logMap_mul this hx]; rw [logMap_real]; rw [zero_add]

中文:
定理 logMap_real_smul
  条件: (hx : mixedEmbedding.norm x != 0) {c : 实数} (hc : c != 0)
  证明: by
  have : mixedEmbedding.norm (c • (1 : mixedSpace K)) != 0 := by
    rw [norm_smul]; rw [map_one]; rw [mul_one]
    exact pow_ne_zero _ (abs_ne_zero.mpr hc)
  rw [← smul_one_mul]; rw [logMap_mul this hx]; rw [logMap_real]; rw [zero_add]

Depends on / 依赖: abs_ne_zero, abs_ne_zero.mpr, logMap_mul, logMap_real, map_one, mixedEmbedding, mixedEmbedding.norm, mixedSpace, mul_one, norm_smul, pow_ne_zero, smul_one_mul, zero_add
-/
theorem logMap_real_smul (hx : mixedEmbedding.norm x != 0) {c : Real} (hc : c != 0) :
    logMap (c • x) = logMap x := by
  have : mixedEmbedding.norm (c • (1 : mixedSpace K)) != 0 := by
    rw [norm_smul]; rw [map_one]; rw [mul_one]
    exact pow_ne_zero _ (abs_ne_zero.mpr hc)
  rw [← smul_one_mul]; rw [logMap_mul this hx]; rw [logMap_real]; rw [zero_add]

/--
theorem `logMap_eq_of_normAtPlace_eq` / 定理 `logMap_eq_of_normAtPlace_eq`

English:
theorem logMap_eq_of_normAtPlace_eq
  given: (h : forall w, normAtPlace w x = normAtPlace w y)
  proof: by
  ext
  simp_rw [logMap_apply, h, norm_eq_of_normAtPlace_eq h]

中文:
定理 logMap_eq_of_normAtPlace_eq
  条件: (h : 对任意 w, normAtPlace w x = normAtPlace w y)
  证明: by
  ext
  simp_rw [logMap_apply, h, norm_eq_of_normAtPlace_eq h]

Depends on / 依赖: logMap_apply, norm_eq_of_normAtPlace_eq, simp_rw
-/
theorem logMap_eq_of_normAtPlace_eq (h : forall w, normAtPlace w x = normAtPlace w y) :
    logMap x = logMap y := by
  ext
  simp_rw [logMap_apply, h, norm_eq_of_normAtPlace_eq h]

end logMap

noncomputable section

open NumberField.Units NumberField.Units.dirichletUnitTheorem

variable [NumberField K]

open scoped Classical in
/--
Definition of `fundamentalCone` / `fundamentalCone` 的定义

English:
definition fundamentalCone
  signature: : Set (mixedSpace K)
  body: logMap ⁻¹' (ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis Real _)) \
      {x | mixedEmbedding.norm x = 0}

中文:
定义 fundamentalCone
  签名: : 集合 (mixedSpace K)
  定义体: logMap ⁻¹' (ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis Real _)) \
      {x | mixedEmbedding.norm x = 0}

Depends on / 依赖: ZSpan.fundamentalDomain, basisUnitLattice, fundamentalDomain, logMap, mixedEmbedding, mixedEmbedding.norm, ofZLatticeBasis
-/
def fundamentalCone : Set (mixedSpace K) :=
  logMap ⁻¹' (ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis Real _)) \
      {x | mixedEmbedding.norm x = 0}

/--
theorem `measurableSet_fundamentalCone` / 定理 `measurableSet_fundamentalCone`

English:
theorem measurableSet_fundamentalCone
  proof: by
  classical
  refine MeasurableSet.diff ?_ ?_
  · unfold logMap
refine MeasurableSet.preimage (ZSpan.fundamentalDomain_measurableSet _)
      measurable_pi_iff.mpr fun w => measurable_const.mul ?_
exact (continuous_normAtPlace _).measurable.log.sub
      (mixedEmbedding.continuous_norm _).measurable.log.mul measurable_const
  · exact measurableSet_eq_fun (mixedEmbedding.continuous_norm K).measurable measurable_const

中文:
定理 measurableSet_fundamentalCone
  证明: by
  classical
  refine MeasurableSet.diff ?_ ?_
  · unfold logMap
refine MeasurableSet.preimage (ZSpan.fundamentalDomain_measurableSet _)
      measurable_pi_iff.mpr fun w => measurable_const.mul ?_
exact (continuous_normAtPlace _).measurable.log.sub
      (mixedEmbedding.continuous_norm _).measurable.log.mul measurable_const
  · exact measurableSet_eq_fun (mixedEmbedding.continuous_norm K).measurable measurable_const

Depends on / 依赖: MeasurableSet, MeasurableSet.diff, MeasurableSet.preimage, ZSpan.fundamentalDomain_measurableSet, classical, continuous_norm, continuous_normAtPlace, fundamentalDomain_measurableSet, logMap, measurable, measurable.log.mul, measurable.log.sub, measurableSet_eq_fun, measurable_const, measurable_const.mul, measurable_pi_iff, measurable_pi_iff.mpr, mixedEmbedding, mixedEmbedding.continuous_norm, preimage
-/
theorem measurableSet_fundamentalCone :
    MeasurableSet (fundamentalCone K) := by
  classical
  refine MeasurableSet.diff ?_ ?_
  · unfold logMap
refine MeasurableSet.preimage (ZSpan.fundamentalDomain_measurableSet _)
      measurable_pi_iff.mpr fun w => measurable_const.mul ?_
exact (continuous_normAtPlace _).measurable.log.sub
      (mixedEmbedding.continuous_norm _).measurable.log.mul measurable_const
  · exact measurableSet_eq_fun (mixedEmbedding.continuous_norm K).measurable measurable_const

namespace fundamentalCone

variable {K} {x y : mixedSpace K} {c : Real}

/--
theorem `norm_pos_of_mem` / 定理 `norm_pos_of_mem`

English:
theorem norm_pos_of_mem
  given: (hx : x in fundamentalCone K)
  proof: lt_of_le_of_ne (mixedEmbedding.norm_nonneg _) (Ne.symm hx.2)

中文:
定理 norm_pos_of_mem
  条件: (hx : x in fundamentalCone K)
  证明: lt_of_le_of_ne (mixedEmbedding.norm_nonneg _) (Ne.symm hx.2)

Depends on / 依赖: Ne.symm, lt_of_le_of_ne, mixedEmbedding, mixedEmbedding.norm_nonneg, norm_nonneg
-/
theorem norm_pos_of_mem (hx : x in fundamentalCone K) :
    0 < mixedEmbedding.norm x :=
  lt_of_le_of_ne (mixedEmbedding.norm_nonneg _) (Ne.symm hx.2)

/--
theorem `normAtPlace_pos_of_mem` / 定理 `normAtPlace_pos_of_mem`

English:
theorem normAtPlace_pos_of_mem
  given: (hx : x in fundamentalCone K) (w : InfinitePlace K)
  proof: lt_of_le_of_ne (normAtPlace_nonneg _ _)
    (mixedEmbedding.norm_ne_zero_iff.mp (norm_pos_of_mem hx).ne' w).symm

中文:
定理 normAtPlace_pos_of_mem
  条件: (hx : x in fundamentalCone K) (w : InfinitePlace K)
  证明: lt_of_le_of_ne (normAtPlace_nonneg _ _)
    (mixedEmbedding.norm_ne_zero_iff.mp (norm_pos_of_mem hx).ne' w).symm

Depends on / 依赖: lt_of_le_of_ne, mixedEmbedding, mixedEmbedding.norm_ne_zero_iff.mp, normAtPlace_nonneg, norm_ne_zero_iff, norm_pos_of_mem
-/
theorem normAtPlace_pos_of_mem (hx : x in fundamentalCone K) (w : InfinitePlace K) :
    0 < normAtPlace w x :=
  lt_of_le_of_ne (normAtPlace_nonneg _ _)
    (mixedEmbedding.norm_ne_zero_iff.mp (norm_pos_of_mem hx).ne' w).symm

/--
theorem `mem_of_normAtPlace_eq` / 定理 `mem_of_normAtPlace_eq`

English:
theorem mem_of_normAtPlace_eq
  statement: (hx : x in fundamentalCone K)
  proof: by
  refine ⟨?_, by simpa [norm_eq_of_normAtPlace_eq hy] using hx.2⟩
  rw [Set.mem_preimage]; rw [logMap_eq_of_normAtPlace_eq hy]
  exact hx.1

中文:
定理 mem_of_normAtPlace_eq
  结论: (hx : x in fundamentalCone K)
  证明: by
  refine ⟨?_, by simpa [norm_eq_of_normAtPlace_eq hy] using hx.2⟩
  rw [Set.mem_preimage]; rw [logMap_eq_of_normAtPlace_eq hy]
  exact hx.1

Depends on / 依赖: Set.mem_preimage, logMap_eq_of_normAtPlace_eq, mem_preimage, norm_eq_of_normAtPlace_eq
-/
theorem mem_of_normAtPlace_eq (hx : x in fundamentalCone K)
    (hy : forall w, normAtPlace w y = normAtPlace w x) :
    y in fundamentalCone K := by
  refine ⟨?_, by simpa [norm_eq_of_normAtPlace_eq hy] using hx.2⟩
  rw [Set.mem_preimage]; rw [logMap_eq_of_normAtPlace_eq hy]
  exact hx.1

/--
theorem `smul_mem_of_mem` / 定理 `smul_mem_of_mem`

English:
theorem smul_mem_of_mem
  given: (hx : x in fundamentalCone K) (hc : c != 0)
  proof: by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_preimage, logMap_real_smul hx.2 hc]
    exact hx.1
  · rw [Set.mem_ofPred_eq, mixedEmbedding.norm_smul, mul_eq_zero, not_or]
    exact ⟨pow_ne_zero _ (abs_ne_zero.mpr hc), hx.2⟩

中文:
定理 smul_mem_of_mem
  条件: (hx : x in fundamentalCone K) (hc : c != 0)
  证明: by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_preimage, logMap_real_smul hx.2 hc]
    exact hx.1
  · rw [Set.mem_ofPred_eq, mixedEmbedding.norm_smul, mul_eq_zero, not_or]
    exact ⟨pow_ne_zero _ (abs_ne_zero.mpr hc), hx.2⟩

Depends on / 依赖: Set.mem_ofPred_eq, Set.mem_preimage, abs_ne_zero, abs_ne_zero.mpr, logMap_real_smul, mem_ofPred_eq, mem_preimage, mixedEmbedding, mixedEmbedding.norm_smul, mul_eq_zero, norm_smul, not_or, pow_ne_zero
-/
theorem smul_mem_of_mem (hx : x in fundamentalCone K) (hc : c != 0) :
    c • x in fundamentalCone K := by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_preimage, logMap_real_smul hx.2 hc]
    exact hx.1
  · rw [Set.mem_ofPred_eq, mixedEmbedding.norm_smul, mul_eq_zero, not_or]
    exact ⟨pow_ne_zero _ (abs_ne_zero.mpr hc), hx.2⟩

/--
theorem `smul_mem_iff_mem` / 定理 `smul_mem_iff_mem`

English:
theorem smul_mem_iff_mem
  given: (hc : c != 0)
  proof: by
  refine ⟨fun h => ?_, fun h => smul_mem_of_mem h hc⟩
  convert! smul_mem_of_mem h (inv_ne_zero hc)
  rw [eq_inv_smul_iff₀ hc]

中文:
定理 smul_mem_iff_mem
  条件: (hc : c != 0)
  证明: by
  refine ⟨fun h => ?_, fun h => smul_mem_of_mem h hc⟩
  convert! smul_mem_of_mem h (inv_ne_zero hc)
  rw [eq_inv_smul_iff₀ hc]

Depends on / 依赖: convert, inv_ne_zero, smul_mem_of_mem
-/
theorem smul_mem_iff_mem (hc : c != 0) :
    c • x in fundamentalCone K ↔ x in fundamentalCone K := by
  refine ⟨fun h => ?_, fun h => smul_mem_of_mem h hc⟩
  convert! smul_mem_of_mem h (inv_ne_zero hc)
  rw [eq_inv_smul_iff₀ hc]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `exists_unit_smul_mem` / 定理 `exists_unit_smul_mem`

English:
theorem exists_unit_smul_mem
  given: (hx : mixedEmbedding.norm x != 0)
  proof: by
  classical
  let B := (basisUnitLattice K).ofZLatticeBasis Real
  rsuffices ⟨⟨_, ⟨u, _, rfl⟩⟩, hu⟩ : exists e : unitLattice K, e + logMap x in ZSpan.fundamentalDomain B
  · exact ⟨u, by rwa [Set.mem_preimage, logMap_unit_smul u hx], by simp [hx]⟩
  · obtain ⟨⟨e, h₁⟩, h₂, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)
    exact ⟨⟨e, by rwa [← Module.Basis.ofZLatticeBasis_span Real (unitLattice K)]⟩, h₂⟩

中文:
定理 存在_unit_smul_mem
  条件: (hx : mixedEmbedding.norm x != 0)
  证明: by
  classical
  let B := (basisUnitLattice K).ofZLatticeBasis Real
  rsuffices ⟨⟨_, ⟨u, _, rfl⟩⟩, hu⟩ : exists e : unitLattice K, e + logMap x in ZSpan.fundamentalDomain B
  · exact ⟨u, by rwa [Set.mem_preimage, logMap_unit_smul u hx], by simp [hx]⟩
  · obtain ⟨⟨e, h₁⟩, h₂, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)
    exact ⟨⟨e, by rwa [← Module.Basis.ofZLatticeBasis_span Real (unitLattice K)]⟩, h₂⟩

Depends on / 依赖: Module, Module.Basis.ofZLatticeBasis_span, Set.mem_preimage, ZSpan.exist_unique_vadd_mem_fundamentalDomain, ZSpan.fundamentalDomain, basisUnitLattice, classical, exist_unique_vadd_mem_fundamentalDomain, fundamentalDomain, logMap, logMap_unit_smul, mem_preimage, ofZLatticeBasis, ofZLatticeBasis_span, rsuffices, unitLattice
-/
theorem exists_unit_smul_mem (hx : mixedEmbedding.norm x != 0) :
    exists u : (𝓞 K)ˣ, u • x in fundamentalCone K := by
  classical
  let B := (basisUnitLattice K).ofZLatticeBasis Real
  rsuffices ⟨⟨_, ⟨u, _, rfl⟩⟩, hu⟩ : exists e : unitLattice K, e + logMap x in ZSpan.fundamentalDomain B
  · exact ⟨u, by rwa [Set.mem_preimage, logMap_unit_smul u hx], by simp [hx]⟩
  · obtain ⟨⟨e, h₁⟩, h₂, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)
    exact ⟨⟨e, by rwa [← Module.Basis.ofZLatticeBasis_span Real (unitLattice K)]⟩, h₂⟩

/--
theorem `torsion_smul_mem_of_mem` / 定理 `torsion_smul_mem_of_mem`

English:
theorem torsion_smul_mem_of_mem
  given: (hx : x in fundamentalCone K) {ζ : (𝓞 K)ˣ} (hζ : ζ in torsion K)
  proof: by
  constructor
  · rw [Set.mem_preimage, logMap_torsion_smul _ hζ]
    exact hx.1
  · rw [Set.mem_ofPred_eq, unitSMul_smul, map_mul, norm_unit, one_mul]
    exact hx.2

中文:
定理 torsion_smul_mem_of_mem
  条件: (hx : x in fundamentalCone K) {ζ : (𝓞 K)ˣ} (hζ : ζ in torsion K)
  证明: by
  constructor
  · rw [Set.mem_preimage, logMap_torsion_smul _ hζ]
    exact hx.1
  · rw [Set.mem_ofPred_eq, unitSMul_smul, map_mul, norm_unit, one_mul]
    exact hx.2

Depends on / 依赖: Set.mem_ofPred_eq, Set.mem_preimage, logMap_torsion_smul, map_mul, mem_ofPred_eq, mem_preimage, norm_unit, one_mul, unitSMul_smul
-/
theorem torsion_smul_mem_of_mem (hx : x in fundamentalCone K) {ζ : (𝓞 K)ˣ} (hζ : ζ in torsion K) :
    ζ • x in fundamentalCone K := by
  constructor
  · rw [Set.mem_preimage, logMap_torsion_smul _ hζ]
    exact hx.1
  · rw [Set.mem_ofPred_eq, unitSMul_smul, map_mul, norm_unit, one_mul]
    exact hx.2

/--
theorem `unit_smul_mem_iff_mem_torsion` / 定理 `unit_smul_mem_iff_mem_torsion`

English:
theorem unit_smul_mem_iff_mem_torsion
  given: (hx : x in fundamentalCone K) (u : (𝓞 K)ˣ)
  proof: by
  classical
  refine ⟨fun h => ?_, fun h => torsion_smul_mem_of_mem hx h⟩
  rw [← logEmbedding_eq_zero_iff]
  let B := (basisUnitLattice K).ofZLatticeBasis Real
refine (Subtype.mk_eq_mk (h := ?_) (h' := Submodule.zero_mem _)).mp
    (ZSpan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)).unique ?_ ?_
  · rw [Module.Basis.ofZLatticeBasis_span Real (unitLattice K)]
    exact ⟨u, trivial, rfl⟩
  · rw [AddSubmonoid.mk_vadd, vadd_eq_add, ← logMap_unit_smul _ hx.2]
    exact h.1
  · rw [AddSubmonoid.mk_vadd, vadd_eq_add, zero_add]
    exact hx.1

中文:
定理 unit_smul_mem_iff_mem_torsion
  条件: (hx : x in fundamentalCone K) (u : (𝓞 K)ˣ)
  证明: by
  classical
  refine ⟨fun h => ?_, fun h => torsion_smul_mem_of_mem hx h⟩
  rw [← logEmbedding_eq_zero_iff]
  let B := (basisUnitLattice K).ofZLatticeBasis Real
refine (Subtype.mk_eq_mk (h := ?_) (h' := Submodule.zero_mem _)).mp
    (ZSpan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)).unique ?_ ?_
  · rw [Module.Basis.ofZLatticeBasis_span Real (unitLattice K)]
    exact ⟨u, trivial, rfl⟩
  · rw [AddSubmonoid.mk_vadd, vadd_eq_add, ← logMap_unit_smul _ hx.2]
    exact h.1
  · rw [AddSubmonoid.mk_vadd, vadd_eq_add, zero_add]
    exact hx.1

Depends on / 依赖: AddSubmonoid, AddSubmonoid.mk_vadd, Module, Module.Basis.ofZLatticeBasis_span, Submodule, Submodule.zero_mem, Subtype, Subtype.mk_eq_mk, ZSpan.exist_unique_vadd_mem_fundamentalDomain, basisUnitLattice, classical, exist_unique_vadd_mem_fundamentalDomain, logEmbedding_eq_zero_iff, logMap, logMap_unit_smul, mk_eq_mk, mk_vadd, ofZLatticeBasis, ofZLatticeBasis_span, torsion_smul_mem_of_mem
-/
theorem unit_smul_mem_iff_mem_torsion (hx : x in fundamentalCone K) (u : (𝓞 K)ˣ) :
    u • x in fundamentalCone K ↔ u in torsion K := by
  classical
  refine ⟨fun h => ?_, fun h => torsion_smul_mem_of_mem hx h⟩
  rw [← logEmbedding_eq_zero_iff]
  let B := (basisUnitLattice K).ofZLatticeBasis Real
refine (Subtype.mk_eq_mk (h := ?_) (h' := Submodule.zero_mem _)).mp
    (ZSpan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)).unique ?_ ?_
  · rw [Module.Basis.ofZLatticeBasis_span Real (unitLattice K)]
    exact ⟨u, trivial, rfl⟩
  · rw [AddSubmonoid.mk_vadd, vadd_eq_add, ← logMap_unit_smul _ hx.2]
    exact h.1
  · rw [AddSubmonoid.mk_vadd, vadd_eq_add, zero_add]
    exact hx.1

variable (K) in
/--
Definition of `integerSet` / `integerSet` 的定义

English:
definition integerSet
  signature: : Set (mixedSpace K)
  body: fundamentalCone K inter mixedEmbedding.integerLattice K

中文:
定义 integerSet
  签名: : 集合 (mixedSpace K)
  定义体: fundamentalCone K inter mixedEmbedding.integerLattice K

Depends on / 依赖: fundamentalCone, integerLattice, mixedEmbedding, mixedEmbedding.integerLattice
-/
def integerSet : Set (mixedSpace K) :=
  fundamentalCone K inter mixedEmbedding.integerLattice K

/--
theorem `mem_integerSet` / 定理 `mem_integerSet`

English:
theorem mem_integerSet
  given: {a : mixedSpace K}
  proof: by
  simp only [integerSet, Set.mem_inter_iff, SetLike.mem_coe, LinearMap.mem_range,
    AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe, RingHom.coe_comp, Function.comp_apply]

中文:
定理 mem_integerSet
  条件: {a : mixedSpace K}
  证明: by
  simp only [integerSet, Set.mem_inter_iff, SetLike.mem_coe, LinearMap.mem_range,
    AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe, RingHom.coe_comp, Function.comp_apply]

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_apply, Function, Function.comp_apply, LinearMap, LinearMap.mem_range, RingHom, RingHom.coe_comp, RingHom.toIntAlgHom_coe, Set.mem_inter_iff, SetLike, SetLike.mem_coe, coe_comp, comp_apply, integerSet, mem_coe, mem_inter_iff, mem_range, toIntAlgHom_coe, toLinearMap_apply
-/
theorem mem_integerSet {a : mixedSpace K} :
    a in integerSet K ↔ a in fundamentalCone K ∧ exists x : 𝓞 K, mixedEmbedding K x = a := by
  simp only [integerSet, Set.mem_inter_iff, SetLike.mem_coe, LinearMap.mem_range,
    AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe, RingHom.coe_comp, Function.comp_apply]

/--
theorem `existsUnique_preimage_of_mem_integerSet` / 定理 `existsUnique_preimage_of_mem_integerSet`

English:
theorem existsUnique_preimage_of_mem_integerSet
  given: {a : mixedSpace K} (ha : a in integerSet K)
  proof: by
  obtain ⟨_, ⟨x, rfl⟩⟩ := mem_integerSet.mp ha
  refine Function.Injective.existsUnique_of_mem_range ?_ (Set.mem_range_self x)
  exact (mixedEmbedding_injective K).comp RingOfIntegers.coe_injective

中文:
定理 存在Unique_preimage_of_mem_integerSet
  条件: {a : mixedSpace K} (ha : a in integerSet K)
  证明: by
  obtain ⟨_, ⟨x, rfl⟩⟩ := mem_integerSet.mp ha
  refine Function.Injective.existsUnique_of_mem_range ?_ (Set.mem_range_self x)
  exact (mixedEmbedding_injective K).comp RingOfIntegers.coe_injective

Depends on / 依赖: Function, Function.Injective.existsUnique_of_mem_range, Injective, RingOfIntegers, RingOfIntegers.coe_injective, Set.mem_range_self, coe_injective, existsUnique_of_mem_range, mem_integerSet, mem_integerSet.mp, mem_range_self, mixedEmbedding_injective
-/
theorem existsUnique_preimage_of_mem_integerSet {a : mixedSpace K} (ha : a in integerSet K) :
    exists! x : 𝓞 K, mixedEmbedding K x = a := by
  obtain ⟨_, ⟨x, rfl⟩⟩ := mem_integerSet.mp ha
  refine Function.Injective.existsUnique_of_mem_range ?_ (Set.mem_range_self x)
  exact (mixedEmbedding_injective K).comp RingOfIntegers.coe_injective

/--
theorem `ne_zero_of_mem_integerSet` / 定理 `ne_zero_of_mem_integerSet`

English:
theorem ne_zero_of_mem_integerSet
  given: (a : integerSet K)
  statement: (a : mixedSpace K) != 0
  proof: by
  by_contra!
  exact a.prop.1.2 (this.symm ▸ mixedEmbedding.norm.map_zero')

中文:
定理 ne_zero_of_mem_integerSet
  条件: (a : integerSet K)
  结论: (a : mixedSpace K) != 0
  证明: by
  by_contra!
  exact a.prop.1.2 (this.symm ▸ mixedEmbedding.norm.map_zero')

Depends on / 依赖: a.prop, map_zero, mixedEmbedding, mixedEmbedding.norm.map_zero, this.symm
-/
theorem ne_zero_of_mem_integerSet (a : integerSet K) : (a : mixedSpace K) != 0 := by
  by_contra!
  exact a.prop.1.2 (this.symm ▸ mixedEmbedding.norm.map_zero')

open scoped nonZeroDivisors

/--
Definition of `preimageOfMemIntegerSet` / `preimageOfMemIntegerSet` 的定义

English:
definition preimageOfMemIntegerSet
  signature: (a : integerSet K)
  body: ⟨(mem_integerSet.mp a.prop).2.choose, mem_nonZeroDivisors_of_ne_zero (by
  simp_rw [ne_eq, ← RingOfIntegers.coe_injective.eq_iff, ← (mixedEmbedding_injective K).eq_iff,
    map_zero, (mem_integerSet.mp a.prop).2.choose_spec, ne_zero_of_mem_integerSet,
    not_false_eq_true])⟩

@[simp]

中文:
定义 preimageOfMem整数egerSet
  签名: (a : integerSet K)
  定义体: ⟨(mem_integerSet.mp a.prop).2.choose, mem_nonZeroDivisors_of_ne_zero (by
  simp_rw [ne_eq, ← RingOfIntegers.coe_injective.eq_iff, ← (mixedEmbedding_injective K).eq_iff,
    map_zero, (mem_integerSet.mp a.prop).2.choose_spec, ne_zero_of_mem_integerSet,
    not_false_eq_true])⟩

@[simp]

Depends on / 依赖: RingOfIntegers, RingOfIntegers.coe_injective.eq_iff, a.prop, choose_spec, coe_injective, eq_iff, map_zero, mem_integerSet, mem_integerSet.mp, mem_nonZeroDivisors_of_ne_zero, mixedEmbedding_injective, ne_eq, ne_zero_of_mem_integerSet, not_false_eq_true, simp_rw
-/
def preimageOfMemIntegerSet (a : integerSet K) : (𝓞 K)⁰ :=
  ⟨(mem_integerSet.mp a.prop).2.choose, mem_nonZeroDivisors_of_ne_zero (by
  simp_rw [ne_eq, ← RingOfIntegers.coe_injective.eq_iff, ← (mixedEmbedding_injective K).eq_iff,
    map_zero, (mem_integerSet.mp a.prop).2.choose_spec, ne_zero_of_mem_integerSet,
    not_false_eq_true])⟩

@[simp]
/--
theorem `mixedEmbedding_preimageOfMemIntegerSet` / 定理 `mixedEmbedding_preimageOfMemIntegerSet`

English:
theorem mixedEmbedding_preimageOfMemIntegerSet
  given: (a : integerSet K)
  proof: by
  rw [preimageOfMemIntegerSet]; rw [(mem_integerSet.mp a.prop).2.choose_spec]

中文:
定理 mixedEmbedding_preimageOfMem整数egerSet
  条件: (a : integerSet K)
  证明: by
  rw [preimageOfMemIntegerSet]; rw [(mem_integerSet.mp a.prop).2.choose_spec]

Depends on / 依赖: a.prop, choose_spec, mem_integerSet, mem_integerSet.mp, preimageOfMemIntegerSet
-/
theorem mixedEmbedding_preimageOfMemIntegerSet (a : integerSet K) :
    mixedEmbedding K (preimageOfMemIntegerSet a : 𝓞 K) = (a : mixedSpace K) := by
  rw [preimageOfMemIntegerSet]; rw [(mem_integerSet.mp a.prop).2.choose_spec]

/--
theorem `preimageOfMemIntegerSet_mixedEmbedding` / 定理 `preimageOfMemIntegerSet_mixedEmbedding`

English:
theorem preimageOfMemIntegerSet_mixedEmbedding
  statement: {x : (𝓞 K)}
  proof: by
  simp_rw [RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff,
    mixedEmbedding_preimageOfMemIntegerSet]

中文:
定理 preimageOfMem整数egerSet_mixedEmbedding
  结论: {x : (𝓞 K)}
  证明: by
  simp_rw [RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff,
    mixedEmbedding_preimageOfMemIntegerSet]

Depends on / 依赖: RingOfIntegers, RingOfIntegers.ext_iff, eq_iff, ext_iff, mixedEmbedding_injective, mixedEmbedding_preimageOfMemIntegerSet, simp_rw
-/
theorem preimageOfMemIntegerSet_mixedEmbedding {x : (𝓞 K)}
    (hx : mixedEmbedding K (x : 𝓞 K) in integerSet K) :
    preimageOfMemIntegerSet (⟨mixedEmbedding K (x : 𝓞 K), hx⟩) = x := by
  simp_rw [RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff,
    mixedEmbedding_preimageOfMemIntegerSet]

/--
theorem `exists_unitSMul_mem_integerSet` / 定理 `exists_unitSMul_mem_integerSet`

English:
theorem exists_unitSMul_mem_integerSet
  statement: {x : mixedSpace K} (hx : x != 0)
  proof: by
  replace hx : mixedEmbedding.norm x != 0 :=
      (norm_eq_zero_iff' (Set.mem_range_of_mem_image (mixedEmbedding K) _ hx')).not.mpr hx
  obtain ⟨u, hu⟩ := exists_unit_smul_mem hx
  obtain ⟨_, ⟨x, rfl⟩, _, rfl⟩ := hx'
  exact ⟨u, mem_integerSet.mpr ⟨hu, u * x, by simp_rw [unitSMul_smul, ← map_mul]⟩⟩

中文:
定理 存在_unitSMul_mem_integerSet
  结论: {x : mixedSpace K} (hx : x != 0)
  证明: by
  replace hx : mixedEmbedding.norm x != 0 :=
      (norm_eq_zero_iff' (Set.mem_range_of_mem_image (mixedEmbedding K) _ hx')).not.mpr hx
  obtain ⟨u, hu⟩ := exists_unit_smul_mem hx
  obtain ⟨_, ⟨x, rfl⟩, _, rfl⟩ := hx'
  exact ⟨u, mem_integerSet.mpr ⟨hu, u * x, by simp_rw [unitSMul_smul, ← map_mul]⟩⟩

Depends on / 依赖: Set.mem_range_of_mem_image, exists_unit_smul_mem, map_mul, mem_integerSet, mem_integerSet.mpr, mem_range_of_mem_image, mixedEmbedding, mixedEmbedding.norm, norm_eq_zero_iff, not.mpr, replace, simp_rw, unitSMul_smul
-/
theorem exists_unitSMul_mem_integerSet {x : mixedSpace K} (hx : x != 0)
    (hx' : x in mixedEmbedding K '' (Set.range (algebraMap (𝓞 K) K))) :
    exists u : (𝓞 K)ˣ, u • x in integerSet K := by
  replace hx : mixedEmbedding.norm x != 0 :=
      (norm_eq_zero_iff' (Set.mem_range_of_mem_image (mixedEmbedding K) _ hx')).not.mpr hx
  obtain ⟨u, hu⟩ := exists_unit_smul_mem hx
  obtain ⟨_, ⟨x, rfl⟩, _, rfl⟩ := hx'
  exact ⟨u, mem_integerSet.mpr ⟨hu, u * x, by simp_rw [unitSMul_smul, ← map_mul]⟩⟩

/--
theorem `torsion_unitSMul_mem_integerSet` / 定理 `torsion_unitSMul_mem_integerSet`

English:
theorem torsion_unitSMul_mem_integerSet
  statement: {x : mixedSpace K} {ζ : (𝓞 K)ˣ} (hζ : ζ in torsion K)
  proof: by
  obtain ⟨a, ⟨_, rfl⟩, rfl⟩ := (mem_integerSet.mp hx).2
  refine mem_integerSet.mpr ⟨torsion_smul_mem_of_mem hx.1 hζ, ⟨ζ * a, by simp⟩⟩

中文:
定理 torsion_unitSMul_mem_integerSet
  结论: {x : mixedSpace K} {ζ : (𝓞 K)ˣ} (hζ : ζ in torsion K)
  证明: by
  obtain ⟨a, ⟨_, rfl⟩, rfl⟩ := (mem_integerSet.mp hx).2
  refine mem_integerSet.mpr ⟨torsion_smul_mem_of_mem hx.1 hζ, ⟨ζ * a, by simp⟩⟩

Depends on / 依赖: SuccOrder, SuccOrder.succ, mem_integerSet, mem_integerSet.mp, mem_integerSet.mpr, ofDual, toDual, torsion_smul_mem_of_mem
-/
theorem torsion_unitSMul_mem_integerSet {x : mixedSpace K} {ζ : (𝓞 K)ˣ} (hζ : ζ in torsion K)
    (hx : x in integerSet K) : ζ • x in integerSet K := by
  obtain ⟨a, ⟨_, rfl⟩, rfl⟩ := (mem_integerSet.mp hx).2
  refine mem_integerSet.mpr ⟨torsion_smul_mem_of_mem hx.1 hζ, ⟨ζ * a, by simp⟩⟩

/-- The action of `torsion K` on `integerSet K`. -/
@[simps]
/--
Instance `integerSetTorsionSMul` / 实例 `integerSetTorsionSMul`

English:
instance integerSetTorsionSMul
  signature: : SMul (torsion K) (integerSet K) where
  body: fun ⟨ζ, hζ⟩ ⟨x, hx⟩ => ⟨ζ • x, torsion_unitSMul_mem_integerSet hζ hx⟩

中文:
实例 integerSetTorsionSMul
  签名: : 标量乘法 (torsion K) (integerSet K) where
  定义体: fun ⟨ζ, hζ⟩ ⟨x, hx⟩ => ⟨ζ • x, torsion_unitSMul_mem_integerSet hζ hx⟩

Depends on / 依赖: torsion_unitSMul_mem_integerSet
-/
instance integerSetTorsionSMul : SMul (torsion K) (integerSet K) where
  smul := fun ⟨ζ, hζ⟩ ⟨x, hx⟩ => ⟨ζ • x, torsion_unitSMul_mem_integerSet hζ hx⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction (torsion K) (integerSet K)
  body: fun _ => by
    rw [Subtype.mk_eq_mk]; rw [integerSetTorsionSMul_smul_coe]; rw [OneMemClass.coe_one]; rw [one_smul]
  mul_smul := fun _ _ _ => by
    rw [Subtype.mk_eq_mk]
    simp_rw [integerSetTorsionSMul_smul_coe, Subgroup.coe_mul, mul_smul]

中文:
实例 :
  签名: 乘法作用 (torsion K) (integerSet K)
  定义体: fun _ => by
    rw [Subtype.mk_eq_mk]; rw [integerSetTorsionSMul_smul_coe]; rw [OneMemClass.coe_one]; rw [one_smul]
  mul_smul := fun _ _ _ => by
    rw [Subtype.mk_eq_mk]
    simp_rw [integerSetTorsionSMul_smul_coe, Subgroup.coe_mul, mul_smul]

Depends on / 依赖: OneMemClass, OneMemClass.coe_one, Subgroup, Subgroup.coe_mul, Subtype, Subtype.mk_eq_mk, coe_mul, coe_one, integerSetTorsionSMul_smul_coe, mk_eq_mk, mul_smul, one_smul, simp_rw
-/
instance : MulAction (torsion K) (integerSet K) where
  one_smul := fun _ => by
    rw [Subtype.mk_eq_mk]; rw [integerSetTorsionSMul_smul_coe]; rw [OneMemClass.coe_one]; rw [one_smul]
  mul_smul := fun _ _ _ => by
    rw [Subtype.mk_eq_mk]
    simp_rw [integerSetTorsionSMul_smul_coe, Subgroup.coe_mul, mul_smul]

/--
Definition of `intNorm` / `intNorm` 的定义

English:
definition intNorm
  signature: (a : integerSet K)
  body: (Algebra.norm Int (preimageOfMemIntegerSet a : 𝓞 K)).natAbs

@[simp]

中文:
定义 intNorm
  签名: (a : integerSet K)
  定义体: (Algebra.norm Int (preimageOfMemIntegerSet a : 𝓞 K)).natAbs

@[simp]

Depends on / 依赖: Algebra, Algebra.norm, natAbs, preimageOfMemIntegerSet
-/
def intNorm (a : integerSet K) : Nat := (Algebra.norm Int (preimageOfMemIntegerSet a : 𝓞 K)).natAbs

@[simp]
/--
theorem `intNorm_coe` / 定理 `intNorm_coe`

English:
theorem intNorm_coe
  given: (a : integerSet K)
  proof: by
  rw [intNorm]; rw [Nat.cast_natAbs]; rw [← Rat.cast_intCast]; rw [Int.cast_abs]; rw [Algebra.coe_norm_int]; rw [← norm_eq_norm]; rw [mixedEmbedding_preimageOfMemIntegerSet]

中文:
定理 intNorm_coe
  条件: (a : integerSet K)
  证明: by
  rw [intNorm]; rw [Nat.cast_natAbs]; rw [← Rat.cast_intCast]; rw [Int.cast_abs]; rw [Algebra.coe_norm_int]; rw [← norm_eq_norm]; rw [mixedEmbedding_preimageOfMemIntegerSet]

Depends on / 依赖: Algebra, Algebra.coe_norm_int, Int.cast_abs, Nat.cast_natAbs, Rat.cast_intCast, cast_abs, cast_intCast, cast_natAbs, coe_norm_int, intNorm, mixedEmbedding_preimageOfMemIntegerSet, norm_eq_norm
-/
theorem intNorm_coe (a : integerSet K) :
    (intNorm a : Real) = mixedEmbedding.norm (a : mixedSpace K) := by
  rw [intNorm]; rw [Nat.cast_natAbs]; rw [← Rat.cast_intCast]; rw [Int.cast_abs]; rw [Algebra.coe_norm_int]; rw [← norm_eq_norm]; rw [mixedEmbedding_preimageOfMemIntegerSet]

/--
Definition of `quotIntNorm` / `quotIntNorm` 的定义

English:
definition quotIntNorm
  signature: :
  body: Quotient.lift (fun x => intNorm x) fun a b ⟨u, hu⟩ => by
    rw [← Nat.cast_inj (R := Real)]; rw [intNorm_coe]; rw [intNorm_coe]; rw [← hu]; rw [integerSetTorsionSMul_smul_coe]; rw [norm_unit_smul]

@[simp]

中文:
定义 quot整数Norm
  签名: :
  定义体: Quotient.lift (fun x => intNorm x) fun a b ⟨u, hu⟩ => by
    rw [← Nat.cast_inj (R := Real)]; rw [intNorm_coe]; rw [intNorm_coe]; rw [← hu]; rw [integerSetTorsionSMul_smul_coe]; rw [norm_unit_smul]

@[simp]

Depends on / 依赖: Nat.cast_inj, Quotient, Quotient.lift, cast_inj, intNorm, intNorm_coe, integerSetTorsionSMul_smul_coe, norm_unit_smul
-/
def quotIntNorm :
    Quotient (MulAction.orbitRel (torsion K) (integerSet K)) -> Nat :=
  Quotient.lift (fun x => intNorm x) fun a b ⟨u, hu⟩ => by
    rw [← Nat.cast_inj (R := Real)]; rw [intNorm_coe]; rw [intNorm_coe]; rw [← hu]; rw [integerSetTorsionSMul_smul_coe]; rw [norm_unit_smul]

@[simp]
/--
theorem `quotIntNorm_apply` / 定理 `quotIntNorm_apply`

English:
theorem quotIntNorm_apply
  given: (a : integerSet K)
  statement: quotIntNorm ⟦a⟧ = intNorm a
  proof: rfl

中文:
定理 quot整数Norm_apply
  条件: (a : integerSet K)
  结论: quot整数Norm ⟦a⟧ = intNorm a
  证明: rfl
-/
theorem quotIntNorm_apply (a : integerSet K) : quotIntNorm ⟦a⟧ = intNorm a := rfl

variable (K) in
/--
Definition of `integerSetToAssociates` / `integerSetToAssociates` 的定义

English:
definition integerSetToAssociates
  signature: (a : integerSet K)
  body: ⟦preimageOfMemIntegerSet a⟧

@[simp]

中文:
定义 integerSetToAssociates
  签名: (a : integerSet K)
  定义体: ⟦preimageOfMemIntegerSet a⟧

@[simp]

Depends on / 依赖: preimageOfMemIntegerSet
-/
def integerSetToAssociates (a : integerSet K) : Associates (𝓞 K)⁰ :=
  ⟦preimageOfMemIntegerSet a⟧

@[simp]
/--
theorem `integerSetToAssociates_apply` / 定理 `integerSetToAssociates_apply`

English:
theorem integerSetToAssociates_apply
  given: (a : integerSet K)
  proof: rfl

中文:
定理 integerSetToAssociates_apply
  条件: (a : integerSet K)
  证明: rfl
-/
theorem integerSetToAssociates_apply (a : integerSet K) :
    integerSetToAssociates K a = ⟦preimageOfMemIntegerSet a⟧ := rfl

variable (K) in
/--
theorem `integerSetToAssociates_surjective` / 定理 `integerSetToAssociates_surjective`

English:
theorem integerSetToAssociates_surjective
  proof: by
  rintro ⟨x⟩
  obtain ⟨u, hu⟩ : exists u : (𝓞 K)ˣ, u • mixedEmbedding K (x : 𝓞 K) in integerSet K := by
    refine exists_unitSMul_mem_integerSet ?_ ⟨(x : 𝓞 K), Set.mem_range_self _, rfl⟩
exact (map_ne_zero _).mpr RingOfIntegers.coe_ne_zero_iff.mpr (nonZeroDivisors.coe_ne_zero _)
  refine ⟨⟨u • mixedEmbedding K (x : 𝓞 K), hu⟩,
    Quotient.sound ⟨unitsNonZeroDivisorsEquiv.symm u⁻¹, ?_⟩⟩
  simp_rw [Subtype.ext_iff, RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff,
    Submonoid.coe_mul, map_mul, mixedEmbedding_preimageOfMemIntegerSet,
    unitSMul_smul, ← map_mul, mul_comm, map_inv, val_inv_unitsNonZeroDivisorsEquiv_symm_apply_coe,
    Units.mul_inv_cancel_right]

中文:
定理 integerSetToAssociates_surjective
  证明: by
  rintro ⟨x⟩
  obtain ⟨u, hu⟩ : exists u : (𝓞 K)ˣ, u • mixedEmbedding K (x : 𝓞 K) in integerSet K := by
    refine exists_unitSMul_mem_integerSet ?_ ⟨(x : 𝓞 K), Set.mem_range_self _, rfl⟩
exact (map_ne_zero _).mpr RingOfIntegers.coe_ne_zero_iff.mpr (nonZeroDivisors.coe_ne_zero _)
  refine ⟨⟨u • mixedEmbedding K (x : 𝓞 K), hu⟩,
    Quotient.sound ⟨unitsNonZeroDivisorsEquiv.symm u⁻¹, ?_⟩⟩
  simp_rw [Subtype.ext_iff, RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff,
    Submonoid.coe_mul, map_mul, mixedEmbedding_preimageOfMemIntegerSet,
    unitSMul_smul, ← map_mul, mul_comm, map_inv, val_inv_unitsNonZeroDivisorsEquiv_symm_apply_coe,
    Units.mul_inv_cancel_right]

Depends on / 依赖: Quotient, Quotient.sound, RingOfIntegers, RingOfIntegers.coe_ne_zero_iff.mpr, RingOfIntegers.ext_iff, Set.mem_range_self, Submonoid, Submonoid.coe_mul, Subtype, Subtype.ext_iff, coe_mul, coe_ne_zero, coe_ne_zero_iff, eq_iff, exists_unitSMul_mem_integerSet, ext_iff, integerSet, map_mul, map_ne_zero, mem_range_self
-/
theorem integerSetToAssociates_surjective :
    Function.Surjective (integerSetToAssociates K) := by
  rintro ⟨x⟩
  obtain ⟨u, hu⟩ : exists u : (𝓞 K)ˣ, u • mixedEmbedding K (x : 𝓞 K) in integerSet K := by
    refine exists_unitSMul_mem_integerSet ?_ ⟨(x : 𝓞 K), Set.mem_range_self _, rfl⟩
exact (map_ne_zero _).mpr RingOfIntegers.coe_ne_zero_iff.mpr (nonZeroDivisors.coe_ne_zero _)
  refine ⟨⟨u • mixedEmbedding K (x : 𝓞 K), hu⟩,
    Quotient.sound ⟨unitsNonZeroDivisorsEquiv.symm u⁻¹, ?_⟩⟩
  simp_rw [Subtype.ext_iff, RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff,
    Submonoid.coe_mul, map_mul, mixedEmbedding_preimageOfMemIntegerSet,
    unitSMul_smul, ← map_mul, mul_comm, map_inv, val_inv_unitsNonZeroDivisorsEquiv_symm_apply_coe,
    Units.mul_inv_cancel_right]

/--
theorem `integerSetToAssociates_eq_iff` / 定理 `integerSetToAssociates_eq_iff`

English:
theorem integerSetToAssociates_eq_iff
  given: (a b : integerSet K)
  proof: by
  simp_rw [integerSetToAssociates_apply, Associates.quotient_mk_eq_mk,
    Associates.mk_eq_mk_iff_associated, Associated, mul_comm, Subtype.ext_iff,
    RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff, Submonoid.coe_mul, map_mul,
    mixedEmbedding_preimageOfMemIntegerSet, integerSetTorsionSMul_smul_coe]
  refine ⟨fun ⟨u, h⟩ => ⟨⟨unitsNonZeroDivisorsEquiv u, ?_⟩, by simpa using h⟩,
    fun ⟨⟨u, _⟩, h⟩ => ⟨unitsNonZeroDivisorsEquiv.symm u, by simpa using h⟩⟩
  exact (unit_smul_mem_iff_mem_torsion a.prop.1 _).mp (by simpa [h] using b.prop.1)

中文:
定理 integerSetToAssociates_eq_iff
  条件: (a b : integerSet K)
  证明: by
  simp_rw [integerSetToAssociates_apply, Associates.quotient_mk_eq_mk,
    Associates.mk_eq_mk_iff_associated, Associated, mul_comm, Subtype.ext_iff,
    RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff, Submonoid.coe_mul, map_mul,
    mixedEmbedding_preimageOfMemIntegerSet, integerSetTorsionSMul_smul_coe]
  refine ⟨fun ⟨u, h⟩ => ⟨⟨unitsNonZeroDivisorsEquiv u, ?_⟩, by simpa using h⟩,
    fun ⟨⟨u, _⟩, h⟩ => ⟨unitsNonZeroDivisorsEquiv.symm u, by simpa using h⟩⟩
  exact (unit_smul_mem_iff_mem_torsion a.prop.1 _).mp (by simpa [h] using b.prop.1)

Depends on / 依赖: Associated, Associates, Associates.mk_eq_mk_iff_associated, Associates.quotient_mk_eq_mk, RingOfIntegers, RingOfIntegers.ext_iff, Submonoid, Submonoid.coe_mul, Subtype, Subtype.ext_iff, coe_mul, eq_iff, ext_iff, integerSetToAssociates_apply, integerSetTorsionSMul_smul_coe, map_mul, mixedEmbedding_injective, mixedEmbedding_preimageOfMemIntegerSet, mk_eq_mk_iff_associated, mul_comm
-/
theorem integerSetToAssociates_eq_iff (a b : integerSet K) :
    integerSetToAssociates K a = integerSetToAssociates K b ↔
      exists ζ : torsion K, ζ • a = b := by
  simp_rw [integerSetToAssociates_apply, Associates.quotient_mk_eq_mk,
    Associates.mk_eq_mk_iff_associated, Associated, mul_comm, Subtype.ext_iff,
    RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff, Submonoid.coe_mul, map_mul,
    mixedEmbedding_preimageOfMemIntegerSet, integerSetTorsionSMul_smul_coe]
  refine ⟨fun ⟨u, h⟩ => ⟨⟨unitsNonZeroDivisorsEquiv u, ?_⟩, by simpa using h⟩,
    fun ⟨⟨u, _⟩, h⟩ => ⟨unitsNonZeroDivisorsEquiv.symm u, by simpa using h⟩⟩
  exact (unit_smul_mem_iff_mem_torsion a.prop.1 _).mp (by simpa [h] using b.prop.1)

variable (K) in
/--
Definition of `integerSetQuotEquivAssociates` / `integerSetQuotEquivAssociates` 的定义

English:
definition integerSetQuotEquivAssociates
  signature: :
  body: Equiv.ofBijective
    (Quotient.lift (integerSetToAssociates K)
      fun _ _ h => ((integerSetToAssociates_eq_iff _ _).mpr h).symm)
.mpr by ⟨Setoid.lift_injective_iff_ker_eq_of_le _
        ext a b
        rw [Setoid.ker_def]; rw [eq_comm]; rw [integerSetToAssociates_eq_iff b a]; rw [MulAction.orbitRel_apply]; rw [MulAction.mem_orbit_iff],
        (Quot.surjective_lift _).mpr (integerSetToAssociates_surjective K)⟩

@[simp]

中文:
定义 integerSetQuotEquivAssociates
  签名: :
  定义体: Equiv.ofBijective
    (Quotient.lift (integerSetToAssociates K)
      fun _ _ h => ((integerSetToAssociates_eq_iff _ _).mpr h).symm)
.mpr by ⟨Setoid.lift_injective_iff_ker_eq_of_le _
        ext a b
        rw [Setoid.ker_def]; rw [eq_comm]; rw [integerSetToAssociates_eq_iff b a]; rw [MulAction.orbitRel_apply]; rw [MulAction.mem_orbit_iff],
        (Quot.surjective_lift _).mpr (integerSetToAssociates_surjective K)⟩

@[simp]

Depends on / 依赖: Equiv.ofBijective, MulAction, MulAction.mem_orbit_iff, MulAction.orbitRel_apply, Quot.surjective_lift, Quotient, Quotient.lift, Setoid, Setoid.ker_def, Setoid.lift_injective_iff_ker_eq_of_le, eq_comm, integerSetToAssociates, integerSetToAssociates_eq_iff, integerSetToAssociates_surjective, ker_def, lift_injective_iff_ker_eq_of_le, mem_orbit_iff, ofBijective, orbitRel_apply, surjective_lift
-/
def integerSetQuotEquivAssociates :
    Quotient (MulAction.orbitRel (torsion K) (integerSet K)) ≃ Associates (𝓞 K)⁰ :=
  Equiv.ofBijective
    (Quotient.lift (integerSetToAssociates K)
      fun _ _ h => ((integerSetToAssociates_eq_iff _ _).mpr h).symm)
.mpr by ⟨Setoid.lift_injective_iff_ker_eq_of_le _
        ext a b
        rw [Setoid.ker_def]; rw [eq_comm]; rw [integerSetToAssociates_eq_iff b a]; rw [MulAction.orbitRel_apply]; rw [MulAction.mem_orbit_iff],
        (Quot.surjective_lift _).mpr (integerSetToAssociates_surjective K)⟩

@[simp]
/--
theorem `integerSetQuotEquivAssociates_apply` / 定理 `integerSetQuotEquivAssociates_apply`

English:
theorem integerSetQuotEquivAssociates_apply
  given: (a : integerSet K)
  proof: rfl

中文:
定理 integerSetQuotEquivAssociates_apply
  条件: (a : integerSet K)
  证明: rfl
-/
theorem integerSetQuotEquivAssociates_apply (a : integerSet K) :
    integerSetQuotEquivAssociates K ⟦a⟧ = ⟦preimageOfMemIntegerSet a⟧ := rfl

/--
theorem `integerSetTorsionSMul_stabilizer` / 定理 `integerSetTorsionSMul_stabilizer`

English:
theorem integerSetTorsionSMul_stabilizer
  given: (a : integerSet K)
  proof: by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun ζ hζ => ?_
  rwa [MulAction.mem_stabilizer_iff, Subtype.ext_iff, integerSetTorsionSMul_smul_coe,
    unitSMul_smul, ← mixedEmbedding_preimageOfMemIntegerSet, ← map_mul,
    (mixedEmbedding_injective K).eq_iff, ← map_mul, ← RingOfIntegers.ext_iff, mul_eq_right₀,
    Units.val_eq_one, OneMemClass.coe_eq_one] at hζ
  exact nonZeroDivisors.coe_ne_zero _

中文:
定理 integerSetTorsionSMul_stabilizer
  条件: (a : integerSet K)
  证明: by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun ζ hζ => ?_
  rwa [MulAction.mem_stabilizer_iff, Subtype.ext_iff, integerSetTorsionSMul_smul_coe,
    unitSMul_smul, ← mixedEmbedding_preimageOfMemIntegerSet, ← map_mul,
    (mixedEmbedding_injective K).eq_iff, ← map_mul, ← RingOfIntegers.ext_iff, mul_eq_right₀,
    Units.val_eq_one, OneMemClass.coe_eq_one] at hζ
  exact nonZeroDivisors.coe_ne_zero _

Depends on / 依赖: MulAction, MulAction.mem_stabilizer_iff, OneMemClass, OneMemClass.coe_eq_one, RingOfIntegers, RingOfIntegers.ext_iff, Subgroup, Subgroup.eq_bot_iff_forall, Subtype, Subtype.ext_iff, Units.val_eq_one, coe_eq_one, coe_ne_zero, eq_bot_iff_forall, eq_iff, ext_iff, integerSetTorsionSMul_smul_coe, map_mul, mem_stabilizer_iff, mixedEmbedding_injective
-/
theorem integerSetTorsionSMul_stabilizer (a : integerSet K) :
    MulAction.stabilizer (torsion K) a = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun ζ hζ => ?_
  rwa [MulAction.mem_stabilizer_iff, Subtype.ext_iff, integerSetTorsionSMul_smul_coe,
    unitSMul_smul, ← mixedEmbedding_preimageOfMemIntegerSet, ← map_mul,
    (mixedEmbedding_injective K).eq_iff, ← map_mul, ← RingOfIntegers.ext_iff, mul_eq_right₀,
    Units.val_eq_one, OneMemClass.coe_eq_one] at hζ
  exact nonZeroDivisors.coe_ne_zero _

open Submodule Ideal

variable (K) in
/--
Definition of `integerSetEquiv` / `integerSetEquiv` 的定义

English:
definition integerSetEquiv
  signature: :
  body: (MulAction.selfEquivSigmaOrbitsQuotientStabilizer (torsion K) (integerSet K)).trans
    ((Equiv.sigmaEquivProdOfEquiv (by
        intro _
        simp_rw [integerSetTorsionSMul_stabilizer]
        exact QuotientGroup.quotientBot.toEquiv)).trans
      (Equiv.prodCongrLeft (fun _ => (integerSetQuotEquivAssociates K).trans
        (Ideal.associatesNonZeroDivisorsEquivIsPrincipal (𝓞 K)))))

@[simp]

中文:
定义 integerSetEquiv
  签名: :
  定义体: (MulAction.selfEquivSigmaOrbitsQuotientStabilizer (torsion K) (integerSet K)).trans
    ((Equiv.sigmaEquivProdOfEquiv (by
        intro _
        simp_rw [integerSetTorsionSMul_stabilizer]
        exact QuotientGroup.quotientBot.toEquiv)).trans
      (Equiv.prodCongrLeft (fun _ => (integerSetQuotEquivAssociates K).trans
        (Ideal.associatesNonZeroDivisorsEquivIsPrincipal (𝓞 K)))))

@[simp]

Depends on / 依赖: Equiv.prodCongrLeft, Equiv.sigmaEquivProdOfEquiv, Ideal.associatesNonZeroDivisorsEquivIsPrincipal, MulAction, MulAction.selfEquivSigmaOrbitsQuotientStabilizer, QuotientGroup, QuotientGroup.quotientBot.toEquiv, associatesNonZeroDivisorsEquivIsPrincipal, integerSet, integerSetQuotEquivAssociates, integerSetTorsionSMul_stabilizer, prodCongrLeft, quotientBot, selfEquivSigmaOrbitsQuotientStabilizer, sigmaEquivProdOfEquiv, simp_rw, toEquiv, torsion
-/
def integerSetEquiv :
    integerSet K ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.val} × torsion K :=
  (MulAction.selfEquivSigmaOrbitsQuotientStabilizer (torsion K) (integerSet K)).trans
    ((Equiv.sigmaEquivProdOfEquiv (by
        intro _
        simp_rw [integerSetTorsionSMul_stabilizer]
        exact QuotientGroup.quotientBot.toEquiv)).trans
      (Equiv.prodCongrLeft (fun _ => (integerSetQuotEquivAssociates K).trans
        (Ideal.associatesNonZeroDivisorsEquivIsPrincipal (𝓞 K)))))

@[simp]
/--
theorem `integerSetEquiv_apply_fst` / 定理 `integerSetEquiv_apply_fst`

English:
theorem integerSetEquiv_apply_fst
  given: (a : integerSet K)
  proof: rfl

中文:
定理 integerSetEquiv_apply_fst
  条件: (a : integerSet K)
  证明: rfl
-/
theorem integerSetEquiv_apply_fst (a : integerSet K) :
    ((integerSetEquiv K a).1 : Ideal (𝓞 K)) = span {(preimageOfMemIntegerSet a : 𝓞 K)} := rfl

variable (K) in
/--
Definition of `integerSetEquivNorm` / `integerSetEquivNorm` 的定义

English:
definition integerSetEquivNorm
  signature: (n : Nat)
  body: calc
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} × torsion K //
          absNorm (I.1 : Ideal (𝓞 K)) = n} :=
      Equiv.subtypeEquiv (integerSetEquiv K) fun _ => by simp_rw [← intNorm_coe, intNorm,
        Nat.cast_inj, integerSetEquiv_apply_fst, absNorm_span_singleton]
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} // absNorm (I.1 : Ideal (𝓞 K)) = n} ×
          torsion K := Equiv.prodSubtypeFstEquivSubtypeProd
      (p := fun I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} => absNorm (I : Ideal (𝓞 K)) = n)
    _ ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) = n} × (torsion K) := Equiv.prodCongrLeft fun _ =>
      (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun I : (Ideal (𝓞 K))⁰ => IsPrincipal I.1) (fun I => absNorm I.1 = n))

@[simp]

中文:
定义 integerSetEquivNorm
  签名: (n : 自然数)
  定义体: calc
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} × torsion K //
          absNorm (I.1 : Ideal (𝓞 K)) = n} :=
      Equiv.subtypeEquiv (integerSetEquiv K) fun _ => by simp_rw [← intNorm_coe, intNorm,
        Nat.cast_inj, integerSetEquiv_apply_fst, absNorm_span_singleton]
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} // absNorm (I.1 : Ideal (𝓞 K)) = n} ×
          torsion K := Equiv.prodSubtypeFstEquivSubtypeProd
      (p := fun I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} => absNorm (I : Ideal (𝓞 K)) = n)
    _ ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) = n} × (torsion K) := Equiv.prodCongrLeft fun _ =>
      (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun I : (Ideal (𝓞 K))⁰ => IsPrincipal I.1) (fun I => absNorm I.1 = n))

@[simp]

Depends on / 依赖: Equiv.prodSubtypeFstEquivSubtypeProd, Equiv.subtypeEquiv, IsPrincipal, Nat.cast_inj, absNorm, absNorm_span_singleton, cast_inj, intNorm, intNorm_coe, integerSetEquiv, integerSetEquiv_apply_fst, prodSubtypeFstEquivSubtypeProd, simp_rw, subtypeEquiv, torsion
-/
def integerSetEquivNorm (n : Nat) :
    {a : integerSet K // mixedEmbedding.norm (a : mixedSpace K) = n} ≃
      {I : (Ideal (𝓞 K))⁰ // IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) = n} × (torsion K) :=
  calc
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} × torsion K //
          absNorm (I.1 : Ideal (𝓞 K)) = n} :=
      Equiv.subtypeEquiv (integerSetEquiv K) fun _ => by simp_rw [← intNorm_coe, intNorm,
        Nat.cast_inj, integerSetEquiv_apply_fst, absNorm_span_singleton]
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} // absNorm (I.1 : Ideal (𝓞 K)) = n} ×
          torsion K := Equiv.prodSubtypeFstEquivSubtypeProd
      (p := fun I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} => absNorm (I : Ideal (𝓞 K)) = n)
    _ ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) = n} × (torsion K) := Equiv.prodCongrLeft fun _ =>
      (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun I : (Ideal (𝓞 K))⁰ => IsPrincipal I.1) (fun I => absNorm I.1 = n))

@[simp]
/--
theorem `integerSetEquivNorm_apply_fst` / 定理 `integerSetEquivNorm_apply_fst`

English:
theorem integerSetEquivNorm_apply_fst
  statement: {n : Nat}
  proof: by
  simp_rw [integerSetEquivNorm, Equiv.prodSubtypeFstEquivSubtypeProd, Equiv.trans_def,
    Equiv.prodCongrLeft, Equiv.trans_apply, Equiv.subtypeEquiv_apply, Equiv.coe_fn_mk,
    Equiv.subtypeSubtypeEquivSubtypeInter_apply_coe, integerSetEquiv_apply_fst]

中文:
定理 integerSetEquivNorm_apply_fst
  结论: {n : 自然数}
  证明: by
  simp_rw [integerSetEquivNorm, Equiv.prodSubtypeFstEquivSubtypeProd, Equiv.trans_def,
    Equiv.prodCongrLeft, Equiv.trans_apply, Equiv.subtypeEquiv_apply, Equiv.coe_fn_mk,
    Equiv.subtypeSubtypeEquivSubtypeInter_apply_coe, integerSetEquiv_apply_fst]

Depends on / 依赖: Equiv.coe_fn_mk, Equiv.prodCongrLeft, Equiv.prodSubtypeFstEquivSubtypeProd, Equiv.subtypeEquiv_apply, Equiv.subtypeSubtypeEquivSubtypeInter_apply_coe, Equiv.trans_apply, Equiv.trans_def, coe_fn_mk, integerSetEquivNorm, integerSetEquiv_apply_fst, prodCongrLeft, prodSubtypeFstEquivSubtypeProd, simp_rw, subtypeEquiv_apply, subtypeSubtypeEquivSubtypeInter_apply_coe, trans_apply, trans_def
-/
theorem integerSetEquivNorm_apply_fst {n : Nat}
    (a : {a : integerSet K // mixedEmbedding.norm (a : mixedSpace K) = n}) :
    ((integerSetEquivNorm K n a).1 : Ideal (𝓞 K)) =
      span {(preimageOfMemIntegerSet a.val : 𝓞 K)} := by
  simp_rw [integerSetEquivNorm, Equiv.prodSubtypeFstEquivSubtypeProd, Equiv.trans_def,
    Equiv.prodCongrLeft, Equiv.trans_apply, Equiv.subtypeEquiv_apply, Equiv.coe_fn_mk,
    Equiv.subtypeSubtypeEquivSubtypeInter_apply_coe, integerSetEquiv_apply_fst]

variable (K)

/--
theorem `card_isPrincipal_norm_eq_mul_torsion` / 定理 `card_isPrincipal_norm_eq_mul_torsion`

English:
theorem card_isPrincipal_norm_eq_mul_torsion
  given: (n : Nat)
  proof: by
  rw [torsionOrder]; rw [← Nat.card_prod]
  exact Nat.card_congr (integerSetEquivNorm K n).symm

中文:
定理 card_isPrincipal_norm_eq_mul_torsion
  条件: (n : 自然数)
  证明: by
  rw [torsionOrder]; rw [← Nat.card_prod]
  exact Nat.card_congr (integerSetEquivNorm K n).symm

Depends on / 依赖: Nat.card_congr, Nat.card_prod, card_congr, card_prod, integerSetEquivNorm, torsionOrder
-/
theorem card_isPrincipal_norm_eq_mul_torsion (n : Nat) :
    Nat.card {I : (Ideal (𝓞 K))⁰ | IsPrincipal (I : Ideal (𝓞 K)) ∧
      absNorm (I : Ideal (𝓞 K)) = n} * torsionOrder K =
        Nat.card {a : integerSet K | mixedEmbedding.norm (a : mixedSpace K) = n} := by
  rw [torsionOrder]; rw [← Nat.card_prod]
  exact Nat.card_congr (integerSetEquivNorm K n).symm

variable (J : (Ideal (𝓞 K))⁰)

/--
Definition of `idealSet` / `idealSet` 的定义

English:
definition idealSet
  signature: : Set (mixedSpace K)
  body: fundamentalCone K inter (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))

中文:
定义 idealSet
  签名: : 集合 (mixedSpace K)
  定义体: fundamentalCone K inter (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))

Depends on / 依赖: FractionalIdeal, FractionalIdeal.mk0, fundamentalCone, idealLattice, mixedEmbedding, mixedEmbedding.idealLattice
-/
def idealSet : Set (mixedSpace K) :=
  fundamentalCone K inter (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))

set_option backward.isDefEq.respectTransparency.types false in
variable {K J} in
/--
theorem `mem_idealSet` / 定理 `mem_idealSet`

English:
theorem mem_idealSet
  proof: by
  simp_rw [idealSet, Set.mem_inter_iff, idealLattice, SetLike.mem_coe, FractionalIdeal.coe_mk0,
    LinearMap.mem_range, LinearMap.coe_comp, LinearMap.coe_restrictScalars, coe_subtype,
    Function.comp_apply, AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe, Subtype.exists,
    FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal, exists_prop', nonempty_prop,
    exists_exists_and_eq_and]

中文:
定理 mem_idealSet
  证明: by
  simp_rw [idealSet, Set.mem_inter_iff, idealLattice, SetLike.mem_coe, FractionalIdeal.coe_mk0,
    LinearMap.mem_range, LinearMap.coe_comp, LinearMap.coe_restrictScalars, coe_subtype,
    Function.comp_apply, AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe, Subtype.exists,
    FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal, exists_prop', nonempty_prop,
    exists_exists_and_eq_and]

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_apply, FractionalIdeal, FractionalIdeal.coe_mk0, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal, Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearMap.mem_range, RingHom, RingHom.toIntAlgHom_coe, Set.mem_inter_iff, SetLike, SetLike.mem_coe, Subtype, Subtype.exists, coe_comp
-/
theorem mem_idealSet :
    x in idealSet K J ↔ x in fundamentalCone K ∧ exists a : (𝓞 K), (a : 𝓞 K) in (J : Set (𝓞 K)) ∧
      mixedEmbedding K (a : 𝓞 K) = x := by
  simp_rw [idealSet, Set.mem_inter_iff, idealLattice, SetLike.mem_coe, FractionalIdeal.coe_mk0,
    LinearMap.mem_range, LinearMap.coe_comp, LinearMap.coe_restrictScalars, coe_subtype,
    Function.comp_apply, AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe, Subtype.exists,
    FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal, exists_prop', nonempty_prop,
    exists_exists_and_eq_and]

/--
Definition of `idealSetMap` / `idealSetMap` 的定义

English:
definition idealSetMap
  signature: : idealSet K J -> integerSet K
  body: fun ⟨a, ha⟩ => ⟨a, mem_integerSet.mpr ⟨(mem_idealSet.mp ha).1, (mem_idealSet.mp ha).2.choose,
    (mem_idealSet.mp ha).2.choose_spec.2⟩⟩

@[simp]

中文:
定义 idealSetMap
  签名: : idealSet K J -> integerSet K
  定义体: fun ⟨a, ha⟩ => ⟨a, mem_integerSet.mpr ⟨(mem_idealSet.mp ha).1, (mem_idealSet.mp ha).2.choose,
    (mem_idealSet.mp ha).2.choose_spec.2⟩⟩

@[simp]

Depends on / 依赖: choose_spec, mem_idealSet, mem_idealSet.mp, mem_integerSet, mem_integerSet.mpr
-/
def idealSetMap : idealSet K J -> integerSet K :=
  fun ⟨a, ha⟩ => ⟨a, mem_integerSet.mpr ⟨(mem_idealSet.mp ha).1, (mem_idealSet.mp ha).2.choose,
    (mem_idealSet.mp ha).2.choose_spec.2⟩⟩

@[simp]
/--
theorem `idealSetMap_apply` / 定理 `idealSetMap_apply`

English:
theorem idealSetMap_apply
  given: (a : idealSet K J)
  statement: (idealSetMap K J a : mixedSpace K) = a
  proof: rfl

中文:
定理 idealSetMap_apply
  条件: (a : idealSet K J)
  结论: (idealSetMap K J a : mixedSpace K) = a
  证明: rfl
-/
theorem idealSetMap_apply (a : idealSet K J) : (idealSetMap K J a : mixedSpace K) = a := rfl

/--
theorem `preimage_of_IdealSetMap` / 定理 `preimage_of_IdealSetMap`

English:
theorem preimage_of_IdealSetMap
  given: (a : idealSet K J)
  proof: by
  obtain ⟨_, ⟨x, hx₁, hx₂⟩⟩ := mem_idealSet.mp a.prop
  simp_rw [idealSetMap, ← hx₂, preimageOfMemIntegerSet_mixedEmbedding]
  exact hx₁

中文:
定理 preimage_of_IdealSetMap
  条件: (a : idealSet K J)
  证明: by
  obtain ⟨_, ⟨x, hx₁, hx₂⟩⟩ := mem_idealSet.mp a.prop
  simp_rw [idealSetMap, ← hx₂, preimageOfMemIntegerSet_mixedEmbedding]
  exact hx₁

Depends on / 依赖: a.prop, idealSetMap, mem_idealSet, mem_idealSet.mp, preimageOfMemIntegerSet_mixedEmbedding, simp_rw
-/
theorem preimage_of_IdealSetMap (a : idealSet K J) :
    (preimageOfMemIntegerSet (idealSetMap K J a) : 𝓞 K) in (J : Set (𝓞 K)) := by
  obtain ⟨_, ⟨x, hx₁, hx₂⟩⟩ := mem_idealSet.mp a.prop
  simp_rw [idealSetMap, ← hx₂, preimageOfMemIntegerSet_mixedEmbedding]
  exact hx₁

/--
Definition of `idealSetEquiv` / `idealSetEquiv` 的定义

English:
definition idealSetEquiv
  signature: : idealSet K J ≃
  body: Equiv.ofBijective (fun a => ⟨idealSetMap K J a, preimage_of_IdealSetMap K J a⟩)
    ⟨fun _ _ h => (by
        simp_rw [Subtype.ext_iff, idealSetMap_apply] at h
        rwa [Subtype.ext_iff]),
    fun ⟨a, ha₂⟩ => ⟨⟨a.val, mem_idealSet.mpr ⟨a.prop.1,
        ⟨preimageOfMemIntegerSet a, ha₂, mixedEmbedding_preimageOfMemIntegerSet a⟩⟩⟩, rfl⟩⟩

中文:
定义 idealSetEquiv
  签名: : idealSet K J ≃
  定义体: Equiv.ofBijective (fun a => ⟨idealSetMap K J a, preimage_of_IdealSetMap K J a⟩)
    ⟨fun _ _ h => (by
        simp_rw [Subtype.ext_iff, idealSetMap_apply] at h
        rwa [Subtype.ext_iff]),
    fun ⟨a, ha₂⟩ => ⟨⟨a.val, mem_idealSet.mpr ⟨a.prop.1,
        ⟨preimageOfMemIntegerSet a, ha₂, mixedEmbedding_preimageOfMemIntegerSet a⟩⟩⟩, rfl⟩⟩

Depends on / 依赖: Equiv.ofBijective, Subtype, Subtype.ext_iff, a.prop, a.val, ext_iff, idealSetMap, idealSetMap_apply, mem_idealSet, mem_idealSet.mpr, mixedEmbedding_preimageOfMemIntegerSet, ofBijective, preimageOfMemIntegerSet, preimage_of_IdealSetMap, simp_rw
-/
def idealSetEquiv : idealSet K J ≃
    {a : integerSet K | (preimageOfMemIntegerSet a : 𝓞 K) in (J : Set (𝓞 K))} :=
  Equiv.ofBijective (fun a => ⟨idealSetMap K J a, preimage_of_IdealSetMap K J a⟩)
    ⟨fun _ _ h => (by
        simp_rw [Subtype.ext_iff, idealSetMap_apply] at h
        rwa [Subtype.ext_iff]),
    fun ⟨a, ha₂⟩ => ⟨⟨a.val, mem_idealSet.mpr ⟨a.prop.1,
        ⟨preimageOfMemIntegerSet a, ha₂, mixedEmbedding_preimageOfMemIntegerSet a⟩⟩⟩, rfl⟩⟩

variable {K J}

/--
theorem `idealSetEquiv_apply` / 定理 `idealSetEquiv_apply`

English:
theorem idealSetEquiv_apply
  given: (a : idealSet K J)
  proof: rfl

中文:
定理 idealSetEquiv_apply
  条件: (a : idealSet K J)
  证明: rfl
-/
theorem idealSetEquiv_apply (a : idealSet K J) :
    (idealSetEquiv K J a : mixedSpace K) = a := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `idealSetEquiv_symm_apply` / 定理 `idealSetEquiv_symm_apply`

English:
theorem idealSetEquiv_symm_apply
  proof: by
  rw [← (idealSetEquiv_apply ((idealSetEquiv K J).symm a))]; rw [Equiv.apply_symm_apply]

中文:
定理 idealSetEquiv_symm_apply
  证明: by
  rw [← (idealSetEquiv_apply ((idealSetEquiv K J).symm a))]; rw [Equiv.apply_symm_apply]

Depends on / 依赖: Equiv.apply_symm_apply, apply_symm_apply, idealSetEquiv, idealSetEquiv_apply
-/
theorem idealSetEquiv_symm_apply
    (a : {a : integerSet K // (preimageOfMemIntegerSet a : 𝓞 K) in (J : Set (𝓞 K)) }) :
    ((idealSetEquiv K J).symm a : mixedSpace K) = a := by
  rw [← (idealSetEquiv_apply ((idealSetEquiv K J).symm a))]; rw [Equiv.apply_symm_apply]

/--
theorem `intNorm_idealSetEquiv_apply` / 定理 `intNorm_idealSetEquiv_apply`

English:
theorem intNorm_idealSetEquiv_apply
  given: (a : idealSet K J)
  proof: by
  rw [intNorm_coe]; rw [idealSetEquiv_apply]

中文:
定理 intNorm_idealSetEquiv_apply
  条件: (a : idealSet K J)
  证明: by
  rw [intNorm_coe]; rw [idealSetEquiv_apply]

Depends on / 依赖: idealSetEquiv_apply, intNorm_coe
-/
theorem intNorm_idealSetEquiv_apply (a : idealSet K J) :
    intNorm (idealSetEquiv K J a).val = mixedEmbedding.norm (a : mixedSpace K) := by
  rw [intNorm_coe]; rw [idealSetEquiv_apply]

variable (K J)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `idealSetEquivNorm` / `idealSetEquivNorm` 的定义

English:
definition idealSetEquivNorm
  signature: (n : Nat)
  body: calc
    _ ≃ {a : {a : integerSet K // (preimageOfMemIntegerSet a).1 in J.1} //
            mixedEmbedding.norm a.1.1 = n} := by
        convert! (Equiv.subtypeEquivOfSubtype (idealSetEquiv K J).symm).symm using 3
        rw [idealSetEquiv_symm_apply]
    _ ≃ {a : integerSet K // (preimageOfMemIntegerSet a).1 in J.1 ∧
          mixedEmbedding.norm a.1 = n} := Equiv.subtypeSubtypeEquivSubtypeInter
        (fun a : integerSet K => (preimageOfMemIntegerSet a).1 in J.1)
        (fun a => mixedEmbedding.norm a.1 = n)
    _ ≃ {a : {a :integerSet K // mixedEmbedding.norm a.1 = n} //
          (preimageOfMemIntegerSet a.1).1 in J.1} := ((Equiv.subtypeSubtypeEquivSubtypeInter
        (fun a : integerSet K => mixedEmbedding.norm a.1 = n)
        (fun a => (preimageOfMemIntegerSet a).1 in J.1)).trans
        (Equiv.subtypeEquivRight (fun _ => by simp [and_comm]))).symm
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = n} × (torsion K) //
          J.1 ∣ I.1.1} := by
      convert! Equiv.subtypeEquivOfSubtype (p := fun I => J.1 ∣ I.1) (integerSetEquivNorm K n)
      rw [integerSetEquivNorm_apply_fst]; rw [dvd_span_singleton]
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = n} // J.1 ∣ I.1} ×
        (torsion K) := Equiv.prodSubtypeFstEquivSubtypeProd
        (p := fun I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = n} => J.1 ∣ I.1)
    _ ≃ {I : (Ideal (𝓞 K))⁰ // (IsPrincipal I.1 ∧ absNorm I.1 = n) ∧ J.1 ∣ I.1} × (torsion K) :=
      Equiv.prodCongrLeft fun _ => (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun I : (Ideal (𝓞 K))⁰ => IsPrincipal I.1 ∧ absNorm I.1 = n)
        (fun I => J.1 ∣ I.1))
    _ ≃ {I : (Ideal (𝓞 K))⁰ // J.1 ∣ I.1 ∧ IsPrincipal I.1 ∧ absNorm I.1 = n} ×
          (Units.torsion K) :=
      Equiv.prodCongrLeft fun _ => Equiv.subtypeEquivRight fun _ => by rw [and_comm]

中文:
定义 idealSetEquivNorm
  签名: (n : 自然数)
  定义体: calc
    _ ≃ {a : {a : integerSet K // (preimageOfMemIntegerSet a).1 in J.1} //
            mixedEmbedding.norm a.1.1 = n} := by
        convert! (Equiv.subtypeEquivOfSubtype (idealSetEquiv K J).symm).symm using 3
        rw [idealSetEquiv_symm_apply]
    _ ≃ {a : integerSet K // (preimageOfMemIntegerSet a).1 in J.1 ∧
          mixedEmbedding.norm a.1 = n} := Equiv.subtypeSubtypeEquivSubtypeInter
        (fun a : integerSet K => (preimageOfMemIntegerSet a).1 in J.1)
        (fun a => mixedEmbedding.norm a.1 = n)
    _ ≃ {a : {a :integerSet K // mixedEmbedding.norm a.1 = n} //
          (preimageOfMemIntegerSet a.1).1 in J.1} := ((Equiv.subtypeSubtypeEquivSubtypeInter
        (fun a : integerSet K => mixedEmbedding.norm a.1 = n)
        (fun a => (preimageOfMemIntegerSet a).1 in J.1)).trans
        (Equiv.subtypeEquivRight (fun _ => by simp [and_comm]))).symm
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = n} × (torsion K) //
          J.1 ∣ I.1.1} := by
      convert! Equiv.subtypeEquivOfSubtype (p := fun I => J.1 ∣ I.1) (integerSetEquivNorm K n)
      rw [integerSetEquivNorm_apply_fst]; rw [dvd_span_singleton]
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = n} // J.1 ∣ I.1} ×
        (torsion K) := Equiv.prodSubtypeFstEquivSubtypeProd
        (p := fun I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = n} => J.1 ∣ I.1)
    _ ≃ {I : (Ideal (𝓞 K))⁰ // (IsPrincipal I.1 ∧ absNorm I.1 = n) ∧ J.1 ∣ I.1} × (torsion K) :=
      Equiv.prodCongrLeft fun _ => (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun I : (Ideal (𝓞 K))⁰ => IsPrincipal I.1 ∧ absNorm I.1 = n)
        (fun I => J.1 ∣ I.1))
    _ ≃ {I : (Ideal (𝓞 K))⁰ // J.1 ∣ I.1 ∧ IsPrincipal I.1 ∧ absNorm I.1 = n} ×
          (Units.torsion K) :=
      Equiv.prodCongrLeft fun _ => Equiv.subtypeEquivRight fun _ => by rw [and_comm]

Depends on / 依赖: Equiv.subtypeEquivOfSubtype, Equiv.subtypeSubtypeEquivSubtypeInter, convert, idealSetEquiv, idealSetEquiv_symm_apply, integerSet, mixedEmbedding, mixedEmbedding.norm, preimageOfMemIntegerSet, subtypeEquivOfSubtype, subtypeSubtypeEquivSubtypeInter
-/
def idealSetEquivNorm (n : Nat) :
    {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) = n} ≃
      {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) = n} × (torsion K) :=
  calc
    _ ≃ {a : {a : integerSet K // (preimageOfMemIntegerSet a).1 in J.1} //
            mixedEmbedding.norm a.1.1 = n} := by
        convert! (Equiv.subtypeEquivOfSubtype (idealSetEquiv K J).symm).symm using 3
        rw [idealSetEquiv_symm_apply]
    _ ≃ {a : integerSet K // (preimageOfMemIntegerSet a).1 in J.1 ∧
          mixedEmbedding.norm a.1 = n} := Equiv.subtypeSubtypeEquivSubtypeInter
        (fun a : integerSet K => (preimageOfMemIntegerSet a).1 in J.1)
        (fun a => mixedEmbedding.norm a.1 = n)
    _ ≃ {a : {a :integerSet K // mixedEmbedding.norm a.1 = n} //
          (preimageOfMemIntegerSet a.1).1 in J.1} := ((Equiv.subtypeSubtypeEquivSubtypeInter
        (fun a : integerSet K => mixedEmbedding.norm a.1 = n)
        (fun a => (preimageOfMemIntegerSet a).1 in J.1)).trans
        (Equiv.subtypeEquivRight (fun _ => by simp [and_comm]))).symm
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = n} × (torsion K) //
          J.1 ∣ I.1.1} := by
      convert! Equiv.subtypeEquivOfSubtype (p := fun I => J.1 ∣ I.1) (integerSetEquivNorm K n)
      rw [integerSetEquivNorm_apply_fst]; rw [dvd_span_singleton]
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = n} // J.1 ∣ I.1} ×
        (torsion K) := Equiv.prodSubtypeFstEquivSubtypeProd
        (p := fun I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = n} => J.1 ∣ I.1)
    _ ≃ {I : (Ideal (𝓞 K))⁰ // (IsPrincipal I.1 ∧ absNorm I.1 = n) ∧ J.1 ∣ I.1} × (torsion K) :=
      Equiv.prodCongrLeft fun _ => (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun I : (Ideal (𝓞 K))⁰ => IsPrincipal I.1 ∧ absNorm I.1 = n)
        (fun I => J.1 ∣ I.1))
    _ ≃ {I : (Ideal (𝓞 K))⁰ // J.1 ∣ I.1 ∧ IsPrincipal I.1 ∧ absNorm I.1 = n} ×
          (Units.torsion K) :=
      Equiv.prodCongrLeft fun _ => Equiv.subtypeEquivRight fun _ => by rw [and_comm]

/--
theorem `card_isPrincipal_dvd_norm_le` / 定理 `card_isPrincipal_dvd_norm_le`

English:
theorem card_isPrincipal_dvd_norm_le
  given: (s : Real)
  proof: by
  obtain hs | hs := le_or_gt 0 s
  · simp_rw [← intNorm_idealSetEquiv_apply, ← Nat.le_floor_iff hs]
    rw [torsionOrder]; rw [← Nat.card_prod]
refine Nat.card_congr @Equiv.ofFiberEquiv _ (γ := Finset.Iic ⌊s⌋₊) _
      (fun I => ⟨absNorm I.1.val.1, Finset.mem_Iic.mpr I.1.prop.2.2⟩)
      (fun a => ⟨intNorm (idealSetEquiv K J a.1).1, Finset.mem_Iic.mpr a.prop⟩) fun ⟨i, hi⟩ => ?_
    simp_rw [Subtype.mk.injEq]
    calc _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // _ ∧ _ ∧ _} // absNorm I.1.1 = i} × torsion K :=
        Equiv.prodSubtypeFstEquivSubtypeProd
      _ ≃ {I : (Ideal (𝓞 K))⁰ // (_ ∧ _ ∧ absNorm I.1 <= ⌊s⌋₊) ∧ absNorm I.1 = i}
            × torsion K := Equiv.prodCongrLeft fun _ => (Equiv.subtypeSubtypeEquivSubtypeInter
        (p := fun I : (Ideal (𝓞 K))⁰ => J.1 ∣ I.1 ∧ IsPrincipal I.1 ∧ absNorm I.1 <= ⌊s⌋₊)
        (q := fun I => absNorm I.1 = i))
      _ ≃ {I : (Ideal (𝓞 K))⁰ // J.1 ∣ I.1 ∧ IsPrincipal I.1 ∧ absNorm I.1 = i}
            × torsion K := Equiv.prodCongrLeft fun _ => Equiv.subtypeEquivRight fun _ => by grind
      _ ≃ {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) = i} :=
            (idealSetEquivNorm K J i).symm
      _ ≃ {a : idealSet K J // intNorm (idealSetEquiv K J a).1 = i} := by
        simp_rw [← intNorm_idealSetEquiv_apply, Nat.cast_inj]
        rfl
      _ ≃ {b : {a : idealSet K J // intNorm (idealSetEquiv K J a).1 <= ⌊s⌋₊} //
            intNorm (idealSetEquiv K J b).1 = i} :=
        (Equiv.subtypeSubtypeEquivSubtype fun h => Finset.mem_Iic.mp (h ▸ hi)).symm
  · simp_rw [lt_iff_not_ge.mp (lt_of_lt_of_le hs (Nat.cast_nonneg _)), lt_iff_not_ge.mp
      (lt_of_lt_of_le hs (mixedEmbedding.norm_nonneg _)), and_false, Nat.card_of_isEmpty,
      zero_mul]

中文:
定理 card_isPrincipal_dvd_norm_le
  条件: (s : 实数)
  证明: by
  obtain hs | hs := le_or_gt 0 s
  · simp_rw [← intNorm_idealSetEquiv_apply, ← Nat.le_floor_iff hs]
    rw [torsionOrder]; rw [← Nat.card_prod]
refine Nat.card_congr @Equiv.ofFiberEquiv _ (γ := Finset.Iic ⌊s⌋₊) _
      (fun I => ⟨absNorm I.1.val.1, Finset.mem_Iic.mpr I.1.prop.2.2⟩)
      (fun a => ⟨intNorm (idealSetEquiv K J a.1).1, Finset.mem_Iic.mpr a.prop⟩) fun ⟨i, hi⟩ => ?_
    simp_rw [Subtype.mk.injEq]
    calc _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // _ ∧ _ ∧ _} // absNorm I.1.1 = i} × torsion K :=
        Equiv.prodSubtypeFstEquivSubtypeProd
      _ ≃ {I : (Ideal (𝓞 K))⁰ // (_ ∧ _ ∧ absNorm I.1 <= ⌊s⌋₊) ∧ absNorm I.1 = i}
            × torsion K := Equiv.prodCongrLeft fun _ => (Equiv.subtypeSubtypeEquivSubtypeInter
        (p := fun I : (Ideal (𝓞 K))⁰ => J.1 ∣ I.1 ∧ IsPrincipal I.1 ∧ absNorm I.1 <= ⌊s⌋₊)
        (q := fun I => absNorm I.1 = i))
      _ ≃ {I : (Ideal (𝓞 K))⁰ // J.1 ∣ I.1 ∧ IsPrincipal I.1 ∧ absNorm I.1 = i}
            × torsion K := Equiv.prodCongrLeft fun _ => Equiv.subtypeEquivRight fun _ => by grind
      _ ≃ {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) = i} :=
            (idealSetEquivNorm K J i).symm
      _ ≃ {a : idealSet K J // intNorm (idealSetEquiv K J a).1 = i} := by
        simp_rw [← intNorm_idealSetEquiv_apply, Nat.cast_inj]
        rfl
      _ ≃ {b : {a : idealSet K J // intNorm (idealSetEquiv K J a).1 <= ⌊s⌋₊} //
            intNorm (idealSetEquiv K J b).1 = i} :=
        (Equiv.subtypeSubtypeEquivSubtype fun h => Finset.mem_Iic.mp (h ▸ hi)).symm
  · simp_rw [lt_iff_not_ge.mp (lt_of_lt_of_le hs (Nat.cast_nonneg _)), lt_iff_not_ge.mp
      (lt_of_lt_of_le hs (mixedEmbedding.norm_nonneg _)), and_false, Nat.card_of_isEmpty,
      zero_mul]

Depends on / 依赖: Equiv.ofFiberEquiv, Equiv.prodSubtypeFstEqui, Finset, Finset.Iic, Finset.mem_Iic.mpr, Nat.card_congr, Nat.card_prod, Nat.le_floor_iff, Subtype, Subtype.mk.injEq, a.prop, absNorm, card_congr, card_prod, idealSetEquiv, intNorm, intNorm_idealSetEquiv_apply, le_floor_iff, le_or_gt, mem_Iic
-/
theorem card_isPrincipal_dvd_norm_le (s : Real) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
      absNorm (I : Ideal (𝓞 K)) <= s} * torsionOrder K =
        Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) <= s} := by
  obtain hs | hs := le_or_gt 0 s
  · simp_rw [← intNorm_idealSetEquiv_apply, ← Nat.le_floor_iff hs]
    rw [torsionOrder]; rw [← Nat.card_prod]
refine Nat.card_congr @Equiv.ofFiberEquiv _ (γ := Finset.Iic ⌊s⌋₊) _
      (fun I => ⟨absNorm I.1.val.1, Finset.mem_Iic.mpr I.1.prop.2.2⟩)
      (fun a => ⟨intNorm (idealSetEquiv K J a.1).1, Finset.mem_Iic.mpr a.prop⟩) fun ⟨i, hi⟩ => ?_
    simp_rw [Subtype.mk.injEq]
    calc _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // _ ∧ _ ∧ _} // absNorm I.1.1 = i} × torsion K :=
        Equiv.prodSubtypeFstEquivSubtypeProd
      _ ≃ {I : (Ideal (𝓞 K))⁰ // (_ ∧ _ ∧ absNorm I.1 <= ⌊s⌋₊) ∧ absNorm I.1 = i}
            × torsion K := Equiv.prodCongrLeft fun _ => (Equiv.subtypeSubtypeEquivSubtypeInter
        (p := fun I : (Ideal (𝓞 K))⁰ => J.1 ∣ I.1 ∧ IsPrincipal I.1 ∧ absNorm I.1 <= ⌊s⌋₊)
        (q := fun I => absNorm I.1 = i))
      _ ≃ {I : (Ideal (𝓞 K))⁰ // J.1 ∣ I.1 ∧ IsPrincipal I.1 ∧ absNorm I.1 = i}
            × torsion K := Equiv.prodCongrLeft fun _ => Equiv.subtypeEquivRight fun _ => by grind
      _ ≃ {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) = i} :=
            (idealSetEquivNorm K J i).symm
      _ ≃ {a : idealSet K J // intNorm (idealSetEquiv K J a).1 = i} := by
        simp_rw [← intNorm_idealSetEquiv_apply, Nat.cast_inj]
        rfl
      _ ≃ {b : {a : idealSet K J // intNorm (idealSetEquiv K J a).1 <= ⌊s⌋₊} //
            intNorm (idealSetEquiv K J b).1 = i} :=
        (Equiv.subtypeSubtypeEquivSubtype fun h => Finset.mem_Iic.mp (h ▸ hi)).symm
  · simp_rw [lt_iff_not_ge.mp (lt_of_lt_of_le hs (Nat.cast_nonneg _)), lt_iff_not_ge.mp
      (lt_of_lt_of_le hs (mixedEmbedding.norm_nonneg _)), and_false, Nat.card_of_isEmpty,
      zero_mul]

end fundamentalCone

end

end NumberField.mixedEmbedding
