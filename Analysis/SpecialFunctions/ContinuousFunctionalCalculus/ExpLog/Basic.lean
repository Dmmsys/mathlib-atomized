/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-!
# The exponential and logarithm based on the continuous functional calculus

This file defines the logarithm via the continuous functional calculus (CFC) and builds its API.
This allows one to take logs of matrices, operators, elements of a C⋆-algebra, etc.

It also shows that exponentials defined via the continuous functional calculus are equal to
`NormedSpace.exp` (defined via power series) whenever the former are not junk values.

## Main declarations

+ `CFC.log`: the real log function based on the CFC, i.e. `cfc Real.log`
+ `CFC.exp_eq_normedSpace_exp`: exponentials based on the CFC are equal to exponentials based
  on power series.
+ `CFC.log_exp` and `CFC.exp_log`: `CFC.log` and `NormedSpace.exp ℝ` are inverses of each other.

## Implementation notes

Since `cfc Real.exp` and `cfc Complex.exp` are strictly less general than `NormedSpace.exp`
(defined via power series), we only give minimal API for these here in order to relate
`NormedSpace.exp` to functions defined via the CFC. In particular, we don't give separate
definitions for them.

## TODO

+ Show that `log (a * b) = log a + log b` whenever `a` and `b` commute (and the same for indexed
  products).
+ Relate `CFC.log` to `rpow`, `zpow`, `sqrt`, `inv`.
-/

@[expose] public section

open NormedSpace

section general_exponential
variable {𝕜 : Type*} {α : Type*} [RCLike 𝕜] [TopologicalSpace α] [CompactSpace α]

/--
lemma `NormedSpace.exp_continuousMap_eq` / 引理 `NormedSpace.exp_continuousMap_eq`

English:
lemma NormedSpace.exp_continuousMap_eq
  given: (f : C(α, 𝕜))
  proof: by
  ext a
  simp_rw [NormedSpace.exp_eq_expSeries_sum (𝔸 := C(α, 𝕜)) 𝕜, FormalMultilinearSeries.sum]
  have h_sum := NormedSpace.expSeries_summable (𝕂 := 𝕜) f
  simp_rw [← ContinuousMap.tsum_apply h_sum a, NormedSpace.expSeries_apply_eq]
  simp [NormedSpace.exp_eq_tsum 𝕜]

中文:
引理 赋范空间.exp_continuousMap_eq
  条件: (f : C(α, 𝕜))
  证明: by
  ext a
  simp_rw [NormedSpace.exp_eq_expSeries_sum (𝔸 := C(α, 𝕜)) 𝕜, FormalMultilinearSeries.sum]
  have h_sum := NormedSpace.expSeries_summable (𝕂 := 𝕜) f
  simp_rw [← ContinuousMap.tsum_apply h_sum a, NormedSpace.expSeries_apply_eq]
  simp [NormedSpace.exp_eq_tsum 𝕜]

Depends on / 依赖: ContinuousMap, ContinuousMap.tsum_apply, FormalMultilinearSeries, FormalMultilinearSeries.sum, NormedSpace, NormedSpace.expSeries_apply_eq, NormedSpace.expSeries_summable, NormedSpace.exp_eq_expSeries_sum, NormedSpace.exp_eq_tsum, expSeries_apply_eq, expSeries_summable, exp_eq_expSeries_sum, exp_eq_tsum, h_sum, simp_rw, tsum_apply
-/
lemma NormedSpace.exp_continuousMap_eq (f : C(α, 𝕜)) :
    exp f = (⟨exp ∘ f, exp_continuous.comp f.continuous⟩ : C(α, 𝕜)) := by
  ext a
  simp_rw [NormedSpace.exp_eq_expSeries_sum (𝔸 := C(α, 𝕜)) 𝕜, FormalMultilinearSeries.sum]
  have h_sum := NormedSpace.expSeries_summable (𝕂 := 𝕜) f
  simp_rw [← ContinuousMap.tsum_apply h_sum a, NormedSpace.expSeries_apply_eq]
  simp [NormedSpace.exp_eq_tsum 𝕜]

end general_exponential

namespace CFC
section RCLikeNormed

variable {𝕜 : Type*} {A : Type*} [RCLike 𝕜] {p : A -> Prop} [NormedRing A]
  [StarRing A] [NormedAlgebra 𝕜 A] [ContinuousFunctionalCalculus 𝕜 A p]

open scoped ContinuousFunctionalCalculus in
/--
lemma `exp_eq_normedSpace_exp` / 引理 `exp_eq_normedSpace_exp`

English:
lemma exp_eq_normedSpace_exp
  given: {a : A} (ha : p a := by cfc_tac)
  proof: by
  conv_rhs => rw [← cfc_id 𝕜 a ha, cfc_apply id a ha]
  have h := cfcHom_continuous (R := 𝕜) ha
  have _ : ContinuousOn exp (spectrum 𝕜 a) := exp_continuous.continuousOn
  let +nondep : Algebra Rat A := .restrictScalars Rat 𝕜 A
  simp_rw [← map_exp _ h, cfc_apply exp a ha]
  congr 1
  ext
  simp [exp_continuousMap_eq]

中文:
引理 exp_eq_normedSpace_exp
  条件: {a : A} (ha : p a := by cfc_tac)
  证明: by
  conv_rhs => rw [← cfc_id 𝕜 a ha, cfc_apply id a ha]
  have h := cfcHom_continuous (R := 𝕜) ha
  have _ : ContinuousOn exp (spectrum 𝕜 a) := exp_continuous.continuousOn
  let +nondep : Algebra Rat A := .restrictScalars Rat 𝕜 A
  simp_rw [← map_exp _ h, cfc_apply exp a ha]
  congr 1
  ext
  simp [exp_continuousMap_eq]

Depends on / 依赖: Algebra, ContinuousOn, cfcHom_continuous, cfc_apply, cfc_id, cfc_tac, continuousOn, conv_rhs, exp_continuous, exp_continuous.continuousOn, exp_continuousMap_eq, map_exp, nondep, restrictScalars, simp_rw, spectrum
-/
lemma exp_eq_normedSpace_exp {a : A} (ha : p a := by cfc_tac) :
    cfc (exp : 𝕜 -> 𝕜) a = exp a := by
  conv_rhs => rw [← cfc_id 𝕜 a ha, cfc_apply id a ha]
  have h := cfcHom_continuous (R := 𝕜) ha
  have _ : ContinuousOn exp (spectrum 𝕜 a) := exp_continuous.continuousOn
  let +nondep : Algebra Rat A := .restrictScalars Rat 𝕜 A
  simp_rw [← map_exp _ h, cfc_apply exp a ha]
  congr 1
  ext
  simp [exp_continuousMap_eq]

end RCLikeNormed

section RealNormed

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra Real A]
  [ContinuousFunctionalCalculus Real A IsSelfAdjoint]

/--
lemma `real_exp_eq_normedSpace_exp` / 引理 `real_exp_eq_normedSpace_exp`

English:
lemma real_exp_eq_normedSpace_exp
  given: {a : A} (ha : IsSelfAdjoint a := by cfc_tac)
  proof: Real.exp_eq_exp_Real ▸ exp_eq_normedSpace_exp ha

@[aesop safe apply (rule_sets := [CStarAlgebra])]

中文:
引理 real_exp_eq_normedSpace_exp
  条件: {a : A} (ha : IsSelfAdjoint a := by cfc_tac)
  证明: Real.exp_eq_exp_Real ▸ exp_eq_normedSpace_exp ha

@[aesop safe apply (rule_sets := [CStarAlgebra])]

Depends on / 依赖: Real.exp, Real.exp_eq_exp_Real, cfc_tac, exp_eq_exp_Real, exp_eq_normedSpace_exp
-/
lemma real_exp_eq_normedSpace_exp {a : A} (ha : IsSelfAdjoint a := by cfc_tac) :
    cfc Real.exp a = exp a :=
  Real.exp_eq_exp_Real ▸ exp_eq_normedSpace_exp ha

@[aesop safe apply (rule_sets := [CStarAlgebra])]
/--
lemma `_root_.IsSelfAdjoint.exp_nonneg` / 引理 `_root_.IsSelfAdjoint.exp_nonneg`

English:
lemma _root_.IsSelfAdjoint.exp_nonneg
  proof: by
  rw [← real_exp_eq_normedSpace_exp]
  exact cfc_nonneg fun x _ => Real.exp_nonneg x

中文:
引理 _root_.IsSelfAdjoint.exp_nonneg
  证明: by
  rw [← real_exp_eq_normedSpace_exp]
  exact cfc_nonneg fun x _ => Real.exp_nonneg x

Depends on / 依赖: Real.exp_nonneg, cfc_nonneg, exp_nonneg, isCoseparator_coseparator, isRightAdjoint_of_preservesLimits_of_isCoseparating, real_exp_eq_normedSpace_exp
-/
lemma _root_.IsSelfAdjoint.exp_nonneg
    [PartialOrder A] [StarOrderedRing A] {a : A} (ha : IsSelfAdjoint a) :
    0 <= exp a := by
  rw [← real_exp_eq_normedSpace_exp]
  exact cfc_nonneg fun x _ => Real.exp_nonneg x

end RealNormed

section ComplexNormed

variable {A : Type*} {p : A -> Prop} [NormedRing A] [StarRing A]
  [NormedAlgebra Complex A] [ContinuousFunctionalCalculus Complex A p]

/--
lemma `complex_exp_eq_normedSpace_exp` / 引理 `complex_exp_eq_normedSpace_exp`

English:
lemma complex_exp_eq_normedSpace_exp
  given: {a : A} (ha : p a := by cfc_tac)
  proof: Complex.exp_eq_exp_Complex ▸ exp_eq_normedSpace_exp ha

中文:
引理 complex_exp_eq_normedSpace_exp
  条件: {a : A} (ha : p a := by cfc_tac)
  证明: Complex.exp_eq_exp_Complex ▸ exp_eq_normedSpace_exp ha

Depends on / 依赖: Complex.exp, Complex.exp_eq_exp_Complex, cfc_tac, exp_eq_exp_Complex, exp_eq_normedSpace_exp
-/
lemma complex_exp_eq_normedSpace_exp {a : A} (ha : p a := by cfc_tac) :
    cfc Complex.exp a = exp a :=
  Complex.exp_eq_exp_Complex ▸ exp_eq_normedSpace_exp ha

end ComplexNormed


section real_log

open scoped ComplexOrder

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra Real A]
  [ContinuousFunctionalCalculus Real A IsSelfAdjoint]

/--
Definition of `log` / `log` 的定义

English:
definition log
  signature: (a : A)
  body: cfc Real.log a

@[simp, grind =>]

中文:
定义 log
  签名: (a : A)
  定义体: cfc Real.log a

@[simp, grind =>]

Depends on / 依赖: Real.log
-/
noncomputable def log (a : A) : A := cfc Real.log a

@[simp, grind =>]
/--
lemma `_root_.IsSelfAdjoint.log` / 引理 `_root_.IsSelfAdjoint.log`

English:
lemma _root_.IsSelfAdjoint.log
  given: {a : A}
  statement: IsSelfAdjoint (log a)
  proof: cfc_predicate _ a

中文:
引理 _root_.IsSelfAdjoint.log
  条件: {a : A}
  结论: IsSelfAdjoint (log a)
  证明: cfc_predicate _ a

Depends on / 依赖: isLeftAdjoint, tensorObjPreadditiveCoyonedaObjAdjunction
-/
protected lemma _root_.IsSelfAdjoint.log {a : A} : IsSelfAdjoint (log a) := cfc_predicate _ a

/--
lemma `log_zero` / 引理 `log_zero`

English:
lemma log_zero
  statement: log (0 : A) = 0
  proof: by simp [log]

中文:
引理 log_zero
  结论: log (0 : A) = 0
  证明: by simp [log]
-/
@[simp, grind =] lemma log_zero : log (0 : A) = 0 := by simp [log]

/--
lemma `log_one` / 引理 `log_one`

English:
lemma log_one
  statement: log (1 : A) = 0
  proof: by simp [log]

@[simp, grind =]

中文:
引理 log_one
  结论: log (1 : A) = 0
  证明: by simp [log]

@[simp, grind =]
-/
@[simp, grind =] lemma log_one : log (1 : A) = 0 := by simp [log]

@[simp, grind =]
/--
lemma `log_algebraMap` / 引理 `log_algebraMap`

English:
lemma log_algebraMap
  given: {r : Real}
  statement: log (algebraMap Real A r) = algebraMap Real A (Real.log r)
  proof: by
  simp [log]

中文:
引理 log_algebraMap
  条件: {r : 实数}
  结论: log (algebraMap 实数 A r) = algebraMap 实数 A (实数.log r)
  证明: by
  simp [log]
-/
lemma log_algebraMap {r : Real} : log (algebraMap Real A r) = algebraMap Real A (Real.log r) := by
  simp [log]

/--
lemma `log_smul` / 引理 `log_smul`

English:
lemma log_smul
  statement: {r : Real} (a : A) (ha₂ : forall x in spectrum Real a, x != 0) (hr : r != 0)
  proof: by
  rw [log]; rw [← cfc_smul_id (R := Real) r a]; rw [← cfc_comp Real.log (r • ·) a]; rw [log]
  calc
    _ = cfc (fun z => Real.log r + Real.log z) a :=
      cfc_congr (Real.log_mul hr <| ha₂ · ·)
    _ = _ := by rw [cfc_const_add _ _ _]

@[grind =]

中文:
引理 log_smul
  结论: {r : 实数} (a : A) (ha₂ : 对任意 x in spectrum 实数 a, x != 0) (hr : r != 0)
  证明: by
  rw [log]; rw [← cfc_smul_id (R := Real) r a]; rw [← cfc_comp Real.log (r • ·) a]; rw [log]
  calc
    _ = cfc (fun z => Real.log r + Real.log z) a :=
      cfc_congr (Real.log_mul hr <| ha₂ · ·)
    _ = _ := by rw [cfc_const_add _ _ _]

@[grind =]

Depends on / 依赖: Real.log, Real.log_mul, algebraMap, cfc_comp, cfc_congr, cfc_const_add, cfc_smul_id, cfc_tac, log_mul
-/
lemma log_smul {r : Real} (a : A) (ha₂ : forall x in spectrum Real a, x != 0) (hr : r != 0)
    (ha₁ : IsSelfAdjoint a := by cfc_tac) :
    log (r • a) = algebraMap Real A (Real.log r) + log a := by
  rw [log]; rw [← cfc_smul_id (R := Real) r a]; rw [← cfc_comp Real.log (r • ·) a]; rw [log]
  calc
    _ = cfc (fun z => Real.log r + Real.log z) a :=
      cfc_congr (Real.log_mul hr <| ha₂ · ·)
    _ = _ := by rw [cfc_const_add _ _ _]

@[grind =]
/--
lemma `log_smul'` / 引理 `log_smul'`

English:
lemma log_smul'
  statement: [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass Real A] {r : Real} (a : A)
  proof: by
  grind [log_smul]

中文:
引理 log_smul'
  结论: [偏序 A] [StarOrdered环 A] [NonnegSpectrum类 实数 A] {r : 实数} (a : A)
  证明: by
  grind [log_smul]

Depends on / 依赖: Real.log, algebraMap, cfc_tac, log_smul
-/
lemma log_smul' [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass Real A] {r : Real} (a : A)
    (hr : 0 < r) (ha : IsStrictlyPositive a := by cfc_tac) :
    log (r • a) = algebraMap Real A (Real.log r) + log a := by
  grind [log_smul]

/--
lemma `log_pow` / 引理 `log_pow`

English:
lemma log_pow
  statement: (n : Nat) (a : A) (ha₂ : forall x in spectrum Real a, x != 0)
  proof: by
  have ha₂' : ContinuousOn Real.log (spectrum Real a) := by fun_prop
  have ha₂'' : ContinuousOn Real.log ((· ^ n) '' spectrum Real a) := by fun_prop (disch := aesop)
  rw [log]; rw [← cfc_pow_id (R := Real) a n ha₁]; rw [← cfc_comp' Real.log (· ^ n) a ha₂'']; rw [log]
  simp_rw [Real.log_pow, ← Nat.cast_smul_eq_nsmul Real n, cfc_const_mul (n : Real) Real.log a ha₂']

@[grind =]

中文:
引理 log_pow
  结论: (n : 自然数) (a : A) (ha₂ : 对任意 x in spectrum 实数 a, x != 0)
  证明: by
  have ha₂' : ContinuousOn Real.log (spectrum Real a) := by fun_prop
  have ha₂'' : ContinuousOn Real.log ((· ^ n) '' spectrum Real a) := by fun_prop (disch := aesop)
  rw [log]; rw [← cfc_pow_id (R := Real) a n ha₁]; rw [← cfc_comp' Real.log (· ^ n) a ha₂'']; rw [log]
  simp_rw [Real.log_pow, ← Nat.cast_smul_eq_nsmul Real n, cfc_const_mul (n : Real) Real.log a ha₂']

@[grind =]

Depends on / 依赖: ContinuousOn, Nat.cast_smul_eq_nsmul, Real.log, Real.log_pow, cast_smul_eq_nsmul, cfc_comp, cfc_const_mul, cfc_pow_id, cfc_tac, fun_prop, log_pow, simp_rw, spectrum
-/
lemma log_pow (n : Nat) (a : A) (ha₂ : forall x in spectrum Real a, x != 0)
    (ha₁ : IsSelfAdjoint a := by cfc_tac) : log (a ^ n) = n • log a := by
  have ha₂' : ContinuousOn Real.log (spectrum Real a) := by fun_prop
  have ha₂'' : ContinuousOn Real.log ((· ^ n) '' spectrum Real a) := by fun_prop (disch := aesop)
  rw [log]; rw [← cfc_pow_id (R := Real) a n ha₁]; rw [← cfc_comp' Real.log (· ^ n) a ha₂'']; rw [log]
  simp_rw [Real.log_pow, ← Nat.cast_smul_eq_nsmul Real n, cfc_const_mul (n : Real) Real.log a ha₂']

@[grind =]
/--
lemma `log_pow'` / 引理 `log_pow'`

English:
lemma log_pow'
  statement: [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass Real A] (n : Nat) (a : A)
  proof: by
  grind [log_pow]

中文:
引理 log_pow'
  结论: [偏序 A] [StarOrdered环 A] [NonnegSpectrum类 实数 A] (n : 自然数) (a : A)
  证明: by
  grind [log_pow]

Depends on / 依赖: cfc_tac, log_pow
-/
lemma log_pow' [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass Real A] (n : Nat) (a : A)
    (ha : IsStrictlyPositive a := by cfc_tac) :
    log (a ^ n) = n • log a := by
  grind [log_pow]

open NormedSpace in
@[grind =]
/--
lemma `log_exp` / 引理 `log_exp`

English:
lemma log_exp
  given: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  statement: log (exp a) = a
  proof: by
  have hcont : ContinuousOn Real.log (Real.exp '' spectrum Real a) := by fun_prop (disch := simp)
  rw [log]; rw [← real_exp_eq_normedSpace_exp]; rw [← cfc_comp' Real.log Real.exp a hcont]
  simp [cfc_id' (R := Real) a]

中文:
引理 log_exp
  条件: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  结论: log (exp a) = a
  证明: by
  have hcont : ContinuousOn Real.log (Real.exp '' spectrum Real a) := by fun_prop (disch := simp)
  rw [log]; rw [← real_exp_eq_normedSpace_exp]; rw [← cfc_comp' Real.log Real.exp a hcont]
  simp [cfc_id' (R := Real) a]

Depends on / 依赖: ContinuousOn, Real.exp, Real.log, cfc_comp, cfc_id, cfc_tac, fun_prop, real_exp_eq_normedSpace_exp, spectrum
-/
lemma log_exp (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : log (exp a) = a := by
  have hcont : ContinuousOn Real.log (Real.exp '' spectrum Real a) := by fun_prop (disch := simp)
  rw [log]; rw [← real_exp_eq_normedSpace_exp]; rw [← cfc_comp' Real.log Real.exp a hcont]
  simp [cfc_id' (R := Real) a]

open NormedSpace in
@[grind =]
/--
lemma `exp_log` / 引理 `exp_log`

English:
lemma exp_log
  statement: [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass Real A] (a : A)
  proof: by
  have ha₂ : forall x in spectrum Real a, x != 0 := by grind
  rw [← real_exp_eq_normedSpace_exp .log]; rw [log]; rw [← cfc_comp' Real.exp Real.log a (by fun_prop)]
  conv_rhs => rw [← cfc_id (R := Real) a]
  refine cfc_congr fun x hx => ?_
  grind [Real.exp_log]

中文:
引理 exp_log
  结论: [偏序 A] [StarOrdered环 A] [NonnegSpectrum类 实数 A] (a : A)
  证明: by
  have ha₂ : forall x in spectrum Real a, x != 0 := by grind
  rw [← real_exp_eq_normedSpace_exp .log]; rw [log]; rw [← cfc_comp' Real.exp Real.log a (by fun_prop)]
  conv_rhs => rw [← cfc_id (R := Real) a]
  refine cfc_congr fun x hx => ?_
  grind [Real.exp_log]

Depends on / 依赖: Real.exp, Real.exp_log, Real.log, cfc_comp, cfc_congr, cfc_id, cfc_tac, conv_rhs, exp_log, fun_prop, real_exp_eq_normedSpace_exp, spectrum
-/
lemma exp_log [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass Real A] (a : A)
    (ha : IsStrictlyPositive a := by cfc_tac) : exp (log a) = a := by
  have ha₂ : forall x in spectrum Real a, x != 0 := by grind
  rw [← real_exp_eq_normedSpace_exp .log]; rw [log]; rw [← cfc_comp' Real.exp Real.log a (by fun_prop)]
  conv_rhs => rw [← cfc_id (R := Real) a]
  refine cfc_congr fun x hx => ?_
  grind [Real.exp_log]

/--
lemma `continuousOn_log` / 引理 `continuousOn_log`

English:
lemma continuousOn_log
  statement: {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra Real A]
  proof: continuousOn_id.cfc_of_mem_nhdsSet _ (s := {0}ᶜ) by
    simpa using fun _ _ => spectrum.zero_notMem Real

中文:
引理 continuousOn_log
  结论: {A : 类型} [赋范环 A] [对合环 A] [赋范代数 实数 A]
  证明: continuousOn_id.cfc_of_mem_nhdsSet _ (s := {0}ᶜ) by
    simpa using fun _ _ => spectrum.zero_notMem Real

Depends on / 依赖: cfc_of_mem_nhdsSet, continuousOn_id, continuousOn_id.cfc_of_mem_nhdsSet, spectrum, spectrum.zero_notMem, zero_notMem
-/
lemma continuousOn_log {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra Real A]
    [IsometricContinuousFunctionalCalculus Real A IsSelfAdjoint] [ContinuousStar A] [CompleteSpace A] :
    ContinuousOn log {a : A | IsSelfAdjoint a ∧ IsUnit a} :=
continuousOn_id.cfc_of_mem_nhdsSet _ (s := {0}ᶜ) by
    simpa using fun _ _ => spectrum.zero_notMem Real

end real_log
end CFC
