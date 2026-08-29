/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
module

public import Mathlib.RingTheory.Derivation.MapCoeffs
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# Differential Fields

This file defines the logarithmic derivative `Differential.logDeriv` and proves properties of it.
This is defined algebraically, compared to `logDeriv` which is analytical.
-/

@[expose] public section

namespace Differential

open algebraMap Polynomial IntermediateField

variable {R : Type*} [Field R] [Differential R] (a b : R)

/--
Definition of `logDeriv` / `logDeriv` 的定义

English:
definition logDeriv
  signature: : R
  body: a′ / a

@[simp]

中文:
定义 logDeriv
  签名: : R
  定义体: a′ / a

@[simp]
-/
def logDeriv : R := a′ / a

@[simp]
/--
lemma `logDeriv_zero` / 引理 `logDeriv_zero`

English:
lemma logDeriv_zero
  statement: logDeriv (0 : R) = 0
  proof: by
  simp [logDeriv]

@[simp]

中文:
引理 logDeriv_zero
  结论: logDeriv (0 : R) = 0
  证明: by
  simp [logDeriv]

@[simp]

Depends on / 依赖: logDeriv
-/
lemma logDeriv_zero : logDeriv (0 : R) = 0 := by
  simp [logDeriv]

@[simp]
/--
lemma `logDeriv_one` / 引理 `logDeriv_one`

English:
lemma logDeriv_one
  statement: logDeriv (1 : R) = 0
  proof: by
  simp [logDeriv]

中文:
引理 logDeriv_one
  结论: logDeriv (1 : R) = 0
  证明: by
  simp [logDeriv]

Depends on / 依赖: logDeriv
-/
lemma logDeriv_one : logDeriv (1 : R) = 0 := by
  simp [logDeriv]

/--
lemma `logDeriv_mul` / 引理 `logDeriv_mul`

English:
lemma logDeriv_mul
  given: (ha : a != 0) (hb : b != 0)
  statement: logDeriv (a * b) = logDeriv a + logDeriv b
  proof: by
  unfold logDeriv
  simp [field]
  ring

中文:
引理 logDeriv_mul
  条件: (ha : a != 0) (hb : b != 0)
  结论: logDeriv (a * b) = logDeriv a + logDeriv b
  证明: by
  unfold logDeriv
  simp [field]
  ring

Depends on / 依赖: logDeriv
-/
lemma logDeriv_mul (ha : a != 0) (hb : b != 0) : logDeriv (a * b) = logDeriv a + logDeriv b := by
  unfold logDeriv
  simp [field]
  ring

/--
lemma `logDeriv_div` / 引理 `logDeriv_div`

English:
lemma logDeriv_div
  given: (ha : a != 0) (hb : b != 0)
  statement: logDeriv (a / b) = logDeriv a - logDeriv b
  proof: by
  unfold logDeriv
  simp [field, Derivation.leibniz_div]

@[simp]

中文:
引理 logDeriv_div
  条件: (ha : a != 0) (hb : b != 0)
  结论: logDeriv (a / b) = logDeriv a - logDeriv b
  证明: by
  unfold logDeriv
  simp [field, Derivation.leibniz_div]

@[simp]

Depends on / 依赖: Derivation, Derivation.leibniz_div, leibniz_div, logDeriv
-/
lemma logDeriv_div (ha : a != 0) (hb : b != 0) : logDeriv (a / b) = logDeriv a - logDeriv b := by
  unfold logDeriv
  simp [field, Derivation.leibniz_div]

@[simp]
/--
lemma `logDeriv_pow` / 引理 `logDeriv_pow`

English:
lemma logDeriv_pow
  given: (n : Nat) (a : R)
  statement: logDeriv (a ^ n) = n * logDeriv a
  proof: by
  induction n with
  | zero => simp
  | succ n h2 =>
    obtain rfl | hb := eq_or_ne a 0
    · simp
    · rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← h2, pow_succ, logDeriv_mul] <;>
      simp [hb]

中文:
引理 logDeriv_pow
  条件: (n : 自然数) (a : R)
  结论: logDeriv (a ^ n) = n * logDeriv a
  证明: by
  induction n with
  | zero => simp
  | succ n h2 =>
    obtain rfl | hb := eq_or_ne a 0
    · simp
    · rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← h2, pow_succ, logDeriv_mul] <;>
      simp [hb]

Depends on / 依赖: Nat.cast_add, Nat.cast_one, add_mul, cast_add, cast_one, eq_or_ne, logDeriv_mul, one_mul, pow_succ
-/
lemma logDeriv_pow (n : Nat) (a : R) : logDeriv (a ^ n) = n * logDeriv a := by
  induction n with
  | zero => simp
  | succ n h2 =>
    obtain rfl | hb := eq_or_ne a 0
    · simp
    · rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← h2, pow_succ, logDeriv_mul] <;>
      simp [hb]

/--
lemma `logDeriv_eq_zero` / 引理 `logDeriv_eq_zero`

English:
lemma logDeriv_eq_zero
  statement: logDeriv a = 0 ↔ a′ = 0
  proof: ⟨fun h => by simp only [logDeriv, _root_.div_eq_zero_iff] at h; rcases h with h|h <;> simp [h],
  fun h => by unfold logDeriv at *; simp [h]⟩

中文:
引理 logDeriv_eq_zero
  结论: logDeriv a = 0 ↔ a′ = 0
  证明: ⟨fun h => by simp only [logDeriv, _root_.div_eq_zero_iff] at h; rcases h with h|h <;> simp [h],
  fun h => by unfold logDeriv at *; simp [h]⟩

Depends on / 依赖: _root_, _root_.div_eq_zero_iff, div_eq_zero_iff, logDeriv
-/
lemma logDeriv_eq_zero : logDeriv a = 0 ↔ a′ = 0 :=
  ⟨fun h => by simp only [logDeriv, _root_.div_eq_zero_iff] at h; rcases h with h|h <;> simp [h],
  fun h => by unfold logDeriv at *; simp [h]⟩

/--
lemma `logDeriv_multisetProd` / 引理 `logDeriv_multisetProd`

English:
lemma logDeriv_multisetProd
  given: {ι : Type*} (s : Multiset ι) {f : ι -> R} (h : forall x in s, f x != 0)
  proof: by
  induction s using Multiset.induction_on
  · simp
  · rename_i h₂
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons]
    rw [← h₂]
    · apply logDeriv_mul
      · simp [h]
      · simp_all
    · simp_all

中文:
引理 logDeriv_multisetProd
  条件: {ι : 类型} (s : Multiset ι) {f : ι -> R} (h : 对任意 x in s, f x != 0)
  证明: by
  induction s using Multiset.induction_on
  · simp
  · rename_i h₂
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons]
    rw [← h₂]
    · apply logDeriv_mul
      · simp [h]
      · simp_all
    · simp_all

Depends on / 依赖: Multiset, Multiset.induction_on, Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, induction_on, logDeriv_mul, map_cons, prod_cons, rename_i, sum_cons
-/
lemma logDeriv_multisetProd {ι : Type*} (s : Multiset ι) {f : ι -> R} (h : forall x in s, f x != 0) :
    logDeriv (s.map f).prod = (s.map fun x => logDeriv (f x)).sum := by
  induction s using Multiset.induction_on
  · simp
  · rename_i h₂
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons]
    rw [← h₂]
    · apply logDeriv_mul
      · simp [h]
      · simp_all
    · simp_all

/--
lemma `logDeriv_prod` / 引理 `logDeriv_prod`

English:
lemma logDeriv_prod
  given: (ι : Type*) (s : Finset ι) (f : ι -> R) (h : forall x in s, f x != 0)
  proof: logDeriv_multisetProd _ h

中文:
引理 logDeriv_prod
  条件: (ι : 类型) (s : Finset ι) (f : ι -> R) (h : 对任意 x in s, f x != 0)
  证明: logDeriv_multisetProd _ h

Depends on / 依赖: logDeriv_multisetProd
-/
lemma logDeriv_prod (ι : Type*) (s : Finset ι) (f : ι -> R) (h : forall x in s, f x != 0) :
    logDeriv (∏ x in s, f x) = ∑ x in s, logDeriv (f x) := logDeriv_multisetProd _ h

/--
lemma `logDeriv_prod_of_eq_zero` / 引理 `logDeriv_prod_of_eq_zero`

English:
lemma logDeriv_prod_of_eq_zero
  given: (ι : Type*) (s : Finset ι) (f : ι -> R) (h : forall x in s, f x = 0)
  proof: by
  unfold logDeriv
  simp_all

中文:
引理 logDeriv_prod_of_eq_zero
  条件: (ι : 类型) (s : Finset ι) (f : ι -> R) (h : 对任意 x in s, f x = 0)
  证明: by
  unfold logDeriv
  simp_all

Depends on / 依赖: logDeriv
-/
lemma logDeriv_prod_of_eq_zero (ι : Type*) (s : Finset ι) (f : ι -> R) (h : forall x in s, f x = 0) :
    logDeriv (∏ x in s, f x) = ∑ x in s, logDeriv (f x) := by
  unfold logDeriv
  simp_all

/--
lemma `logDeriv_algebraMap` / 引理 `logDeriv_algebraMap`

English:
lemma logDeriv_algebraMap
  statement: {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
  proof: by
  unfold logDeriv
  simp [deriv_algebraMap]

@[norm_cast]

中文:
引理 logDeriv_algebraMap
  结论: {F K : 类型} [Field F] [Field K] [Differential F] [Differential K]
  证明: by
  unfold logDeriv
  simp [deriv_algebraMap]

@[norm_cast]

Depends on / 依赖: deriv_algebraMap, logDeriv
-/
lemma logDeriv_algebraMap {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K]
    (a : F) : logDeriv (algebraMap F K a) = algebraMap F K (logDeriv a) := by
  unfold logDeriv
  simp [deriv_algebraMap]

@[norm_cast]
/--
lemma `_root_.algebraMap.coe_logDeriv` / 引理 `_root_.algebraMap.coe_logDeriv`

English:
lemma _root_.algebraMap.coe_logDeriv
  statement: {F K : Type*} [Field F] [Field K] [Differential F]
  proof: (logDeriv_algebraMap a).symm

中文:
引理 _root_.algebraMap.coe_logDeriv
  结论: {F K : 类型} [Field F] [Field K] [Differential F]
  证明: (logDeriv_algebraMap a).symm

Depends on / 依赖: logDeriv_algebraMap
-/
lemma _root_.algebraMap.coe_logDeriv {F K : Type*} [Field F] [Field K] [Differential F]
    [Differential K] [Algebra F K] [DifferentialAlgebra F K]
    (a : F) : logDeriv a = logDeriv (a : K) := (logDeriv_algebraMap a).symm

variable {F : Type*} [Field F] [Differential F] [CharZero F]

set_option backward.isDefEq.respectTransparency false in
noncomputable instance (p : F[X]) [Fact (Irreducible p)] [Fact p.Monic] :
    Differential (AdjoinRoot p) where
  deriv := Derivation.liftOfSurjective (f := (AdjoinRoot.mk p).toIntAlgHom) AdjoinRoot.mk_surjective
    (d := implicitDeriv <| AdjoinRoot.modByMonicHom Fact.out <|
      - (aeval (AdjoinRoot.root p) (mapCoeffs p)) / (aeval (AdjoinRoot.root p) (derivative p))) (by
      rintro x hx
      simp_all only [RingHom.toIntAlgHom_apply, AdjoinRoot.mk_eq_zero]
      obtain ⟨q, rfl⟩ := hx
      simp only [Derivation.leibniz, smul_eq_mul]
      apply dvd_add (dvd_mul_right ..)
      apply dvd_mul_of_dvd_right
      rw [← AdjoinRoot.mk_eq_zero]
      unfold implicitDeriv
      simp only [AdjoinRoot.aeval_eq, Derivation.coe_add, Derivation.coe_smul, Pi.add_apply,
        Pi.smul_apply, Derivation.restrictScalars_apply, derivative'_apply, smul_eq_mul, map_add,
        map_mul, AdjoinRoot.mk_leftInverse Fact.out _]
      rw [div_mul_cancel₀]; rw [add_neg_cancel]
      simp only [ne_eq, AdjoinRoot.mk_eq_zero]
      have : 0 < p.natDegree := Irreducible.natDegree_pos (Fact.out)
      apply not_dvd_of_natDegree_lt
      · intro nh
        simp_all
      apply natDegree_derivative_lt
      exact Nat.ne_zero_of_lt this)

set_option backward.isDefEq.respectTransparency false in
instance (p : F[X]) [Fact (Irreducible p)] [Fact p.Monic] :
    DifferentialAlgebra F (AdjoinRoot p) where
  deriv_algebraMap a := by
    change (Derivation.liftOfSurjective _ _) ((AdjoinRoot.mk p).toIntAlgHom (C a)) = _
    rw [Derivation.liftOfSurjective_apply]; rw [implicitDeriv_C]
    rfl

variable {K : Type*} [Field K] [Algebra F K]

variable (F K) in
/--
If `K` is a finite field extension of `F` then we can define a differential algebra on `K`, by
choosing a primitive element of `K`, `k` and then using the equivalence to `AdjoinRoot (minpoly k)`.
-/
@[reducible]
/--
Definition of `differentialFiniteDimensional` / `differentialFiniteDimensional` 的定义

English:
definition differentialFiniteDimensional
  signature: [FiniteDimensional F K]
  body: let k := (Field.exists_primitive_element F K).choose
  have h : F⟮k⟯ = ⊤ := (Field.exists_primitive_element F K).choose_spec
  have : Fact (minpoly F k).Monic := ⟨minpoly.monic (IsAlgebraic.of_finite ..).isIntegral⟩
  have : Fact (Irreducible (minpoly F k)) :=
    ⟨minpoly.irreducible (IsAlgebraic.o

中文:
定义 differentialFiniteDimensional
  签名: [FiniteDimensional F K]
  定义体: let k := (Field.exists_primitive_element F K).choose
  have h : F⟮k⟯ = ⊤ := (Field.exists_primitive_element F K).choose_spec
  have : Fact (minpoly F k).Monic := ⟨minpoly.monic (IsAlgebraic.of_finite ..).isIntegral⟩
  have : Fact (Irreducible (minpoly F k)) :=
    ⟨minpoly.irreducible (IsAlgebraic.o

Depends on / 依赖: Differential, Differential.equiv, Field.exists_primitive_element, IntermediateField, IntermediateField.adjoinRootEquivAdjoin, IntermediateField.equivOfEq, IntermediateField.topEquiv, Irreducible, IsAlgebraic, IsAlgebraic.of_finite, adjoinRootEquivAdjoin, choose_spec, equivOfEq, exists_primitive_element, irreducible, isIntegral, minpoly, minpoly.irreducible, minpoly.monic, of_finite
-/
noncomputable def differentialFiniteDimensional [FiniteDimensional F K] : Differential K :=
  let k := (Field.exists_primitive_element F K).choose
  have h : F⟮k⟯ = ⊤ := (Field.exists_primitive_element F K).choose_spec
  have : Fact (minpoly F k).Monic := ⟨minpoly.monic (IsAlgebraic.of_finite ..).isIntegral⟩
  have : Fact (Irreducible (minpoly F k)) :=
    ⟨minpoly.irreducible (IsAlgebraic.of_finite ..).isIntegral⟩
  Differential.equiv (IntermediateField.adjoinRootEquivAdjoin F
.trans .trans (IntermediateField.equivOfEq h) (IsAlgebraic.of_finite F k).isIntegral
    IntermediateField.topEquiv).symm.toRingEquiv

/--
lemma `differentialAlgebraFiniteDimensional` / 引理 `differentialAlgebraFiniteDimensional`

English:
lemma differentialAlgebraFiniteDimensional
  given: [FiniteDimensional F K]
  proof: differentialFiniteDimensional F K
    DifferentialAlgebra F K := by
  let k := (Field.exists_primitive_element F K).choose
  have h : F⟮k⟯ = ⊤ := (Field.exists_primitive_element F K).choose_spec
  have : Fact (minpoly F k).Monic := ⟨minpoly.monic (IsAlgebraic.of_finite ..).isIntegral⟩
  have : Fact 

中文:
引理 differentialAlgebraFiniteDimensional
  条件: [FiniteDimensional F K]
  证明: differentialFiniteDimensional F K
    DifferentialAlgebra F K := by
  let k := (Field.exists_primitive_element F K).choose
  have h : F⟮k⟯ = ⊤ := (Field.exists_primitive_element F K).choose_spec
  have : Fact (minpoly F k).Monic := ⟨minpoly.monic (IsAlgebraic.of_finite ..).isIntegral⟩
  have : Fact 

Depends on / 依赖: differentialFiniteDimensional
-/
lemma differentialAlgebraFiniteDimensional [FiniteDimensional F K] :
    letI := differentialFiniteDimensional F K
    DifferentialAlgebra F K := by
  let k := (Field.exists_primitive_element F K).choose
  have h : F⟮k⟯ = ⊤ := (Field.exists_primitive_element F K).choose_spec
  have : Fact (minpoly F k).Monic := ⟨minpoly.monic (IsAlgebraic.of_finite ..).isIntegral⟩
  have : Fact (Irreducible (minpoly F k)) :=
    ⟨minpoly.irreducible (IsAlgebraic.of_finite ..).isIntegral⟩
  apply DifferentialAlgebra.equiv

/--
A finite extension of a differential field has a unique derivation which agrees with the one on the
base field.
-/
@[instance_reducible]
/--
Definition of `uniqueDifferentialAlgebraFiniteDimensional` / `uniqueDifferentialAlgebraFiniteDimensional` 的定义

English:
definition uniqueDifferentialAlgebraFiniteDimensional
  signature: [FiniteDimensional F K]
  body: by
  let default : {_a : Differential K // DifferentialAlgebra F K} :=
      ⟨differentialFiniteDimensional F K, differentialAlgebraFiniteDimensional⟩
  refine ⟨⟨default⟩, fun ⟨a, ha⟩ => ?_⟩
  ext x
  apply_fun (aeval x (mapCoeffs (minpoly F x)) + aeval x (derivative (minpoly F x)) * ·)
  · conv_lhs

中文:
定义 uniqueDifferentialAlgebraFiniteDimensional
  签名: [FiniteDimensional F K]
  定义体: by
  let default : {_a : Differential K // DifferentialAlgebra F K} :=
      ⟨differentialFiniteDimensional F K, differentialAlgebraFiniteDimensional⟩
  refine ⟨⟨default⟩, fun ⟨a, ha⟩ => ?_⟩
  ext x
  apply_fun (aeval x (mapCoeffs (minpoly F x)) + aeval x (derivative (minpoly F x)) * ·)
  · conv_lhs

Depends on / 依赖: Differential, DifferentialAlgebra, add_right_injective, apply_fun, conv_lhs, conv_rhs, deriv_aeval_eq, derivative, differentialAlgebraFiniteDimensional, differentialFiniteDimensional, dvd_iff, mapCoeffs, minpoly, minpoly.dvd_iff, ne_eq
-/
noncomputable def uniqueDifferentialAlgebraFiniteDimensional [FiniteDimensional F K] :
    Unique {_a : Differential K // DifferentialAlgebra F K} := by
  let default : {_a : Differential K // DifferentialAlgebra F K} :=
      ⟨differentialFiniteDimensional F K, differentialAlgebraFiniteDimensional⟩
  refine ⟨⟨default⟩, fun ⟨a, ha⟩ => ?_⟩
  ext x
  apply_fun (aeval x (mapCoeffs (minpoly F x)) + aeval x (derivative (minpoly F x)) * ·)
  · conv_lhs => apply (deriv_aeval_eq ..).symm
    conv_rhs => apply (@deriv_aeval_eq _ _ _ _ _ default.1 _ default.2 _ _).symm
    simp
  · apply (add_right_injective _).comp
    apply mul_right_injective₀
    rw [ne_eq]; rw [← minpoly.dvd_iff]
    have : 0 < (minpoly F x).natDegree := Irreducible.natDegree_pos
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral _))
    apply not_dvd_of_natDegree_lt
    · intro nh
      simp_all
    apply natDegree_derivative_lt
    exact Nat.ne_zero_of_lt this

noncomputable instance (B : IntermediateField F K) [FiniteDimensional F B] : Differential B :=
  differentialFiniteDimensional F B

instance (B : IntermediateField F K) [FiniteDimensional F B] :
    DifferentialAlgebra F B := differentialAlgebraFiniteDimensional

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Differential
  signature: K] [DifferentialAlgebra F K] (B
  body: by
    change (B.val a)′ = B.val a′
    rw [algHom_deriv']
    exact Subtype.val_injective

中文:
实例 [Differential
  签名: K] [DifferentialAlgebra F K] (B
  定义体: by
    change (B.val a)′ = B.val a′
    rw [algHom_deriv']
    exact Subtype.val_injective

Depends on / 依赖: B.val, Subtype, Subtype.val_injective, algHom_deriv, val_injective
-/
instance [Differential K] [DifferentialAlgebra F K] (B : IntermediateField F K)
    [FiniteDimensional F B] : DifferentialAlgebra B K where
  deriv_algebraMap a := by
    change (B.val a)′ = B.val a′
    rw [algHom_deriv']
    exact Subtype.val_injective

end Differential
