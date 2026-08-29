/-
Copyright (c) 2025 Michal Staromiejski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Staromiejski
-/
module

public import Mathlib.RingTheory.Trace.Basic

/-!

# Normalized trace

This file defines the *normalized trace* map; that is, an `F`-linear map from the algebraic closure
of `F` to `F` defined as the trace of an element from its adjoin extension divided by its degree.

To avoid heavy imports, we define it here as a map from an arbitrary algebraic (equivalently
integral) extension of `F`.

## Main definitions

- `normalizedTrace`: the trace of an element from the simple adjoin divided by the degree;
  it is a non-trivial `F`-linear map from an arbitrary algebraic extension `K` to `F`.

## Main results

- `normalizedTrace_intermediateField`: for a tower `K / E / F` of algebraic extensions,
  `normalizedTrace F E` agrees with `normalizedTrace F K` on `E`.
- `normalizedTrace_trans`: for a tower `K / E / F` of algebraic extensions, the normalized trace
  from `K` to `E` composed with the normalized trace from `E` to `F` equals the normalized trace
  from `K` to `F`.
- `normalizedTrace_self`: `normalizedTrace F F` is the identity map.

-/

@[expose] public section

namespace Algebra

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

open IntermediateField

set_option backward.privateInPublic true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def normalizedTraceAux (a : K)
  body: (Module.finrank F F⟮a⟯ : F)⁻¹ • trace F F⟮a⟯ (AdjoinSimple.gen F a)

中文:
定义 noncomputable
  签名: def normalizedTraceAux (a : K)
  定义体: (Module.finrank F F⟮a⟯ : F)⁻¹ • trace F F⟮a⟯ (AdjoinSimple.gen F a)
-/
private noncomputable def normalizedTraceAux (a : K) : F :=
  (Module.finrank F F⟮a⟯ : F)⁻¹ • trace F F⟮a⟯ (AdjoinSimple.gen F a)

/--
theorem `normalizedTraceAux_def` / 定理 `normalizedTraceAux_def`

English:
theorem normalizedTraceAux_def
  given: (a : K)
  statement: normalizedTraceAux F K a =
  proof: rfl

中文:
定理 normalizedTraceAux_def
  条件: (a : K)
  结论: normalizedTraceAux F K a =
  证明: rfl
-/
private theorem normalizedTraceAux_def (a : K) : normalizedTraceAux F K a =
    (Module.finrank F F⟮a⟯ : F)⁻¹ • trace F F⟮a⟯ (AdjoinSimple.gen F a) := rfl

/--
theorem `normalizedTraceAux_map` / 定理 `normalizedTraceAux_map`

English:
theorem normalizedTraceAux_map
  given: {E : Type*} [Field E] [Algebra F E] (f : E ->ₐ[F] K) (a : E)
  proof: by
  let e := (F⟮a⟯.equivMap f).trans (equivOfEq <| Set.image_singleton ▸ adjoin_map F {a} f)
  simp_rw [normalizedTraceAux, ← LinearEquiv.finrank_eq e.toLinearEquiv]
  congr
exact trace_eq_of_algEquiv e AdjoinSimple.gen F a

中文:
定理 normalizedTraceAux_map
  条件: {E : 类型} [Field E] [Algebra F E] (f : E ->ₐ[F] K) (a : E)
  证明: by
  let e := (F⟮a⟯.equivMap f).trans (equivOfEq <| Set.image_singleton ▸ adjoin_map F {a} f)
  simp_rw [normalizedTraceAux, ← LinearEquiv.finrank_eq e.toLinearEquiv]
  congr
exact trace_eq_of_algEquiv e AdjoinSimple.gen F a
-/
private theorem normalizedTraceAux_map {E : Type*} [Field E] [Algebra F E] (f : E ->ₐ[F] K) (a : E) :
    normalizedTraceAux F K (f a) = normalizedTraceAux F E a := by
  let e := (F⟮a⟯.equivMap f).trans (equivOfEq <| Set.image_singleton ▸ adjoin_map F {a} f)
  simp_rw [normalizedTraceAux, ← LinearEquiv.finrank_eq e.toLinearEquiv]
  congr
exact trace_eq_of_algEquiv e AdjoinSimple.gen F a

/--
theorem `normalizedTraceAux_intermediateField` / 定理 `normalizedTraceAux_intermediateField`

English:
theorem normalizedTraceAux_intermediateField
  given: {E : IntermediateField F K} (a : E)
  proof: normalizedTraceAux_map F K E.val a

中文:
定理 normalizedTraceAux_intermediateField
  条件: {E : 整数ermediateField F K} (a : E)
  证明: normalizedTraceAux_map F K E.val a
-/
private theorem normalizedTraceAux_intermediateField {E : IntermediateField F K} (a : E) :
    normalizedTraceAux F K a = normalizedTraceAux F E a :=
  normalizedTraceAux_map F K E.val a

variable [CharZero F]

variable {K} in
/--
theorem `normalizedTraceAux_eq_of_finiteDimensional` / 定理 `normalizedTraceAux_eq_of_finiteDimensional`

English:
theorem normalizedTraceAux_eq_of_finiteDimensional
  given: [FiniteDimensional F K] (a : K)
  proof: by
have h := (Nat.cast_ne_zero (R := F)).mpr
Nat.pos_iff_ne_zero.mp Module.finrank_pos (R := F⟮a⟯) (M := K)
  rw [smul_eq_mul]; rw [mul_comm]; rw [← div_eq_mul_inv]; rw [trace_eq_trace_adjoin F a]; rw [← Module.finrank_mul_finrank F F⟮a⟯ K]; rw [nsmul_eq_mul]; rw [Nat.cast_mul]; rw [mul_comm]; rw [m

中文:
定理 normalizedTraceAux_eq_of_finiteDimensional
  条件: [FiniteDimensional F K] (a : K)
  证明: by
have h := (Nat.cast_ne_zero (R := F)).mpr
Nat.pos_iff_ne_zero.mp Module.finrank_pos (R := F⟮a⟯) (M := K)
  rw [smul_eq_mul]; rw [mul_comm]; rw [← div_eq_mul_inv]; rw [trace_eq_trace_adjoin F a]; rw [← Module.finrank_mul_finrank F F⟮a⟯ K]; rw [nsmul_eq_mul]; rw [Nat.cast_mul]; rw [mul_comm]; rw [m
-/
private theorem normalizedTraceAux_eq_of_finiteDimensional [FiniteDimensional F K] (a : K) :
    normalizedTraceAux F K a = (Module.finrank F K : F)⁻¹ • trace F K a := by
have h := (Nat.cast_ne_zero (R := F)).mpr
Nat.pos_iff_ne_zero.mp Module.finrank_pos (R := F⟮a⟯) (M := K)
  rw [smul_eq_mul]; rw [mul_comm]; rw [← div_eq_mul_inv]; rw [trace_eq_trace_adjoin F a]; rw [← Module.finrank_mul_finrank F F⟮a⟯ K]; rw [nsmul_eq_mul]; rw [Nat.cast_mul]; rw [mul_comm]; rw [mul_div_mul_right _ _ h]; rw [div_eq_mul_inv]; rw [mul_comm]; rw [← smul_eq_mul]; rw [normalizedTraceAux_def]

variable [Algebra.IsIntegral F K]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `normalizedTrace` / `normalizedTrace` 的定义

English:
definition normalizedTrace
  signature: : K ->ₗ[F] F where
  body: normalizedTraceAux F K
  map_add' a b := by
    let E := F⟮a⟯ ⊔ F⟮b⟯
    have : FiniteDimensional F F⟮a⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral a)
    have : FiniteDimensional F F⟮b⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral b)
have ha : a in E := (le_sup_left : F⟮a⟯ <= E) mem_a

中文:
定义 normalizedTrace
  签名: : K ->ₗ[F] F where
  定义体: normalizedTraceAux F K
  map_add' a b := by
    let E := F⟮a⟯ ⊔ F⟮b⟯
    have : FiniteDimensional F F⟮a⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral a)
    have : FiniteDimensional F F⟮b⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral b)
have ha : a in E := (le_sup_left : F⟮a⟯ <= E) mem_a

Depends on / 依赖: normalizedTraceAux
-/
noncomputable def normalizedTrace : K ->ₗ[F] F where
  toFun := normalizedTraceAux F K
  map_add' a b := by
    let E := F⟮a⟯ ⊔ F⟮b⟯
    have : FiniteDimensional F F⟮a⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral a)
    have : FiniteDimensional F F⟮b⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral b)
have ha : a in E := (le_sup_left : F⟮a⟯ <= E) mem_adjoin_simple_self F a
have hb : b in E := (le_sup_right : F⟮b⟯ <= E) mem_adjoin_simple_self F b
    have hab : a + b in E := IntermediateField.add_mem E ha hb
    let a' : E := ⟨a, ha⟩
    let b' : E := ⟨b, hb⟩
    let ab' : E := ⟨a + b, hab⟩
    rw [normalizedTraceAux_intermediateField F K a']; rw [normalizedTraceAux_intermediateField F K b']; rw [normalizedTraceAux_intermediateField F K ab']; rw [normalizedTraceAux_eq_of_finiteDimensional F a']; rw [normalizedTraceAux_eq_of_finiteDimensional F b']; rw [normalizedTraceAux_eq_of_finiteDimensional F ab']; rw [← smul_add]; rw [← map_add]; rw [AddMemClass.mk_add_mk]
  map_smul' m a := by
    dsimp only [AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply]
    let E := F⟮a⟯
    have : FiniteDimensional F F⟮a⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral a)
    have ha : a in E := mem_adjoin_simple_self F a
    have hma : m • a in E := smul_mem E ha
    let a' : E := ⟨a, ha⟩
    let ma' : E := ⟨m • a, hma⟩
    rw [normalizedTraceAux_intermediateField F K a']; rw [normalizedTraceAux_intermediateField F K ma']; rw [normalizedTraceAux_eq_of_finiteDimensional F a']; rw [normalizedTraceAux_eq_of_finiteDimensional F ma']; rw [smul_comm]; rw [← map_smul _ m]; rw [SetLike.mk_smul_mk]

/--
theorem `normalizedTrace_def` / 定理 `normalizedTrace_def`

English:
theorem normalizedTrace_def
  given: (a : K)
  statement: normalizedTrace F K a =
  proof: rfl

中文:
定理 normalizedTrace_def
  条件: (a : K)
  结论: normalizedTrace F K a =
  证明: rfl

Depends on / 依赖: RingHom, RingHom.id
-/
theorem normalizedTrace_def (a : K) : normalizedTrace F K a =
    (Module.finrank F F⟮a⟯ : F)⁻¹ • trace F F⟮a⟯ (AdjoinSimple.gen F a) :=
  rfl

variable {K} in
/--
theorem `normalizedTrace_minpoly` / 定理 `normalizedTrace_minpoly`

English:
theorem normalizedTrace_minpoly
  given: (a : K)
  proof: have ha : IsIntegral F a := IsIntegral.isIntegral a
  IntermediateField.adjoin.finrank ha ▸ trace_adjoinSimpleGen ha ▸ normalizedTrace_def F K a

中文:
定理 normalizedTrace_minpoly
  条件: (a : K)
  证明: have ha : IsIntegral F a := IsIntegral.isIntegral a
  IntermediateField.adjoin.finrank ha ▸ trace_adjoinSimpleGen ha ▸ normalizedTrace_def F K a

Depends on / 依赖: IntermediateField, IntermediateField.adjoin.finrank, IsIntegral, IsIntegral.isIntegral, adjoin, finrank, isIntegral, normalizedTrace_def, trace_adjoinSimpleGen
-/
theorem normalizedTrace_minpoly (a : K) :
    normalizedTrace F K a = ((minpoly F a).natDegree : F)⁻¹ • -(minpoly F a).nextCoeff :=
  have ha : IsIntegral F a := IsIntegral.isIntegral a
  IntermediateField.adjoin.finrank ha ▸ trace_adjoinSimpleGen ha ▸ normalizedTrace_def F K a

variable {F} in
/--
theorem `normalizedTrace_self_apply` / 定理 `normalizedTrace_self_apply`

English:
theorem normalizedTrace_self_apply
  given: (a : F)
  statement: normalizedTrace F F a = a
  proof: by
  dsimp [normalizedTrace]
  rw [normalizedTraceAux_eq_of_finiteDimensional F a]; rw [Module.finrank_self F]; rw [Nat.cast_one]; rw [inv_one]; rw [one_smul]; rw [trace_self_apply]

@[simp]

中文:
定理 normalizedTrace_self_apply
  条件: (a : F)
  结论: normalizedTrace F F a = a
  证明: by
  dsimp [normalizedTrace]
  rw [normalizedTraceAux_eq_of_finiteDimensional F a]; rw [Module.finrank_self F]; rw [Nat.cast_one]; rw [inv_one]; rw [one_smul]; rw [trace_self_apply]

@[simp]

Depends on / 依赖: Module, Module.finrank_self, Nat.cast_one, cast_one, finrank_self, inv_one, normalizedTrace, normalizedTraceAux_eq_of_finiteDimensional, one_smul, trace_self_apply
-/
theorem normalizedTrace_self_apply (a : F) : normalizedTrace F F a = a := by
  dsimp [normalizedTrace]
  rw [normalizedTraceAux_eq_of_finiteDimensional F a]; rw [Module.finrank_self F]; rw [Nat.cast_one]; rw [inv_one]; rw [one_smul]; rw [trace_self_apply]

@[simp]
/--
theorem `normalizedTrace_self` / 定理 `normalizedTrace_self`

English:
theorem normalizedTrace_self
  statement: normalizedTrace F F = LinearMap.id
  proof: LinearMap.ext normalizedTrace_self_apply

中文:
定理 normalizedTrace_self
  结论: normalizedTrace F F = LinearMap.id
  证明: LinearMap.ext normalizedTrace_self_apply

Depends on / 依赖: LinearMap, LinearMap.ext, normalizedTrace_self_apply
-/
theorem normalizedTrace_self : normalizedTrace F F = LinearMap.id :=
  LinearMap.ext normalizedTrace_self_apply

variable {K} in
/--
theorem `normalizedTrace_eq_of_finiteDimensional_apply` / 定理 `normalizedTrace_eq_of_finiteDimensional_apply`

English:
theorem normalizedTrace_eq_of_finiteDimensional_apply
  given: [FiniteDimensional F K] (a : K)
  proof: normalizedTraceAux_eq_of_finiteDimensional F a

中文:
定理 normalizedTrace_eq_of_finiteDimensional_apply
  条件: [FiniteDimensional F K] (a : K)
  证明: normalizedTraceAux_eq_of_finiteDimensional F a

Depends on / 依赖: normalizedTraceAux_eq_of_finiteDimensional
-/
theorem normalizedTrace_eq_of_finiteDimensional_apply [FiniteDimensional F K] (a : K) :
    normalizedTrace F K a = (Module.finrank F K : F)⁻¹ • trace F K a :=
  normalizedTraceAux_eq_of_finiteDimensional F a

/--
theorem `normalizedTrace_eq_of_finiteDimensional` / 定理 `normalizedTrace_eq_of_finiteDimensional`

English:
theorem normalizedTrace_eq_of_finiteDimensional
  given: [FiniteDimensional F K]
  proof: LinearMap.ext normalizedTrace_eq_of_finiteDimensional_apply F

中文:
定理 normalizedTrace_eq_of_finiteDimensional
  条件: [FiniteDimensional F K]
  证明: LinearMap.ext normalizedTrace_eq_of_finiteDimensional_apply F

Depends on / 依赖: LinearMap, LinearMap.ext, normalizedTrace_eq_of_finiteDimensional_apply
-/
theorem normalizedTrace_eq_of_finiteDimensional [FiniteDimensional F K] :
    normalizedTrace F K = (Module.finrank F K : F)⁻¹ • trace F K :=
LinearMap.ext normalizedTrace_eq_of_finiteDimensional_apply F

/-- The normalized trace transfers via (injective) maps. -/
@[simp]
/--
theorem `normalizedTrace_map` / 定理 `normalizedTrace_map`

English:
theorem normalizedTrace_map
  statement: {E : Type*} [Field E] [Algebra F E] [Algebra.IsIntegral F E]
  proof: normalizedTraceAux_map F K f a

中文:
定理 normalizedTrace_map
  结论: {E : 类型} [Field E] [Algebra F E] [Algebra.Is整数egral F E]
  证明: normalizedTraceAux_map F K f a

Depends on / 依赖: normalizedTraceAux_map
-/
theorem normalizedTrace_map {E : Type*} [Field E] [Algebra F E] [Algebra.IsIntegral F E]
    (f : E ->ₐ[F] K) (a : E) : normalizedTrace F K (f a) = normalizedTrace F E a :=
  normalizedTraceAux_map F K f a

/--
theorem `normalizedTrace_intermediateField` / 定理 `normalizedTrace_intermediateField`

English:
theorem normalizedTrace_intermediateField
  given: {E : IntermediateField F K} (a : E)
  proof: normalizedTraceAux_intermediateField F K a

中文:
定理 normalizedTrace_intermediateField
  条件: {E : 整数ermediateField F K} (a : E)
  证明: normalizedTraceAux_intermediateField F K a

Depends on / 依赖: normalizedTraceAux_intermediateField
-/
theorem normalizedTrace_intermediateField {E : IntermediateField F K} (a : E) :
    normalizedTrace F K a = normalizedTrace F E a :=
  normalizedTraceAux_intermediateField F K a

section IsScalarTower

variable (F E K : Type*) [Field F] [Field E] [Field K]
variable [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
variable [Algebra.IsIntegral F E] [Algebra.IsIntegral F K]
variable [CharZero F]

@[simp]
/--
theorem `normalizedTrace_algebraMap_apply` / 定理 `normalizedTrace_algebraMap_apply`

English:
theorem normalizedTrace_algebraMap_apply
  given: (a : E)
  proof: normalizedTrace_map F K (IsScalarTower.toAlgHom F E K) a

@[simp]

中文:
定理 normalizedTrace_algebraMap_apply
  条件: (a : E)
  证明: normalizedTrace_map F K (IsScalarTower.toAlgHom F E K) a

@[simp]

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, normalizedTrace_map, toAlgHom
-/
theorem normalizedTrace_algebraMap_apply (a : E) :
    normalizedTrace F K (algebraMap E K a) = normalizedTrace F E a :=
  normalizedTrace_map F K (IsScalarTower.toAlgHom F E K) a

@[simp]
/--
theorem `normalizedTrace_algebraMap` / 定理 `normalizedTrace_algebraMap`

English:
theorem normalizedTrace_algebraMap
  proof: LinearMap.ext normalizedTrace_algebraMap_apply F E K

omit [Algebra.IsIntegral F E] in

中文:
定理 normalizedTrace_algebraMap
  证明: LinearMap.ext normalizedTrace_algebraMap_apply F E K

omit [Algebra.IsIntegral F E] in

Depends on / 依赖: LinearMap, LinearMap.ext, normalizedTrace_algebraMap_apply
-/
theorem normalizedTrace_algebraMap :
    normalizedTrace F K ∘ₗ Algebra.linearMap E K = normalizedTrace F E :=
LinearMap.ext normalizedTrace_algebraMap_apply F E K

omit [Algebra.IsIntegral F E] in
/--
theorem `normalizedTrace_algebraMap_of_lifts` / 定理 `normalizedTrace_algebraMap_of_lifts`

English:
theorem normalizedTrace_algebraMap_of_lifts
  statement: [CharZero E] [Algebra.IsIntegral E K] (a : K)
  proof: by
  have ha : IsIntegral F a := IsIntegral.isIntegral a
  simp [normalizedTrace_minpoly F a, normalizedTrace_minpoly E a, ← minpoly.map_algebraMap ha h,
    (minpoly F a).nextCoeff_map_eq, map_mul, map_neg]

中文:
定理 normalizedTrace_algebraMap_of_lifts
  结论: [CharZero E] [Algebra.Is整数egral E K] (a : K)
  证明: by
  have ha : IsIntegral F a := IsIntegral.isIntegral a
  simp [normalizedTrace_minpoly F a, normalizedTrace_minpoly E a, ← minpoly.map_algebraMap ha h,
    (minpoly F a).nextCoeff_map_eq, map_mul, map_neg]

Depends on / 依赖: IsIntegral, IsIntegral.isIntegral, isIntegral, map_algebraMap, map_mul, map_neg, minpoly, minpoly.map_algebraMap, nextCoeff_map_eq, normalizedTrace_minpoly
-/
theorem normalizedTrace_algebraMap_of_lifts [CharZero E] [Algebra.IsIntegral E K] (a : K)
    (h : minpoly E a in Polynomial.lifts (algebraMap F E)) :
    algebraMap F E (normalizedTrace F K a) = normalizedTrace E K a := by
  have ha : IsIntegral F a := IsIntegral.isIntegral a
  simp [normalizedTrace_minpoly F a, normalizedTrace_minpoly E a, ← minpoly.map_algebraMap ha h,
    (minpoly F a).nextCoeff_map_eq, map_mul, map_neg]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `normalizedTrace_trans_apply_aux` / 定理 `normalizedTrace_trans_apply_aux`

English:
theorem normalizedTrace_trans_apply_aux
  statement: [FiniteDimensional F E] [Algebra.IsIntegral E K]
  proof: by
  have : FiniteDimensional E E⟮a⟯ :=
    IntermediateField.adjoin.finiteDimensional (IsIntegral.isIntegral a)
  rw [normalizedTrace_def E K]; rw [inv_natCast_smul_eq (R := E) (S := F)]; rw [map_smul]; rw [normalizedTrace_eq_of_finiteDimensional F E]; rw [LinearMap.smul_apply]; rw [← smul_assoc]; 

中文:
定理 normalizedTrace_trans_apply_aux
  结论: [FiniteDimensional F E] [Algebra.Is整数egral E K]
  证明: by
  have : FiniteDimensional E E⟮a⟯ :=
    IntermediateField.adjoin.finiteDimensional (IsIntegral.isIntegral a)
  rw [normalizedTrace_def E K]; rw [inv_natCast_smul_eq (R := E) (S := F)]; rw [map_smul]; rw [normalizedTrace_eq_of_finiteDimensional F E]; rw [LinearMap.smul_apply]; rw [← smul_assoc]; 
-/
private theorem normalizedTrace_trans_apply_aux [FiniteDimensional F E] [Algebra.IsIntegral E K]
    [CharZero E] (a : K) :
    normalizedTrace F E (normalizedTrace E K a) = normalizedTrace F K a := by
  have : FiniteDimensional E E⟮a⟯ :=
    IntermediateField.adjoin.finiteDimensional (IsIntegral.isIntegral a)
  rw [normalizedTrace_def E K]; rw [inv_natCast_smul_eq (R := E) (S := F)]; rw [map_smul]; rw [normalizedTrace_eq_of_finiteDimensional F E]; rw [LinearMap.smul_apply]; rw [← smul_assoc]; rw [smul_eq_mul (a := _⁻¹)]; rw [← mul_inv]; rw [trace_trace]; rw [mul_comm]; rw [← Nat.cast_mul]; rw [Module.finrank_mul_finrank]; rw [eq_comm]
  let E' := E⟮a⟯.restrictScalars F
  have : FiniteDimensional F E' := Module.Finite.trans E E⟮a⟯
  have h_finrank_eq : Module.finrank F E⟮a⟯ = Module.finrank F E' := rfl
  have h_trace_eq : trace F E⟮a⟯ (AdjoinSimple.gen E a) = trace F E' (AdjoinSimple.gen E a : E') :=
    rfl
  let a' : E' := AdjoinSimple.gen E a
  rw [h_finrank_eq]; rw [h_trace_eq]; rw [← normalizedTrace_eq_of_finiteDimensional_apply F]; rw [← normalizedTrace_intermediateField F K a']
  congr

/--
theorem `normalizedTrace_trans_apply` / 定理 `normalizedTrace_trans_apply`

English:
theorem normalizedTrace_trans_apply
  given: [Algebra.IsIntegral E K] [CharZero E] (a : K)
  proof: let S : Set E := (minpoly E a).coeffs
  let E₀ := IntermediateField.adjoin F S
  have : FiniteDimensional F E₀ := IntermediateField.finiteDimensional_adjoin
    fun x _ => Algebra.IsIntegral.isIntegral x
  have : Algebra.IsIntegral E₀ E := IsIntegral.tower_top F
  have : Algebra.IsIntegral E₀ K := I

中文:
定理 normalizedTrace_trans_apply
  条件: [Algebra.Is整数egral E K] [CharZero E] (a : K)
  证明: let S : Set E := (minpoly E a).coeffs
  let E₀ := IntermediateField.adjoin F S
  have : FiniteDimensional F E₀ := IntermediateField.finiteDimensional_adjoin
    fun x _ => Algebra.IsIntegral.isIntegral x
  have : Algebra.IsIntegral E₀ E := IsIntegral.tower_top F
  have : Algebra.IsIntegral E₀ K := I

Depends on / 依赖: Algebra, Algebra.IsIntegral, Algebra.IsIntegral.isIntegral, FiniteDimensional, IntermediateField, IntermediateField.adjoin, IntermediateField.finiteDimensional_adjoin, IntermediateField.subset_adjoin, IsIntegral, IsIntegral.tower_top, IsIntegral.trans, Polynomial, Polynomial.lifts_iff_coeffs_subset_range, Subalgebra, Subalgebra.range_algebraMap, adjoin, algebraMap, coeffs, finiteDimensional_adjoin, hlifts
-/
theorem normalizedTrace_trans_apply [Algebra.IsIntegral E K] [CharZero E] (a : K) :
    normalizedTrace F E (normalizedTrace E K a) = normalizedTrace F K a :=
  let S : Set E := (minpoly E a).coeffs
  let E₀ := IntermediateField.adjoin F S
  have : FiniteDimensional F E₀ := IntermediateField.finiteDimensional_adjoin
    fun x _ => Algebra.IsIntegral.isIntegral x
  have : Algebra.IsIntegral E₀ E := IsIntegral.tower_top F
  have : Algebra.IsIntegral E₀ K := IsIntegral.trans E
  have hsub : S subseteq (algebraMap E₀ E).range :=
    Subalgebra.range_algebraMap E₀.toSubalgebra ▸ IntermediateField.subset_adjoin F S
  have hlifts := (Polynomial.lifts_iff_coeffs_subset_range _).mpr hsub
  (normalizedTrace_trans_apply_aux F E₀ K _ ▸
    normalizedTrace_algebraMap_apply F E₀ E _ ▸
    congrArg (normalizedTrace F E) (normalizedTrace_algebraMap_of_lifts E₀ E K a hlifts)).symm

@[simp]
/--
theorem `normalizedTrace_trans` / 定理 `normalizedTrace_trans`

English:
theorem normalizedTrace_trans
  given: [Algebra.IsIntegral E K] [CharZero E]
  proof: LinearMap.ext normalizedTrace_trans_apply F E K

中文:
定理 normalizedTrace_trans
  条件: [Algebra.Is整数egral E K] [CharZero E]
  证明: LinearMap.ext normalizedTrace_trans_apply F E K

Depends on / 依赖: LinearMap, LinearMap.ext, normalizedTrace_trans_apply
-/
theorem normalizedTrace_trans [Algebra.IsIntegral E K] [CharZero E] :
    normalizedTrace F E ∘ₗ normalizedTrace E K = normalizedTrace F K :=
LinearMap.ext normalizedTrace_trans_apply F E K

end IsScalarTower

/--
theorem `normalizedTrace_algebraMap_apply_eq_self` / 定理 `normalizedTrace_algebraMap_apply_eq_self`

English:
theorem normalizedTrace_algebraMap_apply_eq_self
  given: (a : F)
  proof: by simp

中文:
定理 normalizedTrace_algebraMap_apply_eq_self
  条件: (a : F)
  证明: by simp
-/
theorem normalizedTrace_algebraMap_apply_eq_self (a : F) :
    normalizedTrace F K (algebraMap F K a) = a := by simp

/--
theorem `normalizedTrace_algebraMap_eq_id` / 定理 `normalizedTrace_algebraMap_eq_id`

English:
theorem normalizedTrace_algebraMap_eq_id
  proof: LinearMap.ext normalizedTrace_algebraMap_apply_eq_self F K

中文:
定理 normalizedTrace_algebraMap_eq_id
  证明: LinearMap.ext normalizedTrace_algebraMap_apply_eq_self F K

Depends on / 依赖: LinearMap, LinearMap.ext, normalizedTrace_algebraMap_apply_eq_self
-/
theorem normalizedTrace_algebraMap_eq_id :
    normalizedTrace F K ∘ₗ Algebra.linearMap F K = LinearMap.id :=
LinearMap.ext normalizedTrace_algebraMap_apply_eq_self F K

/-- The normalized trace commutes with (injective) maps. -/
@[simp]
/--
theorem `normalizedTrace_comp_algHom` / 定理 `normalizedTrace_comp_algHom`

English:
theorem normalizedTrace_comp_algHom
  statement: {E : Type*} [Field E] [Algebra F E] [Algebra.IsIntegral F E]
  proof: LinearMap.ext normalizedTrace_map F K f

中文:
定理 normalizedTrace_comp_algHom
  结论: {E : 类型} [Field E] [Algebra F E] [Algebra.Is整数egral F E]
  证明: LinearMap.ext normalizedTrace_map F K f

Depends on / 依赖: LinearMap, LinearMap.ext, normalizedTrace_map
-/
theorem normalizedTrace_comp_algHom {E : Type*} [Field E] [Algebra F E] [Algebra.IsIntegral F E]
    (f : E ->ₐ[F] K) : normalizedTrace F K ∘ₗ f = normalizedTrace F E :=
LinearMap.ext normalizedTrace_map F K f

/--
theorem `normalizedTrace_surjective` / 定理 `normalizedTrace_surjective`

English:
theorem normalizedTrace_surjective
  statement: Function.Surjective (normalizedTrace F K)
  proof: fun a => ⟨algebraMap F K a, normalizedTrace_algebraMap_apply_eq_self F K a⟩

中文:
定理 normalizedTrace_surjective
  结论: Function.Surjective (normalizedTrace F K)
  证明: fun a => ⟨algebraMap F K a, normalizedTrace_algebraMap_apply_eq_self F K a⟩

Depends on / 依赖: algebraMap, normalizedTrace_algebraMap_apply_eq_self
-/
theorem normalizedTrace_surjective : Function.Surjective (normalizedTrace F K) :=
  fun a => ⟨algebraMap F K a, normalizedTrace_algebraMap_apply_eq_self F K a⟩

/--
theorem `normalizedTrace_ne_zero` / 定理 `normalizedTrace_ne_zero`

English:
theorem normalizedTrace_ne_zero
  statement: normalizedTrace F K != 0
  proof: let ⟨a, ha⟩ := normalizedTrace_surjective F K 1
DFunLike.ne_iff.mpr ⟨a, ha ▸ one_ne_zero⟩

中文:
定理 normalizedTrace_ne_zero
  结论: normalizedTrace F K != 0
  证明: let ⟨a, ha⟩ := normalizedTrace_surjective F K 1
DFunLike.ne_iff.mpr ⟨a, ha ▸ one_ne_zero⟩

Depends on / 依赖: DFunLike, DFunLike.ne_iff.mpr, ne_iff, normalizedTrace_surjective, one_ne_zero
-/
theorem normalizedTrace_ne_zero : normalizedTrace F K != 0 :=
  let ⟨a, ha⟩ := normalizedTrace_surjective F K 1
DFunLike.ne_iff.mpr ⟨a, ha ▸ one_ne_zero⟩

end Algebra
