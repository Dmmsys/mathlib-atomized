/-
Copyright (c) 2023 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Conductor
public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.Trace.Quotient

/-!
# The different ideal

## Main definition
- `Submodule.traceDual`: The dual `L`-sub `B`-module under the trace form.
- `FractionalIdeal.dual`: The dual fractional ideal under the trace form.
- `differentIdeal`: The different ideal of an extension of integral domains.

## Main results
- `conductor_mul_differentIdeal`:
  If `L = K[x]`, with `x` integral over `A`, then `𝔣 * 𝔇 = (f'(x))`
    with `f` being the minimal polynomial of `x`.
- `aeval_derivative_mem_differentIdeal`:
  If `L = K[x]`, with `x` integral over `A`, then `f'(x) ∈ 𝔇`
    with `f` being the minimal polynomial of `x`.
- `not_dvd_differentIdeal_iff`: A prime does not divide the different ideal iff it is unramified
  (in the sense of `Algebra.IsUnramifiedAt`).
- `differentIdeal_eq_differentIdeal_mul_differentIdeal`: Transitivity of the different ideal.

## TODO
- Show properties of the different ideal
-/

@[expose] public section

open Module

universe u

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
  Ideal.Quotient.field

variable (A K : Type*) {L : Type u} {B} [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]

open nonZeroDivisors IsLocalization Matrix Algebra Pointwise Polynomial Submodule
section BIsDomain

/-- Under the AKLB setting, `Iᵛ := traceDual A K (I : Submodule B L)` is the
`Submodule B L` such that `x ∈ Iᵛ ↔ ∀ y ∈ I, Tr(x, y) ∈ A` -/
noncomputable
/--
Definition of `Submodule.traceDual` / `Submodule.traceDual` 的定义

English:
definition Submodule.traceDual
  signature: (I : Submodule B L)
  body: (traceForm K L).dualSubmodule (I.restrictScalars A)
  smul_mem' c x hx a ha := by
    rw [traceForm_apply]; rw [smul_mul_assoc]; rw [mul_comm]; rw [← smul_mul_assoc]; rw [mul_comm]
    exact hx _ (Submodule.smul_mem _ c ha)

中文:
定义 子模.traceDual
  签名: (I : 子模 B L)
  定义体: (traceForm K L).dualSubmodule (I.restrictScalars A)
  smul_mem' c x hx a ha := by
    rw [traceForm_apply]; rw [smul_mul_assoc]; rw [mul_comm]; rw [← smul_mul_assoc]; rw [mul_comm]
    exact hx _ (Submodule.smul_mem _ c ha)

Depends on / 依赖: I.restrictScalars, dualSubmodule, restrictScalars, traceForm
-/
def Submodule.traceDual (I : Submodule B L) : Submodule B L where
  __ := (traceForm K L).dualSubmodule (I.restrictScalars A)
  smul_mem' c x hx a ha := by
    rw [traceForm_apply]; rw [smul_mul_assoc]; rw [mul_comm]; rw [← smul_mul_assoc]; rw [mul_comm]
    exact hx _ (Submodule.smul_mem _ c ha)

variable {A K}

local notation:max I:max "ᵛ" => Submodule.traceDual A K I

namespace Submodule

/--
lemma `mem_traceDual` / 引理 `mem_traceDual`

English:
lemma mem_traceDual
  given: {I : Submodule B L} {x}
  proof: forall₂_congr fun _ _ => mem_one

中文:
引理 mem_traceDual
  条件: {I : 子模 B L} {x}
  证明: forall₂_congr fun _ _ => mem_one

Depends on / 依赖: mem_one
-/
lemma mem_traceDual {I : Submodule B L} {x} :
    x in Iᵛ ↔ forall a in I, traceForm K L x a in (algebraMap A K).range :=
  forall₂_congr fun _ _ => mem_one

/--
lemma `le_traceDual_iff_map_le_one` / 引理 `le_traceDual_iff_map_le_one`

English:
lemma le_traceDual_iff_map_le_one
  given: {I J : Submodule B L}
  proof: by
  rw [Submodule.map_le_iff_le_comap]; rw [Submodule.restrictScalars_mul]; rw [Submodule.mul_le]
  simp [SetLike.le_def, mem_traceDual]

中文:
引理 le_traceDual_iff_map_le_one
  条件: {I J : 子模 B L}
  证明: by
  rw [Submodule.map_le_iff_le_comap]; rw [Submodule.restrictScalars_mul]; rw [Submodule.mul_le]
  simp [SetLike.le_def, mem_traceDual]

Depends on / 依赖: SetLike, SetLike.le_def, Submodule, Submodule.map_le_iff_le_comap, Submodule.mul_le, Submodule.restrictScalars_mul, le_def, map_le_iff_le_comap, mem_traceDual, mul_le, restrictScalars_mul
-/
lemma le_traceDual_iff_map_le_one {I J : Submodule B L} :
    I <= Jᵛ ↔ ((I * J : Submodule B L).restrictScalars A).map
      ((trace K L).restrictScalars A) <= 1 := by
  rw [Submodule.map_le_iff_le_comap]; rw [Submodule.restrictScalars_mul]; rw [Submodule.mul_le]
  simp [SetLike.le_def, mem_traceDual]

/--
lemma `le_traceDual_mul_iff` / 引理 `le_traceDual_mul_iff`

English:
lemma le_traceDual_mul_iff
  given: {I J J' : Submodule B L}
  proof: by
  simp_rw [le_traceDual_iff_map_le_one, mul_assoc]

中文:
引理 le_traceDual_mul_iff
  条件: {I J J' : 子模 B L}
  证明: by
  simp_rw [le_traceDual_iff_map_le_one, mul_assoc]

Depends on / 依赖: le_traceDual_iff_map_le_one, mul_assoc, simp_rw
-/
lemma le_traceDual_mul_iff {I J J' : Submodule B L} :
    I <= (J * J')ᵛ ↔ I * J <= J'ᵛ := by
  simp_rw [le_traceDual_iff_map_le_one, mul_assoc]

/--
lemma `le_traceDual` / 引理 `le_traceDual`

English:
lemma le_traceDual
  given: {I J : Submodule B L}
  proof: by
  rw [← le_traceDual_mul_iff]; rw [mul_one]

中文:
引理 le_traceDual
  条件: {I J : 子模 B L}
  证明: by
  rw [← le_traceDual_mul_iff]; rw [mul_one]

Depends on / 依赖: le_traceDual_mul_iff, mul_one
-/
lemma le_traceDual {I J : Submodule B L} :
    I <= Jᵛ ↔ I * J <= 1ᵛ := by
  rw [← le_traceDual_mul_iff]; rw [mul_one]

/--
lemma `le_traceDual_comm` / 引理 `le_traceDual_comm`

English:
lemma le_traceDual_comm
  given: {I J : Submodule B L}
  proof: by rw [le_traceDual, mul_comm, ← le_traceDual]

中文:
引理 le_traceDual_comm
  条件: {I J : 子模 B L}
  证明: by rw [le_traceDual, mul_comm, ← le_traceDual]

Depends on / 依赖: le_traceDual, mul_comm
-/
lemma le_traceDual_comm {I J : Submodule B L} :
    I <= Jᵛ ↔ J <= Iᵛ := by rw [le_traceDual, mul_comm, ← le_traceDual]

/--
lemma `le_traceDual_traceDual` / 引理 `le_traceDual_traceDual`

English:
lemma le_traceDual_traceDual
  given: {I : Submodule B L}
  proof: le_traceDual_comm.mpr le_rfl

@[simp]

中文:
引理 le_traceDual_traceDual
  条件: {I : 子模 B L}
  证明: le_traceDual_comm.mpr le_rfl

@[simp]

Depends on / 依赖: le_rfl, le_traceDual_comm, le_traceDual_comm.mpr
-/
lemma le_traceDual_traceDual {I : Submodule B L} :
    I <= Iᵛᵛ := le_traceDual_comm.mpr le_rfl

@[simp]
/--
lemma `restrictScalars_traceDual` / 引理 `restrictScalars_traceDual`

English:
lemma restrictScalars_traceDual
  given: {I : Submodule B L}
  proof: rfl

中文:
引理 restrictScalars_traceDual
  条件: {I : 子模 B L}
  证明: rfl
-/
lemma restrictScalars_traceDual {I : Submodule B L} :
    Iᵛ.restrictScalars A = (Algebra.traceForm K L).dualSubmodule (I.restrictScalars A) := rfl

variable (A) in
/--
theorem `traceDual_span_of_basis` / 定理 `traceDual_span_of_basis`

English:
theorem traceDual_span_of_basis
  statement: [FiniteDimensional K L] [Algebra.IsSeparable K L]
  proof: by
  rw [restrictScalars_traceDual]; rw [hb]
  exact (traceForm K L).dualSubmodule_span_of_basis (traceForm_nondegenerate K L) b

@[simp]

中文:
定理 traceDual_span_of_basis
  结论: [有限维 K L] [代数.是可分 K L]
  证明: by
  rw [restrictScalars_traceDual]; rw [hb]
  exact (traceForm K L).dualSubmodule_span_of_basis (traceForm_nondegenerate K L) b

@[simp]

Depends on / 依赖: dualSubmodule_span_of_basis, restrictScalars_traceDual, traceForm, traceForm_nondegenerate
-/
theorem traceDual_span_of_basis [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (I : Submodule B L) {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι K L)
    (hb : I.restrictScalars A = Submodule.span A (Set.range b)) :
    (traceDual A K I).restrictScalars A = span A (Set.range b.traceDual) := by
  rw [restrictScalars_traceDual]; rw [hb]
  exact (traceForm K L).dualSubmodule_span_of_basis (traceForm_nondegenerate K L) b

@[simp]
/--
lemma `traceDual_bot` / 引理 `traceDual_bot`

English:
lemma traceDual_bot
  proof: by ext; simp [mem_traceDual, -RingHom.mem_range]

中文:
引理 traceDual_bot
  证明: by ext; simp [mem_traceDual, -RingHom.mem_range]

Depends on / 依赖: RingHom, RingHom.mem_range, mem_range, mem_traceDual
-/
lemma traceDual_bot :
    (⊥ : Submodule B L)ᵛ = ⊤ := by ext; simp [mem_traceDual, -RingHom.mem_range]

open scoped Classical in
/--
lemma `traceDual_top'` / 引理 `traceDual_top'`

English:
lemma traceDual_top'
  proof: by
  split_ifs with h
  · rw [_root_.eq_top_iff]
    exact fun _ _ _ _ => h ⟨_, rfl⟩
  · simp only [SetLike.le_def, restrictScalars_mem, LinearMap.mem_range, mem_one,
      forall_exists_index, forall_apply_eq_imp_iff, not_forall, not_exists] at h
    obtain ⟨b, hb⟩ := h
    simp_rw [eq_bot_iff, SetLike.le_def, mem_bot, mem_traceDual, mem_top, true_implies,
      traceForm_apply, RingHom.mem_range]
    contrapose! hb with hx'
    obtain ⟨c, hc, hc0⟩ := hx'
    simpa [hc0] using hc (c⁻¹ * b)

中文:
引理 traceDual_top'
  证明: by
  split_ifs with h
  · rw [_root_.eq_top_iff]
    exact fun _ _ _ _ => h ⟨_, rfl⟩
  · simp only [SetLike.le_def, restrictScalars_mem, LinearMap.mem_range, mem_one,
      forall_exists_index, forall_apply_eq_imp_iff, not_forall, not_exists] at h
    obtain ⟨b, hb⟩ := h
    simp_rw [eq_bot_iff, SetLike.le_def, mem_bot, mem_traceDual, mem_top, true_implies,
      traceForm_apply, RingHom.mem_range]
    contrapose! hb with hx'
    obtain ⟨c, hc, hc0⟩ := hx'
    simpa [hc0] using hc (c⁻¹ * b)

Depends on / 依赖: LinearMap, LinearMap.mem_range, RingHom, RingHom.mem_range, SetLike, SetLike.le_def, _root_, _root_.eq_top_iff, contrapose, eq_bot_iff, eq_top_iff, forall_apply_eq_imp_iff, forall_exists_index, le_def, mem_bot, mem_one, mem_range, mem_top, mem_traceDual, not_exists
-/
lemma traceDual_top' :
    (⊤ : Submodule B L)ᵛ =
      if ((LinearMap.range (Algebra.trace K L)).restrictScalars A <= 1) then ⊤ else ⊥ := by
  split_ifs with h
  · rw [_root_.eq_top_iff]
    exact fun _ _ _ _ => h ⟨_, rfl⟩
  · simp only [SetLike.le_def, restrictScalars_mem, LinearMap.mem_range, mem_one,
      forall_exists_index, forall_apply_eq_imp_iff, not_forall, not_exists] at h
    obtain ⟨b, hb⟩ := h
    simp_rw [eq_bot_iff, SetLike.le_def, mem_bot, mem_traceDual, mem_top, true_implies,
      traceForm_apply, RingHom.mem_range]
    contrapose! hb with hx'
    obtain ⟨c, hc, hc0⟩ := hx'
    simpa [hc0] using hc (c⁻¹ * b)

variable [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/--
lemma `traceDual_top` / 引理 `traceDual_top`

English:
lemma traceDual_top
  given: [Decidable (IsField A)]
  proof: by
  convert! traceDual_top'
  rw [← IsFractionRing.surjective_iff_isField (R := A) (K := K)]; rw [LinearMap.range_eq_top.mpr (Algebra.trace_surjective K L)]; rw [← RingHom.range_eq_top]; rw [_root_.eq_top_iff]
  simp [SetLike.le_def]

中文:
引理 traceDual_top
  条件: [可判定 (是域 A)]
  证明: by
  convert! traceDual_top'
  rw [← IsFractionRing.surjective_iff_isField (R := A) (K := K)]; rw [LinearMap.range_eq_top.mpr (Algebra.trace_surjective K L)]; rw [← RingHom.range_eq_top]; rw [_root_.eq_top_iff]
  simp [SetLike.le_def]

Depends on / 依赖: Algebra, Algebra.trace_surjective, IsFractionRing, IsFractionRing.surjective_iff_isField, LinearMap, LinearMap.range_eq_top.mpr, RingHom, RingHom.range_eq_top, SetLike, SetLike.le_def, _root_, _root_.eq_top_iff, convert, eq_top_iff, le_def, range_eq_top, surjective_iff_isField, traceDual_top, trace_surjective
-/
lemma traceDual_top [Decidable (IsField A)] :
    (⊤ : Submodule B L)ᵛ = if IsField A then ⊤ else ⊥ := by
  convert! traceDual_top'
  rw [← IsFractionRing.surjective_iff_isField (R := A) (K := K)]; rw [LinearMap.range_eq_top.mpr (Algebra.trace_surjective K L)]; rw [← RingHom.range_eq_top]; rw [_root_.eq_top_iff]
  simp [SetLike.le_def]

end Submodule

open Submodule

variable [IsFractionRing A K]

variable (A K) in
/--
lemma `map_equiv_traceDual` / 引理 `map_equiv_traceDual`

English:
lemma map_equiv_traceDual
  statement: [IsDomain A] [IsFractionRing B L] [IsDomain B]
  proof: by
  change Submodule.map (FractionRing.algEquiv B L).toLinearEquiv.toLinearMap _ =
    traceDual A K (I.map (FractionRing.algEquiv B L).toLinearEquiv.toLinearMap)
  rw [Submodule.map_equiv_eq_comap_symm]; rw [Submodule.map_equiv_eq_comap_symm]
  ext x
  simp only [traceDual, Submodule.mem_comap]
  apply (FractionRing.algEquiv B L).forall_congr
  simp only [restrictScalars_mem, LinearEquiv.coe_coe, AlgEquiv.coe_symm_toLinearEquiv,
    traceForm_apply, mem_one, AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, mem_comap,
    AlgEquiv.symm_apply_apply]
  refine fun {y} => (forall_congr' fun hy => ?_)
  rw [Algebra.trace_eq_of_equiv_equiv (FractionRing.algEquiv A K).toRingEquiv
    (FractionRing.algEquiv B L).toRingEquiv]
  swap
  · ext
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K) (FractionRing.algEquiv B L) _
  simp only [map_mul, AlgEquiv.coe_ringEquiv,
    AlgEquiv.apply_symm_apply, ← AlgEquiv.symm_toRingEquiv, AlgEquiv.algebraMap_eq_apply]

中文:
引理 map_equiv_traceDual
  结论: [是整环 A] [IsFractionRing B L] [是整环 B]
  证明: by
  change Submodule.map (FractionRing.algEquiv B L).toLinearEquiv.toLinearMap _ =
    traceDual A K (I.map (FractionRing.algEquiv B L).toLinearEquiv.toLinearMap)
  rw [Submodule.map_equiv_eq_comap_symm]; rw [Submodule.map_equiv_eq_comap_symm]
  ext x
  simp only [traceDual, Submodule.mem_comap]
  apply (FractionRing.algEquiv B L).forall_congr
  simp only [restrictScalars_mem, LinearEquiv.coe_coe, AlgEquiv.coe_symm_toLinearEquiv,
    traceForm_apply, mem_one, AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, mem_comap,
    AlgEquiv.symm_apply_apply]
  refine fun {y} => (forall_congr' fun hy => ?_)
  rw [Algebra.trace_eq_of_equiv_equiv (FractionRing.algEquiv A K).toRingEquiv
    (FractionRing.algEquiv B L).toRingEquiv]
  swap
  · ext
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K) (FractionRing.algEquiv B L) _
  simp only [map_mul, AlgEquiv.coe_ringEquiv,
    AlgEquiv.apply_symm_apply, ← AlgEquiv.symm_toRingEquiv, AlgEquiv.algebraMap_eq_apply]

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_symm_toLinearEquiv, AlgEquiv.toEquiv_eq_coe, EquivLike, EquivLike.coe_coe, FractionRing, FractionRing.algEquiv, I.map, LinearEquiv, LinearEquiv.coe_coe, Submodule, Submodule.map, Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, algEquiv, coe_coe, coe_symm_toLinearEquiv, forall_congr, map_equiv_eq_comap_symm, mem_comap
-/
lemma map_equiv_traceDual [IsDomain A] [IsFractionRing B L] [IsDomain B]
    [FaithfulSMul A B] (I : Submodule B (FractionRing B)) :
    (traceDual A (FractionRing A) I).map (FractionRing.algEquiv B L).toLinearMap =
      traceDual A K (I.map (FractionRing.algEquiv B L).toLinearMap) := by
  change Submodule.map (FractionRing.algEquiv B L).toLinearEquiv.toLinearMap _ =
    traceDual A K (I.map (FractionRing.algEquiv B L).toLinearEquiv.toLinearMap)
  rw [Submodule.map_equiv_eq_comap_symm]; rw [Submodule.map_equiv_eq_comap_symm]
  ext x
  simp only [traceDual, Submodule.mem_comap]
  apply (FractionRing.algEquiv B L).forall_congr
  simp only [restrictScalars_mem, LinearEquiv.coe_coe, AlgEquiv.coe_symm_toLinearEquiv,
    traceForm_apply, mem_one, AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, mem_comap,
    AlgEquiv.symm_apply_apply]
  refine fun {y} => (forall_congr' fun hy => ?_)
  rw [Algebra.trace_eq_of_equiv_equiv (FractionRing.algEquiv A K).toRingEquiv
    (FractionRing.algEquiv B L).toRingEquiv]
  swap
  · ext
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K) (FractionRing.algEquiv B L) _
  simp only [map_mul, AlgEquiv.coe_ringEquiv,
    AlgEquiv.apply_symm_apply, ← AlgEquiv.symm_toRingEquiv, AlgEquiv.algebraMap_eq_apply]

variable [IsIntegrallyClosed A]

/--
lemma `Submodule.mem_traceDual_iff_isIntegral` / 引理 `Submodule.mem_traceDual_iff_isIntegral`

English:
lemma Submodule.mem_traceDual_iff_isIntegral
  given: {I : Submodule B L} {x}
  proof: forall₂_congr fun _ _ => mem_one.trans IsIntegrallyClosed.isIntegral_iff.symm

中文:
引理 子模.mem_traceDual_iff_is整数egral
  条件: {I : 子模 B L} {x}
  证明: forall₂_congr fun _ _ => mem_one.trans IsIntegrallyClosed.isIntegral_iff.symm

Depends on / 依赖: IsIntegrallyClosed, IsIntegrallyClosed.isIntegral_iff.symm, isIntegral_iff, mem_one, mem_one.trans
-/
lemma Submodule.mem_traceDual_iff_isIntegral {I : Submodule B L} {x} :
    x in Iᵛ ↔ forall a in I, IsIntegral A (traceForm K L x a) :=
  forall₂_congr fun _ _ => mem_one.trans IsIntegrallyClosed.isIntegral_iff.symm

variable [FiniteDimensional K L] [IsIntegralClosure B A L]

/--
lemma `Submodule.one_le_traceDual_one` / 引理 `Submodule.one_le_traceDual_one`

English:
lemma Submodule.one_le_traceDual_one
  proof: by
  rw [le_traceDual_iff_map_le_one]; rw [mul_one]; rw [one_eq_range]
  rintro _ ⟨x, ⟨x, rfl⟩, rfl⟩
  rw [mem_one]
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  rw [IsIntegralClosure.isIntegral_iff (A := B)]
  exact ⟨_, rfl⟩

中文:
引理 子模.one_le_traceDual_one
  证明: by
  rw [le_traceDual_iff_map_le_one]; rw [mul_one]; rw [one_eq_range]
  rintro _ ⟨x, ⟨x, rfl⟩, rfl⟩
  rw [mem_one]
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  rw [IsIntegralClosure.isIntegral_iff (A := B)]
  exact ⟨_, rfl⟩

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isIntegral_iff, IsIntegrallyClosed, IsIntegrallyClosed.isIntegral_iff.mp, isIntegral_iff, isIntegral_trace, le_traceDual_iff_map_le_one, mem_one, mul_one, one_eq_range
-/
lemma Submodule.one_le_traceDual_one :
    (1 : Submodule B L) <= 1ᵛ := by
  rw [le_traceDual_iff_map_le_one]; rw [mul_one]; rw [one_eq_range]
  rintro _ ⟨x, ⟨x, rfl⟩, rfl⟩
  rw [mem_one]
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  rw [IsIntegralClosure.isIntegral_iff (A := B)]
  exact ⟨_, rfl⟩

variable [Algebra.IsSeparable K L]

/--
lemma `isIntegral_discr_mul_of_mem_traceDual` / 引理 `isIntegral_discr_mul_of_mem_traceDual`

English:
lemma isIntegral_discr_mul_of_mem_traceDual
  proof: by
  have hinv : IsUnit (traceMatrix K b).det := by
    simpa [← discr_def] using discr_isUnit_of_basis _ b
  have H := mulVec_cramer (traceMatrix K b) fun i => trace K L (x * a * b i)
  have : Function.Injective (traceMatrix K b).mulVec := by
    rwa [mulVec_injective_iff_isUnit, isUnit_iff_isUnit_det]
  rw [← traceMatrix_of_basis_mulVec]; rw [← mulVec_smul]; rw [this.eq_iff]; rw [traceMatrix_of_basis_mulVec] at H
  rw [← b.equivFun.symm_apply_apply (_ * _)]; rw [b.equivFun_symm_apply]
  apply IsIntegral.sum
  intro i _
  rw [smul_mul_assoc]; rw [b.equivFun.map_smul]; rw [discr_def]; rw [mul_comm]; rw [← H]; rw [Algebra.smul_def]
  refine RingHom.IsIntegralElem.mul _ ?_ (hb _)
  apply IsIntegral.algebraMap
  rw [cramer_apply]
  apply IsIntegral.det
  intro j k
  rw [updateCol_apply]
  split
  · rw [mul_assoc]
    rw [mem_traceDual_iff_isIntegral] at hx
    apply hx
    have ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp (hb j)
    rw [mul_comm]; rw [← hy]; rw [← Algebra.smul_def]
    exact I.smul_mem _ (ha)
  · exact isIntegral_trace (RingHom.IsIntegralElem.mul _ (hb j) (hb k))

中文:
引理 is整数egral_discr_mul_of_mem_traceDual
  证明: by
  have hinv : IsUnit (traceMatrix K b).det := by
    simpa [← discr_def] using discr_isUnit_of_basis _ b
  have H := mulVec_cramer (traceMatrix K b) fun i => trace K L (x * a * b i)
  have : Function.Injective (traceMatrix K b).mulVec := by
    rwa [mulVec_injective_iff_isUnit, isUnit_iff_isUnit_det]
  rw [← traceMatrix_of_basis_mulVec]; rw [← mulVec_smul]; rw [this.eq_iff]; rw [traceMatrix_of_basis_mulVec] at H
  rw [← b.equivFun.symm_apply_apply (_ * _)]; rw [b.equivFun_symm_apply]
  apply IsIntegral.sum
  intro i _
  rw [smul_mul_assoc]; rw [b.equivFun.map_smul]; rw [discr_def]; rw [mul_comm]; rw [← H]; rw [Algebra.smul_def]
  refine RingHom.IsIntegralElem.mul _ ?_ (hb _)
  apply IsIntegral.algebraMap
  rw [cramer_apply]
  apply IsIntegral.det
  intro j k
  rw [updateCol_apply]
  split
  · rw [mul_assoc]
    rw [mem_traceDual_iff_isIntegral] at hx
    apply hx
    have ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp (hb j)
    rw [mul_comm]; rw [← hy]; rw [← Algebra.smul_def]
    exact I.smul_mem _ (ha)
  · exact isIntegral_trace (RingHom.IsIntegralElem.mul _ (hb j) (hb k))

Depends on / 依赖: Function, Function.Injective, Injective, IsIntegral, IsIntegral.sum, IsUnit, b.equivFun.symm_apply_apply, b.equivFun_symm_apply, discr_def, discr_isUnit_of_basis, eq_iff, equivFun, equivFun_symm_apply, isUnit_iff_isUnit_det, mulVec, mulVec_cramer, mulVec_injective_iff_isUnit, mulVec_smul, symm_apply_apply, this.eq_iff
-/
lemma isIntegral_discr_mul_of_mem_traceDual
    (I : Submodule B L) {ι} [DecidableEq ι] [Fintype ι]
    {b : Basis ι K L} (hb : forall i, IsIntegral A (b i))
    {a x : L} (ha : a in I) (hx : x in Iᵛ) :
    IsIntegral A ((discr K b) • a * x) := by
  have hinv : IsUnit (traceMatrix K b).det := by
    simpa [← discr_def] using discr_isUnit_of_basis _ b
  have H := mulVec_cramer (traceMatrix K b) fun i => trace K L (x * a * b i)
  have : Function.Injective (traceMatrix K b).mulVec := by
    rwa [mulVec_injective_iff_isUnit, isUnit_iff_isUnit_det]
  rw [← traceMatrix_of_basis_mulVec]; rw [← mulVec_smul]; rw [this.eq_iff]; rw [traceMatrix_of_basis_mulVec] at H
  rw [← b.equivFun.symm_apply_apply (_ * _)]; rw [b.equivFun_symm_apply]
  apply IsIntegral.sum
  intro i _
  rw [smul_mul_assoc]; rw [b.equivFun.map_smul]; rw [discr_def]; rw [mul_comm]; rw [← H]; rw [Algebra.smul_def]
  refine RingHom.IsIntegralElem.mul _ ?_ (hb _)
  apply IsIntegral.algebraMap
  rw [cramer_apply]
  apply IsIntegral.det
  intro j k
  rw [updateCol_apply]
  split
  · rw [mul_assoc]
    rw [mem_traceDual_iff_isIntegral] at hx
    apply hx
    have ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp (hb j)
    rw [mul_comm]; rw [← hy]; rw [← Algebra.smul_def]
    exact I.smul_mem _ (ha)
  · exact isIntegral_trace (RingHom.IsIntegralElem.mul _ (hb j) (hb k))

variable (A K)

variable [IsDomain A] [IsFractionRing B L] [Nontrivial B] [NoZeroDivisors B]

namespace FractionalIdeal

/-- The dual of a non-zero fractional ideal is the dual of the submodule under the trace form. -/
noncomputable
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: (I : FractionalIdeal B⁰ L)
  body: open scoped Classical in
  if hI : I = 0 then 0 else
  ⟨Iᵛ, by
    classical
    have ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
    obtain ⟨x, hx, hx'⟩ := exists_ne_zero_mem_isInteger hI
    have ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp
      (IsIntegral.algebraMap (B := L) (discr_isIntegral K hb))
    refine ⟨y * x, mem_nonZeroDivisors_iff_ne_zero.mpr (mul_ne_zero ?_ hx), fun z hz => ?_⟩
    · rw [← (IsIntegralClosure.algebraMap_injective B A L).ne_iff, hy, map_zero,
        ← (algebraMap K L).map_zero, (algebraMap K L).injective.ne_iff]
      exact discr_not_zero_of_basis K b
    · convert! isIntegral_discr_mul_of_mem_traceDual I hb hx' hz using 1
      · ext w; exact (IsIntegralClosure.isIntegral_iff (A := B)).symm
      · rw [Algebra.smul_def, map_mul, hy, ← Algebra.smul_def]⟩

中文:
定义 dual
  签名: (I : FractionalIdeal B⁰ L)
  定义体: open scoped Classical in
  if hI : I = 0 then 0 else
  ⟨Iᵛ, by
    classical
    have ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
    obtain ⟨x, hx, hx'⟩ := exists_ne_zero_mem_isInteger hI
    have ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp
      (IsIntegral.algebraMap (B := L) (discr_isIntegral K hb))
    refine ⟨y * x, mem_nonZeroDivisors_iff_ne_zero.mpr (mul_ne_zero ?_ hx), fun z hz => ?_⟩
    · rw [← (IsIntegralClosure.algebraMap_injective B A L).ne_iff, hy, map_zero,
        ← (algebraMap K L).map_zero, (algebraMap K L).injective.ne_iff]
      exact discr_not_zero_of_basis K b
    · convert! isIntegral_discr_mul_of_mem_traceDual I hb hx' hz using 1
      · ext w; exact (IsIntegralClosure.isIntegral_iff (A := B)).symm
      · rw [Algebra.smul_def, map_mul, hy, ← Algebra.smul_def]⟩

Depends on / 依赖: Classical, FiniteDimensional, FiniteDimensional.exists_is_basis_integral, IsIntegral, IsIntegral.algebraMap, IsIntegralClosure, IsIntegralClosure.algebraMap_injective, IsIntegralClosure.isIntegral_iff, algebraMap, algebraMap_injective, classical, discr_isIntegral, exists_is_basis_integral, exists_ne_zero_mem_isInteger, isIntegral_iff, map_, map_zero, mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero.mpr, mul_ne_zero
-/
def dual (I : FractionalIdeal B⁰ L) :
    FractionalIdeal B⁰ L :=
  open scoped Classical in
  if hI : I = 0 then 0 else
  ⟨Iᵛ, by
    classical
    have ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
    obtain ⟨x, hx, hx'⟩ := exists_ne_zero_mem_isInteger hI
    have ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp
      (IsIntegral.algebraMap (B := L) (discr_isIntegral K hb))
    refine ⟨y * x, mem_nonZeroDivisors_iff_ne_zero.mpr (mul_ne_zero ?_ hx), fun z hz => ?_⟩
    · rw [← (IsIntegralClosure.algebraMap_injective B A L).ne_iff, hy, map_zero,
        ← (algebraMap K L).map_zero, (algebraMap K L).injective.ne_iff]
      exact discr_not_zero_of_basis K b
    · convert! isIntegral_discr_mul_of_mem_traceDual I hb hx' hz using 1
      · ext w; exact (IsIntegralClosure.isIntegral_iff (A := B)).symm
      · rw [Algebra.smul_def, map_mul, hy, ← Algebra.smul_def]⟩

end FractionalIdeal

end BIsDomain

variable [IsDomain A] [IsFractionRing A K]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]

namespace FractionalIdeal

variable [IsFractionRing B L] [IsIntegrallyClosed A]

open Submodule

local notation:max I:max "ᵛ" => Submodule.traceDual A K I

variable [IsDedekindDomain B] {I J : FractionalIdeal B⁰ L}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `coe_dual` / 引理 `coe_dual`

English:
lemma coe_dual
  given: (hI : I != 0)
  proof: by rw [dual, dif_neg hI, coe_mk]

中文:
引理 coe_dual
  条件: (hI : I != 0)
  证明: by rw [dual, dif_neg hI, coe_mk]

Depends on / 依赖: coe_mk, dif_neg
-/
lemma coe_dual (hI : I != 0) :
    (dual A K I : Submodule B L) = Iᵛ := by rw [dual, dif_neg hI, coe_mk]

variable (B L)

@[simp]
/--
lemma `coe_dual_one` / 引理 `coe_dual_one`

English:
lemma coe_dual_one
  proof: by
  rw [← coe_one]; rw [coe_dual]
  exact one_ne_zero

中文:
引理 coe_dual_one
  证明: by
  rw [← coe_one]; rw [coe_dual]
  exact one_ne_zero

Depends on / 依赖: coe_dual, coe_one, one_ne_zero
-/
lemma coe_dual_one :
    (dual A K (1 : FractionalIdeal B⁰ L) : Submodule B L) = 1ᵛ := by
  rw [← coe_one]; rw [coe_dual]
  exact one_ne_zero

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `dual_zero` / 引理 `dual_zero`

English:
lemma dual_zero
  proof: by rw [dual, dif_pos rfl]

中文:
引理 dual_zero
  证明: by rw [dual, dif_pos rfl]

Depends on / 依赖: dif_pos
-/
lemma dual_zero :
    dual A K (0 : FractionalIdeal B⁰ L) = 0 := by rw [dual, dif_pos rfl]

variable {A K L B}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mem_dual` / 引理 `mem_dual`

English:
lemma mem_dual
  given: (hI : I != 0) {x}
  proof: by
  rw [dual]; rw [dif_neg hI]; exact forall₂_congr fun _ _ => mem_one

中文:
引理 mem_dual
  条件: (hI : I != 0) {x}
  证明: by
  rw [dual]; rw [dif_neg hI]; exact forall₂_congr fun _ _ => mem_one

Depends on / 依赖: dif_neg, mem_one
-/
lemma mem_dual (hI : I != 0) {x} :
    x in dual A K I ↔ forall a in I, traceForm K L x a in (algebraMap A K).range := by
  rw [dual]; rw [dif_neg hI]; exact forall₂_congr fun _ _ => mem_one

variable (A K)

/--
lemma `dual_ne_zero` / 引理 `dual_ne_zero`

English:
lemma dual_ne_zero
  given: (hI : I != 0)
  proof: by
  obtain ⟨b, hb, hb'⟩ := I.prop
  suffices algebraMap B L b in dual A K I by
    intro e
    rw [e]; rw [mem_zero_iff]; rw [← (algebraMap B L).map_zero]; rw [(IsIntegralClosure.algebraMap_injective B A L).eq_iff] at this
    exact mem_nonZeroDivisors_iff_ne_zero.mp hb this
  rw [mem_dual hI]
  intro a ha
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  dsimp
  convert! hb' a ha using 1
  · ext w
    exact IsIntegralClosure.isIntegral_iff (A := B)
  · exact (Algebra.smul_def _ _).symm

中文:
引理 dual_ne_zero
  条件: (hI : I != 0)
  证明: by
  obtain ⟨b, hb, hb'⟩ := I.prop
  suffices algebraMap B L b in dual A K I by
    intro e
    rw [e]; rw [mem_zero_iff]; rw [← (algebraMap B L).map_zero]; rw [(IsIntegralClosure.algebraMap_injective B A L).eq_iff] at this
    exact mem_nonZeroDivisors_iff_ne_zero.mp hb this
  rw [mem_dual hI]
  intro a ha
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  dsimp
  convert! hb' a ha using 1
  · ext w
    exact IsIntegralClosure.isIntegral_iff (A := B)
  · exact (Algebra.smul_def _ _).symm

Depends on / 依赖: Algebra, Algebra.smul_def, I.prop, IsIntegralClosure, IsIntegralClosure.algebraMap_injective, IsIntegralClosure.isIntegral_iff, IsIntegrallyClosed, IsIntegrallyClosed.isIntegral_iff.mp, algebraMap, algebraMap_injective, convert, eq_iff, isIntegral_iff, isIntegral_trace, map_zero, mem_dual, mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero.mp, mem_zero_iff, smul_def
-/
lemma dual_ne_zero (hI : I != 0) :
    dual A K I != 0 := by
  obtain ⟨b, hb, hb'⟩ := I.prop
  suffices algebraMap B L b in dual A K I by
    intro e
    rw [e]; rw [mem_zero_iff]; rw [← (algebraMap B L).map_zero]; rw [(IsIntegralClosure.algebraMap_injective B A L).eq_iff] at this
    exact mem_nonZeroDivisors_iff_ne_zero.mp hb this
  rw [mem_dual hI]
  intro a ha
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  dsimp
  convert! hb' a ha using 1
  · ext w
    exact IsIntegralClosure.isIntegral_iff (A := B)
  · exact (Algebra.smul_def _ _).symm

variable {A K}

@[simp]
/--
lemma `dual_eq_zero_iff` / 引理 `dual_eq_zero_iff`

English:
lemma dual_eq_zero_iff
  proof: ⟨not_imp_not.mp (dual_ne_zero A K), fun e => e.symm ▸ dual_zero A K L B⟩

中文:
引理 dual_eq_zero_iff
  证明: ⟨not_imp_not.mp (dual_ne_zero A K), fun e => e.symm ▸ dual_zero A K L B⟩

Depends on / 依赖: dual_ne_zero, dual_zero, e.symm, not_imp_not, not_imp_not.mp
-/
lemma dual_eq_zero_iff :
    dual A K I = 0 ↔ I = 0 :=
  ⟨not_imp_not.mp (dual_ne_zero A K), fun e => e.symm ▸ dual_zero A K L B⟩

/--
lemma `dual_ne_zero_iff` / 引理 `dual_ne_zero_iff`

English:
lemma dual_ne_zero_iff
  proof: dual_eq_zero_iff.not

中文:
引理 dual_ne_zero_iff
  证明: dual_eq_zero_iff.not

Depends on / 依赖: dual_eq_zero_iff, dual_eq_zero_iff.not
-/
lemma dual_ne_zero_iff :
    dual A K I != 0 ↔ I != 0 := dual_eq_zero_iff.not

variable (A K)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `le_dual_inv_aux` / 引理 `le_dual_inv_aux`

English:
lemma le_dual_inv_aux
  given: (hI : I != 0) (hIJ : I * J <= 1)
  proof: by
  rw [dual]; rw [dif_neg hI]
  intro x hx y hy
  rw [mem_one]
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  rw [IsIntegralClosure.isIntegral_iff (A := B)]
  have ⟨z, _, hz⟩ := hIJ (FractionalIdeal.mul_mem_mul hy hx)
  rw [mul_comm] at hz
  exact ⟨z, hz⟩

中文:
引理 le_dual_inv_aux
  条件: (hI : I != 0) (hIJ : I * J <= 1)
  证明: by
  rw [dual]; rw [dif_neg hI]
  intro x hx y hy
  rw [mem_one]
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  rw [IsIntegralClosure.isIntegral_iff (A := B)]
  have ⟨z, _, hz⟩ := hIJ (FractionalIdeal.mul_mem_mul hy hx)
  rw [mul_comm] at hz
  exact ⟨z, hz⟩

Depends on / 依赖: FractionalIdeal, FractionalIdeal.mul_mem_mul, IsIntegralClosure, IsIntegralClosure.isIntegral_iff, IsIntegrallyClosed, IsIntegrallyClosed.isIntegral_iff.mp, dif_neg, isIntegral_iff, isIntegral_trace, mem_one, mul_comm, mul_mem_mul
-/
lemma le_dual_inv_aux (hI : I != 0) (hIJ : I * J <= 1) :
    J <= dual A K I := by
  rw [dual]; rw [dif_neg hI]
  intro x hx y hy
  rw [mem_one]
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  rw [IsIntegralClosure.isIntegral_iff (A := B)]
  have ⟨z, _, hz⟩ := hIJ (FractionalIdeal.mul_mem_mul hy hx)
  rw [mul_comm] at hz
  exact ⟨z, hz⟩

/--
lemma `one_le_dual_one` / 引理 `one_le_dual_one`

English:
lemma one_le_dual_one
  proof: le_dual_inv_aux A K one_ne_zero (by rw [one_mul])

中文:
引理 one_le_dual_one
  证明: le_dual_inv_aux A K one_ne_zero (by rw [one_mul])

Depends on / 依赖: le_dual_inv_aux, one_mul, one_ne_zero
-/
lemma one_le_dual_one :
    1 <= dual A K (1 : FractionalIdeal B⁰ L) :=
  le_dual_inv_aux A K one_ne_zero (by rw [one_mul])

/--
lemma `le_dual_iff` / 引理 `le_dual_iff`

English:
lemma le_dual_iff
  given: (hJ : J != 0)
  proof: by
  by_cases hI : I = 0
  · simp [hI]
  rw [← coe_le_coe]; rw [← coe_le_coe]; rw [coe_mul]; rw [coe_dual A K hJ]; rw [coe_dual_one]; rw [le_traceDual]

中文:
引理 le_dual_iff
  条件: (hJ : J != 0)
  证明: by
  by_cases hI : I = 0
  · simp [hI]
  rw [← coe_le_coe]; rw [← coe_le_coe]; rw [coe_mul]; rw [coe_dual A K hJ]; rw [coe_dual_one]; rw [le_traceDual]

Depends on / 依赖: coe_dual, coe_dual_one, coe_le_coe, coe_mul, le_traceDual
-/
lemma le_dual_iff (hJ : J != 0) :
    I <= dual A K J ↔ I * J <= dual A K 1 := by
  by_cases hI : I = 0
  · simp [hI]
  rw [← coe_le_coe]; rw [← coe_le_coe]; rw [coe_mul]; rw [coe_dual A K hJ]; rw [coe_dual_one]; rw [le_traceDual]

variable (I)

/--
lemma `inv_le_dual` / 引理 `inv_le_dual`

English:
lemma inv_le_dual
  proof: by
  classical
  exact if hI : I = 0 then by simp [hI] else le_dual_inv_aux A K hI (le_of_eq (mul_inv_cancel₀ hI))

中文:
引理 inv_le_dual
  证明: by
  classical
  exact if hI : I = 0 then by simp [hI] else le_dual_inv_aux A K hI (le_of_eq (mul_inv_cancel₀ hI))

Depends on / 依赖: classical, le_dual_inv_aux, le_of_eq
-/
lemma inv_le_dual :
    I⁻¹ <= dual A K I := by
  classical
  exact if hI : I = 0 then by simp [hI] else le_dual_inv_aux A K hI (le_of_eq (mul_inv_cancel₀ hI))

/--
lemma `dual_inv_le` / 引理 `dual_inv_le`

English:
lemma dual_inv_le
  proof: by
  by_cases hI : I = 0; · simp [hI]
  rw [inv_le_comm₀ (by simpa [pos_iff_ne_zero]) (by simpa [pos_iff_ne_zero])]
  exact inv_le_dual ..

中文:
引理 dual_inv_le
  证明: by
  by_cases hI : I = 0; · simp [hI]
  rw [inv_le_comm₀ (by simpa [pos_iff_ne_zero]) (by simpa [pos_iff_ne_zero])]
  exact inv_le_dual ..

Depends on / 依赖: inv_le_dual, pos_iff_ne_zero
-/
lemma dual_inv_le :
    (dual A K I)⁻¹ <= I := by
  by_cases hI : I = 0; · simp [hI]
  rw [inv_le_comm₀ (by simpa [pos_iff_ne_zero]) (by simpa [pos_iff_ne_zero])]
  exact inv_le_dual ..

/--
lemma `dual_eq_mul_inv` / 引理 `dual_eq_mul_inv`

English:
lemma dual_eq_mul_inv
  proof: by
  by_cases hI : I = 0; · simp [hI]
  apply le_antisymm
  · rw [le_mul_inv_iff₀ (pos_iff_ne_zero.2 hI), ← le_dual_iff A K hI]
  rw [le_dual_iff A K hI]; rw [mul_assoc]; rw [inv_mul_cancel₀ hI]; rw [mul_one]

中文:
引理 dual_eq_mul_inv
  证明: by
  by_cases hI : I = 0; · simp [hI]
  apply le_antisymm
  · rw [le_mul_inv_iff₀ (pos_iff_ne_zero.2 hI), ← le_dual_iff A K hI]
  rw [le_dual_iff A K hI]; rw [mul_assoc]; rw [inv_mul_cancel₀ hI]; rw [mul_one]

Depends on / 依赖: le_antisymm, le_dual_iff, mul_assoc, mul_one, pos_iff_ne_zero
-/
lemma dual_eq_mul_inv :
    dual A K I = dual A K 1 * I⁻¹ := by
  by_cases hI : I = 0; · simp [hI]
  apply le_antisymm
  · rw [le_mul_inv_iff₀ (pos_iff_ne_zero.2 hI), ← le_dual_iff A K hI]
  rw [le_dual_iff A K hI]; rw [mul_assoc]; rw [inv_mul_cancel₀ hI]; rw [mul_one]

variable {I}

/--
lemma `dual_div_dual` / 引理 `dual_div_dual`

English:
lemma dual_div_dual
  proof: by
  rw [dual_eq_mul_inv A K J]; rw [dual_eq_mul_inv A K I]; rw [mul_div_mul_comm]; rw [div_self]; rw [one_mul]
  · exact inv_div_inv J I
  · simp only [ne_eq, dual_eq_zero_iff, one_ne_zero, not_false_eq_true]

中文:
引理 dual_div_dual
  证明: by
  rw [dual_eq_mul_inv A K J]; rw [dual_eq_mul_inv A K I]; rw [mul_div_mul_comm]; rw [div_self]; rw [one_mul]
  · exact inv_div_inv J I
  · simp only [ne_eq, dual_eq_zero_iff, one_ne_zero, not_false_eq_true]

Depends on / 依赖: div_self, dual_eq_mul_inv, dual_eq_zero_iff, inv_div_inv, mul_div_mul_comm, ne_eq, not_false_eq_true, one_mul, one_ne_zero
-/
lemma dual_div_dual :
    dual A K J / dual A K I = I / J := by
  rw [dual_eq_mul_inv A K J]; rw [dual_eq_mul_inv A K I]; rw [mul_div_mul_comm]; rw [div_self]; rw [one_mul]
  · exact inv_div_inv J I
  · simp only [ne_eq, dual_eq_zero_iff, one_ne_zero, not_false_eq_true]

/--
lemma `dual_mul_self` / 引理 `dual_mul_self`

English:
lemma dual_mul_self
  given: (hI : I != 0)
  proof: by
  rw [dual_eq_mul_inv]; rw [mul_assoc]; rw [inv_mul_cancel₀ hI]; rw [mul_one]

中文:
引理 dual_mul_self
  条件: (hI : I != 0)
  证明: by
  rw [dual_eq_mul_inv]; rw [mul_assoc]; rw [inv_mul_cancel₀ hI]; rw [mul_one]

Depends on / 依赖: dual_eq_mul_inv, mul_assoc, mul_one
-/
lemma dual_mul_self (hI : I != 0) :
    dual A K I * I = dual A K 1 := by
  rw [dual_eq_mul_inv]; rw [mul_assoc]; rw [inv_mul_cancel₀ hI]; rw [mul_one]

/--
lemma `self_mul_dual` / 引理 `self_mul_dual`

English:
lemma self_mul_dual
  given: (hI : I != 0)
  proof: by
  rw [mul_comm]; rw [dual_mul_self A K hI]

中文:
引理 self_mul_dual
  条件: (hI : I != 0)
  证明: by
  rw [mul_comm]; rw [dual_mul_self A K hI]

Depends on / 依赖: dual_mul_self, mul_comm
-/
lemma self_mul_dual (hI : I != 0) :
    I * dual A K I = dual A K 1 := by
  rw [mul_comm]; rw [dual_mul_self A K hI]

/--
lemma `dual_inv` / 引理 `dual_inv`

English:
lemma dual_inv
  proof: by rw [dual_eq_mul_inv, inv_inv]

中文:
引理 dual_inv
  证明: by rw [dual_eq_mul_inv, inv_inv]

Depends on / 依赖: dual_eq_mul_inv, inv_inv
-/
lemma dual_inv :
    dual A K I⁻¹ = dual A K 1 * I := by rw [dual_eq_mul_inv, inv_inv]

variable (I)

@[simp]
/--
lemma `dual_dual` / 引理 `dual_dual`

English:
lemma dual_dual
  proof: by
  rw [dual_eq_mul_inv]; rw [dual_eq_mul_inv A K (I := I)]; rw [mul_inv]; rw [inv_inv]; rw [← mul_assoc]; rw [mul_inv_cancel₀]; rw [one_mul]
  rw [dual_ne_zero_iff]
  exact one_ne_zero

中文:
引理 dual_dual
  证明: by
  rw [dual_eq_mul_inv]; rw [dual_eq_mul_inv A K (I := I)]; rw [mul_inv]; rw [inv_inv]; rw [← mul_assoc]; rw [mul_inv_cancel₀]; rw [one_mul]
  rw [dual_ne_zero_iff]
  exact one_ne_zero

Depends on / 依赖: dual_eq_mul_inv, dual_ne_zero_iff, inv_inv, mul_assoc, mul_inv, one_mul, one_ne_zero
-/
lemma dual_dual :
    dual A K (dual A K I) = I := by
  rw [dual_eq_mul_inv]; rw [dual_eq_mul_inv A K (I := I)]; rw [mul_inv]; rw [inv_inv]; rw [← mul_assoc]; rw [mul_inv_cancel₀]; rw [one_mul]
  rw [dual_ne_zero_iff]
  exact one_ne_zero

variable {I}

@[simp]
/--
lemma `dual_le_dual` / 引理 `dual_le_dual`

English:
lemma dual_le_dual
  given: (hI : I != 0) (hJ : J != 0)
  proof: by
  nth_rewrite 2 [← dual_dual A K I]
  rw [le_dual_iff A K hJ]; rw [le_dual_iff A K (I := J) (by rwa [dual_ne_zero_iff]), mul_comm]

中文:
引理 dual_le_dual
  条件: (hI : I != 0) (hJ : J != 0)
  证明: by
  nth_rewrite 2 [← dual_dual A K I]
  rw [le_dual_iff A K hJ]; rw [le_dual_iff A K (I := J) (by rwa [dual_ne_zero_iff]), mul_comm]

Depends on / 依赖: dual_dual, dual_ne_zero_iff, le_dual_iff, mul_comm, nth_rewrite
-/
lemma dual_le_dual (hI : I != 0) (hJ : J != 0) :
    dual A K I <= dual A K J ↔ J <= I := by
  nth_rewrite 2 [← dual_dual A K I]
  rw [le_dual_iff A K hJ]; rw [le_dual_iff A K (I := J) (by rwa [dual_ne_zero_iff]), mul_comm]

variable {A K}

/--
lemma `dual_involutive` / 引理 `dual_involutive`

English:
lemma dual_involutive
  proof: dual_dual A K

中文:
引理 dual_involutive
  证明: dual_dual A K

Depends on / 依赖: dual_dual
-/
lemma dual_involutive :
    Function.Involutive (dual A K : FractionalIdeal B⁰ L -> FractionalIdeal B⁰ L) := dual_dual A K

/--
lemma `dual_injective` / 引理 `dual_injective`

English:
lemma dual_injective
  proof: dual_involutive.injective

中文:
引理 dual_injective
  证明: dual_involutive.injective

Depends on / 依赖: dual_involutive, dual_involutive.injective, injective
-/
lemma dual_injective :
    Function.Injective (dual A K : FractionalIdeal B⁰ L -> FractionalIdeal B⁰ L) :=
  dual_involutive.injective

variable (A K B L)

attribute [local instance] SMulCommClass.of_commMonoid

variable (C M : Type*) [CommRing C] [IsDedekindDomain C] [Field M] [Algebra C M]
  [IsFractionRing C M] [Algebra A C] [Algebra B C] [Algebra A M] [Algebra B M] [Algebra K M]
  [Algebra L M] [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower B C M]
  [IsScalarTower B L M] [IsScalarTower K L M] [IsIntegralClosure C A M] [FiniteDimensional K M]
  [FiniteDimensional L M] [Algebra.IsSeparable K M]

/--
theorem `trace_mem_dual_one` / 定理 `trace_mem_dual_one`

English:
theorem trace_mem_dual_one
  given: (x : M) (hx : x in dual A K (1 : FractionalIdeal C⁰ M))
  proof: by
  simp only [ne_eq, one_ne_zero, not_false_eq_true, mem_dual, mem_one_iff, traceForm_apply,
    RingHom.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
    mul_comm _ (algebraMap _ _ _), ← Algebra.smul_def, ← LinearMap.map_smul_of_tower,
    Algebra.trace_trace] at hx ⊢
  simpa using fun b => hx (algebraMap B C b)

中文:
定理 trace_mem_dual_one
  条件: (x : M) (hx : x in dual A K (1 : FractionalIdeal C⁰ M))
  证明: by
  simp only [ne_eq, one_ne_zero, not_false_eq_true, mem_dual, mem_one_iff, traceForm_apply,
    RingHom.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
    mul_comm _ (algebraMap _ _ _), ← Algebra.smul_def, ← LinearMap.map_smul_of_tower,
    Algebra.trace_trace] at hx ⊢
  simpa using fun b => hx (algebraMap B C b)

Depends on / 依赖: Algebra, Algebra.smul_def, Algebra.trace_trace, LinearMap, LinearMap.map_smul_of_tower, RingHom, RingHom.mem_range, algebraMap, forall_apply_eq_imp_iff, forall_exists_index, map_smul_of_tower, mem_dual, mem_one_iff, mem_range, mul_comm, ne_eq, not_false_eq_true, one_ne_zero, smul_def, traceForm_apply
-/
theorem trace_mem_dual_one (x : M) (hx : x in dual A K (1 : FractionalIdeal C⁰ M)) :
    Algebra.trace L M x in dual A K (1 : FractionalIdeal B⁰ L) := by
  simp only [ne_eq, one_ne_zero, not_false_eq_true, mem_dual, mem_one_iff, traceForm_apply,
    RingHom.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
    mul_comm _ (algebraMap _ _ _), ← Algebra.smul_def, ← LinearMap.map_smul_of_tower,
    Algebra.trace_trace] at hx ⊢
  simpa using fun b => hx (algebraMap B C b)

variable [IsIntegralClosure C B M] [Algebra.IsSeparable L M]

/--
theorem `smul_mem_dual_one` / 定理 `smul_mem_dual_one`

English:
theorem smul_mem_dual_one
  statement: {x : L} (hx : x in dual A K (1 : FractionalIdeal B⁰ L))
  proof: by
  simp only [ne_eq, one_ne_zero, not_false_eq_true, mem_dual, mem_one_iff, traceForm_apply,
    RingHom.mem_range, forall_exists_index, forall_apply_eq_imp_iff, mul_comm _ (algebraMap _ _ _),
    ← Algebra.smul_def] at hx hy ⊢
  intro c
  obtain ⟨b, hb⟩ := hy c
  obtain ⟨a, ha⟩ := hx b
  use a
  simpa [Algebra.smul_def b, hb, mul_comm _ x, ← smul_eq_mul, ← (Algebra.trace L M).map_smul,
    Algebra.trace_trace, smul_comm x c y] using ha

中文:
定理 smul_mem_dual_one
  结论: {x : L} (hx : x in dual A K (1 : FractionalIdeal B⁰ L))
  证明: by
  simp only [ne_eq, one_ne_zero, not_false_eq_true, mem_dual, mem_one_iff, traceForm_apply,
    RingHom.mem_range, forall_exists_index, forall_apply_eq_imp_iff, mul_comm _ (algebraMap _ _ _),
    ← Algebra.smul_def] at hx hy ⊢
  intro c
  obtain ⟨b, hb⟩ := hy c
  obtain ⟨a, ha⟩ := hx b
  use a
  simpa [Algebra.smul_def b, hb, mul_comm _ x, ← smul_eq_mul, ← (Algebra.trace L M).map_smul,
    Algebra.trace_trace, smul_comm x c y] using ha

Depends on / 依赖: Algebra, Algebra.smul_def, Algebra.trace, Algebra.trace_trace, RingHom, RingHom.mem_range, algebraMap, forall_apply_eq_imp_iff, forall_exists_index, map_smul, mem_dual, mem_one_iff, mem_range, mul_comm, ne_eq, not_false_eq_true, one_ne_zero, smul_comm, smul_def, smul_eq_mul
-/
theorem smul_mem_dual_one {x : L} (hx : x in dual A K (1 : FractionalIdeal B⁰ L))
    {y : M} (hy : y in dual B L (1 : FractionalIdeal C⁰ M)) :
    x • y in dual A K (1 : FractionalIdeal C⁰ M) := by
  simp only [ne_eq, one_ne_zero, not_false_eq_true, mem_dual, mem_one_iff, traceForm_apply,
    RingHom.mem_range, forall_exists_index, forall_apply_eq_imp_iff, mul_comm _ (algebraMap _ _ _),
    ← Algebra.smul_def] at hx hy ⊢
  intro c
  obtain ⟨b, hb⟩ := hy c
  obtain ⟨a, ha⟩ := hx b
  use a
  simpa [Algebra.smul_def b, hb, mul_comm _ x, ← smul_eq_mul, ← (Algebra.trace L M).map_smul,
    Algebra.trace_trace, smul_comm x c y] using ha

variable [IsTorsionFree B C]

/--
theorem `dual_eq_dual_mul_dual` / 定理 `dual_eq_dual_mul_dual`

English:
theorem dual_eq_dual_mul_dual
  proof: by
  have := IsIntegralClosure.isLocalization B L M C
  have h : B⁰ <= Submonoid.comap (algebraMap B C) C⁰ :=
nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ FaithfulSMul.algebraMap_injective _ _
  have h_alg {x : L} : algebraMap L M x = IsLocalization.map M (algebraMap B C) h x :=
    IsLocalization.algebraMap_apply_eq_map_map_submonoid B⁰ C L M x
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [← spanSingleton_le_iff_mem]; rw [← mul_inv_le_iff₀ (bot_lt_iff_ne_bot.mpr
      (by simp [-extendedHom'_apply])), ← map_inv₀, ← FractionalIdeal.coe_le_coe,
        extendedHom'_apply, coe_mul, coe_spanSingleton, coe_extended_eq_span, coe_dual_one,
        span_mul_span, span_le]
    rintro _ ⟨x, rfl, _, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨m, rfl⟩
    simp only [← h_alg, mul_comm _ (algebraMap _ _ _), ← Algebra.smul_def a, map_smul,
      LinearMap.toSpanSingleton_apply, Algebra.smul_def m, mul_one,
      LinearMap.smul_apply, traceForm_apply, smul_eq_mul]
    rw [← FractionalIdeal.coe_one (S := B⁰)]
    refine (mem_inv_iff (by simp)).mp ha _ (trace_mem_dual_one A K L B C M _ ?_)
    exact Algebra.smul_def m x ▸ smul_mem _ _ hx
  · rw [← FractionalIdeal.coe_le_coe, coe_mul, extendedHom'_apply,
      coe_extended_eq_span, ← span_eq (coeToSubmodule _), span_mul_span, span_le]
    rintro _ ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, mem_coe, ← h_alg, mul_comm a, ← Algebra.smul_def] at ha hb ⊢
    exact smul_mem_dual_one A K L B C M hb ha

中文:
定理 dual_eq_dual_mul_dual
  证明: by
  have := IsIntegralClosure.isLocalization B L M C
  have h : B⁰ <= Submonoid.comap (algebraMap B C) C⁰ :=
nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ FaithfulSMul.algebraMap_injective _ _
  have h_alg {x : L} : algebraMap L M x = IsLocalization.map M (algebraMap B C) h x :=
    IsLocalization.algebraMap_apply_eq_map_map_submonoid B⁰ C L M x
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [← spanSingleton_le_iff_mem]; rw [← mul_inv_le_iff₀ (bot_lt_iff_ne_bot.mpr
      (by simp [-extendedHom'_apply])), ← map_inv₀, ← FractionalIdeal.coe_le_coe,
        extendedHom'_apply, coe_mul, coe_spanSingleton, coe_extended_eq_span, coe_dual_one,
        span_mul_span, span_le]
    rintro _ ⟨x, rfl, _, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨m, rfl⟩
    simp only [← h_alg, mul_comm _ (algebraMap _ _ _), ← Algebra.smul_def a, map_smul,
      LinearMap.toSpanSingleton_apply, Algebra.smul_def m, mul_one,
      LinearMap.smul_apply, traceForm_apply, smul_eq_mul]
    rw [← FractionalIdeal.coe_one (S := B⁰)]
    refine (mem_inv_iff (by simp)).mp ha _ (trace_mem_dual_one A K L B C M _ ?_)
    exact Algebra.smul_def m x ▸ smul_mem _ _ hx
  · rw [← FractionalIdeal.coe_le_coe, coe_mul, extendedHom'_apply,
      coe_extended_eq_span, ← span_eq (coeToSubmodule _), span_mul_span, span_le]
    rintro _ ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, mem_coe, ← h_alg, mul_comm a, ← Algebra.smul_def] at ha hb ⊢
    exact smul_mem_dual_one A K L B C M hb ha

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsIntegralClosure, IsIntegralClosure.isLocalization, IsLocalization, IsLocalization.algebraMap_apply_eq_map_map_submonoid, IsLocalization.map, Submonoid, Submonoid.comap, _apply, algebraMap, algebraMap_apply_eq_map_map_submonoid, algebraMap_injective, bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mpr, extendedHom, h_alg, isLocalization, le_antisymm, nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
-/
theorem dual_eq_dual_mul_dual :
    dual A K (1 : FractionalIdeal C⁰ M) = dual B L (1 : FractionalIdeal C⁰ M) *
        (dual A K (1 : FractionalIdeal B⁰ L)).extendedHom M C := by
  have := IsIntegralClosure.isLocalization B L M C
  have h : B⁰ <= Submonoid.comap (algebraMap B C) C⁰ :=
nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ FaithfulSMul.algebraMap_injective _ _
  have h_alg {x : L} : algebraMap L M x = IsLocalization.map M (algebraMap B C) h x :=
    IsLocalization.algebraMap_apply_eq_map_map_submonoid B⁰ C L M x
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [← spanSingleton_le_iff_mem]; rw [← mul_inv_le_iff₀ (bot_lt_iff_ne_bot.mpr
      (by simp [-extendedHom'_apply])), ← map_inv₀, ← FractionalIdeal.coe_le_coe,
        extendedHom'_apply, coe_mul, coe_spanSingleton, coe_extended_eq_span, coe_dual_one,
        span_mul_span, span_le]
    rintro _ ⟨x, rfl, _, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨m, rfl⟩
    simp only [← h_alg, mul_comm _ (algebraMap _ _ _), ← Algebra.smul_def a, map_smul,
      LinearMap.toSpanSingleton_apply, Algebra.smul_def m, mul_one,
      LinearMap.smul_apply, traceForm_apply, smul_eq_mul]
    rw [← FractionalIdeal.coe_one (S := B⁰)]
    refine (mem_inv_iff (by simp)).mp ha _ (trace_mem_dual_one A K L B C M _ ?_)
    exact Algebra.smul_def m x ▸ smul_mem _ _ hx
  · rw [← FractionalIdeal.coe_le_coe, coe_mul, extendedHom'_apply,
      coe_extended_eq_span, ← span_eq (coeToSubmodule _), span_mul_span, span_le]
    rintro _ ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, mem_coe, ← h_alg, mul_comm a, ← Algebra.smul_def] at ha hb ⊢
    exact smul_mem_dual_one A K L B C M hb ha

end FractionalIdeal

section IsIntegrallyClosed

variable (B)
variable [IsIntegrallyClosed A] [IsDedekindDomain B] [IsTorsionFree A B]

/--
Definition of `differentIdeal` / `differentIdeal` 的定义

English:
definition differentIdeal
  signature: : Ideal B
  body: (1 / Submodule.traceDual A (FractionRing A) 1 : Submodule B (FractionRing B)).comap
    (Algebra.linearMap B (FractionRing B))

中文:
定义 differentIdeal
  签名: : 理想 B
  定义体: (1 / Submodule.traceDual A (FractionRing A) 1 : Submodule B (FractionRing B)).comap
    (Algebra.linearMap B (FractionRing B))

Depends on / 依赖: Algebra, Algebra.linearMap, FractionRing, Submodule, Submodule.traceDual, linearMap, traceDual
-/
noncomputable def differentIdeal : Ideal B :=
  (1 / Submodule.traceDual A (FractionRing A) 1 : Submodule B (FractionRing B)).comap
    (Algebra.linearMap B (FractionRing B))

/--
lemma `coeSubmodule_differentIdeal_fractionRing` / 引理 `coeSubmodule_differentIdeal_fractionRing`

English:
lemma coeSubmodule_differentIdeal_fractionRing
  statement: [Algebra.IsIntegral A B]
  proof: by
  rw [coeSubmodule]; rw [differentIdeal]; rw [Submodule.map_comap_eq]; rw [inf_eq_right]
  have := FractionalIdeal.dual_inv_le (A := A) (K := FractionRing A)
    (1 : FractionalIdeal B⁰ (FractionRing B))
  have : _ <= ((1 : FractionalIdeal B⁰ (FractionRing B)) : Submodule B (FractionRing B)) := this
  rw [← one_div]; rw [FractionalIdeal.coe_div (FractionalIdeal.dual_ne_zero _ _ _)]; rw [FractionalIdeal.coe_dual] at this
  · simpa only [FractionalIdeal.coe_one, Submodule.one_eq_range] using this
  · exact one_ne_zero
  · exact one_ne_zero

中文:
引理 coeSubmodule_differentIdeal_fractionRing
  结论: [代数.是整 A B]
  证明: by
  rw [coeSubmodule]; rw [differentIdeal]; rw [Submodule.map_comap_eq]; rw [inf_eq_right]
  have := FractionalIdeal.dual_inv_le (A := A) (K := FractionRing A)
    (1 : FractionalIdeal B⁰ (FractionRing B))
  have : _ <= ((1 : FractionalIdeal B⁰ (FractionRing B)) : Submodule B (FractionRing B)) := this
  rw [← one_div]; rw [FractionalIdeal.coe_div (FractionalIdeal.dual_ne_zero _ _ _)]; rw [FractionalIdeal.coe_dual] at this
  · simpa only [FractionalIdeal.coe_one, Submodule.one_eq_range] using this
  · exact one_ne_zero
  · exact one_ne_zero

Depends on / 依赖: FractionRing, FractionalIdeal, FractionalIdeal.coe_div, FractionalIdeal.coe_dual, FractionalIdeal.coe_one, FractionalIdeal.dual_inv_le, FractionalIdeal.dual_ne_zero, Submodule, Submodule.map_comap_eq, Submodule.one_eq_range, coeSubmodule, coe_div, coe_dual, coe_one, differentIdeal, dual_inv_le, dual_ne_zero, inf_eq_right, map_comap_eq, one_div
-/
lemma coeSubmodule_differentIdeal_fractionRing [Algebra.IsIntegral A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [FiniteDimensional (FractionRing A) (FractionRing B)] :
    coeSubmodule (FractionRing B) (differentIdeal A B) =
      1 / Submodule.traceDual A (FractionRing A) 1 := by
  rw [coeSubmodule]; rw [differentIdeal]; rw [Submodule.map_comap_eq]; rw [inf_eq_right]
  have := FractionalIdeal.dual_inv_le (A := A) (K := FractionRing A)
    (1 : FractionalIdeal B⁰ (FractionRing B))
  have : _ <= ((1 : FractionalIdeal B⁰ (FractionRing B)) : Submodule B (FractionRing B)) := this
  rw [← one_div]; rw [FractionalIdeal.coe_div (FractionalIdeal.dual_ne_zero _ _ _)]; rw [FractionalIdeal.coe_dual] at this
  · simpa only [FractionalIdeal.coe_one, Submodule.one_eq_range] using this
  · exact one_ne_zero
  · exact one_ne_zero

section

variable [IsFractionRing B L]

/--
lemma `coeSubmodule_differentIdeal` / 引理 `coeSubmodule_differentIdeal`

English:
lemma coeSubmodule_differentIdeal
  proof: by
  have : (FractionRing.algEquiv B L).toLinearEquiv.comp (Algebra.linearMap B (FractionRing B)) =
    Algebra.linearMap B L := by ext; simp
  rw [coeSubmodule]; rw [← this]
  have H : RingHom.comp (algebraMap (FractionRing A) (FractionRing B))
      ↑(FractionRing.algEquiv A K).symm.toRingEquiv =
        RingHom.comp ↑(FractionRing.algEquiv B L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext A⁰
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B L]; rw [AlgEquiv.commutes]; rw [← IsScalarTower.algebraMap_apply]
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    Algebra.IsSeparable.of_equiv_equiv _ _ H
  have : FiniteDimensional (FractionRing A) (FractionRing B) := Module.Finite.of_equiv_equiv _ _ H
  have : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra _ L
  simp only [AlgEquiv.toLinearEquiv_toLinearMap, Submodule.map_comp]
  rw [← coeSubmodule]; rw [coeSubmodule_differentIdeal_fractionRing _ _]; rw [Submodule.map_div]; rw [AlgEquiv.toLinearMap]; rw [← AlgEquiv.toAlgHom_toLinearMap]; rw [Submodule.map_one]
  congr 1
  refine (map_equiv_traceDual A K _).trans ?_
  congr 1
  ext
  simp

中文:
引理 coeSubmodule_differentIdeal
  证明: by
  have : (FractionRing.algEquiv B L).toLinearEquiv.comp (Algebra.linearMap B (FractionRing B)) =
    Algebra.linearMap B L := by ext; simp
  rw [coeSubmodule]; rw [← this]
  have H : RingHom.comp (algebraMap (FractionRing A) (FractionRing B))
      ↑(FractionRing.algEquiv A K).symm.toRingEquiv =
        RingHom.comp ↑(FractionRing.algEquiv B L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext A⁰
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B L]; rw [AlgEquiv.commutes]; rw [← IsScalarTower.algebraMap_apply]
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    Algebra.IsSeparable.of_equiv_equiv _ _ H
  have : FiniteDimensional (FractionRing A) (FractionRing B) := Module.Finite.of_equiv_equiv _ _ H
  have : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra _ L
  simp only [AlgEquiv.toLinearEquiv_toLinearMap, Submodule.map_comp]
  rw [← coeSubmodule]; rw [coeSubmodule_differentIdeal_fractionRing _ _]; rw [Submodule.map_div]; rw [AlgEquiv.toLinearMap]; rw [← AlgEquiv.toAlgHom_toLinearMap]; rw [Submodule.map_one]
  congr 1
  refine (map_equiv_traceDual A K _).trans ?_
  congr 1
  ext
  simp

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_ringEquiv, Algebra, Algebra.linearMap, FractionRing, FractionRing.algEquiv, Function, Function.comp_apply, IsLocalization, IsLocalization.ringHom_ext, RingHom, RingHom.coe_coe, RingHom.coe_comp, RingHom.comp, algEquiv, algebraMap, coeSubmodule, coe_coe, coe_comp, coe_ringEquiv
-/
lemma coeSubmodule_differentIdeal :
    coeSubmodule L (differentIdeal A B) = 1 / Submodule.traceDual A K 1 := by
  have : (FractionRing.algEquiv B L).toLinearEquiv.comp (Algebra.linearMap B (FractionRing B)) =
    Algebra.linearMap B L := by ext; simp
  rw [coeSubmodule]; rw [← this]
  have H : RingHom.comp (algebraMap (FractionRing A) (FractionRing B))
      ↑(FractionRing.algEquiv A K).symm.toRingEquiv =
        RingHom.comp ↑(FractionRing.algEquiv B L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext A⁰
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B L]; rw [AlgEquiv.commutes]; rw [← IsScalarTower.algebraMap_apply]
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    Algebra.IsSeparable.of_equiv_equiv _ _ H
  have : FiniteDimensional (FractionRing A) (FractionRing B) := Module.Finite.of_equiv_equiv _ _ H
  have : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra _ L
  simp only [AlgEquiv.toLinearEquiv_toLinearMap, Submodule.map_comp]
  rw [← coeSubmodule]; rw [coeSubmodule_differentIdeal_fractionRing _ _]; rw [Submodule.map_div]; rw [AlgEquiv.toLinearMap]; rw [← AlgEquiv.toAlgHom_toLinearMap]; rw [Submodule.map_one]
  congr 1
  refine (map_equiv_traceDual A K _).trans ?_
  congr 1
  ext
  simp

variable (L)

/--
lemma `coeIdeal_differentIdeal` / 引理 `coeIdeal_differentIdeal`

English:
lemma coeIdeal_differentIdeal
  proof: by
  apply FractionalIdeal.coeToSubmodule_injective
  simp only [FractionalIdeal.coe_div
    (FractionalIdeal.dual_ne_zero _ _ (@one_ne_zero (FractionalIdeal B⁰ L) _ _ _)),
    FractionalIdeal.coe_coeIdeal, coeSubmodule_differentIdeal A K, inv_eq_one_div,
    FractionalIdeal.coe_dual_one, FractionalIdeal.coe_one]

中文:
引理 coeIdeal_differentIdeal
  证明: by
  apply FractionalIdeal.coeToSubmodule_injective
  simp only [FractionalIdeal.coe_div
    (FractionalIdeal.dual_ne_zero _ _ (@one_ne_zero (FractionalIdeal B⁰ L) _ _ _)),
    FractionalIdeal.coe_coeIdeal, coeSubmodule_differentIdeal A K, inv_eq_one_div,
    FractionalIdeal.coe_dual_one, FractionalIdeal.coe_one]

Depends on / 依赖: FractionalIdeal, FractionalIdeal.coeToSubmodule_injective, FractionalIdeal.coe_coeIdeal, FractionalIdeal.coe_div, FractionalIdeal.coe_dual_one, FractionalIdeal.coe_one, FractionalIdeal.dual_ne_zero, coeSubmodule_differentIdeal, coeToSubmodule_injective, coe_coeIdeal, coe_div, coe_dual_one, coe_one, dual_ne_zero, inv_eq_one_div, one_ne_zero
-/
lemma coeIdeal_differentIdeal :
    ↑(differentIdeal A B) = (FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L))⁻¹ := by
  apply FractionalIdeal.coeToSubmodule_injective
  simp only [FractionalIdeal.coe_div
    (FractionalIdeal.dual_ne_zero _ _ (@one_ne_zero (FractionalIdeal B⁰ L) _ _ _)),
    FractionalIdeal.coe_coeIdeal, coeSubmodule_differentIdeal A K, inv_eq_one_div,
    FractionalIdeal.coe_dual_one, FractionalIdeal.coe_one]

variable {A K B L}

/--
theorem `differentIdeal_ne_bot` / 定理 `differentIdeal_ne_bot`

English:
theorem differentIdeal_ne_bot
  statement: [Module.Finite A B]
  proof: by
  let K := FractionRing A
  let L := FractionRing B
  rw [ne_eq]; rw [← FractionalIdeal.coeIdeal_inj (K := L)]; rw [coeIdeal_differentIdeal (K := K)]
  simp

中文:
定理 differentIdeal_ne_bot
  结论: [模.有限 A B]
  证明: by
  let K := FractionRing A
  let L := FractionRing B
  rw [ne_eq]; rw [← FractionalIdeal.coeIdeal_inj (K := L)]; rw [coeIdeal_differentIdeal (K := K)]
  simp

Depends on / 依赖: FractionRing, FractionalIdeal, FractionalIdeal.coeIdeal_inj, coeIdeal_differentIdeal, coeIdeal_inj, ne_eq
-/
theorem differentIdeal_ne_bot [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)] :
    differentIdeal A B != ⊥ := by
  let K := FractionRing A
  let L := FractionRing B
  rw [ne_eq]; rw [← FractionalIdeal.coeIdeal_inj (K := L)]; rw [coeIdeal_differentIdeal (K := K)]
  simp

/--
lemma `differentialIdeal_le_fractionalIdeal_iff` / 引理 `differentialIdeal_le_fractionalIdeal_iff`

English:
lemma differentialIdeal_le_fractionalIdeal_iff
  proof: by
  rw [coeIdeal_differentIdeal A K L B]; rw [FractionalIdeal.inv_le_comm (by simp) hI]; rw [← FractionalIdeal.coe_le_coe]; rw [FractionalIdeal.coe_dual_one]
  refine le_traceDual_iff_map_le_one.trans ?_
  simp

中文:
引理 differentialIdeal_le_fractionalIdeal_iff
  证明: by
  rw [coeIdeal_differentIdeal A K L B]; rw [FractionalIdeal.inv_le_comm (by simp) hI]; rw [← FractionalIdeal.coe_le_coe]; rw [FractionalIdeal.coe_dual_one]
  refine le_traceDual_iff_map_le_one.trans ?_
  simp

Depends on / 依赖: FractionalIdeal, FractionalIdeal.coe_dual_one, FractionalIdeal.coe_le_coe, FractionalIdeal.inv_le_comm, coeIdeal_differentIdeal, coe_dual_one, coe_le_coe, inv_le_comm, le_traceDual_iff_map_le_one, le_traceDual_iff_map_le_one.trans
-/
lemma differentialIdeal_le_fractionalIdeal_iff
    {I : FractionalIdeal B⁰ L} (hI : I != 0) :
    differentIdeal A B <= I ↔ (((I⁻¹ :) : Submodule B L).restrictScalars A).map
      ((Algebra.trace K L).restrictScalars A) <= 1 := by
  rw [coeIdeal_differentIdeal A K L B]; rw [FractionalIdeal.inv_le_comm (by simp) hI]; rw [← FractionalIdeal.coe_le_coe]; rw [FractionalIdeal.coe_dual_one]
  refine le_traceDual_iff_map_le_one.trans ?_
  simp

/--
lemma `differentialIdeal_le_iff` / 引理 `differentialIdeal_le_iff`

English:
lemma differentialIdeal_le_iff
  given: {I : Ideal B} (hI : I != ⊥)
  proof: (FractionalIdeal.coeIdeal_le_coeIdeal _).symm.trans
    (differentialIdeal_le_fractionalIdeal_iff (I := (I : FractionalIdeal B⁰ L)) (by simpa))

中文:
引理 differentialIdeal_le_iff
  条件: {I : 理想 B} (hI : I != ⊥)
  证明: (FractionalIdeal.coeIdeal_le_coeIdeal _).symm.trans
    (differentialIdeal_le_fractionalIdeal_iff (I := (I : FractionalIdeal B⁰ L)) (by simpa))

Depends on / 依赖: FractionalIdeal, FractionalIdeal.coeIdeal_le_coeIdeal, coeIdeal_le_coeIdeal, differentialIdeal_le_fractionalIdeal_iff, symm.trans
-/
lemma differentialIdeal_le_iff {I : Ideal B} (hI : I != ⊥) :
    differentIdeal A B <= I ↔ (((I⁻¹ : FractionalIdeal B⁰ L) : Submodule B L).restrictScalars A).map
      ((Algebra.trace K L).restrictScalars A) <= 1 :=
  (FractionalIdeal.coeIdeal_le_coeIdeal _).symm.trans
    (differentialIdeal_le_fractionalIdeal_iff (I := (I : FractionalIdeal B⁰ L)) (by simpa))

variable (A K B L)

set_option linter.overlappingInstances false

open FractionalIdeal in
/--
theorem `differentIdeal_eq_differentIdeal_mul_differentIdeal` / 定理 `differentIdeal_eq_differentIdeal_mul_differentIdeal`

English:
theorem differentIdeal_eq_differentIdeal_mul_differentIdeal
  statement: (C : Type*) [IsDomain B] [CommRing C]
  proof: by
  have : Algebra.IsSeparable (FractionRing B) (FractionRing C) :=
    isSeparable_tower_top_of_isSeparable (FractionRing A) _ _
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    isSeparable_tower_bot_of_isSeparable _ _ (FractionRing C)
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  have : FiniteDimensional (FractionRing A) (FractionRing C) := .of_isLocalization A C A⁰
  have : FiniteDimensional (FractionRing B) (FractionRing C) := .of_isLocalization B C B⁰
  rw [← coeIdeal_inj (K := FractionRing C)]; rw [coeIdeal_mul]; rw [coeIdeal_differentIdeal A
    (FractionRing A)]; rw [coeIdeal_differentIdeal B (FractionRing B)]
  rw [← extendedHom_coeIdeal_eq_map (K := FractionRing B)]; rw [coeIdeal_differentIdeal A
    (FractionRing A)]; rw [map_inv₀]; rw [← mul_inv]; rw [← inv_eq_iff_eq_inv]; rw [inv_inv]
  exact dual_eq_dual_mul_dual A (FractionRing A) (FractionRing B) B C (FractionRing C)

中文:
定理 differentIdeal_eq_differentIdeal_mul_differentIdeal
  结论: (C : 类型) [是整环 B] [交换环 C]
  证明: by
  have : Algebra.IsSeparable (FractionRing B) (FractionRing C) :=
    isSeparable_tower_top_of_isSeparable (FractionRing A) _ _
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    isSeparable_tower_bot_of_isSeparable _ _ (FractionRing C)
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  have : FiniteDimensional (FractionRing A) (FractionRing C) := .of_isLocalization A C A⁰
  have : FiniteDimensional (FractionRing B) (FractionRing C) := .of_isLocalization B C B⁰
  rw [← coeIdeal_inj (K := FractionRing C)]; rw [coeIdeal_mul]; rw [coeIdeal_differentIdeal A
    (FractionRing A)]; rw [coeIdeal_differentIdeal B (FractionRing B)]
  rw [← extendedHom_coeIdeal_eq_map (K := FractionRing B)]; rw [coeIdeal_differentIdeal A
    (FractionRing A)]; rw [map_inv₀]; rw [← mul_inv]; rw [← inv_eq_iff_eq_inv]; rw [inv_inv]
  exact dual_eq_dual_mul_dual A (FractionRing A) (FractionRing B) B C (FractionRing C)

Depends on / 依赖: Algebra, Algebra.IsSeparable, FiniteDimensional, FractionRing, IsSeparable, isSeparable_tower_bot_of_isSeparable, isSeparable_tower_top_of_isSeparable, of_isLocalizat, of_isLocalization
-/
theorem differentIdeal_eq_differentIdeal_mul_differentIdeal (C : Type*) [IsDomain B] [CommRing C]
    [Algebra B C] [Algebra A C] [IsDedekindDomain C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [IsTorsionFree A C] [IsTorsionFree B C] [IsScalarTower A B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)] :
    differentIdeal A C = differentIdeal B C * (differentIdeal A B).map (algebraMap B C) := by
  have : Algebra.IsSeparable (FractionRing B) (FractionRing C) :=
    isSeparable_tower_top_of_isSeparable (FractionRing A) _ _
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    isSeparable_tower_bot_of_isSeparable _ _ (FractionRing C)
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  have : FiniteDimensional (FractionRing A) (FractionRing C) := .of_isLocalization A C A⁰
  have : FiniteDimensional (FractionRing B) (FractionRing C) := .of_isLocalization B C B⁰
  rw [← coeIdeal_inj (K := FractionRing C)]; rw [coeIdeal_mul]; rw [coeIdeal_differentIdeal A
    (FractionRing A)]; rw [coeIdeal_differentIdeal B (FractionRing B)]
  rw [← extendedHom_coeIdeal_eq_map (K := FractionRing B)]; rw [coeIdeal_differentIdeal A
    (FractionRing A)]; rw [map_inv₀]; rw [← mul_inv]; rw [← inv_eq_iff_eq_inv]; rw [inv_inv]
  exact dual_eq_dual_mul_dual A (FractionRing A) (FractionRing B) B C (FractionRing C)

variable {B L}

/--
lemma `traceForm_dualSubmodule_adjoin` / 引理 `traceForm_dualSubmodule_adjoin`

English:
lemma traceForm_dualSubmodule_adjoin
  proof: by
  have hKx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  let pb := (Algebra.adjoin.powerBasis' hKx).map
    ((Subalgebra.equivOfEq _ _ hx).trans (Subalgebra.topEquiv))
  have pbgen : pb.gen = x := by simp [pb]
  have hnondeg : (traceForm K L).Nondegenerate := traceForm_nondegenerate K L
  have hpb : ⇑(LinearMap.BilinForm.dualBasis (traceForm K L) hnondeg pb.basis) = _ :=
    _root_.funext (Basis.traceDual_powerBasis_eq pb)
  have : (Subalgebra.toSubmodule (Algebra.adjoin A {x})) =
      Submodule.span A (Set.range pb.basis) := by
    rw [← span_range_natDegree_eq_adjoin (minpoly.monic hAx) (minpoly.aeval _ _)]
    congr; ext y
    have : natDegree (minpoly A x) = natDegree (minpoly K x) := by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hAx]; rw [(minpoly.monic hAx).natDegree_map]
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio, Set.mem_range,
      pb.basis_eq_pow, pbgen]
    simp only [this]
    exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩
  clear_value pb
  conv_lhs => rw [this]
  rw [← span_coeff_minpolyDiv hAx]; rw [LinearMap.BilinForm.dualSubmodule_span_of_basis _ hnondeg]; rw [Submodule.smul_span]; rw [hpb]
  change _ = Submodule.span A (_ '' _)
  simp only [← Set.range_comp, smul_eq_mul, div_eq_inv_mul, pbgen,
    minpolyDiv_eq_of_isIntegrallyClosed K hAx]
  apply le_antisymm <;> rw [Submodule.span_le]
  · rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨i, rfl⟩
  · rintro _ ⟨i, rfl⟩
    by_cases! hi : i < pb.dim
    · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · rw [Function.comp_apply, coeff_eq_zero_of_natDegree_lt, mul_zero]
      · exact zero_mem _
      rw [← pb.natDegree_minpoly]; rw [pbgen]; rw [← natDegree_minpolyDiv_succ hKx]; rw [← Nat.succ_eq_add_one] at hi
      exact hi

中文:
引理 traceForm_dualSubmodule_adjoin
  证明: by
  have hKx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  let pb := (Algebra.adjoin.powerBasis' hKx).map
    ((Subalgebra.equivOfEq _ _ hx).trans (Subalgebra.topEquiv))
  have pbgen : pb.gen = x := by simp [pb]
  have hnondeg : (traceForm K L).Nondegenerate := traceForm_nondegenerate K L
  have hpb : ⇑(LinearMap.BilinForm.dualBasis (traceForm K L) hnondeg pb.basis) = _ :=
    _root_.funext (Basis.traceDual_powerBasis_eq pb)
  have : (Subalgebra.toSubmodule (Algebra.adjoin A {x})) =
      Submodule.span A (Set.range pb.basis) := by
    rw [← span_range_natDegree_eq_adjoin (minpoly.monic hAx) (minpoly.aeval _ _)]
    congr; ext y
    have : natDegree (minpoly A x) = natDegree (minpoly K x) := by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hAx]; rw [(minpoly.monic hAx).natDegree_map]
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio, Set.mem_range,
      pb.basis_eq_pow, pbgen]
    simp only [this]
    exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩
  clear_value pb
  conv_lhs => rw [this]
  rw [← span_coeff_minpolyDiv hAx]; rw [LinearMap.BilinForm.dualSubmodule_span_of_basis _ hnondeg]; rw [Submodule.smul_span]; rw [hpb]
  change _ = Submodule.span A (_ '' _)
  simp only [← Set.range_comp, smul_eq_mul, div_eq_inv_mul, pbgen,
    minpolyDiv_eq_of_isIntegrallyClosed K hAx]
  apply le_antisymm <;> rw [Submodule.span_le]
  · rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨i, rfl⟩
  · rintro _ ⟨i, rfl⟩
    by_cases! hi : i < pb.dim
    · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · rw [Function.comp_apply, coeff_eq_zero_of_natDegree_lt, mul_zero]
      · exact zero_mem _
      rw [← pb.natDegree_minpoly]; rw [pbgen]; rw [← natDegree_minpolyDiv_succ hKx]; rw [← Nat.succ_eq_add_one] at hi
      exact hi

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, Algebra.adjoin, Algebra.adjoin.powerBasis, Basis.traceDual_powerBasis_eq, BilinForm, IsIntegral, LinearMap, LinearMap.BilinForm.dualBasis, Nondegenerate, Set.r, Subalgebra, Subalgebra.equivOfEq, Subalgebra.toSubmodule, Subalgebra.topEquiv, Submodule, Submodule.span, _root_, _root_.funext, adjoin
-/
lemma traceForm_dualSubmodule_adjoin
    {x : L} (hx : Algebra.adjoin K {x} = ⊤) (hAx : IsIntegral A x) :
    (traceForm K L).dualSubmodule (Subalgebra.toSubmodule (Algebra.adjoin A {x})) =
      (aeval x (derivative <| minpoly K x) : L)⁻¹ •
        (Subalgebra.toSubmodule (Algebra.adjoin A {x})) := by
  have hKx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  let pb := (Algebra.adjoin.powerBasis' hKx).map
    ((Subalgebra.equivOfEq _ _ hx).trans (Subalgebra.topEquiv))
  have pbgen : pb.gen = x := by simp [pb]
  have hnondeg : (traceForm K L).Nondegenerate := traceForm_nondegenerate K L
  have hpb : ⇑(LinearMap.BilinForm.dualBasis (traceForm K L) hnondeg pb.basis) = _ :=
    _root_.funext (Basis.traceDual_powerBasis_eq pb)
  have : (Subalgebra.toSubmodule (Algebra.adjoin A {x})) =
      Submodule.span A (Set.range pb.basis) := by
    rw [← span_range_natDegree_eq_adjoin (minpoly.monic hAx) (minpoly.aeval _ _)]
    congr; ext y
    have : natDegree (minpoly A x) = natDegree (minpoly K x) := by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hAx]; rw [(minpoly.monic hAx).natDegree_map]
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio, Set.mem_range,
      pb.basis_eq_pow, pbgen]
    simp only [this]
    exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩
  clear_value pb
  conv_lhs => rw [this]
  rw [← span_coeff_minpolyDiv hAx]; rw [LinearMap.BilinForm.dualSubmodule_span_of_basis _ hnondeg]; rw [Submodule.smul_span]; rw [hpb]
  change _ = Submodule.span A (_ '' _)
  simp only [← Set.range_comp, smul_eq_mul, div_eq_inv_mul, pbgen,
    minpolyDiv_eq_of_isIntegrallyClosed K hAx]
  apply le_antisymm <;> rw [Submodule.span_le]
  · rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨i, rfl⟩
  · rintro _ ⟨i, rfl⟩
    by_cases! hi : i < pb.dim
    · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · rw [Function.comp_apply, coeff_eq_zero_of_natDegree_lt, mul_zero]
      · exact zero_mem _
      rw [← pb.natDegree_minpoly]; rw [pbgen]; rw [← natDegree_minpolyDiv_succ hKx]; rw [← Nat.succ_eq_add_one] at hi
      exact hi

end

variable (L) {B}

open Polynomial Pointwise in
/--
lemma `conductor_mul_differentIdeal` / 引理 `conductor_mul_differentIdeal`

English:
lemma conductor_mul_differentIdeal
  proof: by
  have hAx : IsIntegral A x := IsIntegralClosure.isIntegral A L x
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  apply FractionalIdeal.coeIdeal_injective (K := L)
  simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  rw [coeIdeal_differentIdeal A K L B]; rw [mul_inv_eq_iff_eq_mul₀]
  swap
  · exact FractionalIdeal.dual_ne_zero A K one_ne_zero
  apply FractionalIdeal.coeToSubmodule_injective
  simp only [FractionalIdeal.coe_coeIdeal, FractionalIdeal.coe_mul,
    FractionalIdeal.coe_spanSingleton, Submodule.span_singleton_mul]
  ext y
  have hne₁ : aeval (algebraMap B L x) (derivative (minpoly K (algebraMap B L x))) != 0 :=
    (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)
  have : algebraMap B L (aeval x (derivative (minpoly A x))) != 0 := by
    rwa [minpoly.isIntegrallyClosed_eq_field_fractions K L hAx, derivative_map,
      aeval_map_algebraMap, aeval_algebraMap_apply] at hne₁
  rw [Submodule.mem_smul_iff_inv_mul_mem this]; rw [FractionalIdeal.mem_coe]; rw [FractionalIdeal.mem_dual]; rw [mem_coeSubmodule_conductor]
  swap
  · exact one_ne_zero
  have hne₂ : (aeval (algebraMap B L x) (derivative (minpoly K (algebraMap B L x))))⁻¹ != 0 := by
    rwa [ne_eq, inv_eq_zero]
  have : IsIntegral A (algebraMap B L x) := IsIntegral.map (IsScalarTower.toAlgHom A B L) hAx
  simp_rw [← Subalgebra.mem_toSubmodule, ← Submodule.mul_mem_smul_iff (y := y * _)
    (mem_nonZeroDivisors_of_ne_zero hne₂)]
  rw [← traceForm_dualSubmodule_adjoin A K hx this]
  simp only [LinearMap.BilinForm.mem_dualSubmodule, traceForm_apply, Subalgebra.mem_toSubmodule,
    minpoly.isIntegrallyClosed_eq_field_fractions K L hAx,
    derivative_map, aeval_map_algebraMap, aeval_algebraMap_apply, mul_assoc,
    FractionalIdeal.mem_one_iff, forall_exists_index, forall_apply_eq_imp_iff]
  simp_rw [← IsScalarTower.toAlgHom_apply A B L x, ← AlgHom.map_adjoin_singleton]
  simp only [Subalgebra.mem_map, IsScalarTower.coe_toAlgHom', Submodule.one_eq_range,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, ← map_mul]
  exact ⟨fun H b => (mul_one b) ▸ H b 1 (one_mem _), fun H _ _ _ => H _⟩

中文:
引理 conductor_mul_differentIdeal
  证明: by
  have hAx : IsIntegral A x := IsIntegralClosure.isIntegral A L x
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  apply FractionalIdeal.coeIdeal_injective (K := L)
  simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  rw [coeIdeal_differentIdeal A K L B]; rw [mul_inv_eq_iff_eq_mul₀]
  swap
  · exact FractionalIdeal.dual_ne_zero A K one_ne_zero
  apply FractionalIdeal.coeToSubmodule_injective
  simp only [FractionalIdeal.coe_coeIdeal, FractionalIdeal.coe_mul,
    FractionalIdeal.coe_spanSingleton, Submodule.span_singleton_mul]
  ext y
  have hne₁ : aeval (algebraMap B L x) (derivative (minpoly K (algebraMap B L x))) != 0 :=
    (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)
  have : algebraMap B L (aeval x (derivative (minpoly A x))) != 0 := by
    rwa [minpoly.isIntegrallyClosed_eq_field_fractions K L hAx, derivative_map,
      aeval_map_algebraMap, aeval_algebraMap_apply] at hne₁
  rw [Submodule.mem_smul_iff_inv_mul_mem this]; rw [FractionalIdeal.mem_coe]; rw [FractionalIdeal.mem_dual]; rw [mem_coeSubmodule_conductor]
  swap
  · exact one_ne_zero
  have hne₂ : (aeval (algebraMap B L x) (derivative (minpoly K (algebraMap B L x))))⁻¹ != 0 := by
    rwa [ne_eq, inv_eq_zero]
  have : IsIntegral A (algebraMap B L x) := IsIntegral.map (IsScalarTower.toAlgHom A B L) hAx
  simp_rw [← Subalgebra.mem_toSubmodule, ← Submodule.mul_mem_smul_iff (y := y * _)
    (mem_nonZeroDivisors_of_ne_zero hne₂)]
  rw [← traceForm_dualSubmodule_adjoin A K hx this]
  simp only [LinearMap.BilinForm.mem_dualSubmodule, traceForm_apply, Subalgebra.mem_toSubmodule,
    minpoly.isIntegrallyClosed_eq_field_fractions K L hAx,
    derivative_map, aeval_map_algebraMap, aeval_algebraMap_apply, mul_assoc,
    FractionalIdeal.mem_one_iff, forall_exists_index, forall_apply_eq_imp_iff]
  simp_rw [← IsScalarTower.toAlgHom_apply A B L x, ← AlgHom.map_adjoin_singleton]
  simp only [Subalgebra.mem_map, IsScalarTower.coe_toAlgHom', Submodule.one_eq_range,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, ← map_mul]
  exact ⟨fun H b => (mul_one b) ▸ H b 1 (one_mem _), fun H _ _ _ => H _⟩

Depends on / 依赖: FractionalIdeal, FractionalIdeal.coeIdeal_injective, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeToSubmodule_injective, FractionalIdeal.coe_, FractionalIdeal.coe_coeIdeal, FractionalIdeal.dual_ne_zero, IsIntegral, IsIntegralClosure, IsIntegralClosure.isFractionRing_of_finite_extension, IsIntegralClosure.isIntegral, coeIdeal_differentIdeal, coeIdeal_injective, coeIdeal_mul, coeIdeal_span_singleton, coeToSubmodule_injective, coe_, coe_coeIdeal, dual_ne_zero
-/
lemma conductor_mul_differentIdeal
    (x : B) (hx : Algebra.adjoin K {algebraMap B L x} = ⊤) :
    (conductor A x) * differentIdeal A B = Ideal.span {aeval x (derivative (minpoly A x))} := by
  have hAx : IsIntegral A x := IsIntegralClosure.isIntegral A L x
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  apply FractionalIdeal.coeIdeal_injective (K := L)
  simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  rw [coeIdeal_differentIdeal A K L B]; rw [mul_inv_eq_iff_eq_mul₀]
  swap
  · exact FractionalIdeal.dual_ne_zero A K one_ne_zero
  apply FractionalIdeal.coeToSubmodule_injective
  simp only [FractionalIdeal.coe_coeIdeal, FractionalIdeal.coe_mul,
    FractionalIdeal.coe_spanSingleton, Submodule.span_singleton_mul]
  ext y
  have hne₁ : aeval (algebraMap B L x) (derivative (minpoly K (algebraMap B L x))) != 0 :=
    (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)
  have : algebraMap B L (aeval x (derivative (minpoly A x))) != 0 := by
    rwa [minpoly.isIntegrallyClosed_eq_field_fractions K L hAx, derivative_map,
      aeval_map_algebraMap, aeval_algebraMap_apply] at hne₁
  rw [Submodule.mem_smul_iff_inv_mul_mem this]; rw [FractionalIdeal.mem_coe]; rw [FractionalIdeal.mem_dual]; rw [mem_coeSubmodule_conductor]
  swap
  · exact one_ne_zero
  have hne₂ : (aeval (algebraMap B L x) (derivative (minpoly K (algebraMap B L x))))⁻¹ != 0 := by
    rwa [ne_eq, inv_eq_zero]
  have : IsIntegral A (algebraMap B L x) := IsIntegral.map (IsScalarTower.toAlgHom A B L) hAx
  simp_rw [← Subalgebra.mem_toSubmodule, ← Submodule.mul_mem_smul_iff (y := y * _)
    (mem_nonZeroDivisors_of_ne_zero hne₂)]
  rw [← traceForm_dualSubmodule_adjoin A K hx this]
  simp only [LinearMap.BilinForm.mem_dualSubmodule, traceForm_apply, Subalgebra.mem_toSubmodule,
    minpoly.isIntegrallyClosed_eq_field_fractions K L hAx,
    derivative_map, aeval_map_algebraMap, aeval_algebraMap_apply, mul_assoc,
    FractionalIdeal.mem_one_iff, forall_exists_index, forall_apply_eq_imp_iff]
  simp_rw [← IsScalarTower.toAlgHom_apply A B L x, ← AlgHom.map_adjoin_singleton]
  simp only [Subalgebra.mem_map, IsScalarTower.coe_toAlgHom', Submodule.one_eq_range,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, ← map_mul]
  exact ⟨fun H b => (mul_one b) ▸ H b 1 (one_mem _), fun H _ _ _ => H _⟩

open Polynomial Pointwise in
/--
lemma `aeval_derivative_mem_differentIdeal` / 引理 `aeval_derivative_mem_differentIdeal`

English:
lemma aeval_derivative_mem_differentIdeal
  proof: by
  refine SetLike.le_def.mp ?_ (Ideal.mem_span_singleton_self _)
  rw [← conductor_mul_differentIdeal A K L x hx]
  exact Ideal.mul_le_right

中文:
引理 aeval_derivative_mem_differentIdeal
  证明: by
  refine SetLike.le_def.mp ?_ (Ideal.mem_span_singleton_self _)
  rw [← conductor_mul_differentIdeal A K L x hx]
  exact Ideal.mul_le_right

Depends on / 依赖: Ideal.mem_span_singleton_self, Ideal.mul_le_right, SetLike, SetLike.le_def.mp, conductor_mul_differentIdeal, le_def, mem_span_singleton_self, mul_le_right
-/
lemma aeval_derivative_mem_differentIdeal
    (x : B) (hx : Algebra.adjoin K {algebraMap B L x} = ⊤) :
    aeval x (derivative (minpoly A x)) in differentIdeal A B := by
  refine SetLike.le_def.mp ?_ (Ideal.mem_span_singleton_self _)
  rw [← conductor_mul_differentIdeal A K L x hx]
  exact Ideal.mul_le_right

end IsIntegrallyClosed
section

variable (L)
variable [IsFractionRing B L] [IsDedekindDomain A] [IsDedekindDomain B]
  [IsTorsionFree A B] [Module.Finite A B]

set_option linter.overlappingInstances false

include K L in
/--
lemma `pow_sub_one_dvd_differentIdeal_aux` / 引理 `pow_sub_one_dvd_differentIdeal_aux`

English:
lemma pow_sub_one_dvd_differentIdeal_aux
  proof: by
  obtain ⟨a, ha⟩ := (pow_dvd_pow _ (Nat.sub_le e 1)).trans hP
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have habot : a != ⊥ := fun ha' => hp' (by simpa [ha'] using ha)
  have hPbot : P != ⊥ := by
    rintro rfl; apply hp'
    rwa [← Ideal.zero_eq_bot, zero_pow he, zero_dvd_iff, Ideal.zero_eq_bot] at hP
  have : p.map (algebraMap A B) ∣ a ^ e := by
    obtain ⟨b, hb⟩ := hP
    apply_fun (· ^ e : Ideal B -> _) at ha
    apply_fun (· ^ (e - 1) : Ideal B -> _) at hb
    simp only [mul_pow, ← pow_mul, mul_comm e] at ha hb
    conv_lhs at ha => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he)]
    rw [pow_add]; rw [hb]; rw [mul_assoc]; rw [mul_right_inj' (pow_ne_zero _ hPbot)]; rw [pow_one]; rw [mul_comm] at ha
    exact ⟨_, ha.symm⟩
  suffices forall x in a, intTrace A B x in p by
    have hP : ((P ^ (e - 1) :)⁻¹ : FractionalIdeal B⁰ L) = a / p.map (algebraMap A B) := by
      apply inv_involutive.injective
      simp only [inv_inv, ha, FractionalIdeal.coeIdeal_mul, inv_div,
          mul_div_assoc]
      rw [div_self (by simpa)]; rw [mul_one]
    rw [Ideal.dvd_iff_le]; rw [differentialIdeal_le_iff (K := K) (L := L) (pow_ne_zero _ hPbot)]; rw [hP]; rw [Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.restrictScalars_mem]; rw [FractionalIdeal.mem_coe]; rw [FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp')] at hx
    rw [Submodule.mem_comap]; rw [LinearMap.coe_restrictScalars]; rw [← FractionalIdeal.coe_one]; rw [← div_self (G₀ := FractionalIdeal A⁰ K) (a := p) (by simpa using hp)]; rw [FractionalIdeal.mem_coe]; rw [FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp)]
    simp only [FractionalIdeal.mem_coeIdeal, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hx
    intro y hy'
    obtain ⟨y, hy, rfl : algebraMap A K _ = _⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy'
    obtain ⟨z, hz, hz'⟩ := hx _ (Ideal.mem_map_of_mem _ hy)
    have : trace K L (algebraMap B L z) in (p : FractionalIdeal A⁰ K) := by
      rw [← algebraMap_intTrace (A := A)]
      exact ⟨intTrace A B z, this z hz, rfl⟩
    rwa [mul_comm, ← smul_eq_mul, ← map_smul, Algebra.smul_def, mul_comm,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L, ← hz']
  intro x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem]; rw [← trace_quotient_eq_of_isDedekindDomain]; rw [← isNilpotent_iff_eq_zero]
  refine isNilpotent_trace_of_isNilpotent ⟨e, ?_⟩
  rw [← map_pow]; rw [Ideal.Quotient.eq_zero_iff_mem]
exact (Ideal.dvd_iff_le.mp this) Ideal.pow_mem_pow hx _

中文:
引理 pow_sub_one_dvd_differentIdeal_aux
  证明: by
  obtain ⟨a, ha⟩ := (pow_dvd_pow _ (Nat.sub_le e 1)).trans hP
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have habot : a != ⊥ := fun ha' => hp' (by simpa [ha'] using ha)
  have hPbot : P != ⊥ := by
    rintro rfl; apply hp'
    rwa [← Ideal.zero_eq_bot, zero_pow he, zero_dvd_iff, Ideal.zero_eq_bot] at hP
  have : p.map (algebraMap A B) ∣ a ^ e := by
    obtain ⟨b, hb⟩ := hP
    apply_fun (· ^ e : Ideal B -> _) at ha
    apply_fun (· ^ (e - 1) : Ideal B -> _) at hb
    simp only [mul_pow, ← pow_mul, mul_comm e] at ha hb
    conv_lhs at ha => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he)]
    rw [pow_add]; rw [hb]; rw [mul_assoc]; rw [mul_right_inj' (pow_ne_zero _ hPbot)]; rw [pow_one]; rw [mul_comm] at ha
    exact ⟨_, ha.symm⟩
  suffices forall x in a, intTrace A B x in p by
    have hP : ((P ^ (e - 1) :)⁻¹ : FractionalIdeal B⁰ L) = a / p.map (algebraMap A B) := by
      apply inv_involutive.injective
      simp only [inv_inv, ha, FractionalIdeal.coeIdeal_mul, inv_div,
          mul_div_assoc]
      rw [div_self (by simpa)]; rw [mul_one]
    rw [Ideal.dvd_iff_le]; rw [differentialIdeal_le_iff (K := K) (L := L) (pow_ne_zero _ hPbot)]; rw [hP]; rw [Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.restrictScalars_mem]; rw [FractionalIdeal.mem_coe]; rw [FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp')] at hx
    rw [Submodule.mem_comap]; rw [LinearMap.coe_restrictScalars]; rw [← FractionalIdeal.coe_one]; rw [← div_self (G₀ := FractionalIdeal A⁰ K) (a := p) (by simpa using hp)]; rw [FractionalIdeal.mem_coe]; rw [FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp)]
    simp only [FractionalIdeal.mem_coeIdeal, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hx
    intro y hy'
    obtain ⟨y, hy, rfl : algebraMap A K _ = _⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy'
    obtain ⟨z, hz, hz'⟩ := hx _ (Ideal.mem_map_of_mem _ hy)
    have : trace K L (algebraMap B L z) in (p : FractionalIdeal A⁰ K) := by
      rw [← algebraMap_intTrace (A := A)]
      exact ⟨intTrace A B z, this z hz, rfl⟩
    rwa [mul_comm, ← smul_eq_mul, ← map_smul, Algebra.smul_def, mul_comm,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L, ← hz']
  intro x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem]; rw [← trace_quotient_eq_of_isDedekindDomain]; rw [← isNilpotent_iff_eq_zero]
  refine isNilpotent_trace_of_isNilpotent ⟨e, ?_⟩
  rw [← map_pow]; rw [Ideal.Quotient.eq_zero_iff_mem]
exact (Ideal.dvd_iff_le.mp this) Ideal.pow_mem_pow hx _

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Ideal.map_eq_bot_iff_of_injective, Ideal.zero_eq_bot, Nat.sub_le, algebraMap, algebraMap_injective, apply_fun, map_eq_bot_iff_of_injective, not.mpr, p.map, pow_dvd_pow, sub_le, zero_dvd_iff, zero_eq_bot, zero_pow
-/
lemma pow_sub_one_dvd_differentIdeal_aux
    {p : Ideal A} [p.IsMaximal] (P : Ideal B) {e : Nat} (he : e != 0) (hp : p != ⊥)
    (hP : P ^ e ∣ p.map (algebraMap A B)) : P ^ (e - 1) ∣ differentIdeal A B := by
  obtain ⟨a, ha⟩ := (pow_dvd_pow _ (Nat.sub_le e 1)).trans hP
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have habot : a != ⊥ := fun ha' => hp' (by simpa [ha'] using ha)
  have hPbot : P != ⊥ := by
    rintro rfl; apply hp'
    rwa [← Ideal.zero_eq_bot, zero_pow he, zero_dvd_iff, Ideal.zero_eq_bot] at hP
  have : p.map (algebraMap A B) ∣ a ^ e := by
    obtain ⟨b, hb⟩ := hP
    apply_fun (· ^ e : Ideal B -> _) at ha
    apply_fun (· ^ (e - 1) : Ideal B -> _) at hb
    simp only [mul_pow, ← pow_mul, mul_comm e] at ha hb
    conv_lhs at ha => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he)]
    rw [pow_add]; rw [hb]; rw [mul_assoc]; rw [mul_right_inj' (pow_ne_zero _ hPbot)]; rw [pow_one]; rw [mul_comm] at ha
    exact ⟨_, ha.symm⟩
  suffices forall x in a, intTrace A B x in p by
    have hP : ((P ^ (e - 1) :)⁻¹ : FractionalIdeal B⁰ L) = a / p.map (algebraMap A B) := by
      apply inv_involutive.injective
      simp only [inv_inv, ha, FractionalIdeal.coeIdeal_mul, inv_div,
          mul_div_assoc]
      rw [div_self (by simpa)]; rw [mul_one]
    rw [Ideal.dvd_iff_le]; rw [differentialIdeal_le_iff (K := K) (L := L) (pow_ne_zero _ hPbot)]; rw [hP]; rw [Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.restrictScalars_mem]; rw [FractionalIdeal.mem_coe]; rw [FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp')] at hx
    rw [Submodule.mem_comap]; rw [LinearMap.coe_restrictScalars]; rw [← FractionalIdeal.coe_one]; rw [← div_self (G₀ := FractionalIdeal A⁰ K) (a := p) (by simpa using hp)]; rw [FractionalIdeal.mem_coe]; rw [FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp)]
    simp only [FractionalIdeal.mem_coeIdeal, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hx
    intro y hy'
    obtain ⟨y, hy, rfl : algebraMap A K _ = _⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy'
    obtain ⟨z, hz, hz'⟩ := hx _ (Ideal.mem_map_of_mem _ hy)
    have : trace K L (algebraMap B L z) in (p : FractionalIdeal A⁰ K) := by
      rw [← algebraMap_intTrace (A := A)]
      exact ⟨intTrace A B z, this z hz, rfl⟩
    rwa [mul_comm, ← smul_eq_mul, ← map_smul, Algebra.smul_def, mul_comm,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L, ← hz']
  intro x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem]; rw [← trace_quotient_eq_of_isDedekindDomain]; rw [← isNilpotent_iff_eq_zero]
  refine isNilpotent_trace_of_isNilpotent ⟨e, ?_⟩
  rw [← map_pow]; rw [Ideal.Quotient.eq_zero_iff_mem]
exact (Ideal.dvd_iff_le.mp this) Ideal.pow_mem_pow hx _

/--
lemma `pow_sub_one_dvd_differentIdeal` / 引理 `pow_sub_one_dvd_differentIdeal`

English:
lemma pow_sub_one_dvd_differentIdeal
  statement: [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
  proof: by
  have : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  by_cases he : e = 0
  · rw [he, pow_zero]; exact one_dvd _
  exact pow_sub_one_dvd_differentIdeal_aux A (FractionRing A) (FractionRing B) _ he hp hP

中文:
引理 pow_sub_one_dvd_differentIdeal
  结论: [代数.是可分 (FractionRing A) (FractionRing B)]
  证明: by
  have : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  by_cases he : e = 0
  · rw [he, pow_zero]; exact one_dvd _
  exact pow_sub_one_dvd_differentIdeal_aux A (FractionRing A) (FractionRing B) _ he hp hP

Depends on / 依赖: FiniteDimensional, FractionRing, IsIntegralClosure, IsIntegralClosure.isLocalization, IsLocalization, algebraMapSubmonoid, isLocalization, of_isLocalization, one_dvd, pow_sub_one_dvd_differentIdeal_aux, pow_zero
-/
lemma pow_sub_one_dvd_differentIdeal [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] (P : Ideal B) (e : Nat) (hp : p != ⊥)
    (hP : P ^ e ∣ p.map (algebraMap A B)) : P ^ (e - 1) ∣ differentIdeal A B := by
  have : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  by_cases he : e = 0
  · rw [he, pow_zero]; exact one_dvd _
  exact pow_sub_one_dvd_differentIdeal_aux A (FractionRing A) (FractionRing B) _ he hp hP

/--
theorem `not_dvd_differentIdeal_of_intTrace_not_mem` / 定理 `not_dvd_differentIdeal_of_intTrace_not_mem`

English:
theorem not_dvd_differentIdeal_of_intTrace_not_mem
  proof: by
  by_cases hp : p = ⊥
  · subst hp
    simp only [Ideal.map_bot, Ideal.mul_eq_bot] at hP
    obtain (rfl | rfl) := hP
    · rw [← Ideal.zero_eq_bot, zero_dvd_iff]
      exact differentIdeal_ne_bot
    · obtain rfl := hxQ
      simp at hx
  let : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap]; rw [← hP]
      exact Ideal.mul_le_right)
  let K := FractionRing A
  let L := FractionRing B
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization _ K _ _
  have : FiniteDimensional K L := .of_isLocalization A B A⁰
  rw [Ideal.dvd_iff_le]
  intro H
  replace H := (mul_le_mul_left H Q).trans_eq hP
  replace H := (FractionalIdeal.coeIdeal_le_coeIdeal' _ (P := L) le_rfl).mpr H
  rw [FractionalIdeal.coeIdeal_mul]; rw [coeIdeal_differentIdeal A K] at H
  replace H := mul_le_mul_right H (FractionalIdeal.dual A K 1)
  have hne : (1 : FractionalIdeal B⁰ L) != 0 := one_ne_zero
  rw [mul_inv_cancel_left₀ (FractionalIdeal.dual_ne_zero A K hne)] at H
  apply hx
  suffices Algebra.trace K L (algebraMap B L x) in (p : FractionalIdeal A⁰ K) by
    obtain ⟨y, hy, e⟩ := this
    rw [← Algebra.algebraMap_intTrace (A := A)]; rw [Algebra.linearMap_apply]; rw [(IsLocalization.injective _ le_rfl).eq_iff] at e
    exact e ▸ hy
  refine FractionalIdeal.mul_induction_on (H ⟨_, hxQ, rfl⟩) ?_ ?_
  · rintro x hx _ ⟨y, hy, rfl⟩
    induction hy using Submodule.span_induction generalizing x with
    | mem y h =>
      obtain ⟨y, hy, rfl⟩ := h
      obtain ⟨z, hz⟩ :=
        (FractionalIdeal.mem_dual (by simp)).mp hx 1 ⟨1, trivial, (algebraMap B L).map_one⟩
      simp only [Algebra.traceForm_apply, mul_one] at hz
      refine ⟨z * y, Ideal.mul_mem_left _ _ hy, ?_⟩
      rw [Algebra.linearMap_apply]; rw [Algebra.linearMap_apply]; rw [mul_comm x]; rw [← IsScalarTower.algebraMap_apply]; rw [← Algebra.smul_def]; rw [LinearMap.map_smul_of_tower]; rw [← hz]; rw [Algebra.smul_def]; rw [map_mul]; rw [mul_comm]
    | zero => simp
    | add y z _ _ hy hz =>
      simp only [map_add, mul_add]
      exact Submodule.add_mem _ (hy x hx) (hz x hx)
    | smul y z hz IH =>
      simpa [Algebra.smul_def, mul_assoc, -FractionalIdeal.mem_coeIdeal, mul_left_comm x] using
        IH _ (Submodule.smul_mem _ y hx)
  · simp only [map_add]
    exact fun _ _ h₁ h₂ => Submodule.add_mem _ h₁ h₂

中文:
定理 not_dvd_differentIdeal_of_intTrace_not_mem
  证明: by
  by_cases hp : p = ⊥
  · subst hp
    simp only [Ideal.map_bot, Ideal.mul_eq_bot] at hP
    obtain (rfl | rfl) := hP
    · rw [← Ideal.zero_eq_bot, zero_dvd_iff]
      exact differentIdeal_ne_bot
    · obtain rfl := hxQ
      simp at hx
  let : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap]; rw [← hP]
      exact Ideal.mul_le_right)
  let K := FractionRing A
  let L := FractionRing B
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization _ K _ _
  have : FiniteDimensional K L := .of_isLocalization A B A⁰
  rw [Ideal.dvd_iff_le]
  intro H
  replace H := (mul_le_mul_left H Q).trans_eq hP
  replace H := (FractionalIdeal.coeIdeal_le_coeIdeal' _ (P := L) le_rfl).mpr H
  rw [FractionalIdeal.coeIdeal_mul]; rw [coeIdeal_differentIdeal A K] at H
  replace H := mul_le_mul_right H (FractionalIdeal.dual A K 1)
  have hne : (1 : FractionalIdeal B⁰ L) != 0 := one_ne_zero
  rw [mul_inv_cancel_left₀ (FractionalIdeal.dual_ne_zero A K hne)] at H
  apply hx
  suffices Algebra.trace K L (algebraMap B L x) in (p : FractionalIdeal A⁰ K) by
    obtain ⟨y, hy, e⟩ := this
    rw [← Algebra.algebraMap_intTrace (A := A)]; rw [Algebra.linearMap_apply]; rw [(IsLocalization.injective _ le_rfl).eq_iff] at e
    exact e ▸ hy
  refine FractionalIdeal.mul_induction_on (H ⟨_, hxQ, rfl⟩) ?_ ?_
  · rintro x hx _ ⟨y, hy, rfl⟩
    induction hy using Submodule.span_induction generalizing x with
    | mem y h =>
      obtain ⟨y, hy, rfl⟩ := h
      obtain ⟨z, hz⟩ :=
        (FractionalIdeal.mem_dual (by simp)).mp hx 1 ⟨1, trivial, (algebraMap B L).map_one⟩
      simp only [Algebra.traceForm_apply, mul_one] at hz
      refine ⟨z * y, Ideal.mul_mem_left _ _ hy, ?_⟩
      rw [Algebra.linearMap_apply]; rw [Algebra.linearMap_apply]; rw [mul_comm x]; rw [← IsScalarTower.algebraMap_apply]; rw [← Algebra.smul_def]; rw [LinearMap.map_smul_of_tower]; rw [← hz]; rw [Algebra.smul_def]; rw [map_mul]; rw [mul_comm]
    | zero => simp
    | add y z _ _ hy hz =>
      simp only [map_add, mul_add]
      exact Submodule.add_mem _ (hy x hx) (hz x hx)
    | smul y z hz IH =>
      simpa [Algebra.smul_def, mul_assoc, -FractionalIdeal.mem_coeIdeal, mul_left_comm x] using
        IH _ (Submodule.smul_mem _ y hx)
  · simp only [map_add]
    exact fun _ _ h₁ h₂ => Submodule.add_mem _ h₁ h₂

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, FractionRing, Ideal.Quotient.algebraQuotientOfLEComap, Ideal.map_bot, Ideal.map_le_iff_le_comap, Ideal.mul_eq_bot, Ideal.mul_le_right, Ideal.zero_eq_bot, IsIntegralClosure, IsIntegralClosure.isLocalization, IsLocalization, Quotient, algebraMapSubmonoid, algebraQuotientOfLEComap, differentIdeal_ne_bot, isLocalization, map_bot, map_le_iff_le_comap, mul_eq_bot
-/
theorem not_dvd_differentIdeal_of_intTrace_not_mem
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} (P Q : Ideal B) (hP : P * Q = Ideal.map (algebraMap A B) p)
    (x : B) (hxQ : x in Q) (hx : Algebra.intTrace A B x ∉ p) :
    ¬ P ∣ differentIdeal A B := by
  by_cases hp : p = ⊥
  · subst hp
    simp only [Ideal.map_bot, Ideal.mul_eq_bot] at hP
    obtain (rfl | rfl) := hP
    · rw [← Ideal.zero_eq_bot, zero_dvd_iff]
      exact differentIdeal_ne_bot
    · obtain rfl := hxQ
      simp at hx
  let : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap]; rw [← hP]
      exact Ideal.mul_le_right)
  let K := FractionRing A
  let L := FractionRing B
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization _ K _ _
  have : FiniteDimensional K L := .of_isLocalization A B A⁰
  rw [Ideal.dvd_iff_le]
  intro H
  replace H := (mul_le_mul_left H Q).trans_eq hP
  replace H := (FractionalIdeal.coeIdeal_le_coeIdeal' _ (P := L) le_rfl).mpr H
  rw [FractionalIdeal.coeIdeal_mul]; rw [coeIdeal_differentIdeal A K] at H
  replace H := mul_le_mul_right H (FractionalIdeal.dual A K 1)
  have hne : (1 : FractionalIdeal B⁰ L) != 0 := one_ne_zero
  rw [mul_inv_cancel_left₀ (FractionalIdeal.dual_ne_zero A K hne)] at H
  apply hx
  suffices Algebra.trace K L (algebraMap B L x) in (p : FractionalIdeal A⁰ K) by
    obtain ⟨y, hy, e⟩ := this
    rw [← Algebra.algebraMap_intTrace (A := A)]; rw [Algebra.linearMap_apply]; rw [(IsLocalization.injective _ le_rfl).eq_iff] at e
    exact e ▸ hy
  refine FractionalIdeal.mul_induction_on (H ⟨_, hxQ, rfl⟩) ?_ ?_
  · rintro x hx _ ⟨y, hy, rfl⟩
    induction hy using Submodule.span_induction generalizing x with
    | mem y h =>
      obtain ⟨y, hy, rfl⟩ := h
      obtain ⟨z, hz⟩ :=
        (FractionalIdeal.mem_dual (by simp)).mp hx 1 ⟨1, trivial, (algebraMap B L).map_one⟩
      simp only [Algebra.traceForm_apply, mul_one] at hz
      refine ⟨z * y, Ideal.mul_mem_left _ _ hy, ?_⟩
      rw [Algebra.linearMap_apply]; rw [Algebra.linearMap_apply]; rw [mul_comm x]; rw [← IsScalarTower.algebraMap_apply]; rw [← Algebra.smul_def]; rw [LinearMap.map_smul_of_tower]; rw [← hz]; rw [Algebra.smul_def]; rw [map_mul]; rw [mul_comm]
    | zero => simp
    | add y z _ _ hy hz =>
      simp only [map_add, mul_add]
      exact Submodule.add_mem _ (hy x hx) (hz x hx)
    | smul y z hz IH =>
      simpa [Algebra.smul_def, mul_assoc, -FractionalIdeal.mem_coeIdeal, mul_left_comm x] using
        IH _ (Submodule.smul_mem _ y hx)
  · simp only [map_add]
    exact fun _ _ h₁ h₂ => Submodule.add_mem _ h₁ h₂

open nonZeroDivisors

/--
theorem `not_dvd_differentIdeal_of_isCoprime_of_isSeparable` / 定理 `not_dvd_differentIdeal_of_isCoprime_of_isSeparable`

English:
theorem not_dvd_differentIdeal_of_isCoprime_of_isSeparable
  proof: by
  let : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap]; rw [← hP]
      exact Ideal.mul_le_right)
  have : IsScalarTower A (A ⧸ p) (B ⧸ Q) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ Q)
  let e : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p] ((B ⧸ P) × B ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hP.symm).trans (Ideal.quotientMulEquivQuotientProd P Q hPQ),
      commutes' := Quotient.ind fun _ => rfl }
  obtain ⟨x, hx⟩ : exists x, Algebra.trace (A ⧸ p) (B ⧸ P) x != 0 := by
    simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero (A ⧸ p) (B ⧸ P)
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e.symm (x, 0))
  refine not_dvd_differentIdeal_of_intTrace_not_mem A P Q hP y ?_ ?_
  · have := congr((e $hy).2)
    simp at this
    simpa [e, Ideal.Quotient.eq_zero_iff_mem] using this
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain,
      hy, Algebra.trace_eq_of_algEquiv, Algebra.trace_prod_apply]
    simpa

中文:
定理 not_dvd_differentIdeal_of_isCoprime_of_isSeparable
  证明: by
  let : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap]; rw [← hP]
      exact Ideal.mul_le_right)
  have : IsScalarTower A (A ⧸ p) (B ⧸ Q) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ Q)
  let e : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p] ((B ⧸ P) × B ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hP.symm).trans (Ideal.quotientMulEquivQuotientProd P Q hPQ),
      commutes' := Quotient.ind fun _ => rfl }
  obtain ⟨x, hx⟩ : exists x, Algebra.trace (A ⧸ p) (B ⧸ P) x != 0 := by
    simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero (A ⧸ p) (B ⧸ P)
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e.symm (x, 0))
  refine not_dvd_differentIdeal_of_intTrace_not_mem A P Q hP y ?_ ?_
  · have := congr((e $hy).2)
    simp at this
    simpa [e, Ideal.Quotient.eq_zero_iff_mem] using this
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain,
      hy, Algebra.trace_eq_of_algEquiv, Algebra.trace_prod_apply]
    simpa

Depends on / 依赖: Algebra, Finite, Ideal.Quotient.algebraQuotientOfLEComap, Ideal.map_le_iff_le_comap, Ideal.mul_le_right, Ideal.quotEquivOfEq, Ideal.quotientMulEquivQuotientProd, IsScalarTower, Module, Module.Finite, Module.Finite.of_restrictScalars_finite, Quotient, Quotient.ind, algebraMap, algebraQuotientOfLEComap, commutes, hP.symm, map_le_iff_le_comap, mul_le_right, of_algebraMap_eq
-/
theorem not_dvd_differentIdeal_of_isCoprime_of_isSeparable
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] (P Q : Ideal B) [P.IsMaximal] [P.LiesOver p]
    (hPQ : IsCoprime P Q) (hP : P * Q = Ideal.map (algebraMap A B) p)
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] :
    ¬ P ∣ differentIdeal A B := by
  let : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap]; rw [← hP]
      exact Ideal.mul_le_right)
  have : IsScalarTower A (A ⧸ p) (B ⧸ Q) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ Q)
  let e : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p] ((B ⧸ P) × B ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hP.symm).trans (Ideal.quotientMulEquivQuotientProd P Q hPQ),
      commutes' := Quotient.ind fun _ => rfl }
  obtain ⟨x, hx⟩ : exists x, Algebra.trace (A ⧸ p) (B ⧸ P) x != 0 := by
    simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero (A ⧸ p) (B ⧸ P)
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e.symm (x, 0))
  refine not_dvd_differentIdeal_of_intTrace_not_mem A P Q hP y ?_ ?_
  · have := congr((e $hy).2)
    simp at this
    simpa [e, Ideal.Quotient.eq_zero_iff_mem] using this
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain,
      hy, Algebra.trace_eq_of_algEquiv, Algebra.trace_prod_apply]
    simpa

/--
theorem `not_dvd_differentIdeal_of_isCoprime` / 定理 `not_dvd_differentIdeal_of_isCoprime`

English:
theorem not_dvd_differentIdeal_of_isCoprime
  proof: by
  have : P.LiesOver p := by
    constructor
    refine ‹p.IsMaximal›.eq_of_le ?_ ?_
    · simpa using ‹P.IsMaximal›.ne_top
    · rw [← Ideal.map_le_iff_le_comap, ← hP]
      exact Ideal.mul_le_left
  exact not_dvd_differentIdeal_of_isCoprime_of_isSeparable A P Q hPQ hP

中文:
定理 not_dvd_differentIdeal_of_isCoprime
  证明: by
  have : P.LiesOver p := by
    constructor
    refine ‹p.IsMaximal›.eq_of_le ?_ ?_
    · simpa using ‹P.IsMaximal›.ne_top
    · rw [← Ideal.map_le_iff_le_comap, ← hP]
      exact Ideal.mul_le_left
  exact not_dvd_differentIdeal_of_isCoprime_of_isSeparable A P Q hPQ hP

Depends on / 依赖: Ideal.map_le_iff_le_comap, Ideal.mul_le_left, IsMaximal, LiesOver, P.IsMaximal, P.LiesOver, eq_of_le, map_le_iff_le_comap, mul_le_left, ne_top, not_dvd_differentIdeal_of_isCoprime_of_isSeparable, p.IsMaximal
-/
theorem not_dvd_differentIdeal_of_isCoprime
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] [Finite (A ⧸ p)] (P Q : Ideal B) [P.IsMaximal]
    (hPQ : IsCoprime P Q) (hP : P * Q = Ideal.map (algebraMap A B) p) :
    ¬ P ∣ differentIdeal A B := by
  have : P.LiesOver p := by
    constructor
    refine ‹p.IsMaximal›.eq_of_le ?_ ?_
    · simpa using ‹P.IsMaximal›.ne_top
    · rw [← Ideal.map_le_iff_le_comap, ← hP]
      exact Ideal.mul_le_left
  exact not_dvd_differentIdeal_of_isCoprime_of_isSeparable A P Q hPQ hP

/--
lemma `dvd_differentIdeal_of_not_isSeparable` / 引理 `dvd_differentIdeal_of_not_isSeparable`

English:
lemma dvd_differentIdeal_of_not_isSeparable
  proof: by
  obtain ⟨a, ha⟩ : P ∣ p.map (algebraMap A B) :=
    Ideal.dvd_iff_le.mpr (Ideal.map_le_iff_le_comap.mpr Ideal.LiesOver.over.le)
  by_cases hPa : P ∣ a
  · simpa using pow_sub_one_dvd_differentIdeal A P 2 hp
      (by rw [pow_two, ha]; exact mul_dvd_mul_left _ hPa)
  let K := FractionRing A
  let L := FractionRing B
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have habot : a != ⊥ := fun ha' => hp' (by simpa [ha'] using ha)
  have hPbot : P != ⊥ := by
    rintro rfl; apply hp'
    rwa [Ideal.bot_mul] at ha
  suffices forall x in a, Algebra.intTrace A B x in p by
    have hP : ((P :)⁻¹ : FractionalIdeal B⁰ L) = a / p.map (algebraMap A B) := by
      apply inv_involutive.injective
      simp only [ha, FractionalIdeal.coeIdeal_mul, inv_div, mul_div_assoc]
      rw [div_self (by simpa)]; rw [mul_one]; rw [inv_inv]
    rw [Ideal.dvd_iff_le]; rw [differentialIdeal_le_iff (K := K) (L := L) hPbot]; rw [hP]; rw [Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.restrictScalars_mem]; rw [FractionalIdeal.mem_coe]; rw [FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp')] at hx
    rw [Submodule.mem_comap]; rw [LinearMap.coe_restrictScalars]; rw [← FractionalIdeal.coe_one]; rw [← div_self (G₀ := FractionalIdeal A⁰ K) (a := p) (by simpa using hp)]; rw [FractionalIdeal.mem_coe]; rw [FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp)]
    simp only [FractionalIdeal.mem_coeIdeal, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hx
    intro y hy'
    obtain ⟨y, hy, rfl : algebraMap A K _ = _⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy'
    obtain ⟨z, hz, hz'⟩ := hx _ (Ideal.mem_map_of_mem _ hy)
    have : Algebra.trace K L (algebraMap B L z) in (p : FractionalIdeal A⁰ K) := by
      rw [← Algebra.algebraMap_intTrace (A := A)]
      exact ⟨Algebra.intTrace A B z, this z hz, rfl⟩
    rwa [mul_comm, ← smul_eq_mul, ← map_smul, Algebra.smul_def, mul_comm,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L, ← hz']
  intro x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem]; rw [← Algebra.trace_quotient_eq_of_isDedekindDomain]
  let : Algebra (A ⧸ p) (B ⧸ a) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp
      (Ideal.dvd_iff_le.mp ⟨_, ha.trans (mul_comm _ _)⟩))
  have : IsScalarTower A (A ⧸ p) (B ⧸ a) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ a) := .of_restrictScalars_finite A _ _
  have := ((Ideal.prime_iff_isPrime hPbot).mpr inferInstance)
  rw [← this.irreducible.gcd_eq_one_iff]; rw [← Ideal.isCoprime_iff_gcd] at hPa
  let e : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p] ((B ⧸ P) × B ⧸ a) :=
    { __ := (Ideal.quotEquivOfEq ha).trans (Ideal.quotientMulEquivQuotientProd P a hPa),
      commutes' := Quotient.ind fun _ => rfl }
  have hx' : (e (Ideal.Quotient.mk _ x)).2 = 0 := by
    simpa [e, Ideal.Quotient.eq_zero_iff_mem]
  rw [← Algebra.trace_eq_of_algEquiv e]; rw [Algebra.trace_prod_apply]; rw [Algebra.trace_eq_zero_of_not_isSeparable H]; rw [LinearMap.zero_apply]; rw [zero_add]; rw [hx']; rw [map_zero]

中文:
引理 dvd_differentIdeal_of_not_isSeparable
  证明: by
  obtain ⟨a, ha⟩ : P ∣ p.map (algebraMap A B) :=
    Ideal.dvd_iff_le.mpr (Ideal.map_le_iff_le_comap.mpr Ideal.LiesOver.over.le)
  by_cases hPa : P ∣ a
  · simpa using pow_sub_one_dvd_differentIdeal A P 2 hp
      (by rw [pow_two, ha]; exact mul_dvd_mul_left _ hPa)
  let K := FractionRing A
  let L := FractionRing B
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have habot : a != ⊥ := fun ha' => hp' (by simpa [ha'] using ha)
  have hPbot : P != ⊥ := by
    rintro rfl; apply hp'
    rwa [Ideal.bot_mul] at ha
  suffices forall x in a, Algebra.intTrace A B x in p by
    have hP : ((P :)⁻¹ : FractionalIdeal B⁰ L) = a / p.map (algebraMap A B) := by
      apply inv_involutive.injective
      simp only [ha, FractionalIdeal.coeIdeal_mul, inv_div, mul_div_assoc]
      rw [div_self (by simpa)]; rw [mul_one]; rw [inv_inv]
    rw [Ideal.dvd_iff_le]; rw [differentialIdeal_le_iff (K := K) (L := L) hPbot]; rw [hP]; rw [Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.restrictScalars_mem]; rw [FractionalIdeal.mem_coe]; rw [FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp')] at hx
    rw [Submodule.mem_comap]; rw [LinearMap.coe_restrictScalars]; rw [← FractionalIdeal.coe_one]; rw [← div_self (G₀ := FractionalIdeal A⁰ K) (a := p) (by simpa using hp)]; rw [FractionalIdeal.mem_coe]; rw [FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp)]
    simp only [FractionalIdeal.mem_coeIdeal, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hx
    intro y hy'
    obtain ⟨y, hy, rfl : algebraMap A K _ = _⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy'
    obtain ⟨z, hz, hz'⟩ := hx _ (Ideal.mem_map_of_mem _ hy)
    have : Algebra.trace K L (algebraMap B L z) in (p : FractionalIdeal A⁰ K) := by
      rw [← Algebra.algebraMap_intTrace (A := A)]
      exact ⟨Algebra.intTrace A B z, this z hz, rfl⟩
    rwa [mul_comm, ← smul_eq_mul, ← map_smul, Algebra.smul_def, mul_comm,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L, ← hz']
  intro x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem]; rw [← Algebra.trace_quotient_eq_of_isDedekindDomain]
  let : Algebra (A ⧸ p) (B ⧸ a) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp
      (Ideal.dvd_iff_le.mp ⟨_, ha.trans (mul_comm _ _)⟩))
  have : IsScalarTower A (A ⧸ p) (B ⧸ a) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ a) := .of_restrictScalars_finite A _ _
  have := ((Ideal.prime_iff_isPrime hPbot).mpr inferInstance)
  rw [← this.irreducible.gcd_eq_one_iff]; rw [← Ideal.isCoprime_iff_gcd] at hPa
  let e : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p] ((B ⧸ P) × B ⧸ a) :=
    { __ := (Ideal.quotEquivOfEq ha).trans (Ideal.quotientMulEquivQuotientProd P a hPa),
      commutes' := Quotient.ind fun _ => rfl }
  have hx' : (e (Ideal.Quotient.mk _ x)).2 = 0 := by
    simpa [e, Ideal.Quotient.eq_zero_iff_mem]
  rw [← Algebra.trace_eq_of_algEquiv e]; rw [Algebra.trace_prod_apply]; rw [Algebra.trace_eq_zero_of_not_isSeparable H]; rw [LinearMap.zero_apply]; rw [zero_add]; rw [hx']; rw [map_zero]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, FractionRing, Ideal.LiesOver.over.le, Ideal.dvd_iff_le.mpr, Ideal.map_eq_bot_iff_of_injective, Ideal.map_le_iff_le_comap.mpr, LiesOver, algebraMap, algebraMap_injective, dvd_iff_le, map_eq_bot_iff_of_injective, map_le_iff_le_comap, mul_dvd_mul_left, not.mpr, p.map, pow_sub_one_dvd_differentIdeal, pow_two
-/
lemma dvd_differentIdeal_of_not_isSeparable
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] (hp : p != ⊥)
    (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    (H : ¬ Algebra.IsSeparable (A ⧸ p) (B ⧸ P)) : P ∣ differentIdeal A B := by
  obtain ⟨a, ha⟩ : P ∣ p.map (algebraMap A B) :=
    Ideal.dvd_iff_le.mpr (Ideal.map_le_iff_le_comap.mpr Ideal.LiesOver.over.le)
  by_cases hPa : P ∣ a
  · simpa using pow_sub_one_dvd_differentIdeal A P 2 hp
      (by rw [pow_two, ha]; exact mul_dvd_mul_left _ hPa)
  let K := FractionRing A
  let L := FractionRing B
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have habot : a != ⊥ := fun ha' => hp' (by simpa [ha'] using ha)
  have hPbot : P != ⊥ := by
    rintro rfl; apply hp'
    rwa [Ideal.bot_mul] at ha
  suffices forall x in a, Algebra.intTrace A B x in p by
    have hP : ((P :)⁻¹ : FractionalIdeal B⁰ L) = a / p.map (algebraMap A B) := by
      apply inv_involutive.injective
      simp only [ha, FractionalIdeal.coeIdeal_mul, inv_div, mul_div_assoc]
      rw [div_self (by simpa)]; rw [mul_one]; rw [inv_inv]
    rw [Ideal.dvd_iff_le]; rw [differentialIdeal_le_iff (K := K) (L := L) hPbot]; rw [hP]; rw [Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.restrictScalars_mem]; rw [FractionalIdeal.mem_coe]; rw [FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp')] at hx
    rw [Submodule.mem_comap]; rw [LinearMap.coe_restrictScalars]; rw [← FractionalIdeal.coe_one]; rw [← div_self (G₀ := FractionalIdeal A⁰ K) (a := p) (by simpa using hp)]; rw [FractionalIdeal.mem_coe]; rw [FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp)]
    simp only [FractionalIdeal.mem_coeIdeal, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hx
    intro y hy'
    obtain ⟨y, hy, rfl : algebraMap A K _ = _⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy'
    obtain ⟨z, hz, hz'⟩ := hx _ (Ideal.mem_map_of_mem _ hy)
    have : Algebra.trace K L (algebraMap B L z) in (p : FractionalIdeal A⁰ K) := by
      rw [← Algebra.algebraMap_intTrace (A := A)]
      exact ⟨Algebra.intTrace A B z, this z hz, rfl⟩
    rwa [mul_comm, ← smul_eq_mul, ← map_smul, Algebra.smul_def, mul_comm,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L, ← hz']
  intro x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem]; rw [← Algebra.trace_quotient_eq_of_isDedekindDomain]
  let : Algebra (A ⧸ p) (B ⧸ a) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp
      (Ideal.dvd_iff_le.mp ⟨_, ha.trans (mul_comm _ _)⟩))
  have : IsScalarTower A (A ⧸ p) (B ⧸ a) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ a) := .of_restrictScalars_finite A _ _
  have := ((Ideal.prime_iff_isPrime hPbot).mpr inferInstance)
  rw [← this.irreducible.gcd_eq_one_iff]; rw [← Ideal.isCoprime_iff_gcd] at hPa
  let e : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p] ((B ⧸ P) × B ⧸ a) :=
    { __ := (Ideal.quotEquivOfEq ha).trans (Ideal.quotientMulEquivQuotientProd P a hPa),
      commutes' := Quotient.ind fun _ => rfl }
  have hx' : (e (Ideal.Quotient.mk _ x)).2 = 0 := by
    simpa [e, Ideal.Quotient.eq_zero_iff_mem]
  rw [← Algebra.trace_eq_of_algEquiv e]; rw [Algebra.trace_prod_apply]; rw [Algebra.trace_eq_zero_of_not_isSeparable H]; rw [LinearMap.zero_apply]; rw [zero_add]; rw [hx']; rw [map_zero]

variable {A}

/--
theorem `not_dvd_differentIdeal_iff` / 定理 `not_dvd_differentIdeal_iff`

English:
theorem not_dvd_differentIdeal_iff
  proof: by
  rcases eq_or_ne P ⊥ with rfl | hPbot
  · simp_rw [← Ideal.zero_eq_bot, zero_dvd_iff]
    simp only [Submodule.zero_eq_bot, differentIdeal_ne_bot, not_false_eq_true, true_iff]
    let K := FractionRing A
    let L := FractionRing B
    have : IsLocalization B⁰ (Localization.AtPrime (⊥ : Ideal B)) := by
      convert!
        (inferInstance :
          IsLocalization (⊥ : Ideal B).primeCompl (Localization.AtPrime (⊥ : Ideal B)))
      ext; simp [Ideal.primeCompl]
    refine (Algebra.FormallyUnramified.iff_of_equiv (A := L)
      ((IsLocalization.algEquiv B⁰ _ _).restrictScalars A)).mp ?_
    have : Algebra.FormallyUnramified K L := by
      rwa [Algebra.FormallyUnramified.iff_isSeparable]
    refine .comp A K L
  have hp : P.under A != ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hPbot
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have := Ideal.IsPrime.isMaximal inferInstance hPbot
  let := Localization.AtPrime.algebraOfLiesOver (P.under A) P
  constructor
  · intro H
    · rw [Algebra.isUnramifiedAt_iff_map_eq (p := P.under A)]
      constructor
      · suffices Algebra.IsSeparable (A ⧸ P.under A) (B ⧸ P) by infer_instance
        contrapose H
        exact dvd_differentIdeal_of_not_isSeparable A hp P H
      · rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff hPbot Ideal.map_comap_le]
        apply Ideal.ramificationIdx'_spec
        · simp [Ideal.map_le_iff_le_comap]
        · contrapose H
          rw [← pow_one P]; rw [show 1 = 2 - 1 by simp]
          apply pow_sub_one_dvd_differentIdeal _ _ _ hp
          simpa [Ideal.dvd_iff_le] using H
  · intro H
    obtain ⟨Q, h₁, h₂⟩ := Ideal.eq_prime_pow_mul_coprime hp' P
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ hp']; rw [Ideal.ramificationIdx_eq_one_of_isUnramifiedAt]; rw [pow_one] at h₂
    obtain ⟨h₃, h₄⟩ := (Algebra.isUnramifiedAt_iff_map_eq (p := P.under A) _ _).mp H
    exact not_dvd_differentIdeal_of_isCoprime_of_isSeparable
      A P Q (Ideal.isCoprime_iff_sup_eq.mpr h₁) h₂.symm

中文:
定理 not_dvd_differentIdeal_iff
  证明: by
  rcases eq_or_ne P ⊥ with rfl | hPbot
  · simp_rw [← Ideal.zero_eq_bot, zero_dvd_iff]
    simp only [Submodule.zero_eq_bot, differentIdeal_ne_bot, not_false_eq_true, true_iff]
    let K := FractionRing A
    let L := FractionRing B
    have : IsLocalization B⁰ (Localization.AtPrime (⊥ : Ideal B)) := by
      convert!
        (inferInstance :
          IsLocalization (⊥ : Ideal B).primeCompl (Localization.AtPrime (⊥ : Ideal B)))
      ext; simp [Ideal.primeCompl]
    refine (Algebra.FormallyUnramified.iff_of_equiv (A := L)
      ((IsLocalization.algEquiv B⁰ _ _).restrictScalars A)).mp ?_
    have : Algebra.FormallyUnramified K L := by
      rwa [Algebra.FormallyUnramified.iff_isSeparable]
    refine .comp A K L
  have hp : P.under A != ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hPbot
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have := Ideal.IsPrime.isMaximal inferInstance hPbot
  let := Localization.AtPrime.algebraOfLiesOver (P.under A) P
  constructor
  · intro H
    · rw [Algebra.isUnramifiedAt_iff_map_eq (p := P.under A)]
      constructor
      · suffices Algebra.IsSeparable (A ⧸ P.under A) (B ⧸ P) by infer_instance
        contrapose H
        exact dvd_differentIdeal_of_not_isSeparable A hp P H
      · rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff hPbot Ideal.map_comap_le]
        apply Ideal.ramificationIdx'_spec
        · simp [Ideal.map_le_iff_le_comap]
        · contrapose H
          rw [← pow_one P]; rw [show 1 = 2 - 1 by simp]
          apply pow_sub_one_dvd_differentIdeal _ _ _ hp
          simpa [Ideal.dvd_iff_le] using H
  · intro H
    obtain ⟨Q, h₁, h₂⟩ := Ideal.eq_prime_pow_mul_coprime hp' P
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ hp']; rw [Ideal.ramificationIdx_eq_one_of_isUnramifiedAt]; rw [pow_one] at h₂
    obtain ⟨h₃, h₄⟩ := (Algebra.isUnramifiedAt_iff_map_eq (p := P.under A) _ _).mp H
    exact not_dvd_differentIdeal_of_isCoprime_of_isSeparable
      A P Q (Ideal.isCoprime_iff_sup_eq.mpr h₁) h₂.symm

Depends on / 依赖: Algebra, Algebra.FormallyUnramified.iff_of_equiv, AtPrime, FormallyUnramified, FractionRing, Ideal.primeCompl, Ideal.zero_eq_bot, IsLocalization, IsLocalization.algEq, Localization, Localization.AtPrime, Submodule, Submodule.zero_eq_bot, convert, differentIdeal_ne_bot, eq_or_ne, iff_of_equiv, not_false_eq_true, primeCompl, simp_rw
-/
theorem not_dvd_differentIdeal_iff
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)] {P : Ideal B} [P.IsPrime] :
    ¬ P ∣ differentIdeal A B ↔ Algebra.IsUnramifiedAt A P := by
  rcases eq_or_ne P ⊥ with rfl | hPbot
  · simp_rw [← Ideal.zero_eq_bot, zero_dvd_iff]
    simp only [Submodule.zero_eq_bot, differentIdeal_ne_bot, not_false_eq_true, true_iff]
    let K := FractionRing A
    let L := FractionRing B
    have : IsLocalization B⁰ (Localization.AtPrime (⊥ : Ideal B)) := by
      convert!
        (inferInstance :
          IsLocalization (⊥ : Ideal B).primeCompl (Localization.AtPrime (⊥ : Ideal B)))
      ext; simp [Ideal.primeCompl]
    refine (Algebra.FormallyUnramified.iff_of_equiv (A := L)
      ((IsLocalization.algEquiv B⁰ _ _).restrictScalars A)).mp ?_
    have : Algebra.FormallyUnramified K L := by
      rwa [Algebra.FormallyUnramified.iff_isSeparable]
    refine .comp A K L
  have hp : P.under A != ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hPbot
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have := Ideal.IsPrime.isMaximal inferInstance hPbot
  let := Localization.AtPrime.algebraOfLiesOver (P.under A) P
  constructor
  · intro H
    · rw [Algebra.isUnramifiedAt_iff_map_eq (p := P.under A)]
      constructor
      · suffices Algebra.IsSeparable (A ⧸ P.under A) (B ⧸ P) by infer_instance
        contrapose H
        exact dvd_differentIdeal_of_not_isSeparable A hp P H
      · rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff hPbot Ideal.map_comap_le]
        apply Ideal.ramificationIdx'_spec
        · simp [Ideal.map_le_iff_le_comap]
        · contrapose H
          rw [← pow_one P]; rw [show 1 = 2 - 1 by simp]
          apply pow_sub_one_dvd_differentIdeal _ _ _ hp
          simpa [Ideal.dvd_iff_le] using H
  · intro H
    obtain ⟨Q, h₁, h₂⟩ := Ideal.eq_prime_pow_mul_coprime hp' P
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ hp']; rw [Ideal.ramificationIdx_eq_one_of_isUnramifiedAt]; rw [pow_one] at h₂
    obtain ⟨h₃, h₄⟩ := (Algebra.isUnramifiedAt_iff_map_eq (p := P.under A) _ _).mp H
    exact not_dvd_differentIdeal_of_isCoprime_of_isSeparable
      A P Q (Ideal.isCoprime_iff_sup_eq.mpr h₁) h₂.symm

/--
theorem `dvd_differentIdeal_iff` / 定理 `dvd_differentIdeal_iff`

English:
theorem dvd_differentIdeal_iff
  proof: iff_not_comm.mp not_dvd_differentIdeal_iff.symm

中文:
定理 dvd_differentIdeal_iff
  证明: iff_not_comm.mp not_dvd_differentIdeal_iff.symm

Depends on / 依赖: iff_not_comm, iff_not_comm.mp, not_dvd_differentIdeal_iff, not_dvd_differentIdeal_iff.symm
-/
theorem dvd_differentIdeal_iff
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)] {P : Ideal B} [P.IsPrime] :
    P ∣ differentIdeal A B ↔ ¬ Algebra.IsUnramifiedAt A P :=
  iff_not_comm.mp not_dvd_differentIdeal_iff.symm

end
