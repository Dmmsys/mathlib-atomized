/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.Quotient.ChineseRemainder
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Support
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Finite modules over local rings

This file gathers various results about finite modules over a local ring `(R, 𝔪, k)`.

## Main results
- `IsLocalRing.subsingleton_tensorProduct`: If `M` is finitely generated, `k ⊗ M = 0 ↔ M = 0`.
- `Module.free_of_maximalIdeal_rTensor_injective`:
  If `M` is a finitely presented module such that `m ⊗ M → M` is injective
  (for example when `M` is flat), then `M` is free.
- `Module.free_of_lTensor_residueField_injective`: If `N → M → P → 0` is a presentation of `P` with
  `N` finite and `M` finite free, then injectivity of `k ⊗ N → k ⊗ M` implies that `P` is free.
- `IsLocalRing.split_injective_iff_lTensor_residueField_injective`:
  Given an `R`-linear map `l : M → N` with `M` finite and `N` finite free,
  `l` is a split injection if and only if `k ⊗ l` is a (split) injection.
-/

public section

open Module

universe u
variable {R M N P : Type*} [CommRing R]

section

variable [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

open Function (Injective Surjective Exact)
open IsLocalRing TensorProduct

local notation "k" => ResidueField R
local notation "𝔪" => maximalIdeal R

variable [AddCommGroup P] [Module R P] (f : M ->ₗ[R] N) (g : N ->ₗ[R] P)

namespace IsLocalRing

variable [IsLocalRing R]

/--
theorem `map_mkQ_eq` / 定理 `map_mkQ_eq`

English:
theorem map_mkQ_eq
  given: {N₁ N₂ : Submodule R M} (h : N₁ <= N₂) (h' : N₂.FG)
  proof: by
  constructor
  · intro hN
    have : N₂ <= 𝔪 • N₂ ⊔ N₁ := by
      simpa using Submodule.comap_mono (f := Submodule.mkQ (𝔪 • N₂)) hN.ge
    rw [sup_comm] at this
    exact h.antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot h'
      (by rw [jacobson_eq_maximalIdeal]; exact bot_ne_top) this)
  · rintro rfl; simp

中文:
定理 map_mkQ_eq
  条件: {N₁ N₂ : 子模 R M} (h : N₁ <= N₂) (h' : N₂.FG)
  证明: by
  constructor
  · intro hN
    have : N₂ <= 𝔪 • N₂ ⊔ N₁ := by
      simpa using Submodule.comap_mono (f := Submodule.mkQ (𝔪 • N₂)) hN.ge
    rw [sup_comm] at this
    exact h.antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot h'
      (by rw [jacobson_eq_maximalIdeal]; exact bot_ne_top) this)
  · rintro rfl; simp

Depends on / 依赖: Submodule, Submodule.comap_mono, Submodule.le_of_le_smul_of_le_jacobson_bot, Submodule.mkQ, antisymm, bot_ne_top, comap_mono, h.antisymm, hN.ge, jacobson_eq_maximalIdeal, le_of_le_smul_of_le_jacobson_bot, sup_comm
-/
theorem map_mkQ_eq {N₁ N₂ : Submodule R M} (h : N₁ <= N₂) (h' : N₂.FG) :
    N₁.map (Submodule.mkQ (𝔪 • N₂)) = N₂.map (Submodule.mkQ (𝔪 • N₂)) ↔ N₁ = N₂ := by
  constructor
  · intro hN
    have : N₂ <= 𝔪 • N₂ ⊔ N₁ := by
      simpa using Submodule.comap_mono (f := Submodule.mkQ (𝔪 • N₂)) hN.ge
    rw [sup_comm] at this
    exact h.antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot h'
      (by rw [jacobson_eq_maximalIdeal]; exact bot_ne_top) this)
  · rintro rfl; simp

/--
theorem `map_mkQ_eq_top` / 定理 `map_mkQ_eq_top`

English:
theorem map_mkQ_eq_top
  given: {N : Submodule R M} [Module.Finite R M]
  proof: by
  rw [← map_mkQ_eq (N₁ := N) le_top Module.Finite.fg_top]; rw [Submodule.map_top]; rw [Submodule.range_mkQ]

中文:
定理 map_mkQ_eq_top
  条件: {N : 子模 R M} [模.有限 R M]
  证明: by
  rw [← map_mkQ_eq (N₁ := N) le_top Module.Finite.fg_top]; rw [Submodule.map_top]; rw [Submodule.range_mkQ]

Depends on / 依赖: Finite, Module, Module.Finite.fg_top, Submodule, Submodule.map_top, Submodule.range_mkQ, fg_top, le_top, map_mkQ_eq, map_top, range_mkQ
-/
theorem map_mkQ_eq_top {N : Submodule R M} [Module.Finite R M] :
    N.map (Submodule.mkQ (𝔪 • ⊤)) = ⊤ ↔ N = ⊤ := by
  rw [← map_mkQ_eq (N₁ := N) le_top Module.Finite.fg_top]; rw [Submodule.map_top]; rw [Submodule.range_mkQ]

/--
theorem `map_tensorProduct_mk_eq_top` / 定理 `map_tensorProduct_mk_eq_top`

English:
theorem map_tensorProduct_mk_eq_top
  given: {N : Submodule R M} [Module.Finite R M]
  proof: by
  constructor
  · intro hN
    let : Module k (M ⧸ (𝔪 • ⊤ : Submodule R M)) :=
      inferInstanceAs (Module (R ⧸ 𝔪) (M ⧸ 𝔪 • (⊤ : Submodule R M)))
    let : IsScalarTower R k (M ⧸ (𝔪 • ⊤ : Submodule R M)) :=
      inferInstanceAs (IsScalarTower R (R ⧸ 𝔪) (M ⧸ 𝔪 • (⊤ : Submodule R M)))
    let f := AlgebraTensorModule.lift (((LinearMap.ringLmapEquivSelf k k _).symm
      (Submodule.mkQ (𝔪 • ⊤ : Submodule R M))).restrictScalars R)
    have : f.comp (TensorProduct.mk R k M 1) = Submodule.mkQ (𝔪 • ⊤) := by ext; simp [f]
    have hf : Function.Surjective f := by
      intro x; obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
      rw [← this]; rw [LinearMap.comp_apply]; exact ⟨_, rfl⟩
    apply_fun Submodule.map f at hN
    rwa [← Submodule.map_comp, this, Submodule.map_top, LinearMap.range_eq_top.2 hf,
      map_mkQ_eq_top] at hN
  · rintro rfl; rw [Submodule.map_top, LinearMap.range_eq_top]
    exact TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective

中文:
定理 map_tensorProduct_mk_eq_top
  条件: {N : 子模 R M} [模.有限 R M]
  证明: by
  constructor
  · intro hN
    let : Module k (M ⧸ (𝔪 • ⊤ : Submodule R M)) :=
      inferInstanceAs (Module (R ⧸ 𝔪) (M ⧸ 𝔪 • (⊤ : Submodule R M)))
    let : IsScalarTower R k (M ⧸ (𝔪 • ⊤ : Submodule R M)) :=
      inferInstanceAs (IsScalarTower R (R ⧸ 𝔪) (M ⧸ 𝔪 • (⊤ : Submodule R M)))
    let f := AlgebraTensorModule.lift (((LinearMap.ringLmapEquivSelf k k _).symm
      (Submodule.mkQ (𝔪 • ⊤ : Submodule R M))).restrictScalars R)
    have : f.comp (TensorProduct.mk R k M 1) = Submodule.mkQ (𝔪 • ⊤) := by ext; simp [f]
    have hf : Function.Surjective f := by
      intro x; obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
      rw [← this]; rw [LinearMap.comp_apply]; exact ⟨_, rfl⟩
    apply_fun Submodule.map f at hN
    rwa [← Submodule.map_comp, this, Submodule.map_top, LinearMap.range_eq_top.2 hf,
      map_mkQ_eq_top] at hN
  · rintro rfl; rw [Submodule.map_top, LinearMap.range_eq_top]
    exact TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.lift, IsScalarTower, LinearMap, LinearMap.ringLmapEquivSelf, Module, Submodule, Submodule.mkQ, TensorProduct, TensorProduct.mk, f.comp, restrictScalars, ringLmapEquivSelf
-/
theorem map_tensorProduct_mk_eq_top {N : Submodule R M} [Module.Finite R M] :
    N.map (TensorProduct.mk R k M 1) = ⊤ ↔ N = ⊤ := by
  constructor
  · intro hN
    let : Module k (M ⧸ (𝔪 • ⊤ : Submodule R M)) :=
      inferInstanceAs (Module (R ⧸ 𝔪) (M ⧸ 𝔪 • (⊤ : Submodule R M)))
    let : IsScalarTower R k (M ⧸ (𝔪 • ⊤ : Submodule R M)) :=
      inferInstanceAs (IsScalarTower R (R ⧸ 𝔪) (M ⧸ 𝔪 • (⊤ : Submodule R M)))
    let f := AlgebraTensorModule.lift (((LinearMap.ringLmapEquivSelf k k _).symm
      (Submodule.mkQ (𝔪 • ⊤ : Submodule R M))).restrictScalars R)
    have : f.comp (TensorProduct.mk R k M 1) = Submodule.mkQ (𝔪 • ⊤) := by ext; simp [f]
    have hf : Function.Surjective f := by
      intro x; obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
      rw [← this]; rw [LinearMap.comp_apply]; exact ⟨_, rfl⟩
    apply_fun Submodule.map f at hN
    rwa [← Submodule.map_comp, this, Submodule.map_top, LinearMap.range_eq_top.2 hf,
      map_mkQ_eq_top] at hN
  · rintro rfl; rw [Submodule.map_top, LinearMap.range_eq_top]
    exact TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective

/--
theorem `subsingleton_tensorProduct` / 定理 `subsingleton_tensorProduct`

English:
theorem subsingleton_tensorProduct
  given: [Module.Finite R M]
  proof: by
  rw [← Submodule.subsingleton_iff R]; rw [← subsingleton_iff_bot_eq_top]; rw [← Submodule.subsingleton_iff R]; rw [← subsingleton_iff_bot_eq_top]; rw [← map_tensorProduct_mk_eq_top (M := M)]; rw [Submodule.map_bot]

中文:
定理 subsingleton_tensorProduct
  条件: [模.有限 R M]
  证明: by
  rw [← Submodule.subsingleton_iff R]; rw [← subsingleton_iff_bot_eq_top]; rw [← Submodule.subsingleton_iff R]; rw [← subsingleton_iff_bot_eq_top]; rw [← map_tensorProduct_mk_eq_top (M := M)]; rw [Submodule.map_bot]

Depends on / 依赖: Submodule, Submodule.map_bot, Submodule.subsingleton_iff, map_bot, map_tensorProduct_mk_eq_top, subsingleton_iff, subsingleton_iff_bot_eq_top
-/
theorem subsingleton_tensorProduct [Module.Finite R M] :
    Subsingleton (k otimes[R] M) ↔ Subsingleton M := by
  rw [← Submodule.subsingleton_iff R]; rw [← subsingleton_iff_bot_eq_top]; rw [← Submodule.subsingleton_iff R]; rw [← subsingleton_iff_bot_eq_top]; rw [← map_tensorProduct_mk_eq_top (M := M)]; rw [Submodule.map_bot]

/--
theorem `span_eq_top_of_tmul_eq_basis` / 定理 `span_eq_top_of_tmul_eq_basis`

English:
theorem span_eq_top_of_tmul_eq_basis
  statement: [Module.Finite R M] {ι}
  proof: by
  rw [← map_tensorProduct_mk_eq_top]; rw [Submodule.map_span]; rw [← Submodule.restrictScalars_span R k
    Ideal.Quotient.mk_surjective]; rw [Submodule.restrictScalars_eq_top_iff]; rw [← b.span_eq]; rw [← Set.range_comp]
  simp only [Function.comp_def, mk_apply, hb, Basis.span_eq]

中文:
定理 span_eq_top_of_tmul_eq_basis
  结论: [模.有限 R M] {ι}
  证明: by
  rw [← map_tensorProduct_mk_eq_top]; rw [Submodule.map_span]; rw [← Submodule.restrictScalars_span R k
    Ideal.Quotient.mk_surjective]; rw [Submodule.restrictScalars_eq_top_iff]; rw [← b.span_eq]; rw [← Set.range_comp]
  simp only [Function.comp_def, mk_apply, hb, Basis.span_eq]

Depends on / 依赖: Basis.span_eq, Function, Function.comp_def, Ideal.Quotient.mk_surjective, Quotient, Set.range_comp, Submodule, Submodule.map_span, Submodule.restrictScalars_eq_top_iff, Submodule.restrictScalars_span, b.span_eq, comp_def, map_span, map_tensorProduct_mk_eq_top, mk_apply, mk_surjective, range_comp, restrictScalars_eq_top_iff, restrictScalars_span, span_eq
-/
theorem span_eq_top_of_tmul_eq_basis [Module.Finite R M] {ι}
    (f : ι -> M) (b : Basis ι k (k otimes[R] M))
    (hb : forall i, 1 otimesₜ f i = b i) : Submodule.span R (Set.range f) = ⊤ := by
  rw [← map_tensorProduct_mk_eq_top]; rw [Submodule.map_span]; rw [← Submodule.restrictScalars_span R k
    Ideal.Quotient.mk_surjective]; rw [Submodule.restrictScalars_eq_top_iff]; rw [← b.span_eq]; rw [← Set.range_comp]
  simp only [Function.comp_def, mk_apply, hb, Basis.span_eq]

end IsLocalRing

/--
lemma `Module.mem_support_iff_nontrivial_residueField_tensorProduct` / 引理 `Module.mem_support_iff_nontrivial_residueField_tensorProduct`

English:
lemma Module.mem_support_iff_nontrivial_residueField_tensorProduct
  statement: [Module.Finite R M]
  proof: by
  let K := p.asIdeal.ResidueField
  let e := (AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime p.asIdeal) K K M).symm
  rw [e.nontrivial_congr]; rw [Module.mem_support_iff]; rw [(LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M).nontrivial_congr]; rw [← not_iff_not]; rw [not_nontrivial_iff_subsingleton]; rw [not_nontrivial_iff_subsingleton]; rw [IsLocalRing.subsingleton_tensorProduct]

中文:
引理 模.mem_support_iff_nontrivial_residueField_tensorProduct
  结论: [模.有限 R M]
  证明: by
  let K := p.asIdeal.ResidueField
  let e := (AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime p.asIdeal) K K M).symm
  rw [e.nontrivial_congr]; rw [Module.mem_support_iff]; rw [(LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M).nontrivial_congr]; rw [← not_iff_not]; rw [not_nontrivial_iff_subsingleton]; rw [not_nontrivial_iff_subsingleton]; rw [IsLocalRing.subsingleton_tensorProduct]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.cancelBaseChange, AtPrime, IsLocalRing, IsLocalRing.subsingleton_tensorProduct, Localization, Localization.AtPrime, LocalizedModule, LocalizedModule.equivTensorProduct, Module, Module.mem_support_iff, ResidueField, asIdeal, cancelBaseChange, e.nontrivial_congr, equivTensorProduct, mem_support_iff, nontrivial_congr, not_iff_not, not_nontrivial_iff_subsingleton
-/
lemma Module.mem_support_iff_nontrivial_residueField_tensorProduct [Module.Finite R M]
    (p : PrimeSpectrum R) :
    p in Module.support R M ↔ Nontrivial (p.asIdeal.ResidueField otimes[R] M) := by
  let K := p.asIdeal.ResidueField
  let e := (AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime p.asIdeal) K K M).symm
  rw [e.nontrivial_congr]; rw [Module.mem_support_iff]; rw [(LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M).nontrivial_congr]; rw [← not_iff_not]; rw [not_nontrivial_iff_subsingleton]; rw [not_nontrivial_iff_subsingleton]; rw [IsLocalRing.subsingleton_tensorProduct]

open Function in
/--
theorem `lTensor_injective_of_exact_of_exact_of_rTensor_injective` / 定理 `lTensor_injective_of_exact_of_exact_of_rTensor_injective`

English:
theorem lTensor_injective_of_exact_of_exact_of_rTensor_injective
  proof: by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := f₂.rTensor_surjective N₁ hfsurj x
  have : f₂.rTensor N₂ (g₁.lTensor M₂ x) = 0 := by
    rw [← hx]; rw [← LinearMap.comp_apply]; rw [← LinearMap.comp_apply]; rw [LinearMap.rTensor_comp_lTensor]; rw [LinearMap.lTensor_comp_rTensor]
  obtain ⟨y, hy⟩ := (rTensor_exact N₂ hfexact hfsurj _).mp this
  have : g₂.lTensor M₁ y = 0 := by
    apply hfinj
    trans g₂.lTensor M₂ (g₁.lTensor M₂ x)
    · rw [← hy, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        LinearMap.lTensor_comp_rTensor]
    rw [← LinearMap.comp_apply]; rw [← LinearMap.lTensor_comp]; rw [hgexact.linearMap_comp_eq_zero]
    simp
  obtain ⟨z, rfl⟩ := (lTensor_exact _ hgexact hgsurj _).mp this
  obtain rfl : f₁.rTensor N₁ z = x := by
    apply hginj
    simp only [← hy, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  rw [← LinearMap.comp_apply]; rw [← LinearMap.rTensor_comp]; rw [hfexact.linearMap_comp_eq_zero]
  simp

中文:
定理 lTensor_injective_of_exact_of_exact_of_rTensor_injective
  证明: by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := f₂.rTensor_surjective N₁ hfsurj x
  have : f₂.rTensor N₂ (g₁.lTensor M₂ x) = 0 := by
    rw [← hx]; rw [← LinearMap.comp_apply]; rw [← LinearMap.comp_apply]; rw [LinearMap.rTensor_comp_lTensor]; rw [LinearMap.lTensor_comp_rTensor]
  obtain ⟨y, hy⟩ := (rTensor_exact N₂ hfexact hfsurj _).mp this
  have : g₂.lTensor M₁ y = 0 := by
    apply hfinj
    trans g₂.lTensor M₂ (g₁.lTensor M₂ x)
    · rw [← hy, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        LinearMap.lTensor_comp_rTensor]
    rw [← LinearMap.comp_apply]; rw [← LinearMap.lTensor_comp]; rw [hgexact.linearMap_comp_eq_zero]
    simp
  obtain ⟨z, rfl⟩ := (lTensor_exact _ hgexact hgsurj _).mp this
  obtain rfl : f₁.rTensor N₁ z = x := by
    apply hginj
    simp only [← hy, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  rw [← LinearMap.comp_apply]; rw [← LinearMap.rTensor_comp]; rw [hfexact.linearMap_comp_eq_zero]
  simp

Depends on / 依赖: Linear, LinearMap, LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor, comp_apply, hfexact, hfsurj, injective_iff_map_eq_zero, lTensor, lTensor_comp_rTensor, rTensor, rTensor_comp_lTensor, rTensor_exact, rTensor_surjective
-/
theorem lTensor_injective_of_exact_of_exact_of_rTensor_injective
    {M₁ M₂ M₃ N₁ N₂ N₃}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₃] [Module R N₃]
    {f₁ : M₁ ->ₗ[R] M₂} {f₂ : M₂ ->ₗ[R] M₃} {g₁ : N₁ ->ₗ[R] N₂} {g₂ : N₂ ->ₗ[R] N₃}
    (hfexact : Exact f₁ f₂) (hfsurj : Surjective f₂)
    (hgexact : Exact g₁ g₂) (hgsurj : Surjective g₂)
    (hfinj : Injective (f₁.rTensor N₃)) (hginj : Injective (g₁.lTensor M₂)) :
    Injective (g₁.lTensor M₃) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := f₂.rTensor_surjective N₁ hfsurj x
  have : f₂.rTensor N₂ (g₁.lTensor M₂ x) = 0 := by
    rw [← hx]; rw [← LinearMap.comp_apply]; rw [← LinearMap.comp_apply]; rw [LinearMap.rTensor_comp_lTensor]; rw [LinearMap.lTensor_comp_rTensor]
  obtain ⟨y, hy⟩ := (rTensor_exact N₂ hfexact hfsurj _).mp this
  have : g₂.lTensor M₁ y = 0 := by
    apply hfinj
    trans g₂.lTensor M₂ (g₁.lTensor M₂ x)
    · rw [← hy, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        LinearMap.lTensor_comp_rTensor]
    rw [← LinearMap.comp_apply]; rw [← LinearMap.lTensor_comp]; rw [hgexact.linearMap_comp_eq_zero]
    simp
  obtain ⟨z, rfl⟩ := (lTensor_exact _ hgexact hgsurj _).mp this
  obtain rfl : f₁.rTensor N₁ z = x := by
    apply hginj
    simp only [← hy, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  rw [← LinearMap.comp_apply]; rw [← LinearMap.rTensor_comp]; rw [hfexact.linearMap_comp_eq_zero]
  simp

namespace Module

variable [IsLocalRing R]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_basis_of_basis_baseChange` / 引理 `exists_basis_of_basis_baseChange`

English:
lemma exists_basis_of_basis_baseChange
  statement: [Module.FinitePresentation R M]
  proof: by
  let bk : Basis ι k (k otimes[R] M) := Basis.mk hli (by rw [hsp])
  have : Finite ι := Module.Finite.finite_basis bk
  let : Fintype ι := Fintype.ofFinite ι
  let i := Finsupp.linearCombination R v
  have hi : Surjective i := by
    rw [← LinearMap.range_eq_top]; rw [Finsupp.range_linearCombination]
    refine IsLocalRing.span_eq_top_of_tmul_eq_basis (R := R) (f := v) bk
      (fun _ => by simp [bk])
  have : Module.Finite R (LinearMap.ker i) :=
    .of_fg (Module.FinitePresentation.fg_ker i hi)
  -- We claim that `i` is actually a bijection,
  -- hence `v` induces an isomorphism `M ≃[R] Rᴵ` showing that `v` is a basis.
  let iequiv : (ι ->₀ R) ≃ₗ[R] M := by
    refine LinearEquiv.ofBijective i ⟨?_, hi⟩
    -- By Nakayama's lemma, it suffices to show that `k ⊗ ker(i) = 0`.
    rw [← LinearMap.ker_eq_bot]; rw [← Submodule.subsingleton_iff_eq_bot]; rw [← IsLocalRing.subsingleton_tensorProduct (R := R)]; rw [subsingleton_iff_forall_eq 0]
    have : Function.Surjective (i.baseChange k) := i.lTensor_surjective _ hi
    -- By construction, `k ⊗ i : kᴵ → k ⊗ M` is bijective.
    have hi' : Function.Bijective (i.baseChange k) := by
      refine ⟨?_, this⟩
      rw [← LinearMap.ker_eq_bot (M := k otimes[R] (ι ->₀ R)) (f := i.baseChange k),
        ← Submodule.finrank_eq_zero (R := k) (M := k otimes[R] (ι ->₀ R)),
        ← Nat.add_right_inj (n := Module.finrank k (LinearMap.range <| i.baseChange k)),
        LinearMap.finrank_range_add_finrank_ker (V := k otimes[R] (ι ->₀ R)),
        LinearMap.range_eq_top.mpr this, finrank_top]
      simp only [Module.finrank_tensorProduct, Module.finrank_self,
        Module.finrank_finsupp_self, one_mul, add_zero]
      rw [Module.finrank_eq_card_basis bk]
    -- On the other hand, `m ⊗ M → M` injective => `Tor₁(k, M) = 0` => `k ⊗ ker(i) → kᴵ` injective.
    intro x
    refine lTensor_injective_of_exact_of_exact_of_rTensor_injective
      (N₁ := LinearMap.ker i) (N₂ := ι ->₀ R) (N₃ := M)
      (f₁ := (𝔪).subtype) (f₂ := Submodule.mkQ 𝔪)
      (g₁ := (LinearMap.ker i).subtype) (g₂ := i) (LinearMap.exact_subtype_mkQ 𝔪)
      (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_ker_map i) hi H ?_ ?_
    · apply Module.Flat.lTensor_preserves_injective_linearMap
      exact Subtype.val_injective
    · apply hi'.injective
      rw [LinearMap.baseChange_eq_ltensor]
      erw [← LinearMap.comp_apply (i.lTensor k), ← LinearMap.lTensor_comp]
      rw [(LinearMap.exact_subtype_ker_map i).linearMap_comp_eq_zero]
      simp only [LinearMap.lTensor_zero, LinearMap.zero_apply, map_zero]
  use Basis.ofRepr iequiv.symm
  intro j
  simp [iequiv, i]

中文:
引理 存在_basis_of_basis_baseChange
  结论: [模.有限呈现 R M]
  证明: by
  let bk : Basis ι k (k otimes[R] M) := Basis.mk hli (by rw [hsp])
  have : Finite ι := Module.Finite.finite_basis bk
  let : Fintype ι := Fintype.ofFinite ι
  let i := Finsupp.linearCombination R v
  have hi : Surjective i := by
    rw [← LinearMap.range_eq_top]; rw [Finsupp.range_linearCombination]
    refine IsLocalRing.span_eq_top_of_tmul_eq_basis (R := R) (f := v) bk
      (fun _ => by simp [bk])
  have : Module.Finite R (LinearMap.ker i) :=
    .of_fg (Module.FinitePresentation.fg_ker i hi)
  -- We claim that `i` is actually a bijection,
  -- hence `v` induces an isomorphism `M ≃[R] Rᴵ` showing that `v` is a basis.
  let iequiv : (ι ->₀ R) ≃ₗ[R] M := by
    refine LinearEquiv.ofBijective i ⟨?_, hi⟩
    -- By Nakayama's lemma, it suffices to show that `k ⊗ ker(i) = 0`.
    rw [← LinearMap.ker_eq_bot]; rw [← Submodule.subsingleton_iff_eq_bot]; rw [← IsLocalRing.subsingleton_tensorProduct (R := R)]; rw [subsingleton_iff_forall_eq 0]
    have : Function.Surjective (i.baseChange k) := i.lTensor_surjective _ hi
    -- By construction, `k ⊗ i : kᴵ → k ⊗ M` is bijective.
    have hi' : Function.Bijective (i.baseChange k) := by
      refine ⟨?_, this⟩
      rw [← LinearMap.ker_eq_bot (M := k otimes[R] (ι ->₀ R)) (f := i.baseChange k),
        ← Submodule.finrank_eq_zero (R := k) (M := k otimes[R] (ι ->₀ R)),
        ← Nat.add_right_inj (n := Module.finrank k (LinearMap.range <| i.baseChange k)),
        LinearMap.finrank_range_add_finrank_ker (V := k otimes[R] (ι ->₀ R)),
        LinearMap.range_eq_top.mpr this, finrank_top]
      simp only [Module.finrank_tensorProduct, Module.finrank_self,
        Module.finrank_finsupp_self, one_mul, add_zero]
      rw [Module.finrank_eq_card_basis bk]
    -- On the other hand, `m ⊗ M → M` injective => `Tor₁(k, M) = 0` => `k ⊗ ker(i) → kᴵ` injective.
    intro x
    refine lTensor_injective_of_exact_of_exact_of_rTensor_injective
      (N₁ := LinearMap.ker i) (N₂ := ι ->₀ R) (N₃ := M)
      (f₁ := (𝔪).subtype) (f₂ := Submodule.mkQ 𝔪)
      (g₁ := (LinearMap.ker i).subtype) (g₂ := i) (LinearMap.exact_subtype_mkQ 𝔪)
      (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_ker_map i) hi H ?_ ?_
    · apply Module.Flat.lTensor_preserves_injective_linearMap
      exact Subtype.val_injective
    · apply hi'.injective
      rw [LinearMap.baseChange_eq_ltensor]
      erw [← LinearMap.comp_apply (i.lTensor k), ← LinearMap.lTensor_comp]
      rw [(LinearMap.exact_subtype_ker_map i).linearMap_comp_eq_zero]
      simp only [LinearMap.lTensor_zero, LinearMap.zero_apply, map_zero]
  use Basis.ofRepr iequiv.symm
  intro j
  simp [iequiv, i]

Depends on / 依赖: Basis.mk, Finite, FinitePresentation, Finsupp, Finsupp.linearCombination, Finsupp.range_linearCombination, Fintype, Fintype.ofFinite, IsLocalRing, IsLocalRing.span_eq_top_of_tmul_eq_basis, LinearMap, LinearMap.ker, LinearMap.range_eq_top, Module, Module.Finite, Module.Finite.finite_basis, Module.FinitePresentation.fg_ker, Surjective, fg_ker, finite_basis
-/
lemma exists_basis_of_basis_baseChange [Module.FinitePresentation R M]
    {ι : Type*} (v : ι -> M) (hli : LinearIndependent k (TensorProduct.mk R k M 1 ∘ v))
    (hsp : Submodule.span k (Set.range (TensorProduct.mk R k M 1 ∘ v)) = ⊤)
    (H : Function.Injective ((𝔪).subtype.rTensor M)) :
    exists (b : Basis ι R M), forall i, b i = v i := by
  let bk : Basis ι k (k otimes[R] M) := Basis.mk hli (by rw [hsp])
  have : Finite ι := Module.Finite.finite_basis bk
  let : Fintype ι := Fintype.ofFinite ι
  let i := Finsupp.linearCombination R v
  have hi : Surjective i := by
    rw [← LinearMap.range_eq_top]; rw [Finsupp.range_linearCombination]
    refine IsLocalRing.span_eq_top_of_tmul_eq_basis (R := R) (f := v) bk
      (fun _ => by simp [bk])
  have : Module.Finite R (LinearMap.ker i) :=
    .of_fg (Module.FinitePresentation.fg_ker i hi)
  -- We claim that `i` is actually a bijection,
  -- hence `v` induces an isomorphism `M ≃[R] Rᴵ` showing that `v` is a basis.
  let iequiv : (ι ->₀ R) ≃ₗ[R] M := by
    refine LinearEquiv.ofBijective i ⟨?_, hi⟩
    -- By Nakayama's lemma, it suffices to show that `k ⊗ ker(i) = 0`.
    rw [← LinearMap.ker_eq_bot]; rw [← Submodule.subsingleton_iff_eq_bot]; rw [← IsLocalRing.subsingleton_tensorProduct (R := R)]; rw [subsingleton_iff_forall_eq 0]
    have : Function.Surjective (i.baseChange k) := i.lTensor_surjective _ hi
    -- By construction, `k ⊗ i : kᴵ → k ⊗ M` is bijective.
    have hi' : Function.Bijective (i.baseChange k) := by
      refine ⟨?_, this⟩
      rw [← LinearMap.ker_eq_bot (M := k otimes[R] (ι ->₀ R)) (f := i.baseChange k),
        ← Submodule.finrank_eq_zero (R := k) (M := k otimes[R] (ι ->₀ R)),
        ← Nat.add_right_inj (n := Module.finrank k (LinearMap.range <| i.baseChange k)),
        LinearMap.finrank_range_add_finrank_ker (V := k otimes[R] (ι ->₀ R)),
        LinearMap.range_eq_top.mpr this, finrank_top]
      simp only [Module.finrank_tensorProduct, Module.finrank_self,
        Module.finrank_finsupp_self, one_mul, add_zero]
      rw [Module.finrank_eq_card_basis bk]
    -- On the other hand, `m ⊗ M → M` injective => `Tor₁(k, M) = 0` => `k ⊗ ker(i) → kᴵ` injective.
    intro x
    refine lTensor_injective_of_exact_of_exact_of_rTensor_injective
      (N₁ := LinearMap.ker i) (N₂ := ι ->₀ R) (N₃ := M)
      (f₁ := (𝔪).subtype) (f₂ := Submodule.mkQ 𝔪)
      (g₁ := (LinearMap.ker i).subtype) (g₂ := i) (LinearMap.exact_subtype_mkQ 𝔪)
      (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_ker_map i) hi H ?_ ?_
    · apply Module.Flat.lTensor_preserves_injective_linearMap
      exact Subtype.val_injective
    · apply hi'.injective
      rw [LinearMap.baseChange_eq_ltensor]
      erw [← LinearMap.comp_apply (i.lTensor k), ← LinearMap.lTensor_comp]
      rw [(LinearMap.exact_subtype_ker_map i).linearMap_comp_eq_zero]
      simp only [LinearMap.lTensor_zero, LinearMap.zero_apply, map_zero]
  use Basis.ofRepr iequiv.symm
  intro j
  simp [iequiv, i]

/--
lemma `exists_basis_of_span_of_maximalIdeal_rTensor_injective` / 引理 `exists_basis_of_span_of_maximalIdeal_rTensor_injective`

English:
lemma exists_basis_of_span_of_maximalIdeal_rTensor_injective
  statement: [Module.FinitePresentation R M]
  proof: by
  have := (map_tensorProduct_mk_eq_top (N := Submodule.span R (Set.range v))).mpr hv
  rw [← Submodule.span_image]; rw [← Set.range_comp]; rw [eq_top_iff]; rw [← SetLike.coe_subset_coe]; rw [Submodule.top_coe] at this
  have : Submodule.span k (Set.range (TensorProduct.mk R k M 1 ∘ v)) = ⊤ := by
    rw [eq_top_iff]
    exact Set.Subset.trans this (Submodule.span_subset_span _ _ _)
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' k (TensorProduct.mk R k M 1 ∘ v)
  rw [this] at hsp
  obtain ⟨b, hb⟩ := exists_basis_of_basis_baseChange (v ∘ a) hli hsp H
  use κ, a, b, hb

中文:
引理 存在_basis_of_span_of_maximalIdeal_rTensor_injective
  结论: [模.有限呈现 R M]
  证明: by
  have := (map_tensorProduct_mk_eq_top (N := Submodule.span R (Set.range v))).mpr hv
  rw [← Submodule.span_image]; rw [← Set.range_comp]; rw [eq_top_iff]; rw [← SetLike.coe_subset_coe]; rw [Submodule.top_coe] at this
  have : Submodule.span k (Set.range (TensorProduct.mk R k M 1 ∘ v)) = ⊤ := by
    rw [eq_top_iff]
    exact Set.Subset.trans this (Submodule.span_subset_span _ _ _)
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' k (TensorProduct.mk R k M 1 ∘ v)
  rw [this] at hsp
  obtain ⟨b, hb⟩ := exists_basis_of_basis_baseChange (v ∘ a) hli hsp H
  use κ, a, b, hb

Depends on / 依赖: Set.Subset.trans, Set.range, Set.range_comp, SetLike, SetLike.coe_subset_coe, Submodule, Submodule.span, Submodule.span_image, Submodule.span_subset_span, Submodule.top_coe, Subset, TensorProduct, TensorProduct.mk, coe_subset_coe, eq_top_iff, exists_linearIndependent, map_tensorProduct_mk_eq_top, range_comp, span_image, span_subset_span
-/
lemma exists_basis_of_span_of_maximalIdeal_rTensor_injective [Module.FinitePresentation R M]
    (H : Function.Injective ((𝔪).subtype.rTensor M))
    {ι : Type u} (v : ι -> M) (hv : Submodule.span R (Set.range v) = ⊤) :
    exists (κ : Type u) (a : κ -> ι) (b : Basis κ R M), forall i, b i = v (a i) := by
  have := (map_tensorProduct_mk_eq_top (N := Submodule.span R (Set.range v))).mpr hv
  rw [← Submodule.span_image]; rw [← Set.range_comp]; rw [eq_top_iff]; rw [← SetLike.coe_subset_coe]; rw [Submodule.top_coe] at this
  have : Submodule.span k (Set.range (TensorProduct.mk R k M 1 ∘ v)) = ⊤ := by
    rw [eq_top_iff]
    exact Set.Subset.trans this (Submodule.span_subset_span _ _ _)
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' k (TensorProduct.mk R k M 1 ∘ v)
  rw [this] at hsp
  obtain ⟨b, hb⟩ := exists_basis_of_basis_baseChange (v ∘ a) hli hsp H
  use κ, a, b, hb

/--
lemma `exists_basis_of_span_of_flat` / 引理 `exists_basis_of_span_of_flat`

English:
lemma exists_basis_of_span_of_flat
  statement: [Module.FinitePresentation R M] [Module.Flat R M]
  proof: exists_basis_of_span_of_maximalIdeal_rTensor_injective
    (Module.Flat.rTensor_preserves_injective_linearMap (𝔪).subtype Subtype.val_injective) v hv

中文:
引理 存在_basis_of_span_of_flat
  结论: [模.有限呈现 R M] [模.平坦 R M]
  证明: exists_basis_of_span_of_maximalIdeal_rTensor_injective
    (Module.Flat.rTensor_preserves_injective_linearMap (𝔪).subtype Subtype.val_injective) v hv

Depends on / 依赖: Module, Module.Flat.rTensor_preserves_injective_linearMap, Subtype, Subtype.val_injective, exists_basis_of_span_of_maximalIdeal_rTensor_injective, rTensor_preserves_injective_linearMap, subtype, val_injective
-/
lemma exists_basis_of_span_of_flat [Module.FinitePresentation R M] [Module.Flat R M]
    {ι : Type u} (v : ι -> M) (hv : Submodule.span R (Set.range v) = ⊤) :
    exists (κ : Type u) (a : κ -> ι) (b : Basis κ R M), forall i, b i = v (a i) :=
  exists_basis_of_span_of_maximalIdeal_rTensor_injective
    (Module.Flat.rTensor_preserves_injective_linearMap (𝔪).subtype Subtype.val_injective) v hv

/--
theorem `free_of_maximalIdeal_rTensor_injective` / 定理 `free_of_maximalIdeal_rTensor_injective`

English:
theorem free_of_maximalIdeal_rTensor_injective
  statement: [Module.FinitePresentation R M]
  proof: by
  obtain ⟨_, _, b, _⟩ := exists_basis_of_span_of_maximalIdeal_rTensor_injective H id (by simp)
  exact Free.of_basis b

中文:
定理 free_of_maximalIdeal_rTensor_injective
  结论: [模.有限呈现 R M]
  证明: by
  obtain ⟨_, _, b, _⟩ := exists_basis_of_span_of_maximalIdeal_rTensor_injective H id (by simp)
  exact Free.of_basis b

Depends on / 依赖: Free.of_basis, exists_basis_of_span_of_maximalIdeal_rTensor_injective, of_basis
-/
theorem free_of_maximalIdeal_rTensor_injective [Module.FinitePresentation R M]
    (H : Function.Injective ((𝔪).subtype.rTensor M)) :
    Module.Free R M := by
  obtain ⟨_, _, b, _⟩ := exists_basis_of_span_of_maximalIdeal_rTensor_injective H id (by simp)
  exact Free.of_basis b

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `IsLocalRing.linearIndependent_of_flat` / 定理 `IsLocalRing.linearIndependent_of_flat`

English:
theorem IsLocalRing.linearIndependent_of_flat
  statement: [Flat R M] {ι : Type u} (v : ι -> M)
  proof: by
  rw [linearIndependent_iff']; intro s f hfv i hi
  classical
  induction s using Finset.induction generalizing v i with
  | empty => exact (Finset.notMem_empty _ hi).elim
  | insert n s hn ih => ?_
  rw [← Finset.sum_coe_sort] at hfv
  have ⟨l, a, y, hay, hfa⟩ := Flat.isTrivialRelation_of_sum_smul_eq_zero hfv
  have : v n ∉ 𝔪 • (⊤ : Submodule R M) := by
    simpa only [← LinearMap.ker_tensorProductMk] using! h.ne_zero n
  set n : ↥(insert n s) := ⟨n, Finset.mem_insert_self ..⟩ with n_def
  obtain ⟨j, hj⟩ : exists j, IsUnit (a n j) := by
    contrapose! this
    rw [show v n = _ from hay n]
    exact sum_mem fun _ _ => Submodule.smul_mem_smul (this _) ⟨⟩
  let a' (i : ι) : R := if hi : _ then a ⟨i, hi⟩ j else 0
  have a_eq i : a i j = a' i.1 := by simp_rw [a', dif_pos i.2]
  have hfn : f n = -(∑ i in s, f i * a' i) * hj.unit⁻¹ := by
    rw [← hj.mul_left_inj]; rw [mul_assoc]; rw [hj.val_inv_mul]; rw [mul_one]; rw [eq_neg_iff_add_eq_zero]
    convert! hfa j
    simp_rw [a_eq, Finset.sum_coe_sort _ (fun i => f i * a' i), s.sum_insert hn, n_def]
  let c (i : ι) : R := -(if i = n then 0 else a' i) * hj.unit⁻¹
  specialize ih (v + (c · • v n)) ?_ ?_
  · convert! (linearIndependent_add_smul_iff (c := Ideal.Quotient.mk _ ∘ c) (i := n.1) ?_).mpr h
    · ext; simp [tmul_add]; rfl
    simp_rw [Function.comp_def, c, if_pos, neg_zero, zero_mul, map_zero]
  · rw [Finset.sum_coe_sort _ (fun i => f i • v i), s.sum_insert hn, add_comm, hfn] at hfv
    simp_rw [Pi.add_apply, smul_add, s.sum_add_distrib, c, smul_smul, ← s.sum_smul, ← mul_assoc,
      ← s.sum_mul, mul_neg, s.sum_neg_distrib, ← hfv]
    congr 4
    exact s.sum_congr rfl fun i hi => by rw [if_neg (ne_of_mem_of_not_mem hi hn)]
  obtain hi | hi := Finset.mem_insert.mp hi
  · rw [hi, hfn, Finset.sum_eq_zero, neg_zero, zero_mul]
    intro i hi; rw [ih i hi, zero_mul]
  · exact ih i hi

中文:
定理 是局部环.linearIndependent_of_flat
  结论: [平坦 R M] {ι : 类型u} (v : ι -> M)
  证明: by
  rw [linearIndependent_iff']; intro s f hfv i hi
  classical
  induction s using Finset.induction generalizing v i with
  | empty => exact (Finset.notMem_empty _ hi).elim
  | insert n s hn ih => ?_
  rw [← Finset.sum_coe_sort] at hfv
  have ⟨l, a, y, hay, hfa⟩ := Flat.isTrivialRelation_of_sum_smul_eq_zero hfv
  have : v n ∉ 𝔪 • (⊤ : Submodule R M) := by
    simpa only [← LinearMap.ker_tensorProductMk] using! h.ne_zero n
  set n : ↥(insert n s) := ⟨n, Finset.mem_insert_self ..⟩ with n_def
  obtain ⟨j, hj⟩ : exists j, IsUnit (a n j) := by
    contrapose! this
    rw [show v n = _ from hay n]
    exact sum_mem fun _ _ => Submodule.smul_mem_smul (this _) ⟨⟩
  let a' (i : ι) : R := if hi : _ then a ⟨i, hi⟩ j else 0
  have a_eq i : a i j = a' i.1 := by simp_rw [a', dif_pos i.2]
  have hfn : f n = -(∑ i in s, f i * a' i) * hj.unit⁻¹ := by
    rw [← hj.mul_left_inj]; rw [mul_assoc]; rw [hj.val_inv_mul]; rw [mul_one]; rw [eq_neg_iff_add_eq_zero]
    convert! hfa j
    simp_rw [a_eq, Finset.sum_coe_sort _ (fun i => f i * a' i), s.sum_insert hn, n_def]
  let c (i : ι) : R := -(if i = n then 0 else a' i) * hj.unit⁻¹
  specialize ih (v + (c · • v n)) ?_ ?_
  · convert! (linearIndependent_add_smul_iff (c := Ideal.Quotient.mk _ ∘ c) (i := n.1) ?_).mpr h
    · ext; simp [tmul_add]; rfl
    simp_rw [Function.comp_def, c, if_pos, neg_zero, zero_mul, map_zero]
  · rw [Finset.sum_coe_sort _ (fun i => f i • v i), s.sum_insert hn, add_comm, hfn] at hfv
    simp_rw [Pi.add_apply, smul_add, s.sum_add_distrib, c, smul_smul, ← s.sum_smul, ← mul_assoc,
      ← s.sum_mul, mul_neg, s.sum_neg_distrib, ← hfv]
    congr 4
    exact s.sum_congr rfl fun i hi => by rw [if_neg (ne_of_mem_of_not_mem hi hn)]
  obtain hi | hi := Finset.mem_insert.mp hi
  · rw [hi, hfn, Finset.sum_eq_zero, neg_zero, zero_mul]
    intro i hi; rw [ih i hi, zero_mul]
  · exact ih i hi

Depends on / 依赖: Finset, Finset.induction, Finset.mem_insert_self, Finset.notMem_empty, Finset.sum_coe_sort, Flat.isTrivialRelation_of_sum_smul_eq_zero, LinearMap, LinearMap.ker_tensorProductMk, Submodule, classical, generalizing, h.ne_zero, insert, isTrivialRelation_of_sum_smul_eq_zero, ker_tensorProductMk, linearIndependent_iff, mem_insert_self, n_def, ne_zero, notMem_empty
-/
theorem IsLocalRing.linearIndependent_of_flat [Flat R M] {ι : Type u} (v : ι -> M)
    (h : LinearIndependent k (TensorProduct.mk R k M 1 ∘ v)) : LinearIndependent R v := by
  rw [linearIndependent_iff']; intro s f hfv i hi
  classical
  induction s using Finset.induction generalizing v i with
  | empty => exact (Finset.notMem_empty _ hi).elim
  | insert n s hn ih => ?_
  rw [← Finset.sum_coe_sort] at hfv
  have ⟨l, a, y, hay, hfa⟩ := Flat.isTrivialRelation_of_sum_smul_eq_zero hfv
  have : v n ∉ 𝔪 • (⊤ : Submodule R M) := by
    simpa only [← LinearMap.ker_tensorProductMk] using! h.ne_zero n
  set n : ↥(insert n s) := ⟨n, Finset.mem_insert_self ..⟩ with n_def
  obtain ⟨j, hj⟩ : exists j, IsUnit (a n j) := by
    contrapose! this
    rw [show v n = _ from hay n]
    exact sum_mem fun _ _ => Submodule.smul_mem_smul (this _) ⟨⟩
  let a' (i : ι) : R := if hi : _ then a ⟨i, hi⟩ j else 0
  have a_eq i : a i j = a' i.1 := by simp_rw [a', dif_pos i.2]
  have hfn : f n = -(∑ i in s, f i * a' i) * hj.unit⁻¹ := by
    rw [← hj.mul_left_inj]; rw [mul_assoc]; rw [hj.val_inv_mul]; rw [mul_one]; rw [eq_neg_iff_add_eq_zero]
    convert! hfa j
    simp_rw [a_eq, Finset.sum_coe_sort _ (fun i => f i * a' i), s.sum_insert hn, n_def]
  let c (i : ι) : R := -(if i = n then 0 else a' i) * hj.unit⁻¹
  specialize ih (v + (c · • v n)) ?_ ?_
  · convert! (linearIndependent_add_smul_iff (c := Ideal.Quotient.mk _ ∘ c) (i := n.1) ?_).mpr h
    · ext; simp [tmul_add]; rfl
    simp_rw [Function.comp_def, c, if_pos, neg_zero, zero_mul, map_zero]
  · rw [Finset.sum_coe_sort _ (fun i => f i • v i), s.sum_insert hn, add_comm, hfn] at hfv
    simp_rw [Pi.add_apply, smul_add, s.sum_add_distrib, c, smul_smul, ← s.sum_smul, ← mul_assoc,
      ← s.sum_mul, mul_neg, s.sum_neg_distrib, ← hfv]
    congr 4
    exact s.sum_congr rfl fun i hi => by rw [if_neg (ne_of_mem_of_not_mem hi hn)]
  obtain hi | hi := Finset.mem_insert.mp hi
  · rw [hi, hfn, Finset.sum_eq_zero, neg_zero, zero_mul]
    intro i hi; rw [ih i hi, zero_mul]
  · exact ih i hi

set_option backward.isDefEq.respectTransparency.types false in
open Finsupp in
/--
theorem `IsLocalRing.linearCombination_bijective_of_flat` / 定理 `IsLocalRing.linearCombination_bijective_of_flat`

English:
theorem IsLocalRing.linearCombination_bijective_of_flat
  statement: [Module.Finite R M] [Flat R M] {ι : Type u}
  proof: by
  use linearIndependent_of_flat _ h.1
  rw [← LinearMap.range_eq_top]; rw [range_linearCombination]
  refine span_eq_top_of_tmul_eq_basis _ (.mk h.1 ?_) fun _ => ?_
  · simpa only [top_le_iff, ← range_linearCombination, LinearMap.range_eq_top] using h.2
  · simp

@[stacks 00NZ]

中文:
定理 是局部环.linearCombination_bijective_of_flat
  结论: [模.有限 R M] [平坦 R M] {ι : 类型u}
  证明: by
  use linearIndependent_of_flat _ h.1
  rw [← LinearMap.range_eq_top]; rw [range_linearCombination]
  refine span_eq_top_of_tmul_eq_basis _ (.mk h.1 ?_) fun _ => ?_
  · simpa only [top_le_iff, ← range_linearCombination, LinearMap.range_eq_top] using h.2
  · simp

@[stacks 00NZ]

Depends on / 依赖: LinearMap, LinearMap.range_eq_top, linearIndependent_of_flat, range_eq_top, range_linearCombination, span_eq_top_of_tmul_eq_basis, top_le_iff
-/
theorem IsLocalRing.linearCombination_bijective_of_flat [Module.Finite R M] [Flat R M] {ι : Type u}
    (v : ι -> M) (h : Function.Bijective (linearCombination k (TensorProduct.mk R k M 1 ∘ v))) :
    Function.Bijective (linearCombination R v) := by
  use linearIndependent_of_flat _ h.1
  rw [← LinearMap.range_eq_top]; rw [range_linearCombination]
  refine span_eq_top_of_tmul_eq_basis _ (.mk h.1 ?_) fun _ => ?_
  · simpa only [top_le_iff, ← range_linearCombination, LinearMap.range_eq_top] using h.2
  · simp

@[stacks 00NZ]
/--
theorem `free_of_flat_of_isLocalRing` / 定理 `free_of_flat_of_isLocalRing`

English:
theorem free_of_flat_of_isLocalRing
  given: [Module.Finite R P] [Flat R P]
  statement: Free R P
  proof: let w := Free.chooseBasis k (k otimes[R] P)
  have ⟨v, eq⟩ := (TensorProduct.mk_surjective R P k Quotient.mk_surjective).comp_left w
.of_basis .mk (IsLocalRing.linearIndependent_of_flat _ (eq ▸ w.linearIndependent)) by
    exact (span_eq_top_of_tmul_eq_basis _ w <| congr_fun eq).ge

中文:
定理 free_of_flat_of_isLocalRing
  条件: [模.有限 R P] [平坦 R P]
  结论: 自由 R P
  证明: let w := Free.chooseBasis k (k otimes[R] P)
  have ⟨v, eq⟩ := (TensorProduct.mk_surjective R P k Quotient.mk_surjective).comp_left w
.of_basis .mk (IsLocalRing.linearIndependent_of_flat _ (eq ▸ w.linearIndependent)) by
    exact (span_eq_top_of_tmul_eq_basis _ w <| congr_fun eq).ge

Depends on / 依赖: Free.chooseBasis, IsLocalRing, IsLocalRing.linearIndependent_of_flat, Quotient, Quotient.mk_surjective, TensorProduct, TensorProduct.mk_surjective, chooseBasis, comp_left, congr_fun, linearIndependent, linearIndependent_of_flat, mk_surjective, of_basis, otimes, span_eq_top_of_tmul_eq_basis, w.linearIndependent
-/
theorem free_of_flat_of_isLocalRing [Module.Finite R P] [Flat R P] : Free R P :=
  let w := Free.chooseBasis k (k otimes[R] P)
  have ⟨v, eq⟩ := (TensorProduct.mk_surjective R P k Quotient.mk_surjective).comp_left w
.of_basis .mk (IsLocalRing.linearIndependent_of_flat _ (eq ▸ w.linearIndependent)) by
    exact (span_eq_top_of_tmul_eq_basis _ w <| congr_fun eq).ge

/--
theorem `free_of_lTensor_residueField_injective` / 定理 `free_of_lTensor_residueField_injective`

English:
theorem free_of_lTensor_residueField_injective
  statement: (hg : Surjective g) (h : Exact f g)
  proof: by
  have := Module.finitePresentation_of_free_of_surjective g hg
    (by rw [h.linearMap_ker_eq, LinearMap.range_eq_map]; exact (Module.Finite.fg_top).map f)
  apply free_of_maximalIdeal_rTensor_injective
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  apply lTensor_injective_of_exact_of_exact_of_rTensor_injective
    h hg (LinearMap.exact_subtype_mkQ 𝔪) (Submodule.mkQ_surjective _)
    ((LinearMap.lTensor_inj_iff_rTensor_inj _ _).mp hf)
    (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)

中文:
定理 free_of_lTensor_residueField_injective
  结论: (hg : 满射 g) (h : 正合 f g)
  证明: by
  have := Module.finitePresentation_of_free_of_surjective g hg
    (by rw [h.linearMap_ker_eq, LinearMap.range_eq_map]; exact (Module.Finite.fg_top).map f)
  apply free_of_maximalIdeal_rTensor_injective
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  apply lTensor_injective_of_exact_of_exact_of_rTensor_injective
    h hg (LinearMap.exact_subtype_mkQ 𝔪) (Submodule.mkQ_surjective _)
    ((LinearMap.lTensor_inj_iff_rTensor_inj _ _).mp hf)
    (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)

Depends on / 依赖: Finite, LinearMap, LinearMap.exact_subtype_mkQ, LinearMap.lTensor_inj_iff_rTensor_inj, LinearMap.range_eq_map, Module, Module.Finite.fg_top, Module.Flat.lTensor_preserves_injective_linearMap, Module.finitePresentation_of_free_of_surjective, Submodule, Submodule.mkQ_surjective, Subtype, Subtype.val_injective, exact_subtype_mkQ, fg_top, finitePresentation_of_free_of_surjective, free_of_maximalIdeal_rTensor_injective, h.linearMap_ker_eq, lTensor_inj_iff_rTensor_inj, lTensor_injective_of_exact_of_exact_of_rTensor_injective
-/
theorem free_of_lTensor_residueField_injective (hg : Surjective g) (h : Exact f g)
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N]
    (hf : Function.Injective (f.lTensor k)) :
    Module.Free R P := by
  have := Module.finitePresentation_of_free_of_surjective g hg
    (by rw [h.linearMap_ker_eq, LinearMap.range_eq_map]; exact (Module.Finite.fg_top).map f)
  apply free_of_maximalIdeal_rTensor_injective
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  apply lTensor_injective_of_exact_of_exact_of_rTensor_injective
    h hg (LinearMap.exact_subtype_mkQ 𝔪) (Submodule.mkQ_surjective _)
    ((LinearMap.lTensor_inj_iff_rTensor_inj _ _).mp hf)
    (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)

end Module

/--
theorem `IsLocalRing.split_injective_iff_lTensor_residueField_injective` / 定理 `IsLocalRing.split_injective_iff_lTensor_residueField_injective`

English:
theorem IsLocalRing.split_injective_iff_lTensor_residueField_injective
  statement: [IsLocalRing R]
  proof: by
  constructor
  · intro ⟨l', hl⟩
    have : l'.lTensor (ResidueField R) ∘ₗ l.lTensor (ResidueField R) = .id := by
      rw [← LinearMap.lTensor_comp]; rw [hl]; rw [LinearMap.lTensor_id]
    exact Function.HasLeftInverse.injective ⟨_, LinearMap.congr_fun this⟩
  · intro h
    -- By `Module.free_of_lTensor_residueField_injective`, `k ⊗ l` injective => `N ⧸ l(M)` free.
    have := Module.free_of_lTensor_residueField_injective l (LinearMap.range l).mkQ
      (Submodule.mkQ_surjective _) l.exact_map_mkQ_range h
    -- Hence `l(M)` is projective because `0 → l(M) → N → N ⧸ l(M) → 0` splits.
    have : Module.Projective R (LinearMap.range l) := by
      have := (Exact.split_tfae (LinearMap.exact_subtype_mkQ (LinearMap.range l))
        Subtype.val_injective (Submodule.mkQ_surjective _)).out 0 1
      obtain ⟨l', hl'⟩ := this.mp
         (Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _))
      exact Module.Projective.of_split _ _ hl'
    -- Then `0 → ker l → M → l(M) → 0` splits.
    obtain ⟨l', hl'⟩ : exists l', l' ∘ₗ (LinearMap.ker l).subtype = LinearMap.id := by
      have : Function.Exact (LinearMap.ker l).subtype
          (l.codRestrict (LinearMap.range l) (LinearMap.mem_range_self l)) := by
        rw [LinearMap.exact_iff]; rw [LinearMap.ker_rangeRestrict]; rw [Submodule.range_subtype]
      have := (Exact.split_tfae this
        Subtype.val_injective (fun ⟨x, y, e⟩ => ⟨y, Subtype.ext e⟩)).out 0 1
      exact this.mp (Module.projective_lifting_property _ _ (fun ⟨x, y, e⟩ => ⟨y, Subtype.ext e⟩))
    have : Module.Finite R (LinearMap.ker l) := by
      refine Module.Finite.of_surjective l' ?_
      exact Function.HasRightInverse.surjective ⟨_, DFunLike.congr_fun hl'⟩
    -- And tensoring with `k` preserves the injectivity of the first arrow.
    -- That is, `k ⊗ ker l → k ⊗ M` is also injective.
    have H : Function.Injective ((LinearMap.ker l).subtype.lTensor k) := by
      apply_fun (LinearMap.lTensor k) at hl'
      rw [LinearMap.lTensor_comp]; rw [LinearMap.lTensor_id] at hl'
      exact Function.HasLeftInverse.injective ⟨l'.lTensor k, DFunLike.congr_fun hl'⟩
    -- But by assumption `k ⊗ M → k ⊗ l(M)` is already injective, so `k ⊗ ker l = 0`.
    have : Subsingleton (k otimes[R] LinearMap.ker l) := by
      refine (subsingleton_iff_forall_eq 0).mpr fun y => H (h ?_)
      rw [map_zero]; rw [map_zero]; rw [← LinearMap.comp_apply]; rw [← LinearMap.lTensor_comp]; rw [l.exact_subtype_ker_map.linearMap_comp_eq_zero]; rw [LinearMap.lTensor_zero]; rw [LinearMap.zero_apply]
    -- By Nakayama's lemma, `l` is injective.
    have : Function.Injective l := by
      rwa [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot,
        ← IsLocalRing.subsingleton_tensorProduct (R := R)]
    -- Whence `M ≃ l(M)` is projective and the result follows.
    have := (Exact.split_tfae l.exact_map_mkQ_range this (Submodule.mkQ_surjective _)).out 0 1
    rw [← this]
    exact Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _)

中文:
定理 是局部环.split_injective_iff_lTensor_residueField_injective
  结论: [是局部环 R]
  证明: by
  constructor
  · intro ⟨l', hl⟩
    have : l'.lTensor (ResidueField R) ∘ₗ l.lTensor (ResidueField R) = .id := by
      rw [← LinearMap.lTensor_comp]; rw [hl]; rw [LinearMap.lTensor_id]
    exact Function.HasLeftInverse.injective ⟨_, LinearMap.congr_fun this⟩
  · intro h
    -- By `Module.free_of_lTensor_residueField_injective`, `k ⊗ l` injective => `N ⧸ l(M)` free.
    have := Module.free_of_lTensor_residueField_injective l (LinearMap.range l).mkQ
      (Submodule.mkQ_surjective _) l.exact_map_mkQ_range h
    -- Hence `l(M)` is projective because `0 → l(M) → N → N ⧸ l(M) → 0` splits.
    have : Module.Projective R (LinearMap.range l) := by
      have := (Exact.split_tfae (LinearMap.exact_subtype_mkQ (LinearMap.range l))
        Subtype.val_injective (Submodule.mkQ_surjective _)).out 0 1
      obtain ⟨l', hl'⟩ := this.mp
         (Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _))
      exact Module.Projective.of_split _ _ hl'
    -- Then `0 → ker l → M → l(M) → 0` splits.
    obtain ⟨l', hl'⟩ : exists l', l' ∘ₗ (LinearMap.ker l).subtype = LinearMap.id := by
      have : Function.Exact (LinearMap.ker l).subtype
          (l.codRestrict (LinearMap.range l) (LinearMap.mem_range_self l)) := by
        rw [LinearMap.exact_iff]; rw [LinearMap.ker_rangeRestrict]; rw [Submodule.range_subtype]
      have := (Exact.split_tfae this
        Subtype.val_injective (fun ⟨x, y, e⟩ => ⟨y, Subtype.ext e⟩)).out 0 1
      exact this.mp (Module.projective_lifting_property _ _ (fun ⟨x, y, e⟩ => ⟨y, Subtype.ext e⟩))
    have : Module.Finite R (LinearMap.ker l) := by
      refine Module.Finite.of_surjective l' ?_
      exact Function.HasRightInverse.surjective ⟨_, DFunLike.congr_fun hl'⟩
    -- And tensoring with `k` preserves the injectivity of the first arrow.
    -- That is, `k ⊗ ker l → k ⊗ M` is also injective.
    have H : Function.Injective ((LinearMap.ker l).subtype.lTensor k) := by
      apply_fun (LinearMap.lTensor k) at hl'
      rw [LinearMap.lTensor_comp]; rw [LinearMap.lTensor_id] at hl'
      exact Function.HasLeftInverse.injective ⟨l'.lTensor k, DFunLike.congr_fun hl'⟩
    -- But by assumption `k ⊗ M → k ⊗ l(M)` is already injective, so `k ⊗ ker l = 0`.
    have : Subsingleton (k otimes[R] LinearMap.ker l) := by
      refine (subsingleton_iff_forall_eq 0).mpr fun y => H (h ?_)
      rw [map_zero]; rw [map_zero]; rw [← LinearMap.comp_apply]; rw [← LinearMap.lTensor_comp]; rw [l.exact_subtype_ker_map.linearMap_comp_eq_zero]; rw [LinearMap.lTensor_zero]; rw [LinearMap.zero_apply]
    -- By Nakayama's lemma, `l` is injective.
    have : Function.Injective l := by
      rwa [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot,
        ← IsLocalRing.subsingleton_tensorProduct (R := R)]
    -- Whence `M ≃ l(M)` is projective and the result follows.
    have := (Exact.split_tfae l.exact_map_mkQ_range this (Submodule.mkQ_surjective _)).out 0 1
    rw [← this]
    exact Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _)

Depends on / 依赖: Function, Function.HasLeftInverse.injective, HasLeftInverse, LinearMap, LinearMap.congr_fun, LinearMap.lTensor_comp, LinearMap.lTensor_id, ResidueField, congr_fun, injective, l.lTensor, lTensor, lTensor_comp, lTensor_id
-/
theorem IsLocalRing.split_injective_iff_lTensor_residueField_injective [IsLocalRing R]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N] (l : M ->ₗ[R] N) :
    (exists l', l' ∘ₗ l = LinearMap.id) ↔ Function.Injective (l.lTensor (ResidueField R)) := by
  constructor
  · intro ⟨l', hl⟩
    have : l'.lTensor (ResidueField R) ∘ₗ l.lTensor (ResidueField R) = .id := by
      rw [← LinearMap.lTensor_comp]; rw [hl]; rw [LinearMap.lTensor_id]
    exact Function.HasLeftInverse.injective ⟨_, LinearMap.congr_fun this⟩
  · intro h
    -- By `Module.free_of_lTensor_residueField_injective`, `k ⊗ l` injective => `N ⧸ l(M)` free.
    have := Module.free_of_lTensor_residueField_injective l (LinearMap.range l).mkQ
      (Submodule.mkQ_surjective _) l.exact_map_mkQ_range h
    -- Hence `l(M)` is projective because `0 → l(M) → N → N ⧸ l(M) → 0` splits.
    have : Module.Projective R (LinearMap.range l) := by
      have := (Exact.split_tfae (LinearMap.exact_subtype_mkQ (LinearMap.range l))
        Subtype.val_injective (Submodule.mkQ_surjective _)).out 0 1
      obtain ⟨l', hl'⟩ := this.mp
         (Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _))
      exact Module.Projective.of_split _ _ hl'
    -- Then `0 → ker l → M → l(M) → 0` splits.
    obtain ⟨l', hl'⟩ : exists l', l' ∘ₗ (LinearMap.ker l).subtype = LinearMap.id := by
      have : Function.Exact (LinearMap.ker l).subtype
          (l.codRestrict (LinearMap.range l) (LinearMap.mem_range_self l)) := by
        rw [LinearMap.exact_iff]; rw [LinearMap.ker_rangeRestrict]; rw [Submodule.range_subtype]
      have := (Exact.split_tfae this
        Subtype.val_injective (fun ⟨x, y, e⟩ => ⟨y, Subtype.ext e⟩)).out 0 1
      exact this.mp (Module.projective_lifting_property _ _ (fun ⟨x, y, e⟩ => ⟨y, Subtype.ext e⟩))
    have : Module.Finite R (LinearMap.ker l) := by
      refine Module.Finite.of_surjective l' ?_
      exact Function.HasRightInverse.surjective ⟨_, DFunLike.congr_fun hl'⟩
    -- And tensoring with `k` preserves the injectivity of the first arrow.
    -- That is, `k ⊗ ker l → k ⊗ M` is also injective.
    have H : Function.Injective ((LinearMap.ker l).subtype.lTensor k) := by
      apply_fun (LinearMap.lTensor k) at hl'
      rw [LinearMap.lTensor_comp]; rw [LinearMap.lTensor_id] at hl'
      exact Function.HasLeftInverse.injective ⟨l'.lTensor k, DFunLike.congr_fun hl'⟩
    -- But by assumption `k ⊗ M → k ⊗ l(M)` is already injective, so `k ⊗ ker l = 0`.
    have : Subsingleton (k otimes[R] LinearMap.ker l) := by
      refine (subsingleton_iff_forall_eq 0).mpr fun y => H (h ?_)
      rw [map_zero]; rw [map_zero]; rw [← LinearMap.comp_apply]; rw [← LinearMap.lTensor_comp]; rw [l.exact_subtype_ker_map.linearMap_comp_eq_zero]; rw [LinearMap.lTensor_zero]; rw [LinearMap.zero_apply]
    -- By Nakayama's lemma, `l` is injective.
    have : Function.Injective l := by
      rwa [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot,
        ← IsLocalRing.subsingleton_tensorProduct (R := R)]
    -- Whence `M ≃ l(M)` is projective and the result follows.
    have := (Exact.split_tfae l.exact_map_mkQ_range this (Submodule.mkQ_surjective _)).out 0 1
    rw [← this]
    exact Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _)

end

namespace Module

open Ideal TensorProduct Submodule

variable (R M) [Finite (MaximalSpectrum R)] [AddCommGroup M] [Module R M]

/--
theorem `nonempty_basis_of_flat_of_finrank_eq` / 定理 `nonempty_basis_of_flat_of_finrank_eq`

English:
theorem nonempty_basis_of_flat_of_finrank_eq
  statement: [Module.Finite R M] [Flat R M]
  proof: by
  let := @Quotient.field
  /- For every maximal ideal `P`, `R⧸P ⊗[R] M` is an `n`-dimensional vector space over the field
    `R⧸P` by assumption, so we can choose a basis `b' P` indexed by `Fin n`. -/
  have b' (P) := Module.finBasisOfFinrankEq _ _ (rk P)
  /- By Chinese remainder theorem for modules, there exist `n` elements `b i : M` that reduces
    to `b' P i` modulo each maximal ideal `P`. -/
  choose b hb using fun i => pi_tensorProductMk_quotient_surjective M _
    (fun _ _ ne => isCoprime_of_isMaximal (MaximalSpectrum.ext_iff.ne.mp ne)) (b' · i)
  /- It suffices to show the linear map `Rⁿ → M` induced by `b` is bijective, for which
    it suffices to show `Rₚⁿ → Rₚ ⊗[R] M` is bijective for each maximal ideal `P`. -/
refine ⟨⟨.symm .ofBijective (Finsupp.linearCombination R b) bijective_of_isLocalized_maximal
    _ (fun P _ => Finsupp.mapRange.linearMap (Algebra.linearMap R (Localization P.primeCompl)))
    _ (fun P _ => TensorProduct.mk R (Localization P.primeCompl) M 1) _ fun P _ => ?_⟩⟩
  rw [IsLocalizedModule.map_linearCombination]; rw [LinearMap.coe_restrictScalars]
  /- Since `M` is finite flat, it suffices to show
    `(Rₚ⧸PRₚ)ⁿ → Rₚ⧸PRₚ ⊗[Rₚ] Rₚ ⊗[R] M ≃ Rₚ⧸PRₚ ⊗[R⧸P] R⧸P ⊗[R] M` is bijective,
    which follows from that `(R⧸P)ⁿ → R⧸P ⊗[R] M` is bijective. -/
  apply IsLocalRing.linearCombination_bijective_of_flat
  rw [← (AlgebraTensorModule.cancelBaseChange _ _ P.ResidueField ..).comp_bijective]; rw [← (AlgebraTensorModule.cancelBaseChange R (R ⧸ P) P.ResidueField ..).symm.comp_bijective]
  convert! ((b' ⟨P, ‹_›⟩).repr.lTensor _ ≪≫ₗ finsuppScalarRight _ _ P.ResidueField _).symm.bijective
  refine funext fun r => Finsupp.induction_linear r (by simp) (by simp +contextual) fun _ _ => ?_
  simp [smul_tmul', ← funext_iff.mp (hb _)]

中文:
定理 nonempty_basis_of_flat_of_finrank_eq
  结论: [模.有限 R M] [平坦 R M]
  证明: by
  let := @Quotient.field
  /- For every maximal ideal `P`, `R⧸P ⊗[R] M` is an `n`-dimensional vector space over the field
    `R⧸P` by assumption, so we can choose a basis `b' P` indexed by `Fin n`. -/
  have b' (P) := Module.finBasisOfFinrankEq _ _ (rk P)
  /- By Chinese remainder theorem for modules, there exist `n` elements `b i : M` that reduces
    to `b' P i` modulo each maximal ideal `P`. -/
  choose b hb using fun i => pi_tensorProductMk_quotient_surjective M _
    (fun _ _ ne => isCoprime_of_isMaximal (MaximalSpectrum.ext_iff.ne.mp ne)) (b' · i)
  /- It suffices to show the linear map `Rⁿ → M` induced by `b` is bijective, for which
    it suffices to show `Rₚⁿ → Rₚ ⊗[R] M` is bijective for each maximal ideal `P`. -/
refine ⟨⟨.symm .ofBijective (Finsupp.linearCombination R b) bijective_of_isLocalized_maximal
    _ (fun P _ => Finsupp.mapRange.linearMap (Algebra.linearMap R (Localization P.primeCompl)))
    _ (fun P _ => TensorProduct.mk R (Localization P.primeCompl) M 1) _ fun P _ => ?_⟩⟩
  rw [IsLocalizedModule.map_linearCombination]; rw [LinearMap.coe_restrictScalars]
  /- Since `M` is finite flat, it suffices to show
    `(Rₚ⧸PRₚ)ⁿ → Rₚ⧸PRₚ ⊗[Rₚ] Rₚ ⊗[R] M ≃ Rₚ⧸PRₚ ⊗[R⧸P] R⧸P ⊗[R] M` is bijective,
    which follows from that `(R⧸P)ⁿ → R⧸P ⊗[R] M` is bijective. -/
  apply IsLocalRing.linearCombination_bijective_of_flat
  rw [← (AlgebraTensorModule.cancelBaseChange _ _ P.ResidueField ..).comp_bijective]; rw [← (AlgebraTensorModule.cancelBaseChange R (R ⧸ P) P.ResidueField ..).symm.comp_bijective]
  convert! ((b' ⟨P, ‹_›⟩).repr.lTensor _ ≪≫ₗ finsuppScalarRight _ _ P.ResidueField _).symm.bijective
  refine funext fun r => Finsupp.induction_linear r (by simp) (by simp +contextual) fun _ _ => ?_
  simp [smul_tmul', ← funext_iff.mp (hb _)]
-/
@[stacks 02M9] theorem nonempty_basis_of_flat_of_finrank_eq [Module.Finite R M] [Flat R M]
    (n : Nat) (rk : forall P : MaximalSpectrum R, finrank (R ⧸ P.1) ((R ⧸ P.1) otimes[R] M) = n) :
    Nonempty (Basis (Fin n) R M) := by
  let := @Quotient.field
  /- For every maximal ideal `P`, `R⧸P ⊗[R] M` is an `n`-dimensional vector space over the field
    `R⧸P` by assumption, so we can choose a basis `b' P` indexed by `Fin n`. -/
  have b' (P) := Module.finBasisOfFinrankEq _ _ (rk P)
  /- By Chinese remainder theorem for modules, there exist `n` elements `b i : M` that reduces
    to `b' P i` modulo each maximal ideal `P`. -/
  choose b hb using fun i => pi_tensorProductMk_quotient_surjective M _
    (fun _ _ ne => isCoprime_of_isMaximal (MaximalSpectrum.ext_iff.ne.mp ne)) (b' · i)
  /- It suffices to show the linear map `Rⁿ → M` induced by `b` is bijective, for which
    it suffices to show `Rₚⁿ → Rₚ ⊗[R] M` is bijective for each maximal ideal `P`. -/
refine ⟨⟨.symm .ofBijective (Finsupp.linearCombination R b) bijective_of_isLocalized_maximal
    _ (fun P _ => Finsupp.mapRange.linearMap (Algebra.linearMap R (Localization P.primeCompl)))
    _ (fun P _ => TensorProduct.mk R (Localization P.primeCompl) M 1) _ fun P _ => ?_⟩⟩
  rw [IsLocalizedModule.map_linearCombination]; rw [LinearMap.coe_restrictScalars]
  /- Since `M` is finite flat, it suffices to show
    `(Rₚ⧸PRₚ)ⁿ → Rₚ⧸PRₚ ⊗[Rₚ] Rₚ ⊗[R] M ≃ Rₚ⧸PRₚ ⊗[R⧸P] R⧸P ⊗[R] M` is bijective,
    which follows from that `(R⧸P)ⁿ → R⧸P ⊗[R] M` is bijective. -/
  apply IsLocalRing.linearCombination_bijective_of_flat
  rw [← (AlgebraTensorModule.cancelBaseChange _ _ P.ResidueField ..).comp_bijective]; rw [← (AlgebraTensorModule.cancelBaseChange R (R ⧸ P) P.ResidueField ..).symm.comp_bijective]
  convert! ((b' ⟨P, ‹_›⟩).repr.lTensor _ ≪≫ₗ finsuppScalarRight _ _ P.ResidueField _).symm.bijective
  refine funext fun r => Finsupp.induction_linear r (by simp) (by simp +contextual) fun _ _ => ?_
  simp [smul_tmul', ← funext_iff.mp (hb _)]

/--
theorem `free_of_flat_of_finrank_eq` / 定理 `free_of_flat_of_finrank_eq`

English:
theorem free_of_flat_of_finrank_eq
  statement: [Module.Finite R M] [Flat R M]
  proof: have ⟨b⟩ := nonempty_basis_of_flat_of_finrank_eq R M n rk
  .of_basis b

中文:
定理 free_of_flat_of_finrank_eq
  结论: [模.有限 R M] [平坦 R M]
  证明: have ⟨b⟩ := nonempty_basis_of_flat_of_finrank_eq R M n rk
  .of_basis b
-/
@[stacks 02M9] theorem free_of_flat_of_finrank_eq [Module.Finite R M] [Flat R M]
    (n : Nat) (rk : forall P : MaximalSpectrum R, finrank (R ⧸ P.1) ((R ⧸ P.1) otimes[R] M) = n) :
    Free R M :=
  have ⟨b⟩ := nonempty_basis_of_flat_of_finrank_eq R M n rk
  .of_basis b

end Module
