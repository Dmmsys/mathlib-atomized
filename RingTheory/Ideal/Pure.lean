/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Pure ideals

An ideal `I` of a ring `R` is called pure if `R ⧸ I` is flat over `R`
(see [Stacks 04PR](https://stacks.math.columbia.edu/tag/04PR)). In this file we show
some properties of such ideals.

## Main results and definitions

- `Ideal.Pure`: An ideal `I` of `R` is pure if `R ⧸ I` is `R`-flat.
- `Ideal.inf_eq_mul_of_pure`: If `I` is pure, `I ⊓ J = I * J` for every ideal `J`.
- `Ideal.Pure.of_inf_eq_mul`: If for any f.g. ideal `J`, the equality `I ⊓ J = I * J` holds, then
  `I` is pure.
- `Ideal.zeroLocus_inj_of_pure`: If `I` and `J` are pure ideals such that `V(I) = V(J)`, then
  `I = J`.
-/

public section

variable {R : Type*} [CommRing R]

open TensorProduct PrimeSpectrum

/-- An ideal `I` of `R` is pure if `R ⧸ I` is a flat `R`-module. -/
@[stacks 04PR]
/--
Definition of `Ideal.Pure` / `Ideal.Pure` 的定义

English:
abbreviation Ideal.Pure
  signature: (I : Ideal R)
  body: Module.Flat R (R ⧸ I)

中文:
缩写 理想.Pure
  签名: (I : 理想 R)
  定义体: Module.Flat R (R ⧸ I)

Depends on / 依赖: Module, Module.Flat
-/
abbrev Ideal.Pure (I : Ideal R) : Prop :=
  Module.Flat R (R ⧸ I)

/--
lemma `injective_lTensor_quotient_iff_inf_eq_mul` / 引理 `injective_lTensor_quotient_iff_inf_eq_mul`

English:
lemma injective_lTensor_quotient_iff_inf_eq_mul
  given: (I J : Ideal R)
  proof: by
  let f : J ⧸ (I • ⊤ : Submodule R J) ->ₗ[R] R ⧸ I :=
Submodule.mapQ _ _ J.subtype by
      simp [← Submodule.map_le_iff_le_comap, Ideal.mul_le_left]
  have : J.subtype.lTensor (R ⧸ I) =
      (TensorProduct.rid R (R ⧸ I)).symm ∘ₗ f ∘ₗ TensorProduct.quotTensorEquivQuotSMul J I := by
    ext
    simp [f, ← Ideal.Quotient.algebraMap_eq, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rw [this]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective,
    EquivLike.injective_comp, ← LinearMap.ker_eq_bot, f, Submodule.ker_mapQ,
    ← LinearMap.le_ker_iff_map, Submodule.ker_mkQ,
    ← (Submodule.map_le_map_iff_of_injective J.injective_subtype)]
  simp [inf_comm, le_antisymm_iff, Ideal.mul_le_inf (I := I) (J := J)]

@[stacks 04PS "(1) => (2)"]

中文:
引理 injective_lTensor_quotient_iff_inf_eq_mul
  条件: (I J : 理想 R)
  证明: by
  let f : J ⧸ (I • ⊤ : Submodule R J) ->ₗ[R] R ⧸ I :=
Submodule.mapQ _ _ J.subtype by
      simp [← Submodule.map_le_iff_le_comap, Ideal.mul_le_left]
  have : J.subtype.lTensor (R ⧸ I) =
      (TensorProduct.rid R (R ⧸ I)).symm ∘ₗ f ∘ₗ TensorProduct.quotTensorEquivQuotSMul J I := by
    ext
    simp [f, ← Ideal.Quotient.algebraMap_eq, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rw [this]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective,
    EquivLike.injective_comp, ← LinearMap.ker_eq_bot, f, Submodule.ker_mapQ,
    ← LinearMap.le_ker_iff_map, Submodule.ker_mkQ,
    ← (Submodule.map_le_map_iff_of_injective J.injective_subtype)]
  simp [inf_comm, le_antisymm_iff, Ideal.mul_le_inf (I := I) (J := J)]

@[stacks 04PS "(1) => (2)"]

Depends on / 依赖: Algebra, Algebra.TensorProduct.tmul_one_eq_one_tmul, EmbeddingLike, EmbeddingLike.comp_injective, EquivLike, EquivLike.injective_comp, Ideal.Quotient.algebraMap_eq, Ideal.mul_le_left, J.subtype, J.subtype.lTensor, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, LinearMap.ker_eq_bot, Quotient, Submodule, Submodule.mapQ, Submodule.map_le_iff_le_comap, TensorProduct
-/
lemma injective_lTensor_quotient_iff_inf_eq_mul (I J : Ideal R) :
    Function.Injective (J.subtype.lTensor (R ⧸ I)) ↔ I ⊓ J = I * J := by
  let f : J ⧸ (I • ⊤ : Submodule R J) ->ₗ[R] R ⧸ I :=
Submodule.mapQ _ _ J.subtype by
      simp [← Submodule.map_le_iff_le_comap, Ideal.mul_le_left]
  have : J.subtype.lTensor (R ⧸ I) =
      (TensorProduct.rid R (R ⧸ I)).symm ∘ₗ f ∘ₗ TensorProduct.quotTensorEquivQuotSMul J I := by
    ext
    simp [f, ← Ideal.Quotient.algebraMap_eq, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rw [this]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective,
    EquivLike.injective_comp, ← LinearMap.ker_eq_bot, f, Submodule.ker_mapQ,
    ← LinearMap.le_ker_iff_map, Submodule.ker_mkQ,
    ← (Submodule.map_le_map_iff_of_injective J.injective_subtype)]
  simp [inf_comm, le_antisymm_iff, Ideal.mul_le_inf (I := I) (J := J)]

@[stacks 04PS "(1) => (2)"]
/--
lemma `Ideal.inf_eq_mul_of_pure` / 引理 `Ideal.inf_eq_mul_of_pure`

English:
lemma Ideal.inf_eq_mul_of_pure
  given: (I J : Ideal R) [I.Pure]
  proof: by
  rw [← injective_lTensor_quotient_iff_inf_eq_mul]
  apply Module.Flat.lTensor_preserves_injective_linearMap
  exact J.injective_subtype

中文:
引理 理想.inf_eq_mul_of_pure
  条件: (I J : 理想 R) [I.Pure]
  证明: by
  rw [← injective_lTensor_quotient_iff_inf_eq_mul]
  apply Module.Flat.lTensor_preserves_injective_linearMap
  exact J.injective_subtype

Depends on / 依赖: J.injective_subtype, Module, Module.Flat.lTensor_preserves_injective_linearMap, injective_lTensor_quotient_iff_inf_eq_mul, injective_subtype, lTensor_preserves_injective_linearMap
-/
lemma Ideal.inf_eq_mul_of_pure (I J : Ideal R) [I.Pure] :
    I ⊓ J = I * J := by
  rw [← injective_lTensor_quotient_iff_inf_eq_mul]
  apply Module.Flat.lTensor_preserves_injective_linearMap
  exact J.injective_subtype

/--
lemma `Ideal.isIdempotentElem_of_pure` / 引理 `Ideal.isIdempotentElem_of_pure`

English:
lemma Ideal.isIdempotentElem_of_pure
  given: (I : Ideal R) [I.Pure]
  statement: IsIdempotentElem I
  proof: by
  simp [IsIdempotentElem, ← Ideal.inf_eq_mul_of_pure]

中文:
引理 理想.isIdempotentElem_of_pure
  条件: (I : 理想 R) [I.Pure]
  结论: IsIdempotentElem I
  证明: by
  simp [IsIdempotentElem, ← Ideal.inf_eq_mul_of_pure]

Depends on / 依赖: Ideal.inf_eq_mul_of_pure, IsIdempotentElem, inf_eq_mul_of_pure
-/
lemma Ideal.isIdempotentElem_of_pure (I : Ideal R) [I.Pure] : IsIdempotentElem I := by
  simp [IsIdempotentElem, ← Ideal.inf_eq_mul_of_pure]

/--
lemma `Ideal.Pure.of_isIdempotentElem` / 引理 `Ideal.Pure.of_isIdempotentElem`

English:
lemma Ideal.Pure.of_isIdempotentElem
  given: {I : Ideal R} (h : I.FG) (h' : IsIdempotentElem I)
  proof: by
  rw [Ideal.isIdempotentElem_iff_of_fg _ h] at h'
  obtain ⟨e, he, rfl⟩ := h'
  have : Module.Flat R ((R ⧸ R ∙ e) × R ⧸ span {1 - e}) :=
.of_linearEquiv AlgEquiv.prodQuotientOfIsIdempotentElem R he he.one_sub (by simp)
.toLinearEquiv.symm (by grind [IsIdempotentElem])
  apply Module.Flat.of_retract (LinearMap.inl R _ (R ⧸ span {1 - e})) (LinearMap.fst R _ _)
  simp

@[stacks 04PS "(3) => (1)"]

中文:
引理 理想.Pure.of_isIdempotentElem
  条件: {I : 理想 R} (h : I.FG) (h' : IsIdempotentElem I)
  证明: by
  rw [Ideal.isIdempotentElem_iff_of_fg _ h] at h'
  obtain ⟨e, he, rfl⟩ := h'
  have : Module.Flat R ((R ⧸ R ∙ e) × R ⧸ span {1 - e}) :=
.of_linearEquiv AlgEquiv.prodQuotientOfIsIdempotentElem R he he.one_sub (by simp)
.toLinearEquiv.symm (by grind [IsIdempotentElem])
  apply Module.Flat.of_retract (LinearMap.inl R _ (R ⧸ span {1 - e})) (LinearMap.fst R _ _)
  simp

@[stacks 04PS "(3) => (1)"]

Depends on / 依赖: AlgEquiv, AlgEquiv.prodQuotientOfIsIdempotentElem, Ideal.isIdempotentElem_iff_of_fg, IsIdempotentElem, LinearMap, LinearMap.fst, LinearMap.inl, Module, Module.Flat, Module.Flat.of_retract, he.one_sub, isIdempotentElem_iff_of_fg, of_linearEquiv, of_retract, one_sub, prodQuotientOfIsIdempotentElem, toLinearEquiv, toLinearEquiv.symm
-/
lemma Ideal.Pure.of_isIdempotentElem {I : Ideal R} (h : I.FG) (h' : IsIdempotentElem I) :
    I.Pure := by
  rw [Ideal.isIdempotentElem_iff_of_fg _ h] at h'
  obtain ⟨e, he, rfl⟩ := h'
  have : Module.Flat R ((R ⧸ R ∙ e) × R ⧸ span {1 - e}) :=
.of_linearEquiv AlgEquiv.prodQuotientOfIsIdempotentElem R he he.one_sub (by simp)
.toLinearEquiv.symm (by grind [IsIdempotentElem])
  apply Module.Flat.of_retract (LinearMap.inl R _ (R ⧸ span {1 - e})) (LinearMap.fst R _ _)
  simp

@[stacks 04PS "(3) => (1)"]
/--
lemma `Ideal.Pure.of_inf_eq_mul` / 引理 `Ideal.Pure.of_inf_eq_mul`

English:
lemma Ideal.Pure.of_inf_eq_mul
  given: (I : Ideal R) (H : forall ⦃J : Ideal R⦄, J.FG -> I ⊓ J = I * J)
  proof: by
  rw [Pure]; rw [Module.Flat.iff_lTensor_injective]
  intro J hJ
  rw [injective_lTensor_quotient_iff_inf_eq_mul]
  exact H hJ

@[stacks 04PS "(1) => (5)"]

中文:
引理 理想.Pure.of_inf_eq_mul
  条件: (I : 理想 R) (H : 对任意 ⦃J : 理想 R⦄, J.FG -> I ⊓ J = I * J)
  证明: by
  rw [Pure]; rw [Module.Flat.iff_lTensor_injective]
  intro J hJ
  rw [injective_lTensor_quotient_iff_inf_eq_mul]
  exact H hJ

@[stacks 04PS "(1) => (5)"]

Depends on / 依赖: Module, Module.Flat.iff_lTensor_injective, iff_lTensor_injective, injective_lTensor_quotient_iff_inf_eq_mul
-/
lemma Ideal.Pure.of_inf_eq_mul (I : Ideal R) (H : forall ⦃J : Ideal R⦄, J.FG -> I ⊓ J = I * J) :
    I.Pure := by
  rw [Pure]; rw [Module.Flat.iff_lTensor_injective]
  intro J hJ
  rw [injective_lTensor_quotient_iff_inf_eq_mul]
  exact H hJ

@[stacks 04PS "(1) => (5)"]
/--
lemma `Ideal.exists_eq_mul_of_pure` / 引理 `Ideal.exists_eq_mul_of_pure`

English:
lemma Ideal.exists_eq_mul_of_pure
  given: {I : Ideal R} [I.Pure] {x : R} (hx : x in I)
  proof: by
  suffices h : x in I * Ideal.span {x} by
    rw [Ideal.mem_mul_span_singleton] at h
    grind
  rw [← I.inf_eq_mul_of_pure]
  exact ⟨hx, subset_span rfl⟩

@[stacks 04PS "(5) => (7)"]

中文:
引理 理想.存在_eq_mul_of_pure
  条件: {I : 理想 R} [I.Pure] {x : R} (hx : x in I)
  证明: by
  suffices h : x in I * Ideal.span {x} by
    rw [Ideal.mem_mul_span_singleton] at h
    grind
  rw [← I.inf_eq_mul_of_pure]
  exact ⟨hx, subset_span rfl⟩

@[stacks 04PS "(5) => (7)"]

Depends on / 依赖: I.inf_eq_mul_of_pure, Ideal.mem_mul_span_singleton, Ideal.span, inf_eq_mul_of_pure, mem_mul_span_singleton, subset_span
-/
lemma Ideal.exists_eq_mul_of_pure {I : Ideal R} [I.Pure] {x : R} (hx : x in I) :
    exists y in I, x = x * y := by
  suffices h : x in I * Ideal.span {x} by
    rw [Ideal.mem_mul_span_singleton] at h
    grind
  rw [← I.inf_eq_mul_of_pure]
  exact ⟨hx, subset_span rfl⟩

@[stacks 04PS "(5) => (7)"]
/--
lemma `Ideal.le_ker_atPrime_of_forall_exists_eq_mul` / 引理 `Ideal.le_ker_atPrime_of_forall_exists_eq_mul`

English:
lemma Ideal.le_ker_atPrime_of_forall_exists_eq_mul
  statement: {I : Ideal R}
  proof: by
  intro x hx
  obtain ⟨y, hy, heq⟩ := h _ hx
  have : IsUnit (algebraMap R (Localization.AtPrime p) (1 - y)) := by
    rw [IsLocalization.algebraMap_isUnit_iff p.primeCompl]
    refine ⟨1 - y, fun hz => p.one_notMem ?_, by simp⟩
    rw [← sub_add_cancel 1 y]
    exact Ideal.add_mem _ hz (hle hy)
  have hzero : x * (1 - y) = 0 := by simp [mul_sub, ← heq]
  simp only [RingHom.mem_ker, ← this.mul_left_eq_zero, ← RingHom.map_mul, hzero, RingHom.map_zero]

中文:
引理 理想.le_ker_atPrime_of_对任意_存在_eq_mul
  结论: {I : 理想 R}
  证明: by
  intro x hx
  obtain ⟨y, hy, heq⟩ := h _ hx
  have : IsUnit (algebraMap R (Localization.AtPrime p) (1 - y)) := by
    rw [IsLocalization.algebraMap_isUnit_iff p.primeCompl]
    refine ⟨1 - y, fun hz => p.one_notMem ?_, by simp⟩
    rw [← sub_add_cancel 1 y]
    exact Ideal.add_mem _ hz (hle hy)
  have hzero : x * (1 - y) = 0 := by simp [mul_sub, ← heq]
  simp only [RingHom.mem_ker, ← this.mul_left_eq_zero, ← RingHom.map_mul, hzero, RingHom.map_zero]

Depends on / 依赖: AtPrime, Ideal.add_mem, IsLocalization, IsLocalization.algebraMap_isUnit_iff, IsUnit, Localization, Localization.AtPrime, RingHom, RingHom.map_mul, RingHom.map_zero, RingHom.mem_ker, add_mem, algebraMap, algebraMap_isUnit_iff, map_mul, map_zero, mem_ker, mul_left_eq_zero, mul_sub, one_notMem
-/
lemma Ideal.le_ker_atPrime_of_forall_exists_eq_mul {I : Ideal R}
    (h : forall x in I, exists y in I, x = x * y) {p : Ideal R} [p.IsPrime] (hle : I <= p) :
    I <= RingHom.ker (algebraMap R <| Localization.AtPrime p) := by
  intro x hx
  obtain ⟨y, hy, heq⟩ := h _ hx
  have : IsUnit (algebraMap R (Localization.AtPrime p) (1 - y)) := by
    rw [IsLocalization.algebraMap_isUnit_iff p.primeCompl]
    refine ⟨1 - y, fun hz => p.one_notMem ?_, by simp⟩
    rw [← sub_add_cancel 1 y]
    exact Ideal.add_mem _ hz (hle hy)
  have hzero : x * (1 - y) = 0 := by simp [mul_sub, ← heq]
  simp only [RingHom.mem_ker, ← this.mul_left_eq_zero, ← RingHom.map_mul, hzero, RingHom.map_zero]

/--
lemma `Ideal.ker_piRingHom_atPrime_eq_of_pure` / 引理 `Ideal.ker_piRingHom_atPrime_eq_of_pure`

English:
lemma Ideal.ker_piRingHom_atPrime_eq_of_pure
  given: (I : Ideal R) [I.Pure]
  proof: by
  refine le_antisymm ?_ fun x hx => ?_
  · rw [Pi.ker_ringHom]
    refine le_trans ?_ I.iInf_ker_le
    simp only [le_iInf_iff]
    exact fun i hi hle => iInf_le_of_le ⟨⟨i, hi⟩, hle⟩ le_rfl
  · rw [RingHom.mem_ker]
    ext p
    rw [RingHom.pi_apply]; rw [Pi.zero_apply]
    exact Ideal.le_ker_atPrime_of_forall_exists_eq_mul
      (fun x hx => Ideal.exists_eq_mul_of_pure hx) p.2 hx

@[stacks 04PT]

中文:
引理 理想.ker_piRingHom_atPrime_eq_of_pure
  条件: (I : 理想 R) [I.Pure]
  证明: by
  refine le_antisymm ?_ fun x hx => ?_
  · rw [Pi.ker_ringHom]
    refine le_trans ?_ I.iInf_ker_le
    simp only [le_iInf_iff]
    exact fun i hi hle => iInf_le_of_le ⟨⟨i, hi⟩, hle⟩ le_rfl
  · rw [RingHom.mem_ker]
    ext p
    rw [RingHom.pi_apply]; rw [Pi.zero_apply]
    exact Ideal.le_ker_atPrime_of_forall_exists_eq_mul
      (fun x hx => Ideal.exists_eq_mul_of_pure hx) p.2 hx

@[stacks 04PT]

Depends on / 依赖: I.iInf_ker_le, Ideal.exists_eq_mul_of_pure, Ideal.le_ker_atPrime_of_forall_exists_eq_mul, Pi.ker_ringHom, Pi.zero_apply, RingHom, RingHom.mem_ker, RingHom.pi_apply, exists_eq_mul_of_pure, iInf_ker_le, iInf_le_of_le, ker_ringHom, le_antisymm, le_iInf_iff, le_ker_atPrime_of_forall_exists_eq_mul, le_rfl, le_trans, mem_ker, pi_apply, zero_apply
-/
lemma Ideal.ker_piRingHom_atPrime_eq_of_pure (I : Ideal R) [I.Pure] :
    RingHom.ker
      (RingHom.pi fun p : zeroLocus (I : Set R) =>
        algebraMap R (Localization.AtPrime p.val.asIdeal)) = I := by
  refine le_antisymm ?_ fun x hx => ?_
  · rw [Pi.ker_ringHom]
    refine le_trans ?_ I.iInf_ker_le
    simp only [le_iInf_iff]
    exact fun i hi hle => iInf_le_of_le ⟨⟨i, hi⟩, hle⟩ le_rfl
  · rw [RingHom.mem_ker]
    ext p
    rw [RingHom.pi_apply]; rw [Pi.zero_apply]
    exact Ideal.le_ker_atPrime_of_forall_exists_eq_mul
      (fun x hx => Ideal.exists_eq_mul_of_pure hx) p.2 hx

@[stacks 04PT]
/--
lemma `Ideal.zeroLocus_inj_of_pure` / 引理 `Ideal.zeroLocus_inj_of_pure`

English:
lemma Ideal.zeroLocus_inj_of_pure
  given: {I J : Ideal R} [I.Pure] [J.Pure]
  proof: by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rw [← I.ker_piRingHom_atPrime_eq_of_pure]; rw [← J.ker_piRingHom_atPrime_eq_of_pure]
  generalize hs : zeroLocus (I : Set R) = s
  generalize ht : zeroLocus (J : Set R) = t
  obtain rfl : s = t := by rw [← hs, ← ht, h]
  rfl

中文:
引理 理想.zeroLocus_inj_of_pure
  条件: {I J : 理想 R} [I.Pure] [J.Pure]
  证明: by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rw [← I.ker_piRingHom_atPrime_eq_of_pure]; rw [← J.ker_piRingHom_atPrime_eq_of_pure]
  generalize hs : zeroLocus (I : Set R) = s
  generalize ht : zeroLocus (J : Set R) = t
  obtain rfl : s = t := by rw [← hs, ← ht, h]
  rfl

Depends on / 依赖: I.ker_piRingHom_atPrime_eq_of_pure, J.ker_piRingHom_atPrime_eq_of_pure, generalize, ker_piRingHom_atPrime_eq_of_pure, zeroLocus
-/
lemma Ideal.zeroLocus_inj_of_pure {I J : Ideal R} [I.Pure] [J.Pure] :
    zeroLocus (I : Set R) = zeroLocus J ↔ I = J := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rw [← I.ker_piRingHom_atPrime_eq_of_pure]; rw [← J.ker_piRingHom_atPrime_eq_of_pure]
  generalize hs : zeroLocus (I : Set R) = s
  generalize ht : zeroLocus (J : Set R) = t
  obtain rfl : s = t := by rw [← hs, ← ht, h]
  rfl
