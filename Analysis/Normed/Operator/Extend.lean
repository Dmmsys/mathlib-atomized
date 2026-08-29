/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Zhouhang Zhou
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-!

# Extension of continuous linear maps on Banach spaces

In this file we provide two different ways to extend a continuous linear map defined on a dense
subspace to the entire Banach space.

* `ContinuousLinearMap.extend`: Extend `f : E →SL[σ₁₂] F` to a continuous linear map
  `Eₗ →SL[σ₁₂] F`, where `e : E →ₗ[𝕜] Eₗ` is a dense map that is `IsUniformInducing`.
* `LinearMap.extendOfNorm`: Extend `f : E →ₛₗ[σ₁₂] F` to a continuous linear map
  `Eₗ →SL[σ₁₂] F`, where `e : E →ₗ[𝕜] Eₗ` is a dense map and we have the norm estimate
  `‖f x‖ ≤ C * ‖e x‖` for all `x : E`.

Moreover, we can extend a linear equivalence:
* `LinearEquiv.extend`: Extend a linear equivalence between normed spaces to a continuous linear
  equivalence between Banach spaces with two dense maps `e₁` and `e₂` and the corresponding norm
  estimates.
* `LinearEquiv.extendOfIsometry`: Extend `f : E ≃ₗ[𝕜] F` to a linear isometry equivalence
  `Eₗ →ₗᵢ[𝕜] Fₗ`, where `e₁ : E →ₗ[𝕜] Eₗ` and `e₂ : F →ₗ[𝕜] Fₗ` are dense maps into Banach spaces
  and `f` preserves the norm.

-/

@[expose] public section

suppress_compilation

open scoped NNReal

variable {𝕜 𝕜₂ E Eₗ F Fₗ : Type*}

namespace ContinuousLinearMap

section Extend

section Ring

variable [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [T0Space F]
  [AddCommMonoid Eₗ] [UniformSpace Eₗ] [ContinuousAdd Eₗ]
  [Semiring 𝕜] [Semiring 𝕜₂] [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 Eₗ]
  [ContinuousConstSMul 𝕜 Eₗ] [ContinuousConstSMul 𝕜₂ F]
  {σ₁₂ : 𝕜 ->+* 𝕜₂} (f g : E ->SL[σ₁₂] F) [CompleteSpace F] (e : E ->L[𝕜] Eₗ)

open scoped Classical in
/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: : Eₗ ->SL[σ₁₂] F
  body: if h : DenseRange e ∧ IsUniformInducing e then
  -- extension of `f` is continuous
  have cont := (uniformContinuous_uniformly_extend h.2 h.1 f.uniformContinuous).continuous
  -- extension of `f` agrees with `f` on the domain of the embedding `e`
  have eq := uniformly_extend_of_ind h.2 h.1 f.unifor

中文:
定义 extend
  签名: : Eₗ ->SL[σ₁₂] F
  定义体: if h : DenseRange e ∧ IsUniformInducing e then
  -- extension of `f` is continuous
  have cont := (uniformContinuous_uniformly_extend h.2 h.1 f.uniformContinuous).continuous
  -- extension of `f` agrees with `f` on the domain of the embedding `e`
  have eq := uniformly_extend_of_ind h.2 h.1 f.unifor

Depends on / 依赖: DenseRange, IsUniformInducing
-/
def extend : Eₗ ->SL[σ₁₂] F :=
  if h : DenseRange e ∧ IsUniformInducing e then
  -- extension of `f` is continuous
  have cont := (uniformContinuous_uniformly_extend h.2 h.1 f.uniformContinuous).continuous
  -- extension of `f` agrees with `f` on the domain of the embedding `e`
  have eq := uniformly_extend_of_ind h.2 h.1 f.uniformContinuous
  { toFun := (h.2.isDenseInducing h.1).extend f
    map_add' := by
      refine h.1.induction_on₂ ?_ ?_
      · exact isClosed_eq (cont.comp continuous_add)
          ((cont.comp continuous_fst).add (cont.comp continuous_snd))
      · intro x y
        simp only [eq, ← e.map_add]
        exact f.map_add _ _
    map_smul' := fun k => by
      refine fun b => h.1.induction_on b ?_ ?_
      · exact isClosed_eq (cont.comp (continuous_const_smul _))
          ((continuous_const_smul _).comp cont)
      · intro x
        rw [← map_smul]
        simp only [eq]
        exact map_smulₛₗ _ _ _
    cont }
  else 0

variable {e}

@[simp]
/--
theorem `extend_eq` / 定理 `extend_eq`

English:
theorem extend_eq
  given: (h_dense : DenseRange e) (h_e : IsUniformInducing e) (x : E)
  proof: by
  simp only [extend, h_dense, h_e, and_self, ↓reduceDIte, coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  exact IsDenseInducing.extend_eq (h_e.isDenseInducing h_dense) f.cont _

中文:
定理 extend_eq
  条件: (h_dense : DenseRange e) (h_e : IsUniformInducing e) (x : E)
  证明: by
  simp only [extend, h_dense, h_e, and_self, ↓reduceDIte, coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  exact IsDenseInducing.extend_eq (h_e.isDenseInducing h_dense) f.cont _

Depends on / 依赖: AddHom, AddHom.coe_mk, IsDenseInducing, IsDenseInducing.extend_eq, LinearMap, LinearMap.coe_mk, and_self, coe_mk, extend, extend_eq, f.cont, h_dense, h_e.isDenseInducing, isDenseInducing, reduceDIte
-/
theorem extend_eq (h_dense : DenseRange e) (h_e : IsUniformInducing e) (x : E) :
    extend f e (e x) = f x := by
  simp only [extend, h_dense, h_e, and_self, ↓reduceDIte, coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  exact IsDenseInducing.extend_eq (h_e.isDenseInducing h_dense) f.cont _

/--
theorem `extend_unique` / 定理 `extend_unique`

English:
theorem extend_unique
  statement: (h_dense : DenseRange e) (h_e : IsUniformInducing e) (g : Eₗ ->SL[σ₁₂] F)
  proof: by
  simp only [extend, h_dense, h_e, and_self, ↓reduceDIte]
exact ContinuousLinearMap.coeFn_injective
    uniformly_extend_unique h_e h_dense (ContinuousLinearMap.ext_iff.1 H) g.continuous

@[simp]

中文:
定理 extend_unique
  结论: (h_dense : DenseRange e) (h_e : IsUniformInducing e) (g : Eₗ ->SL[σ₁₂] F)
  证明: by
  simp only [extend, h_dense, h_e, and_self, ↓reduceDIte]
exact ContinuousLinearMap.coeFn_injective
    uniformly_extend_unique h_e h_dense (ContinuousLinearMap.ext_iff.1 H) g.continuous

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coeFn_injective, ContinuousLinearMap.ext_iff, and_self, coeFn_injective, continuous, ext_iff, extend, g.continuous, h_dense, reduceDIte, uniformly_extend_unique
-/
theorem extend_unique (h_dense : DenseRange e) (h_e : IsUniformInducing e) (g : Eₗ ->SL[σ₁₂] F)
    (H : g.comp e = f) : extend f e = g := by
  simp only [extend, h_dense, h_e, and_self, ↓reduceDIte]
exact ContinuousLinearMap.coeFn_injective
    uniformly_extend_unique h_e h_dense (ContinuousLinearMap.ext_iff.1 H) g.continuous

@[simp]
/--
theorem `extend_zero` / 定理 `extend_zero`

English:
theorem extend_zero
  given: (h_dense : DenseRange e) (h_e : IsUniformInducing e)
  proof: extend_unique _ h_dense h_e _ (zero_comp _)

中文:
定理 extend_zero
  条件: (h_dense : DenseRange e) (h_e : IsUniformInducing e)
  证明: extend_unique _ h_dense h_e _ (zero_comp _)

Depends on / 依赖: extend_unique, h_dense, zero_comp
-/
theorem extend_zero (h_dense : DenseRange e) (h_e : IsUniformInducing e) :
    extend (0 : E ->SL[σ₁₂] F) e = 0 :=
  extend_unique _ h_dense h_e _ (zero_comp _)

end Ring

section NormedField

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 ->+* 𝕜₂}
  [NormedAddCommGroup E] [NormedAddCommGroup Eₗ] [NormedAddCommGroup F] [NormedAddCommGroup Fₗ]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 Eₗ] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₂ Fₗ] [CompleteSpace F]
  (f g : E ->SL[σ₁₂] F) {e : E ->L[𝕜] Eₗ}

variable (h_dense : DenseRange e) (h_e : IsUniformInducing e)

variable {N : Real>=0} [RingHomIsometric σ₁₂]

/--
theorem `opNorm_extend_le` / 定理 `opNorm_extend_le`

English:
theorem opNorm_extend_le
  given: (h_dense : DenseRange e) (h_e : forall x, ‖x‖ <= N * ‖e x‖)
  proof: by
  -- Add `opNorm_le_of_dense`?
  refine opNorm_le_bound _ ?_ (isClosed_property h_dense (isClosed_le ?_ (by fun_prop)) fun x => ?_)
  · cases le_total 0 N with
    | inl hN => exact mul_nonneg hN (norm_nonneg _)
    | inr hN =>
have : Unique E := ⟨⟨0⟩, fun x => norm_le_zero_iff.mp
        (h_e x)

中文:
定理 opNorm_extend_le
  条件: (h_dense : DenseRange e) (h_e : 对任意 x, ‖x‖ <= N * ‖e x‖)
  证明: by
  -- Add `opNorm_le_of_dense`?
  refine opNorm_le_bound _ ?_ (isClosed_property h_dense (isClosed_le ?_ (by fun_prop)) fun x => ?_)
  · cases le_total 0 N with
    | inl hN => exact mul_nonneg hN (norm_nonneg _)
    | inr hN =>
have : Unique E := ⟨⟨0⟩, fun x => norm_le_zero_iff.mp
        (h_e x)
-/
theorem opNorm_extend_le (h_dense : DenseRange e) (h_e : forall x, ‖x‖ <= N * ‖e x‖) :
    ‖f.extend e‖ <= N * ‖f‖ := by
  -- Add `opNorm_le_of_dense`?
  refine opNorm_le_bound _ ?_ (isClosed_property h_dense (isClosed_le ?_ (by fun_prop)) fun x => ?_)
  · cases le_total 0 N with
    | inl hN => exact mul_nonneg hN (norm_nonneg _)
    | inr hN =>
have : Unique E := ⟨⟨0⟩, fun x => norm_le_zero_iff.mp
        (h_e x).trans (mul_nonpos_of_nonpos_of_nonneg hN (norm_nonneg _))⟩
      obtain rfl : f = 0 := Subsingleton.elim ..
      simp
  · exact (cont _).norm
  · rw [extend_eq _ h_dense (isUniformEmbedding_of_bound _ h_e).isUniformInducing]
    calc
      ‖f x‖ <= ‖f‖ * ‖x‖ := le_opNorm _ _
      _ <= ‖f‖ * (N * ‖e x‖) := by gcongr; exact h_e x
      _ <= N * ‖f‖ * ‖e x‖ := by rw [mul_comm ↑N ‖f‖, mul_assoc]


end NormedField

end Extend

end ContinuousLinearMap

namespace LinearMap

section compInv

variable [DivisionRing 𝕜] [DivisionRing 𝕜₂] {σ₁₂ : 𝕜 ->+* 𝕜₂}
  [AddCommGroup E] [NormedAddCommGroup F] [SeminormedAddCommGroup Eₗ]
  [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 Eₗ]

variable (f : E ->ₛₗ[σ₁₂] F) (g : E ->ₗ[𝕜] Eₗ)

open scoped Classical in
/--
Definition of `compLeftInverse` / `compLeftInverse` 的定义

English:
definition compLeftInverse
  signature: : range g ->SL[σ₁₂] F
  body: if h : exists (C : Real), forall (x : E), ‖f x‖ <= C * ‖g x‖ then
  (((LinearMap.ker g).liftQ f (by
    obtain ⟨C, h⟩ := h
    intro x hx
    specialize h x
    rw [hx] at h
    simpa using h)).comp
    g.quotKerEquivRange.symm.toLinearMap).mkContinuousOfExistsBound
  (by
    obtain ⟨C, h⟩ := h
    

中文:
定义 compLeftInverse
  签名: : range g ->SL[σ₁₂] F
  定义体: if h : exists (C : Real), forall (x : E), ‖f x‖ <= C * ‖g x‖ then
  (((LinearMap.ker g).liftQ f (by
    obtain ⟨C, h⟩ := h
    intro x hx
    specialize h x
    rw [hx] at h
    simpa using h)).comp
    g.quotKerEquivRange.symm.toLinearMap).mkContinuousOfExistsBound
  (by
    obtain ⟨C, h⟩ := h
    

Depends on / 依赖: LinearMap, LinearMap.ker, g.quotKerEquivRange.symm.toLinearMap, mkContinuousOfExistsBound, quotKerEquivRange, specialize, toLinearMap
-/
def compLeftInverse : range g ->SL[σ₁₂] F :=
  if h : exists (C : Real), forall (x : E), ‖f x‖ <= C * ‖g x‖ then
  (((LinearMap.ker g).liftQ f (by
    obtain ⟨C, h⟩ := h
    intro x hx
    specialize h x
    rw [hx] at h
    simpa using h)).comp
    g.quotKerEquivRange.symm.toLinearMap).mkContinuousOfExistsBound
  (by
    obtain ⟨C, h⟩ := h
    use C
    intro ⟨x, y, hxy⟩
    simpa [← hxy] using h y)
  else 0

/--
theorem `compLeftInverse_apply_of_bdd` / 定理 `compLeftInverse_apply_of_bdd`

English:
theorem compLeftInverse_apply_of_bdd
  statement: (h_norm : exists (C : Real), forall (x : E), ‖f x‖ <= C * ‖g x‖)
  proof: by
  simp [compLeftInverse, h_norm, ← hx]

中文:
定理 compLeftInverse_apply_of_bdd
  结论: (h_norm : 存在 (C : 实数), 对任意 (x : E), ‖f x‖ <= C * ‖g x‖)
  证明: by
  simp [compLeftInverse, h_norm, ← hx]

Depends on / 依赖: compLeftInverse, h_norm
-/
theorem compLeftInverse_apply_of_bdd (h_norm : exists (C : Real), forall (x : E), ‖f x‖ <= C * ‖g x‖)
    (x : E) (y : Eₗ) (hx : g x = y) :
    f.compLeftInverse g ⟨y, ⟨x, hx⟩⟩ = f x := by
  simp [compLeftInverse, h_norm, ← hx]

end compInv

section NormedDivisionRing

variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜₂] {σ₁₂ : 𝕜 ->+* 𝕜₂}
  [AddCommGroup E] [SeminormedAddCommGroup Eₗ] [NormedAddCommGroup F]
  [Module 𝕜 E] [Module 𝕜₂ F] [IsBoundedSMul 𝕜₂ F] [Module 𝕜 Eₗ] [IsBoundedSMul 𝕜 Eₗ]
  [CompleteSpace F]

variable (f : E ->ₛₗ[σ₁₂] F) (e : E ->ₗ[𝕜] Eₗ)

/--
Definition of `extendOfNorm` / `extendOfNorm` 的定义

English:
definition extendOfNorm
  signature: : Eₗ ->SL[σ₁₂] F
  body: (f.compLeftInverse e).extend (LinearMap.range e).subtypeL

中文:
定义 extendOfNorm
  签名: : Eₗ ->SL[σ₁₂] F
  定义体: (f.compLeftInverse e).extend (LinearMap.range e).subtypeL

Depends on / 依赖: LinearMap, LinearMap.range, compLeftInverse, extend, f.compLeftInverse, subtypeL
-/
def extendOfNorm : Eₗ ->SL[σ₁₂] F := (f.compLeftInverse e).extend (LinearMap.range e).subtypeL

variable {f e}

/--
theorem `extendOfNorm_eq` / 定理 `extendOfNorm_eq`

English:
theorem extendOfNorm_eq
  statement: (h_dense : DenseRange e) (h_norm : exists C, forall x, ‖f x‖ <= C * ‖e x‖)
  proof: by
  have := (f.compLeftInverse e).extend_eq (e := (LinearMap.range e).subtypeL)
    (by simpa using! h_dense) isUniformEmbedding_subtype_val.isUniformInducing
  convert! this ⟨e x, LinearMap.mem_range_self e x⟩
  exact (compLeftInverse_apply_of_bdd _ _ h_norm _ _ rfl).symm

中文:
定理 extendOfNorm_eq
  结论: (h_dense : DenseRange e) (h_norm : 存在 C, 对任意 x, ‖f x‖ <= C * ‖e x‖)
  证明: by
  have := (f.compLeftInverse e).extend_eq (e := (LinearMap.range e).subtypeL)
    (by simpa using! h_dense) isUniformEmbedding_subtype_val.isUniformInducing
  convert! this ⟨e x, LinearMap.mem_range_self e x⟩
  exact (compLeftInverse_apply_of_bdd _ _ h_norm _ _ rfl).symm

Depends on / 依赖: LinearMap, LinearMap.mem_range_self, LinearMap.range, compLeftInverse, compLeftInverse_apply_of_bdd, convert, extend_eq, f.compLeftInverse, h_dense, h_norm, isUniformEmbedding_subtype_val, isUniformEmbedding_subtype_val.isUniformInducing, isUniformInducing, mem_range_self, subtypeL
-/
theorem extendOfNorm_eq (h_dense : DenseRange e) (h_norm : exists C, forall x, ‖f x‖ <= C * ‖e x‖)
    (x : E) : f.extendOfNorm e (e x) = f x := by
  have := (f.compLeftInverse e).extend_eq (e := (LinearMap.range e).subtypeL)
    (by simpa using! h_dense) isUniformEmbedding_subtype_val.isUniformInducing
  convert! this ⟨e x, LinearMap.mem_range_self e x⟩
  exact (compLeftInverse_apply_of_bdd _ _ h_norm _ _ rfl).symm

/--
theorem `norm_extendOfNorm_apply_le` / 定理 `norm_extendOfNorm_apply_le`

English:
theorem norm_extendOfNorm_apply_le
  statement: (h_dense : DenseRange e) (C : Real)
  proof: by
  have h_mem : forall (x : Eₗ) (hy : x in (LinearMap.range e)), ‖extendOfNorm f e x‖ <= C * ‖x‖ := by
    intro x ⟨y, hxy⟩
    simpa only [← hxy, extendOfNorm_eq h_dense ⟨C, h_norm⟩ y] using h_norm y
  exact h_dense.induction h_mem (isClosed_le (by fun_prop) (by fun_prop)) x

中文:
定理 norm_extendOfNorm_apply_le
  结论: (h_dense : DenseRange e) (C : 实数)
  证明: by
  have h_mem : forall (x : Eₗ) (hy : x in (LinearMap.range e)), ‖extendOfNorm f e x‖ <= C * ‖x‖ := by
    intro x ⟨y, hxy⟩
    simpa only [← hxy, extendOfNorm_eq h_dense ⟨C, h_norm⟩ y] using h_norm y
  exact h_dense.induction h_mem (isClosed_le (by fun_prop) (by fun_prop)) x

Depends on / 依赖: LinearMap, LinearMap.range, extendOfNorm, extendOfNorm_eq, fun_prop, h_dense, h_dense.induction, h_mem, h_norm, isClosed_le
-/
theorem norm_extendOfNorm_apply_le (h_dense : DenseRange e) (C : Real)
    (h_norm : forall (x : E), ‖f x‖ <= C * ‖e x‖) (x : Eₗ) :
    ‖f.extendOfNorm e x‖ <= C * ‖x‖ := by
  have h_mem : forall (x : Eₗ) (hy : x in (LinearMap.range e)), ‖extendOfNorm f e x‖ <= C * ‖x‖ := by
    intro x ⟨y, hxy⟩
    simpa only [← hxy, extendOfNorm_eq h_dense ⟨C, h_norm⟩ y] using h_norm y
  exact h_dense.induction h_mem (isClosed_le (by fun_prop) (by fun_prop)) x

/--
theorem `extendOfNorm_unique` / 定理 `extendOfNorm_unique`

English:
theorem extendOfNorm_unique
  statement: (h_dense : DenseRange e) (C : Real) (h_norm : forall (x : E), ‖f x‖ <= C * ‖e x‖)
  proof: by
  apply ContinuousLinearMap.extend_unique
  · simpa using! h_dense
  · exact isUniformEmbedding_subtype_val.isUniformInducing
  ext ⟨y, x, hxy⟩
  rw [compLeftInverse_apply_of_bdd _ _ ⟨C]; rw [h_norm⟩ x y hxy]
  simp [← hxy, ← H]

中文:
定理 extendOfNorm_unique
  结论: (h_dense : DenseRange e) (C : 实数) (h_norm : 对任意 (x : E), ‖f x‖ <= C * ‖e x‖)
  证明: by
  apply ContinuousLinearMap.extend_unique
  · simpa using! h_dense
  · exact isUniformEmbedding_subtype_val.isUniformInducing
  ext ⟨y, x, hxy⟩
  rw [compLeftInverse_apply_of_bdd _ _ ⟨C]; rw [h_norm⟩ x y hxy]
  simp [← hxy, ← H]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.extend_unique, compLeftInverse_apply_of_bdd, extend_unique, h_dense, h_norm, isUniformEmbedding_subtype_val, isUniformEmbedding_subtype_val.isUniformInducing, isUniformInducing
-/
theorem extendOfNorm_unique (h_dense : DenseRange e) (C : Real) (h_norm : forall (x : E), ‖f x‖ <= C * ‖e x‖)
    (g : Eₗ ->SL[σ₁₂] F) (H : g.toLinearMap.comp e = f) : extendOfNorm f e = g := by
  apply ContinuousLinearMap.extend_unique
  · simpa using! h_dense
  · exact isUniformEmbedding_subtype_val.isUniformInducing
  ext ⟨y, x, hxy⟩
  rw [compLeftInverse_apply_of_bdd _ _ ⟨C]; rw [h_norm⟩ x y hxy]
  simp [← hxy, ← H]

end NormedDivisionRing

section NormedField

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 ->+* 𝕜₂}
  [NormedAddCommGroup F] [SeminormedAddCommGroup Eₗ]
  [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Eₗ]
  [AddCommGroup E] [Module 𝕜 E] [CompleteSpace F]

variable {f : E ->ₛₗ[σ₁₂] F} {e : E ->ₗ[𝕜] Eₗ}

/--
theorem `opNorm_extendOfNorm_le` / 定理 `opNorm_extendOfNorm_le`

English:
theorem opNorm_extendOfNorm_le
  statement: (h_dense : DenseRange e) {C : Real} (hC : 0 <= C)
  proof: (f.extendOfNorm e).opNorm_le_bound hC (norm_extendOfNorm_apply_le h_dense C h_norm)

中文:
定理 opNorm_extendOfNorm_le
  结论: (h_dense : DenseRange e) {C : 实数} (hC : 0 <= C)
  证明: (f.extendOfNorm e).opNorm_le_bound hC (norm_extendOfNorm_apply_le h_dense C h_norm)

Depends on / 依赖: extendOfNorm, f.extendOfNorm, h_dense, h_norm, norm_extendOfNorm_apply_le, opNorm_le_bound
-/
theorem opNorm_extendOfNorm_le (h_dense : DenseRange e) {C : Real} (hC : 0 <= C)
    (h_norm : forall (x : E), ‖f x‖ <= C * ‖e x‖) : ‖f.extendOfNorm e‖ <= C :=
  (f.extendOfNorm e).opNorm_le_bound hC (norm_extendOfNorm_apply_le h_dense C h_norm)

end NormedField

end LinearMap

namespace LinearEquiv

section extend

variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜₂]
  [AddCommGroup E] [NormedAddCommGroup Eₗ] [AddCommGroup F] [NormedAddCommGroup Fₗ]
  [Module 𝕜 E] [Module 𝕜 Eₗ] [IsBoundedSMul 𝕜 Eₗ] [Module 𝕜₂ F] [Module 𝕜₂ Fₗ] [IsBoundedSMul 𝕜₂ Fₗ]
  [CompleteSpace Eₗ] [CompleteSpace Fₗ]

variable {σ₁₂ : 𝕜 ->+* 𝕜₂} {σ₂₁ : 𝕜₂ ->+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable (f : E ≃ₛₗ[σ₁₂] F) (e₁ : E ->ₗ[𝕜] Eₗ) (e₂ : F ->ₗ[𝕜₂] Fₗ)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: (h_dense₁ : DenseRange e₁) (h_norm₁ : exists C, forall x, ‖e₂ (f x)‖ <= C * ‖e₁ x‖)
  body: (e₂ ∘ₛₗ f.toLinearMap).extendOfNorm e₁
  invFun := (e₁ ∘ₛₗ f.symm.toLinearMap).extendOfNorm e₂
  left_inv := by
    refine h_dense₁.induction ?_ ?_
    · rintro _ ⟨_, rfl⟩
      simp [LinearMap.extendOfNorm_eq, h_dense₁, h_norm₁, h_dense₂, h_norm₂]
    · exact isClosed_eq (by simp only [AddHom.toFun

中文:
定义 extend
  签名: (h_dense₁ : DenseRange e₁) (h_norm₁ : 存在 C, 对任意 x, ‖e₂ (f x)‖ <= C * ‖e₁ x‖)
  定义体: (e₂ ∘ₛₗ f.toLinearMap).extendOfNorm e₁
  invFun := (e₁ ∘ₛₗ f.symm.toLinearMap).extendOfNorm e₂
  left_inv := by
    refine h_dense₁.induction ?_ ?_
    · rintro _ ⟨_, rfl⟩
      simp [LinearMap.extendOfNorm_eq, h_dense₁, h_norm₁, h_dense₂, h_norm₂]
    · exact isClosed_eq (by simp only [AddHom.toFun

Depends on / 依赖: extendOfNorm, f.toLinearMap, toLinearMap
-/
def extend (h_dense₁ : DenseRange e₁) (h_norm₁ : exists C, forall x, ‖e₂ (f x)‖ <= C * ‖e₁ x‖)
    (h_dense₂ : DenseRange e₂) (h_norm₂ : exists C, forall x, ‖e₁ (f.symm x)‖ <= C * ‖e₂ x‖) :
    Eₗ ≃SL[σ₁₂] Fₗ where
  __ := (e₂ ∘ₛₗ f.toLinearMap).extendOfNorm e₁
  invFun := (e₁ ∘ₛₗ f.symm.toLinearMap).extendOfNorm e₂
  left_inv := by
    refine h_dense₁.induction ?_ ?_
    · rintro _ ⟨_, rfl⟩
      simp [LinearMap.extendOfNorm_eq, h_dense₁, h_norm₁, h_dense₂, h_norm₂]
    · exact isClosed_eq (by simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      ContinuousLinearMap.coe_coe]; fun_prop) continuous_id
  right_inv := by
    refine h_dense₂.induction ?_ ?_
    · rintro _ ⟨_, rfl⟩
      simp [LinearMap.extendOfNorm_eq, h_dense₁, h_norm₁, h_dense₂, h_norm₂]
    · exact isClosed_eq (by simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      ContinuousLinearMap.coe_coe]; fun_prop) continuous_id
  continuous_invFun := ContinuousLinearMap.continuous _

/--
theorem `extend_apply` / 定理 `extend_apply`

English:
theorem extend_apply
  statement: (h_dense₁ : DenseRange e₁)
  proof: rfl

中文:
定理 extend_apply
  结论: (h_dense₁ : DenseRange e₁)
  证明: rfl
-/
theorem extend_apply (h_dense₁ : DenseRange e₁)
    (h_norm₁ : exists C, forall x, ‖e₂ (f x)‖ <= C * ‖e₁ x‖) (h_dense₂ : DenseRange e₂)
    (h_norm₂ : exists C, forall x, ‖e₁ (f.symm x)‖ <= C * ‖e₂ x‖) (x : Eₗ) :
    (f.extend e₁ e₂ h_dense₁ h_norm₁ h_dense₂ h_norm₂) x =
    (e₂ ∘ₛₗ f.toLinearMap).extendOfNorm e₁ x := rfl

/--
theorem `extend_symm_apply` / 定理 `extend_symm_apply`

English:
theorem extend_symm_apply
  statement: (h_dense₁ : DenseRange e₁)
  proof: rfl

@[simp]

中文:
定理 extend_symm_apply
  结论: (h_dense₁ : DenseRange e₁)
  证明: rfl

@[simp]
-/
theorem extend_symm_apply (h_dense₁ : DenseRange e₁)
    (h_norm₁ : exists C, forall x, ‖e₂ (f x)‖ <= C * ‖e₁ x‖) (h_dense₂ : DenseRange e₂)
    (h_norm₂ : exists C, forall x, ‖e₁ (f.symm x)‖ <= C * ‖e₂ x‖) (x : Fₗ) :
    (f.extend e₁ e₂ h_dense₁ h_norm₁ h_dense₂ h_norm₂).symm x =
    (e₁ ∘ₛₗ f.symm.toLinearMap).extendOfNorm e₂ x := rfl

@[simp]
/--
theorem `extend_eq` / 定理 `extend_eq`

English:
theorem extend_eq
  statement: (h_dense₁ : DenseRange e₁) (h_norm₁ : exists C, forall x, ‖e₂ (f x)‖ <= C * ‖e₁ x‖)
  proof: LinearMap.extendOfNorm_eq h_dense₁ h_norm₁ x

@[simp]

中文:
定理 extend_eq
  结论: (h_dense₁ : DenseRange e₁) (h_norm₁ : 存在 C, 对任意 x, ‖e₂ (f x)‖ <= C * ‖e₁ x‖)
  证明: LinearMap.extendOfNorm_eq h_dense₁ h_norm₁ x

@[simp]

Depends on / 依赖: LinearMap, LinearMap.extendOfNorm_eq, extendOfNorm_eq
-/
theorem extend_eq (h_dense₁ : DenseRange e₁) (h_norm₁ : exists C, forall x, ‖e₂ (f x)‖ <= C * ‖e₁ x‖)
    (h_dense₂ : DenseRange e₂) (h_norm₂ : exists C, forall x, ‖e₁ (f.symm x)‖ <= C * ‖e₂ x‖) (x : E) :
    f.extend e₁ e₂ h_dense₁ h_norm₁ h_dense₂ h_norm₂ (e₁ x) = e₂ (f x) :=
  LinearMap.extendOfNorm_eq h_dense₁ h_norm₁ x

@[simp]
/--
theorem `extend_symm_eq` / 定理 `extend_symm_eq`

English:
theorem extend_symm_eq
  statement: (h_dense₁ : DenseRange e₁) (h_norm₁ : exists C, forall x, ‖e₂ (f x)‖ <= C * ‖e₁ x‖)
  proof: LinearMap.extendOfNorm_eq h_dense₂ h_norm₂ x

中文:
定理 extend_symm_eq
  结论: (h_dense₁ : DenseRange e₁) (h_norm₁ : 存在 C, 对任意 x, ‖e₂ (f x)‖ <= C * ‖e₁ x‖)
  证明: LinearMap.extendOfNorm_eq h_dense₂ h_norm₂ x

Depends on / 依赖: LinearMap, LinearMap.extendOfNorm_eq, extendOfNorm_eq
-/
theorem extend_symm_eq (h_dense₁ : DenseRange e₁) (h_norm₁ : exists C, forall x, ‖e₂ (f x)‖ <= C * ‖e₁ x‖)
    (h_dense₂ : DenseRange e₂) (h_norm₂ : exists C, forall x, ‖e₁ (f.symm x)‖ <= C * ‖e₂ x‖) (x : F) :
    (f.extend e₁ e₂ h_dense₁ h_norm₁ h_dense₂ h_norm₂).symm (e₂ x) = e₁ (f.symm x) :=
  LinearMap.extendOfNorm_eq h_dense₂ h_norm₂ x

/--
theorem `norm_extend_le` / 定理 `norm_extend_le`

English:
theorem norm_extend_le
  statement: (C : Real) (h_dense₁ : DenseRange e₁) (h_norm₁ : forall x, ‖e₂ (f x)‖ <= C * ‖e₁ x‖)
  proof: LinearMap.norm_extendOfNorm_apply_le h_dense₁ _ h_norm₁ _

中文:
定理 norm_extend_le
  结论: (C : 实数) (h_dense₁ : DenseRange e₁) (h_norm₁ : 对任意 x, ‖e₂ (f x)‖ <= C * ‖e₁ x‖)
  证明: LinearMap.norm_extendOfNorm_apply_le h_dense₁ _ h_norm₁ _

Depends on / 依赖: LinearMap, LinearMap.norm_extendOfNorm_apply_le, norm_extendOfNorm_apply_le
-/
theorem norm_extend_le (C : Real) (h_dense₁ : DenseRange e₁) (h_norm₁ : forall x, ‖e₂ (f x)‖ <= C * ‖e₁ x‖)
    (h_dense₂ : DenseRange e₂) (h_norm₂ : exists C, forall x, ‖e₁ (f.symm x)‖ <= C * ‖e₂ x‖) (x : Eₗ) :
    ‖(f.extend e₁ e₂ h_dense₁ ⟨C, h_norm₁⟩ h_dense₂ h_norm₂) x‖ <= C * ‖x‖ :=
  LinearMap.norm_extendOfNorm_apply_le h_dense₁ _ h_norm₁ _

/--
theorem `norm_extend_symm_le` / 定理 `norm_extend_symm_le`

English:
theorem norm_extend_symm_le
  statement: (C : Real) (h_dense₁ : DenseRange e₁)
  proof: LinearMap.norm_extendOfNorm_apply_le h_dense₂ _ h_norm₂ _

中文:
定理 norm_extend_symm_le
  结论: (C : 实数) (h_dense₁ : DenseRange e₁)
  证明: LinearMap.norm_extendOfNorm_apply_le h_dense₂ _ h_norm₂ _

Depends on / 依赖: LinearMap, LinearMap.norm_extendOfNorm_apply_le, norm_extendOfNorm_apply_le
-/
theorem norm_extend_symm_le (C : Real) (h_dense₁ : DenseRange e₁)
    (h_norm₁ : exists C, forall x, ‖e₂ (f x)‖ <= C * ‖e₁ x‖) (h_dense₂ : DenseRange e₂)
    (h_norm₂ : forall x, ‖e₁ (f.symm x)‖ <= C * ‖e₂ x‖) (x : Fₗ) :
    ‖(f.extend e₁ e₂ h_dense₁ h_norm₁ h_dense₂ ⟨C, h_norm₂⟩).symm x‖ <= C * ‖x‖ :=
  LinearMap.norm_extendOfNorm_apply_le h_dense₂ _ h_norm₂ _

end extend

section extendOfIsometry

variable [NormedField 𝕜] [NormedField 𝕜₂]
  [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜₂ F]
  [NormedAddCommGroup Eₗ] [NormedSpace 𝕜 Eₗ] [CompleteSpace Eₗ]
  [NormedAddCommGroup Fₗ] [NormedSpace 𝕜₂ Fₗ] [CompleteSpace Fₗ]

variable {σ₁₂ : 𝕜 ->+* 𝕜₂} {σ₂₁ : 𝕜₂ ->+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable (f : E ≃ₛₗ[σ₁₂] F) (e₁ : E ->ₗ[𝕜] Eₗ) (e₂ : F ->ₗ[𝕜₂] Fₗ)

/--
Definition of `extendOfIsometry` / `extendOfIsometry` 的定义

English:
definition extendOfIsometry
  signature: (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
  body: have h_norm₂ : forall x, ‖e₁ (f.symm x)‖ = ‖e₂ x‖ := fun x => by simpa using (h_norm (f.symm x)).symm
  { __ := f.extend e₁ e₂ h_dense₁ ⟨1, by simp [h_norm]⟩ h_dense₂ ⟨1, by simp [h_norm₂]⟩
    norm_map' := by
      refine h_dense₁.induction ?_ (isClosed_eq (by
        simp only [ContinuousLinearEqu

中文:
定义 extendOfIsometry
  签名: (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
  定义体: have h_norm₂ : forall x, ‖e₁ (f.symm x)‖ = ‖e₂ x‖ := fun x => by simpa using (h_norm (f.symm x)).symm
  { __ := f.extend e₁ e₂ h_dense₁ ⟨1, by simp [h_norm]⟩ h_dense₂ ⟨1, by simp [h_norm₂]⟩
    norm_map' := by
      refine h_dense₁.induction ?_ (isClosed_eq (by
        simp only [ContinuousLinearEqu

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.coe_toLinearEquiv, LinearMap, LinearMap.extendOfNorm_eq, coe_toLinearEquiv, continuous_norm, convert, extend, extendOfNorm_eq, f.extend, f.symm, fun_prop, h_norm, isClosed_eq, norm_map
-/
def extendOfIsometry (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
    (h_norm : forall x, ‖e₂ (f x)‖ = ‖e₁ x‖) :
    Eₗ ≃ₛₗᵢ[σ₁₂] Fₗ :=
  have h_norm₂ : forall x, ‖e₁ (f.symm x)‖ = ‖e₂ x‖ := fun x => by simpa using (h_norm (f.symm x)).symm
  { __ := f.extend e₁ e₂ h_dense₁ ⟨1, by simp [h_norm]⟩ h_dense₂ ⟨1, by simp [h_norm₂]⟩
    norm_map' := by
      refine h_dense₁.induction ?_ (isClosed_eq (by
        simp only [ContinuousLinearEquiv.coe_toLinearEquiv]; fun_prop) continuous_norm)
      rintro x ⟨y, rfl⟩
      convert! h_norm y
      apply LinearMap.extendOfNorm_eq h_dense₁ (by use 1; simp [h_norm]) }

/--
theorem `extendOfIsometry_apply` / 定理 `extendOfIsometry_apply`

English:
theorem extendOfIsometry_apply
  statement: (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
  proof: rfl

中文:
定理 extendOfIsometry_apply
  结论: (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
  证明: rfl
-/
theorem extendOfIsometry_apply (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
    (h_norm : forall x, ‖e₂ (f x)‖ = ‖e₁ x‖) (x : Eₗ) :
    (f.extendOfIsometry e₁ e₂ h_dense₁ h_dense₂ h_norm) x =
    (e₂ ∘ₛₗ f.toLinearMap).extendOfNorm e₁ x := rfl

/--
theorem `extendOfIsometry_symm_apply` / 定理 `extendOfIsometry_symm_apply`

English:
theorem extendOfIsometry_symm_apply
  statement: (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
  proof: rfl

@[simp]

中文:
定理 extendOfIsometry_symm_apply
  结论: (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
  证明: rfl

@[simp]
-/
theorem extendOfIsometry_symm_apply (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
    (h_norm : forall x, ‖e₂ (f x)‖ = ‖e₁ x‖) (x : Fₗ) :
    (f.extendOfIsometry e₁ e₂ h_dense₁ h_dense₂ h_norm).symm x =
    (e₁ ∘ₛₗ f.symm.toLinearMap).extendOfNorm e₂ x := rfl

@[simp]
/--
theorem `extendOfIsometry_eq` / 定理 `extendOfIsometry_eq`

English:
theorem extendOfIsometry_eq
  statement: (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
  proof: LinearMap.extendOfNorm_eq h_dense₁ ⟨1, fun x => by simp [h_norm x]⟩ x

@[simp]

中文:
定理 extendOfIsometry_eq
  结论: (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
  证明: LinearMap.extendOfNorm_eq h_dense₁ ⟨1, fun x => by simp [h_norm x]⟩ x

@[simp]

Depends on / 依赖: LinearMap, LinearMap.extendOfNorm_eq, extendOfNorm_eq, h_norm
-/
theorem extendOfIsometry_eq (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
    (h_norm : forall x, ‖e₂ (f x)‖ = ‖e₁ x‖) (x : E) :
    f.extendOfIsometry e₁ e₂ h_dense₁ h_dense₂ h_norm (e₁ x) = e₂ (f x) :=
  LinearMap.extendOfNorm_eq h_dense₁ ⟨1, fun x => by simp [h_norm x]⟩ x

@[simp]
/--
theorem `extendOfIsometry_symm_eq` / 定理 `extendOfIsometry_symm_eq`

English:
theorem extendOfIsometry_symm_eq
  statement: (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
  proof: have h_norm₂ : forall x, ‖e₁ (f.symm x)‖ = ‖e₂ x‖ :=
    fun x => by simpa using (h_norm (f.symm x)).symm
  LinearMap.extendOfNorm_eq h_dense₂ ⟨1, fun x => by simp [h_norm₂ x]⟩ x

中文:
定理 extendOfIsometry_symm_eq
  结论: (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
  证明: have h_norm₂ : forall x, ‖e₁ (f.symm x)‖ = ‖e₂ x‖ :=
    fun x => by simpa using (h_norm (f.symm x)).symm
  LinearMap.extendOfNorm_eq h_dense₂ ⟨1, fun x => by simp [h_norm₂ x]⟩ x

Depends on / 依赖: LinearMap, LinearMap.extendOfNorm_eq, extendOfNorm_eq, f.symm, h_norm
-/
theorem extendOfIsometry_symm_eq (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
    (h_norm : forall x, ‖e₂ (f x)‖ = ‖e₁ x‖) (x : F) :
    (f.extendOfIsometry e₁ e₂ h_dense₁ h_dense₂ h_norm).symm (e₂ x) = e₁ (f.symm x) :=
  have h_norm₂ : forall x, ‖e₁ (f.symm x)‖ = ‖e₂ x‖ :=
    fun x => by simpa using (h_norm (f.symm x)).symm
  LinearMap.extendOfNorm_eq h_dense₂ ⟨1, fun x => by simp [h_norm₂ x]⟩ x

end extendOfIsometry

end LinearEquiv
