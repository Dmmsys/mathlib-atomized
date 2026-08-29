/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.SiegelsLemma
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.EquivReindex

/-!
# House of an algebraic number

This file defines the house of an algebraic number `α`, which is
the largest of the modulus of its conjugates.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [Hua, L.-K., *Introduction to number theory*][hua1982house]

## Tags
number field, algebraic number, house
-/

@[expose] public section

variable {K : Type*} [Field K] [NumberField K]

namespace NumberField

noncomputable section

open Module.Free Module canonicalEmbedding Matrix Finset

attribute [local instance] Matrix.seminormedAddCommGroup

/--
Definition of `house` / `house` 的定义

English:
definition house
  signature: (α : K)
  body: ‖canonicalEmbedding K α‖

中文:
定义 house
  签名: (α : K)
  定义体: ‖canonicalEmbedding K α‖

Depends on / 依赖: canonicalEmbedding
-/
def house (α : K) : Real := ‖canonicalEmbedding K α‖

/--
theorem `house_eq_sup'` / 定理 `house_eq_sup'`

English:
theorem house_eq_sup'
  given: (α : K)
  proof: by
  rw [house]; rw [← coe_nnnorm]; rw [nnnorm_eq]; rw [← sup'_eq_sup univ_nonempty]

中文:
定理 house_eq_sup'
  条件: (α : K)
  证明: by
  rw [house]; rw [← coe_nnnorm]; rw [nnnorm_eq]; rw [← sup'_eq_sup univ_nonempty]

Depends on / 依赖: _eq_sup, coe_nnnorm, nnnorm_eq, univ_nonempty
-/
theorem house_eq_sup' (α : K) :
    house α = univ.sup' univ_nonempty (fun φ : K ->+* Complex => ‖φ α‖₊) := by
  rw [house]; rw [← coe_nnnorm]; rw [nnnorm_eq]; rw [← sup'_eq_sup univ_nonempty]

/--
theorem `house_sum_le_sum_house` / 定理 `house_sum_le_sum_house`

English:
theorem house_sum_le_sum_house
  given: {ι : Type*} (s : Finset ι) (α : ι -> K)
  proof: by
  simp only [house, map_sum]; apply norm_sum_le_of_le; intros; rfl

中文:
定理 house_sum_le_sum_house
  条件: {ι : 类型} (s : 有限集 ι) (α : ι -> K)
  证明: by
  simp only [house, map_sum]; apply norm_sum_le_of_le; intros; rfl

Depends on / 依赖: intros, map_sum, norm_sum_le_of_le
-/
theorem house_sum_le_sum_house {ι : Type*} (s : Finset ι) (α : ι -> K) :
    house (∑ i in s, α i) <= ∑ i in s, house (α i) := by
  simp only [house, map_sum]; apply norm_sum_le_of_le; intros; rfl

/--
theorem `house_nonneg` / 定理 `house_nonneg`

English:
theorem house_nonneg
  given: (α : K)
  statement: 0 <= house α
  proof: norm_nonneg _

中文:
定理 house_nonneg
  条件: (α : K)
  结论: 0 <= house α
  证明: norm_nonneg _

Depends on / 依赖: norm_nonneg
-/
theorem house_nonneg (α : K) : 0 <= house α := norm_nonneg _

/--
theorem `house_mul_le` / 定理 `house_mul_le`

English:
theorem house_mul_le
  given: (α β : K)
  statement: house (α * β) <= house α * house β
  proof: by
  simp only [house, map_mul]; apply norm_mul_le

中文:
定理 house_mul_le
  条件: (α β : K)
  结论: house (α * β) <= house α * house β
  证明: by
  simp only [house, map_mul]; apply norm_mul_le

Depends on / 依赖: map_mul, norm_mul_le
-/
theorem house_mul_le (α β : K) : house (α * β) <= house α * house β := by
  simp only [house, map_mul]; apply norm_mul_le

/--
lemma `house_prod_le` / 引理 `house_prod_le`

English:
lemma house_prod_le
  given: (s : Finset K)
  statement: house (∏ x in s, x) <= ∏ x in s, house x
  proof: by
  simpa [house, map_prod] using Finset.norm_prod_le _ _

中文:
引理 house_prod_le
  条件: (s : 有限集 K)
  结论: house (∏ x in s, x) <= ∏ x in s, house x
  证明: by
  simpa [house, map_prod] using Finset.norm_prod_le _ _

Depends on / 依赖: Finset, Finset.norm_prod_le, map_prod, norm_prod_le
-/
lemma house_prod_le (s : Finset K) : house (∏ x in s, x) <= ∏ x in s, house x := by
  simpa [house, map_prod] using Finset.norm_prod_le _ _

/--
theorem `house_add_le` / 定理 `house_add_le`

English:
theorem house_add_le
  given: (α β : K)
  statement: house (α + β) <= house α + house β
  proof: by
  simp only [house, map_add]; apply norm_add_le

中文:
定理 house_add_le
  条件: (α β : K)
  结论: house (α + β) <= house α + house β
  证明: by
  simp only [house, map_add]; apply norm_add_le

Depends on / 依赖: map_add, norm_add_le
-/
theorem house_add_le (α β : K) : house (α + β) <= house α + house β := by
  simp only [house, map_add]; apply norm_add_le

/--
theorem `house_pow_le` / 定理 `house_pow_le`

English:
theorem house_pow_le
  given: (α : K) (i : Nat)
  statement: house (α ^ i) <= house α ^ i
  proof: by
  simpa only [house, map_pow] using norm_pow_le ((canonicalEmbedding K) α) i

中文:
定理 house_pow_le
  条件: (α : K) (i : 自然数)
  结论: house (α ^ i) <= house α ^ i
  证明: by
  simpa only [house, map_pow] using norm_pow_le ((canonicalEmbedding K) α) i

Depends on / 依赖: canonicalEmbedding, map_pow, norm_pow_le
-/
theorem house_pow_le (α : K) (i : Nat) : house (α ^ i) <= house α ^ i := by
  simpa only [house, map_pow] using norm_pow_le ((canonicalEmbedding K) α) i

/--
theorem `house_nat_mul` / 定理 `house_nat_mul`

English:
theorem house_nat_mul
  given: (α : K) (c : Nat)
  statement: house (c * α) = c * house α
  proof: by
  rw [house_eq_sup']; rw [house_eq_sup']; rw [Finset.sup'_eq_sup]; rw [Finset.sup'_eq_sup]
  norm_cast
  simp [NNReal.mul_finset_sup]

中文:
定理 house_nat_mul
  条件: (α : K) (c : 自然数)
  结论: house (c * α) = c * house α
  证明: by
  rw [house_eq_sup']; rw [house_eq_sup']; rw [Finset.sup'_eq_sup]; rw [Finset.sup'_eq_sup]
  norm_cast
  simp [NNReal.mul_finset_sup]

Depends on / 依赖: Finset, Finset.sup, NNReal, NNReal.mul_finset_sup, _eq_sup, house_eq_sup, mul_finset_sup
-/
theorem house_nat_mul (α : K) (c : Nat) : house (c * α) = c * house α := by
  rw [house_eq_sup']; rw [house_eq_sup']; rw [Finset.sup'_eq_sup]; rw [Finset.sup'_eq_sup]
  norm_cast
  simp [NNReal.mul_finset_sup]

/--
theorem `house_intCast` / 定理 `house_intCast`

English:
theorem house_intCast
  given: (x : Int)
  statement: house (x : K) = |x|
  proof: by
  simp only [house, map_intCast, Pi.intCast_def, pi_norm_const, Complex.norm_intCast, Int.cast_abs]

中文:
定理 house_intCast
  条件: (x : 整数)
  结论: house (x : K) = |x|
  证明: by
  simp only [house, map_intCast, Pi.intCast_def, pi_norm_const, Complex.norm_intCast, Int.cast_abs]
-/
@[simp] theorem house_intCast (x : Int) : house (x : K) = |x| := by
  simp only [house, map_intCast, Pi.intCast_def, pi_norm_const, Complex.norm_intCast, Int.cast_abs]

/--
lemma `exists_conjugate_one_le_norm` / 引理 `exists_conjugate_one_le_norm`

English:
lemma exists_conjugate_one_le_norm
  given: {α : 𝓞 K} (hα0 : α != 0)
  proof: by
  obtain ⟨w, hw⟩ : exists w : InfinitePlace K, 1 <= w α := by
    by_contra! h_neg
    let w₀ := Classical.arbitrary (InfinitePlace K)
    have h_ge_one : 1 <= w₀ α := InfinitePlace.one_le_of_lt_one hα0 (fun z _ => h_neg z)
    exact (h_neg w₀).not_ge h_ge_one
  use w.embedding
  rwa [InfinitePla

中文:
引理 存在_conjugate_one_le_norm
  条件: {α : 𝓞 K} (hα0 : α != 0)
  证明: by
  obtain ⟨w, hw⟩ : exists w : InfinitePlace K, 1 <= w α := by
    by_contra! h_neg
    let w₀ := Classical.arbitrary (InfinitePlace K)
    have h_ge_one : 1 <= w₀ α := InfinitePlace.one_le_of_lt_one hα0 (fun z _ => h_neg z)
    exact (h_neg w₀).not_ge h_ge_one
  use w.embedding
  rwa [InfinitePla

Depends on / 依赖: Classical, Classical.arbitrary, InfinitePlace, InfinitePlace.norm_embedding_eq, InfinitePlace.one_le_of_lt_one, arbitrary, embedding, h_ge_one, h_neg, norm_embedding_eq, not_ge, one_le_of_lt_one, w.embedding
-/
lemma exists_conjugate_one_le_norm {α : 𝓞 K} (hα0 : α != 0) :
    exists σ : K ->+* Complex, 1 <= ‖σ α‖ := by
  obtain ⟨w, hw⟩ : exists w : InfinitePlace K, 1 <= w α := by
    by_contra! h_neg
    let w₀ := Classical.arbitrary (InfinitePlace K)
    have h_ge_one : 1 <= w₀ α := InfinitePlace.one_le_of_lt_one hα0 (fun z _ => h_neg z)
    exact (h_neg w₀).not_ge h_ge_one
  use w.embedding
  rwa [InfinitePlace.norm_embedding_eq]

/--
lemma `norm_embedding_le_house` / 引理 `norm_embedding_le_house`

English:
lemma norm_embedding_le_house
  given: (α : K) (σ : K ->+* Complex)
  statement: ‖σ α‖ <= house α
  proof: by
  rw [house_eq_sup']
  exact Finset.le_sup' (f := (‖· α‖₊)) (Finset.mem_univ σ)

中文:
引理 norm_embedding_le_house
  条件: (α : K) (σ : K ->+* 复形)
  结论: ‖σ α‖ <= house α
  证明: by
  rw [house_eq_sup']
  exact Finset.le_sup' (f := (‖· α‖₊)) (Finset.mem_univ σ)

Depends on / 依赖: Finset, Finset.le_sup, Finset.mem_univ, house_eq_sup, le_sup, mem_univ
-/
lemma norm_embedding_le_house (α : K) (σ : K ->+* Complex) : ‖σ α‖ <= house α := by
  rw [house_eq_sup']
  exact Finset.le_sup' (f := (‖· α‖₊)) (Finset.mem_univ σ)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `one_le_house_of_isIntegral` / 引理 `one_le_house_of_isIntegral`

English:
lemma one_le_house_of_isIntegral
  given: {α : K} (hα : IsIntegral Int α) (hα0 : α != 0)
  proof: by
  have ⟨σ, hσ⟩ : exists σ : K ->+* Complex, 1 <= ‖σ α‖ := by
    apply exists_conjugate_one_le_norm (K := K) (α := ⟨α, hα⟩)
    simpa [RingOfIntegers.ext_iff]
  apply hσ.trans (norm_embedding_le_house α σ)

中文:
引理 one_le_house_of_is整数egral
  条件: {α : K} (hα : 是整 整数 α) (hα0 : α != 0)
  证明: by
  have ⟨σ, hσ⟩ : exists σ : K ->+* Complex, 1 <= ‖σ α‖ := by
    apply exists_conjugate_one_le_norm (K := K) (α := ⟨α, hα⟩)
    simpa [RingOfIntegers.ext_iff]
  apply hσ.trans (norm_embedding_le_house α σ)

Depends on / 依赖: RingOfIntegers, RingOfIntegers.ext_iff, exists_conjugate_one_le_norm, ext_iff, norm_embedding_le_house
-/
lemma one_le_house_of_isIntegral {α : K} (hα : IsIntegral Int α) (hα0 : α != 0) :
    1 <= house α := by
  have ⟨σ, hσ⟩ : exists σ : K ->+* Complex, 1 <= ‖σ α‖ := by
    apply exists_conjugate_one_le_norm (K := K) (α := ⟨α, hα⟩)
    simpa [RingOfIntegers.ext_iff]
  apply hσ.trans (norm_embedding_le_house α σ)

/--
lemma `norm_norm_le_norm_mul_house_pow` / 引理 `norm_norm_le_norm_mul_house_pow`

English:
lemma norm_norm_le_norm_mul_house_pow
  given: (α : K) (σ : K ->+* Complex)
  proof: by
  classical
  set σ' := σ.toRatAlgHom
  calc _ = ‖∏ τ : K ->ₐ[Rat] Complex, τ α‖ := ?_
       _ = ‖(σ' α) * ∏ τ in univ.erase σ', τ α‖ := by rw [mul_prod_erase univ (· α) (mem_univ σ')]
       _ <= ‖σ' α‖ * ∏ τ in univ.erase σ', ‖τ α‖ := ?_
       _ <= ‖σ' α‖ * ∏ τ in univ.erase σ', house α := by

中文:
引理 norm_norm_le_norm_mul_house_pow
  条件: (α : K) (σ : K ->+* 复形)
  证明: by
  classical
  set σ' := σ.toRatAlgHom
  calc _ = ‖∏ τ : K ->ₐ[Rat] Complex, τ α‖ := ?_
       _ = ‖(σ' α) * ∏ τ in univ.erase σ', τ α‖ := by rw [mul_prod_erase univ (· α) (mem_univ σ')]
       _ <= ‖σ' α‖ * ∏ τ in univ.erase σ', ‖τ α‖ := ?_
       _ <= ‖σ' α‖ * ∏ τ in univ.erase σ', house α := by

Depends on / 依赖: Algebra, Algebra.norm_eq_prod_embeddings, Comple, Complex.norm_ratCast, Module, Module.finrank, Rat.norm_cast_real, Real.norm_eq_abs, classical, eq_ratCast, finrank, mem_univ, mul_prod_erase, norm_cast_real, norm_embedding_le_house, norm_eq_abs, norm_eq_prod_embeddings, norm_ratCast, toRatAlgHom, univ.erase
-/
lemma norm_norm_le_norm_mul_house_pow (α : K) (σ : K ->+* Complex) :
    ‖Algebra.norm Rat α‖ <= ‖σ α‖ * house α ^ (Module.finrank Rat K - 1) := by
  classical
  set σ' := σ.toRatAlgHom
  calc _ = ‖∏ τ : K ->ₐ[Rat] Complex, τ α‖ := ?_
       _ = ‖(σ' α) * ∏ τ in univ.erase σ', τ α‖ := by rw [mul_prod_erase univ (· α) (mem_univ σ')]
       _ <= ‖σ' α‖ * ∏ τ in univ.erase σ', ‖τ α‖ := ?_
       _ <= ‖σ' α‖ * ∏ τ in univ.erase σ', house α := by gcongr; apply norm_embedding_le_house
       _ = ‖σ' α‖ * house α ^ (Module.finrank Rat K - 1) := by simp
  · rw [← Algebra.norm_eq_prod_embeddings, ← Rat.norm_cast_real,
      Real.norm_eq_abs, eq_ratCast, Complex.norm_ratCast]
  · rw [Complex.norm_mul]
    gcongr
    exact norm_prod_le (univ.erase σ') (· α)

end

end NumberField

namespace NumberField.house

noncomputable section

variable (K)

open Module.Free Module canonicalEmbedding Matrix Finset

attribute [local instance] Matrix.seminormedAddCommGroup

section DecidableEq

variable [DecidableEq (K ->+* Complex)]

set_option backward.privateInPublic true in
/--
Definition of `c` / `c` 的定义

English:
definition c
  body: (finrank Rat K) * ‖((basisMatrix K).transpose)⁻¹‖

中文:
定义 c
  定义体: (finrank Rat K) * ‖((basisMatrix K).transpose)⁻¹‖
-/
private def c := (finrank Rat K) * ‖((basisMatrix K).transpose)⁻¹‖

/--
theorem `c_nonneg` / 定理 `c_nonneg`

English:
theorem c_nonneg
  statement: 0 <= c K
  proof: by
  rw [c]
  positivity

中文:
定理 c_nonneg
  结论: 0 <= c K
  证明: by
  rw [c]
  positivity
-/
private theorem c_nonneg : 0 <= c K := by
  rw [c]
  positivity

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `basis_repr_norm_le_const_mul_house` / 定理 `basis_repr_norm_le_const_mul_house`

English:
theorem basis_repr_norm_le_const_mul_house
  given: (α : 𝓞 K) (i : K ->+* Complex)
  proof: by
  let σ := canonicalEmbedding K
  calc
    _ <= ∑ j, ‖(basisMatrix K)ᵀ⁻¹ i j‖ * ‖σ (algebraMap (𝓞 K) K α) j‖ := by
      rw [← inverse_basisMatrix_mulVec_eq_repr]
      exact norm_sum_le_of_le _ fun _ _ => (norm_mul _ _).le
    _ <= ∑ j, ‖((basisMatrix K).transpose)⁻¹‖ * ‖σ (algebraMap (𝓞 K) K α)

中文:
定理 basis_repr_norm_le_const_mul_house
  条件: (α : 𝓞 K) (i : K ->+* 复形)
  证明: by
  let σ := canonicalEmbedding K
  calc
    _ <= ∑ j, ‖(basisMatrix K)ᵀ⁻¹ i j‖ * ‖σ (algebraMap (𝓞 K) K α) j‖ := by
      rw [← inverse_basisMatrix_mulVec_eq_repr]
      exact norm_sum_le_of_le _ fun _ _ => (norm_mul _ _).le
    _ <= ∑ j, ‖((basisMatrix K).transpose)⁻¹‖ * ‖σ (algebraMap (𝓞 K) K α)

Depends on / 依赖: algebraMap, basisMatrix, canonicalEmbedding, inverse_basisMatrix_mulVec_eq_repr, norm_entry_le_entrywise_sup_norm, norm_le, norm_mul, norm_sum_le_of_le, transpose
-/
theorem basis_repr_norm_le_const_mul_house (α : 𝓞 K) (i : K ->+* Complex) :
    ‖(((integralBasis K).reindex (equivReindex K).symm).repr α i : Complex)‖ <=
      (c K) * house (algebraMap (𝓞 K) K α) := by
  let σ := canonicalEmbedding K
  calc
    _ <= ∑ j, ‖(basisMatrix K)ᵀ⁻¹ i j‖ * ‖σ (algebraMap (𝓞 K) K α) j‖ := by
      rw [← inverse_basisMatrix_mulVec_eq_repr]
      exact norm_sum_le_of_le _ fun _ _ => (norm_mul _ _).le
    _ <= ∑ j, ‖((basisMatrix K).transpose)⁻¹‖ * ‖σ (algebraMap (𝓞 K) K α) j‖ := by
      gcongr
      exact norm_entry_le_entrywise_sup_norm ((basisMatrix K).transpose)⁻¹
    _ <= ∑ _ : K ->+* Complex, ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖
        * house (algebraMap (𝓞 K) K α) := by
      gcongr with j
      exact norm_le_pi_norm (σ ((algebraMap (𝓞 K) K) α)) j
    _ = ↑(finrank Rat K) * ‖((basisMatrix K).transpose)⁻¹‖ * house (algebraMap (𝓞 K) K α) := by
      simp [Embeddings.card, mul_assoc]

/--
Definition of `newBasis` / `newBasis` 的定义

English:
definition newBasis
  body: (RingOfIntegers.basis K).reindex (equivReindex K).symm

中文:
定义 newBasis
  定义体: (RingOfIntegers.basis K).reindex (equivReindex K).symm
-/
private def newBasis := (RingOfIntegers.basis K).reindex (equivReindex K).symm

/--
Definition of `supOfBasis` / `supOfBasis` 的定义

English:
definition supOfBasis
  signature: : Real
  body: univ.sup' univ_nonempty
  fun r => house (algebraMap (𝓞 K) K (newBasis K r))

中文:
定义 supOfBasis
  签名: : 实数
  定义体: univ.sup' univ_nonempty
  fun r => house (algebraMap (𝓞 K) K (newBasis K r))
-/
private def supOfBasis : Real := univ.sup' univ_nonempty
  fun r => house (algebraMap (𝓞 K) K (newBasis K r))

end DecidableEq

/--
theorem `supOfBasis_nonneg` / 定理 `supOfBasis_nonneg`

English:
theorem supOfBasis_nonneg
  statement: 0 <= supOfBasis K
  proof: by
  simp only [supOfBasis, le_sup'_iff, mem_univ, and_self,
    exists_const, house_nonneg]

中文:
定理 supOfBasis_nonneg
  结论: 0 <= supOfBasis K
  证明: by
  simp only [supOfBasis, le_sup'_iff, mem_univ, and_self,
    exists_const, house_nonneg]
-/
private theorem supOfBasis_nonneg : 0 <= supOfBasis K := by
  simp only [supOfBasis, le_sup'_iff, mem_univ, and_self,
    exists_const, house_nonneg]

variable {α : Type*} {β : Type*} (a : Matrix α β (𝓞 K))

/--
Definition of `a'` / `a'` 的定义

English:
definition a'
  signature: : α -> β -> (K ->+* Complex) -> (K ->+* Complex) -> Int
  body: fun k l r =>
  (newBasis K).repr (a k l * (newBasis K) r)

中文:
定义 a'
  签名: : α -> β -> (K ->+* 复形) -> (K ->+* 复形) -> 整数
  定义体: fun k l r =>
  (newBasis K).repr (a k l * (newBasis K) r)
-/
private def a' : α -> β -> (K ->+* Complex) -> (K ->+* Complex) -> Int := fun k l r =>
  (newBasis K).repr (a k l * (newBasis K) r)

set_option backward.privateInPublic true in
/--
Definition of `asiegel` / `asiegel` 的定义

English:
definition asiegel
  signature: : Matrix (α × (K ->+* Complex)) (β × (K ->+* Complex)) Int
  body: fun k l => a' K a k.1 l.1 l.2 k.2

中文:
定义 asiegel
  签名: : 矩阵 (α × (K ->+* 复形)) (β × (K ->+* 复形)) 整数
  定义体: fun k l => a' K a k.1 l.1 l.2 k.2
-/
private def asiegel : Matrix (α × (K ->+* Complex)) (β × (K ->+* Complex)) Int := fun k l => a' K a k.1 l.1 l.2 k.2

variable (ha : a != 0)

set_option backward.isDefEq.respectTransparency false in
include ha in
/--
theorem `asiegel_ne_0` / 定理 `asiegel_ne_0`

English:
theorem asiegel_ne_0
  statement: asiegel K a != 0
  proof: by
  simp +unfoldPartialApp only [asiegel, a']
  simp only [ne_eq]
  rw [funext_iff]; intro hs
  simp only [Prod.forall] at hs
  apply ha
  rw [← Matrix.ext_iff]; intro k' l
  specialize hs k'
  let ⟨b⟩ := Fintype.card_pos_iff.1 (Fintype.card_pos (α := (K ->+* Complex)))
have := ((newBasis K).repr.m

中文:
定理 asiegel_ne_0
  结论: asiegel K a != 0
  证明: by
  simp +unfoldPartialApp only [asiegel, a']
  simp only [ne_eq]
  rw [funext_iff]; intro hs
  simp only [Prod.forall] at hs
  apply ha
  rw [← Matrix.ext_iff]; intro k' l
  specialize hs k'
  let ⟨b⟩ := Fintype.card_pos_iff.1 (Fintype.card_pos (α := (K ->+* Complex)))
have := ((newBasis K).repr.m
-/
private theorem asiegel_ne_0 : asiegel K a != 0 := by
  simp +unfoldPartialApp only [asiegel, a']
  simp only [ne_eq]
  rw [funext_iff]; intro hs
  simp only [Prod.forall] at hs
  apply ha
  rw [← Matrix.ext_iff]; intro k' l
  specialize hs k'
  let ⟨b⟩ := Fintype.card_pos_iff.1 (Fintype.card_pos (α := (K ->+* Complex)))
have := ((newBasis K).repr.map_eq_zero_iff (x := (a k' l * (newBasis K) b))).1 by
    ext b'
    specialize hs b'
    rw [funext_iff] at hs
    simp only [Prod.forall] at hs
    apply hs
  simp only [mul_eq_zero] at this
  exact this.resolve_right (Basis.ne_zero (newBasis K) b)

variable {p q : Nat} (h0p : 0 < p) (hpq : p < q) (x : β × (K ->+* Complex) -> Int) (hxl : x != 0)

/--
Definition of `ξ` / `ξ` 的定义

English:
definition ξ
  signature: : β -> 𝓞 K
  body: fun l => ∑ r : K ->+* Complex, x (l, r) * (newBasis K r)

中文:
定义 ξ
  签名: : β -> 𝓞 K
  定义体: fun l => ∑ r : K ->+* Complex, x (l, r) * (newBasis K r)
-/
private def ξ : β -> 𝓞 K := fun l => ∑ r : K ->+* Complex, x (l, r) * (newBasis K r)

set_option backward.privateInPublic true in
include hxl in
/--
theorem `ξ_ne_0` / 定理 `ξ_ne_0`

English:
theorem ξ_ne_0
  statement: ξ K x != 0
  proof: by
  intro H
  apply hxl
  ext ⟨l, r⟩
  rw [funext_iff] at H
  have hblin := Basis.linearIndependent (newBasis K)
  simp only [zsmul_eq_mul, Fintype.linearIndependent_iff] at hblin
  exact hblin (fun r => x (l, r)) (H _) r

中文:
定理 ξ_ne_0
  结论: ξ K x != 0
  证明: by
  intro H
  apply hxl
  ext ⟨l, r⟩
  rw [funext_iff] at H
  have hblin := Basis.linearIndependent (newBasis K)
  simp only [zsmul_eq_mul, Fintype.linearIndependent_iff] at hblin
  exact hblin (fun r => x (l, r)) (H _) r
-/
private theorem ξ_ne_0 : ξ K x != 0 := by
  intro H
  apply hxl
  ext ⟨l, r⟩
  rw [funext_iff] at H
  have hblin := Basis.linearIndependent (newBasis K)
  simp only [zsmul_eq_mul, Fintype.linearIndependent_iff] at hblin
  exact hblin (fun r => x (l, r)) (H _) r

/--
theorem `lin_1` / 定理 `lin_1`

English:
theorem lin_1
  given: (l k r)
  statement: a k l * (newBasis K) r =
  proof: by
  simp only [Basis.sum_repr (newBasis K) (a k l * (newBasis K) r), a', ← zsmul_eq_mul]

中文:
定理 lin_1
  条件: (l k r)
  结论: a k l * (newBasis K) r =
  证明: by
  simp only [Basis.sum_repr (newBasis K) (a k l * (newBasis K) r), a', ← zsmul_eq_mul]
-/
private theorem lin_1 (l k r) : a k l * (newBasis K) r =
    ∑ u, (a' K a k l r u) * (newBasis K) u := by
  simp only [Basis.sum_repr (newBasis K) (a k l * (newBasis K) r), a', ← zsmul_eq_mul]

-- Variable declarations can only reference public items.
set_option backward.privateInPublic true
variable [Fintype β] (cardβ : Fintype.card β = q) (hmulvec0 : asiegel K a *ᵥ x = 0)

include hxl hmulvec0 in
/--
theorem `ξ_mulVec_eq_0` / 定理 `ξ_mulVec_eq_0`

English:
theorem ξ_mulVec_eq_0
  statement: a *ᵥ ξ K x = 0
  proof: by
  funext k; simp only [Pi.zero_apply]; rw [eq_comm]
  have lin_0 : forall u, ∑ r, ∑ l, (a' K a k l r u * x (l, r) : 𝓞 K) = 0 := by
    intro u
    have hξ := ξ_ne_0 K x hxl
    rw [Ne]; rw [funext_iff]; rw [not_forall] at hξ
    rcases hξ with ⟨l, hξ⟩
    rw [funext_iff] at hmulvec0
    specializ

中文:
定理 ξ_mulVec_eq_0
  结论: a *ᵥ ξ K x = 0
  证明: by
  funext k; simp only [Pi.zero_apply]; rw [eq_comm]
  have lin_0 : forall u, ∑ r, ∑ l, (a' K a k l r u * x (l, r) : 𝓞 K) = 0 := by
    intro u
    have hξ := ξ_ne_0 K x hxl
    rw [Ne]; rw [funext_iff]; rw [not_forall] at hξ
    rcases hξ with ⟨l, hξ⟩
    rw [funext_iff] at hmulvec0
    specializ
-/
private theorem ξ_mulVec_eq_0 : a *ᵥ ξ K x = 0 := by
  funext k; simp only [Pi.zero_apply]; rw [eq_comm]
  have lin_0 : forall u, ∑ r, ∑ l, (a' K a k l r u * x (l, r) : 𝓞 K) = 0 := by
    intro u
    have hξ := ξ_ne_0 K x hxl
    rw [Ne]; rw [funext_iff]; rw [not_forall] at hξ
    rcases hξ with ⟨l, hξ⟩
    rw [funext_iff] at hmulvec0
    specialize hmulvec0 ⟨k, u⟩
    simp only [Fintype.sum_prod_type, mulVec, dotProduct, asiegel] at hmulvec0
    rw [sum_comm] at hmulvec0
    exact mod_cast hmulvec0
  have : 0 = ∑ u, (∑ r, ∑ l, a' K a k l r u * x (l, r) : 𝓞 K) * (newBasis K) u := by
    simp only [lin_0, zero_mul, sum_const_zero]
  have : 0 = ∑ r, ∑ l, x (l, r) * ∑ u, a' K a k l r u * (newBasis K) u := by
    conv at this => enter [2, 2, u]; rw [sum_mul]
    rw [sum_comm] at this
    rw [this]; congr 1; ext1 r
    conv => enter [1, 2, l]; rw [sum_mul]
    rw [sum_comm]; congr 1; ext1 r
    rw [mul_sum]; congr 1; ext1 r
    ring
  rw [sum_comm] at this
  rw [this]; congr 1; ext1 l
  rw [ξ]; rw [mul_sum]; congr 1; ext1 l
  rw [← lin_1]; ring

variable {A : Real} (habs : forall k l, (house ((algebraMap (𝓞 K) K) (a k l))) <= A)

variable [DecidableEq (K ->+* Complex)]

/--
Definition of `c₂` / `c₂` 的定义

English:
abbreviation c₂
  body: max 1 (c K) * (supOfBasis K)

中文:
缩写 c₂
  定义体: max 1 (c K) * (supOfBasis K)
-/
private abbrev c₂ := max 1 (c K) * (supOfBasis K)

/--
theorem `c₂_nonneg` / 定理 `c₂_nonneg`

English:
theorem c₂_nonneg
  statement: 0 <= c₂ K
  proof: mul_nonneg (le_trans zero_le_one (le_max_left ..)) (supOfBasis_nonneg _)

中文:
定理 c₂_nonneg
  结论: 0 <= c₂ K
  证明: mul_nonneg (le_trans zero_le_one (le_max_left ..)) (supOfBasis_nonneg _)
-/
private theorem c₂_nonneg : 0 <= c₂ K :=
  mul_nonneg (le_trans zero_le_one (le_max_left ..)) (supOfBasis_nonneg _)

variable [Fintype α] (cardα : Fintype.card α = p) (Apos : 0 <= A)
  (hxbound : ‖x‖ <= (q * finrank Rat K * ‖asiegel K a‖) ^ ((p : Real) / (q - p)))

include habs Apos in
/--
theorem `asiegel_remark` / 定理 `asiegel_remark`

English:
theorem asiegel_remark
  statement: ‖asiegel K a‖ <= c₂ K * A
  proof: by
  have := c_nonneg K
  rw [Matrix.norm_le_iff]
  · intro kr lu
    calc
      ‖asiegel K a kr lu‖ = |asiegel K a kr lu| := ?_
      _ <= c K * house ((algebraMap (𝓞 K) K) (a kr.1 lu.1 * ((newBasis K) lu.2))) := ?_
      _ <= c K * house ((algebraMap (𝓞 K) K) (a kr.1 lu.1)) *
        house ((algeb

中文:
定理 asiegel_remark
  结论: ‖asiegel K a‖ <= c₂ K * A
  证明: by
  have := c_nonneg K
  rw [Matrix.norm_le_iff]
  · intro kr lu
    calc
      ‖asiegel K a kr lu‖ = |asiegel K a kr lu| := ?_
      _ <= c K * house ((algebraMap (𝓞 K) K) (a kr.1 lu.1 * ((newBasis K) lu.2))) := ?_
      _ <= c K * house ((algebraMap (𝓞 K) K) (a kr.1 lu.1)) *
        house ((algeb
-/
private theorem asiegel_remark : ‖asiegel K a‖ <= c₂ K * A := by
  have := c_nonneg K
  rw [Matrix.norm_le_iff]
  · intro kr lu
    calc
      ‖asiegel K a kr lu‖ = |asiegel K a kr lu| := ?_
      _ <= c K * house ((algebraMap (𝓞 K) K) (a kr.1 lu.1 * ((newBasis K) lu.2))) := ?_
      _ <= c K * house ((algebraMap (𝓞 K) K) (a kr.1 lu.1)) *
        house ((algebraMap (𝓞 K) K) ((newBasis K) lu.2)) := ?_
      _ <= c K * A * house ((algebraMap (𝓞 K) K) ((newBasis K) lu.2)) := ?_
      _ <= c K * A * supOfBasis K := ?_
      _ <= c₂ K * A := ?_
    · simp only [Int.cast_abs, ← Real.norm_eq_abs (asiegel K a kr lu)]; rfl
    · have remark := basis_repr_norm_le_const_mul_house K
      simp only [Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
        integralBasis_repr_apply, eq_intCast, Rat.cast_intCast,
          Complex.norm_intCast] at remark
      exact mod_cast remark ((a kr.1 lu.1 * ((newBasis K) lu.2))) kr.2
    · simp only [house, map_mul, mul_assoc]
      gcongr
      apply norm_mul_le
    · rw [mul_assoc, mul_assoc]
      gcongr _ * (?_ * _)
      · apply house_nonneg
      · exact habs kr.1 lu.1
    · gcongr
      simp only [supOfBasis, le_sup'_iff, mem_univ]; use lu.2
    · rw [mul_right_comm, c₂]
      gcongr
      exacts [supOfBasis_nonneg _, le_max_right ..]
  · exact mul_nonneg (c₂_nonneg _) Apos

/--
Definition of `c₁` / `c₁` 的定义

English:
definition c₁
  body: finrank Rat K * c₂ K

include habs Apos hxbound hpq in

中文:
定义 c₁
  定义体: finrank Rat K * c₂ K

include habs Apos hxbound hpq in
-/
private def c₁ := finrank Rat K * c₂ K

include habs Apos hxbound hpq in
/--
theorem `house_le_bound` / 定理 `house_le_bound`

English:
theorem house_le_bound
  statement: forall l, house (ξ K x l).1 <= (c₁ K) *
  proof: by
  let h := finrank Rat K
  intro l
  have H₀ : 0 <= NumberField.house.supOfBasis K := supOfBasis_nonneg _
have H₁ : 0 < (q - p : Real) := sub_pos.mpr mod_cast hpq
  calc _ = house (algebraMap (𝓞 K) K (∑ r, (x (l, r)) * ((newBasis K) r))) := rfl
       _ <= ∑ r, house (((algebraMap (𝓞 K) K) (x (l,

中文:
定理 house_le_bound
  结论: 对任意 l, house (ξ K x l).1 <= (c₁ K) *
  证明: by
  let h := finrank Rat K
  intro l
  have H₀ : 0 <= NumberField.house.supOfBasis K := supOfBasis_nonneg _
have H₁ : 0 < (q - p : Real) := sub_pos.mpr mod_cast hpq
  calc _ = house (algebraMap (𝓞 K) K (∑ r, (x (l, r)) * ((newBasis K) r))) := rfl
       _ <= ∑ r, house (((algebraMap (𝓞 K) K) (x (l,
-/
private theorem house_le_bound : forall l, house (ξ K x l).1 <= (c₁ K) *
    ((c₁ K * q * A) ^ ((p : Real) / (q - p))) := by
  let h := finrank Rat K
  intro l
  have H₀ : 0 <= NumberField.house.supOfBasis K := supOfBasis_nonneg _
have H₁ : 0 < (q - p : Real) := sub_pos.mpr mod_cast hpq
  calc _ = house (algebraMap (𝓞 K) K (∑ r, (x (l, r)) * ((newBasis K) r))) := rfl
       _ <= ∑ r, house (((algebraMap (𝓞 K) K) (x (l, r))) *
        ((algebraMap (𝓞 K) K) ((newBasis K) r))) := ?_
       _ <= ∑ r, ‖x (l, r)‖ * house ((algebraMap (𝓞 K) K) ((newBasis K) r)) := ?_
       _ <= ∑ r, ‖x (l, r)‖ * (supOfBasis K) := ?_
       _ <= ∑ _r : K ->+* Complex, ((↑q * h * ‖asiegel K a‖) ^ ((p : Real) / (q - p))) * supOfBasis K := ?_
       _ <= h * (c₂ K) * ((q * c₁ K * A) ^ ((p : Real) / (q - p))) := ?_
       _ <= c₁ K * ((c₁ K * ↑q * A) ^ ((p : Real) / (q - p))) := ?_
  · simp_rw [← map_mul, map_sum]; apply house_sum_le_sum_house
  · gcongr with r _; convert! house_mul_le ..
    simp only [map_intCast, house_intCast, Int.cast_abs, Int.norm_eq_abs]
  · unfold supOfBasis
    gcongr with r _
    simp only [le_sup'_iff, mem_univ, true_and]; use r
  · gcongr with r _
    exact le_trans (norm_le_pi_norm x ⟨l, r⟩) hxbound
  · simp only [sum_const, card_univ, nsmul_eq_mul]
    rw [Embeddings.card]; rw [mul_comm _ (supOfBasis K)]; rw [c₂]; rw [c₁]; rw [← mul_assoc]; rw [← mul_assoc (q : Real)]; rw [mul_assoc (q * _ : Real)]
    gcongr
    · exact le_mul_of_one_le_left (supOfBasis_nonneg K) (le_max_left ..)
    · exact asiegel_remark K a habs Apos
  · rw [mul_comm (q : Real) (c₁ K)]; rfl

set_option backward.privateInPublic.warn false in
include hpq h0p cardα cardβ ha habs in
/--
theorem `exists_ne_zero_int_vec_house_le` / 定理 `exists_ne_zero_int_vec_house_le`

English:
theorem exists_ne_zero_int_vec_house_le
  proof: by
  let h := finrank Rat K
  have hphqh : p * h < q * h := by gcongr; exact finrank_pos
  have h0ph : 0 < p * h := by rw [mul_pos_iff]; constructor; exact ⟨h0p, finrank_pos⟩
  have hfinp : Fintype.card (α × (K ->+* Complex)) = p * h := by
    rw [Fintype.card_prod]; rw [cardα]; rw [Embeddings.card]

中文:
定理 存在_ne_zero_int_vec_house_le
  证明: by
  let h := finrank Rat K
  have hphqh : p * h < q * h := by gcongr; exact finrank_pos
  have h0ph : 0 < p * h := by rw [mul_pos_iff]; constructor; exact ⟨h0p, finrank_pos⟩
  have hfinp : Fintype.card (α × (K ->+* Complex)) = p * h := by
    rw [Fintype.card_prod]; rw [cardα]; rw [Embeddings.card]

Depends on / 依赖: Embeddings, Embeddings.card, Fintype, Fintype.card, Fintype.card_prod, Int.Matrix.exists_ne_zero_int_vec_norm_le, Matrix, asiegel, card_prod, exists_ne_zero_int_vec_norm_le, finrank, finrank_pos, hmulvec0, hxbound, mul_pos_iff
-/
theorem exists_ne_zero_int_vec_house_le :
    exists (ξ : β -> 𝓞 K), ξ != 0 ∧ a *ᵥ ξ = 0 ∧
    forall l, house (ξ l).1 <= c₁ K * ((c₁ K * q * A) ^ ((p : Real) / (q - p))) := by
  let h := finrank Rat K
  have hphqh : p * h < q * h := by gcongr; exact finrank_pos
  have h0ph : 0 < p * h := by rw [mul_pos_iff]; constructor; exact ⟨h0p, finrank_pos⟩
  have hfinp : Fintype.card (α × (K ->+* Complex)) = p * h := by
    rw [Fintype.card_prod]; rw [cardα]; rw [Embeddings.card]
  have hfinq : Fintype.card (β × (K ->+* Complex)) = q * h := by
    rw [Fintype.card_prod]; rw [cardβ]; rw [Embeddings.card]
  have ⟨x, hxl, hmulvec0, hxbound⟩ :=
    Int.Matrix.exists_ne_zero_int_vec_norm_le' (asiegel K a)
      (by rwa [hfinp, hfinq]) (by rwa [hfinp]) (asiegel_ne_0 K a ha)
  simp only [hfinp, hfinq, Nat.cast_mul] at hmulvec0 hxbound
  rw [← sub_mul]; rw [mul_div_mul_right _ _ (mod_cast finrank_pos.ne')] at hxbound
  have Apos : 0 <= A := by
    have ⟨k⟩ := Fintype.card_pos_iff.1 (cardα ▸ h0p)
    have ⟨l⟩ := Fintype.card_pos_iff.1 (cardβ ▸ h0p.trans hpq)
    exact le_trans (house_nonneg _) (habs k l)
  use ξ K x, ξ_ne_0 K x hxl, ξ_mulVec_eq_0 K a x hxl hmulvec0,
    house_le_bound K a hpq x habs Apos hxbound

end

end NumberField.house
