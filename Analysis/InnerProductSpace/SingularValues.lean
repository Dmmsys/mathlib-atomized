/-
Copyright (c) 2026 Niels Voss, Arnav Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niels Voss, Arnav Mehta
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# Singular values for finite-dimensional linear maps

For a linear map `T` between finite-dimensional inner product spaces `E` and `F`, we define the
singular values, which are the square roots of the eigenvalues of `T.adjoint ∘ₗ T`, arranged in
descending order and repeated according to their multiplicity.

With our definition, there are countably infinitely many singular values, but only the first rank(T)
singular values are nonzero.

The singular values are zero-indexed, so `T.singularValues 0` is the first singular value.
This means the positive singular values occur at `0 ≤ i < rank(T)` and not `1 ≤ i ≤ rank(T)`.

## Main definition

- `LinearMap.singularValues`: The infinite but finitely supported sequence of the singular values of
  a linear map.

## Main statements

- `LinearMap.support_singularValues`: The first rank(T) many singular values are positive, and the
  rest are zero.

## Implementation notes

Suppose `T : E →ₗ[𝕜] F` where `dim(E) = n`, `dim(F) = m`.
In mathematical literature, the number of singular values varies, with popular choices including
- `rank(T)` singular values, all of which are positive.
- `min(n,m)` singular values, some of which might be zero.
- `n` singular values, some of which might be zero. This is the approach taken in [axler2024].
- Countably infinitely many singular values, with all but finitely many of them being zero.

We take the last approach for the following reasons:
- It avoid unnecessary dependent typing.
- You can easily convert this definition to the other three by composing with `Fin.val`, but
  converting between any two of the other definitions is more inconvenient because it involves
  multiple `Fin` types.
- If you prefer a definition where there are `k` singular values, you can treat the singular values
  after `k` as junk values.
  Not having to prove that `i < k` when getting the `i`th singular value has similar advantages to
  not having to prove that `y ≠ 0` when calculating `x / y`.
- This API coincides with a potential future API for approximation numbers, which are a
  generalization of singular values to continuous linear maps between possibly-infinite-dimensional
  normed vector spaces.

## TODO

- Generalize singular values to the approximation numbers for maps between
  possibly-infinite-dimensional normed vector spaces.
  This will likely have a similar type signature to the current singular values definition, except
  it will take in a `ContinuousLinearMap` and will not be finitely supported.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2024]

## Tags

singular values
-/

public section

open Module InnerProductSpace

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E ->ₗ[𝕜] F)

/--
Definition of `singularValues` / `singularValues` 的定义

English:
definition singularValues
  signature: : Nat ->₀ Real
  body: Finsupp.embDomain Fin.valEmbedding
    Finsupp.ofSupportFinite
      (fun i => √(T.isSymmetric_adjoint_comp_self.eigenvalues rfl i))
      (Set.toFinite _)

中文:
定义 singularValues
  签名: : 自然数 ->₀ 实数
  定义体: Finsupp.embDomain Fin.valEmbedding
    Finsupp.ofSupportFinite
      (fun i => √(T.isSymmetric_adjoint_comp_self.eigenvalues rfl i))
      (Set.toFinite _)

Depends on / 依赖: Fin.valEmbedding, Finsupp, Finsupp.embDomain, Finsupp.ofSupportFinite, Set.toFinite, T.isSymmetric_adjoint_comp_self.eigenvalues, eigenvalues, embDomain, isSymmetric_adjoint_comp_self, ofSupportFinite, toFinite, valEmbedding
-/
noncomputable def singularValues : Nat ->₀ Real :=
Finsupp.embDomain Fin.valEmbedding
    Finsupp.ofSupportFinite
      (fun i => √(T.isSymmetric_adjoint_comp_self.eigenvalues rfl i))
      (Set.toFinite _)

/--
theorem `singularValues_nonneg` / 定理 `singularValues_nonneg`

English:
theorem singularValues_nonneg
  given: (i : Nat)
  statement: 0 <= T.singularValues i
  proof: by
  rw [singularValues]; rw [Finsupp.embDomain_apply]; rw [Finsupp.ofSupportFinite_coe]
  split_ifs <;> positivity

中文:
定理 singularValues_nonneg
  条件: (i : 自然数)
  结论: 0 <= T.singularValues i
  证明: by
  rw [singularValues]; rw [Finsupp.embDomain_apply]; rw [Finsupp.ofSupportFinite_coe]
  split_ifs <;> positivity

Depends on / 依赖: Finsupp, Finsupp.embDomain_apply, Finsupp.ofSupportFinite_coe, embDomain_apply, ofSupportFinite_coe, singularValues, split_ifs
-/
theorem singularValues_nonneg (i : Nat) : 0 <= T.singularValues i := by
  rw [singularValues]; rw [Finsupp.embDomain_apply]; rw [Finsupp.ofSupportFinite_coe]
  split_ifs <;> positivity

/--
theorem `singularValues_pos_iff_ne_zero` / 定理 `singularValues_pos_iff_ne_zero`

English:
theorem singularValues_pos_iff_ne_zero
  given: (i : Nat)
  proof: by
  grind [T.singularValues_nonneg i]

中文:
定理 singularValues_pos_iff_ne_zero
  条件: (i : 自然数)
  证明: by
  grind [T.singularValues_nonneg i]

Depends on / 依赖: T.singularValues_nonneg, singularValues_nonneg
-/
theorem singularValues_pos_iff_ne_zero (i : Nat) :
    0 < T.singularValues i ↔ T.singularValues i != 0 := by
  grind [T.singularValues_nonneg i]

/--
theorem `singularValues_fin` / 定理 `singularValues_fin`

English:
theorem singularValues_fin
  given: {n : Nat} (hn : finrank 𝕜 E = n) (i : Fin n)
  proof: by
  subst hn
  exact Finsupp.embDomain_apply_self _ _ i

中文:
定理 singularValues_fin
  条件: {n : 自然数} (hn : finrank 𝕜 E = n) (i : Fin n)
  证明: by
  subst hn
  exact Finsupp.embDomain_apply_self _ _ i

Depends on / 依赖: Finsupp, Finsupp.embDomain_apply_self, embDomain_apply_self
-/
theorem singularValues_fin {n : Nat} (hn : finrank 𝕜 E = n) (i : Fin n) :
    T.singularValues i = √(T.isSymmetric_adjoint_comp_self.eigenvalues hn i) := by
  subst hn
  exact Finsupp.embDomain_apply_self _ _ i

/--
theorem `singularValues_of_lt` / 定理 `singularValues_of_lt`

English:
theorem singularValues_of_lt
  given: {n : Nat} (hn : finrank 𝕜 E = n) {i : Nat} (hi : i < n)
  proof: T.singularValues_fin hn ⟨i, hi⟩

中文:
定理 singularValues_of_lt
  条件: {n : 自然数} (hn : finrank 𝕜 E = n) {i : 自然数} (hi : i < n)
  证明: T.singularValues_fin hn ⟨i, hi⟩

Depends on / 依赖: T.singularValues_fin, singularValues_fin
-/
theorem singularValues_of_lt {n : Nat} (hn : finrank 𝕜 E = n) {i : Nat} (hi : i < n) :
    T.singularValues i = √(T.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨i, hi⟩) :=
  T.singularValues_fin hn ⟨i, hi⟩

/--
theorem `singularValues_of_finrank_le` / 定理 `singularValues_of_finrank_le`

English:
theorem singularValues_of_finrank_le
  given: {i : Nat} (hi : finrank 𝕜 E <= i)
  statement: T.singularValues i = 0
  proof: by
  apply Finsupp.embDomain_of_notMem_range
  simp [hi]

中文:
定理 singularValues_of_finrank_le
  条件: {i : 自然数} (hi : finrank 𝕜 E <= i)
  结论: T.singularValues i = 0
  证明: by
  apply Finsupp.embDomain_of_notMem_range
  simp [hi]

Depends on / 依赖: Finsupp, Finsupp.embDomain_of_notMem_range, embDomain_of_notMem_range
-/
theorem singularValues_of_finrank_le {i : Nat} (hi : finrank 𝕜 E <= i) : T.singularValues i = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  simp [hi]

/--
theorem `sq_singularValues_fin` / 定理 `sq_singularValues_fin`

English:
theorem sq_singularValues_fin
  given: {n : Nat} (hn : finrank 𝕜 E = n) (i : Fin n)
  proof: by
  simp [T.singularValues_fin hn, T.isPositive_adjoint_comp_self.nonneg_eigenvalues hn i]

中文:
定理 sq_singularValues_fin
  条件: {n : 自然数} (hn : finrank 𝕜 E = n) (i : Fin n)
  证明: by
  simp [T.singularValues_fin hn, T.isPositive_adjoint_comp_self.nonneg_eigenvalues hn i]

Depends on / 依赖: T.isPositive_adjoint_comp_self.nonneg_eigenvalues, T.singularValues_fin, isPositive_adjoint_comp_self, nonneg_eigenvalues, singularValues_fin
-/
theorem sq_singularValues_fin {n : Nat} (hn : finrank 𝕜 E = n) (i : Fin n) :
    T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn i := by
  simp [T.singularValues_fin hn, T.isPositive_adjoint_comp_self.nonneg_eigenvalues hn i]

/--
theorem `sq_singularValues_of_lt` / 定理 `sq_singularValues_of_lt`

English:
theorem sq_singularValues_of_lt
  given: {n : Nat} (hn : finrank 𝕜 E = n) {i : Nat} (hi : i < n)
  proof: T.sq_singularValues_fin hn ⟨i, hi⟩

中文:
定理 sq_singularValues_of_lt
  条件: {n : 自然数} (hn : finrank 𝕜 E = n) {i : 自然数} (hi : i < n)
  证明: T.sq_singularValues_fin hn ⟨i, hi⟩

Depends on / 依赖: T.sq_singularValues_fin, sq_singularValues_fin
-/
theorem sq_singularValues_of_lt {n : Nat} (hn : finrank 𝕜 E = n) {i : Nat} (hi : i < n) :
    T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨i, hi⟩ :=
  T.sq_singularValues_fin hn ⟨i, hi⟩

/--
theorem `hasEigenvalue_adjoint_comp_self_sq_singularValues` / 定理 `hasEigenvalue_adjoint_comp_self_sq_singularValues`

English:
theorem hasEigenvalue_adjoint_comp_self_sq_singularValues
  given: {n : Nat} (hn : n < finrank 𝕜 E)
  proof: by
  convert! T.isSymmetric_adjoint_comp_self.hasEigenvalue_eigenvalues rfl ⟨n, hn⟩ using 1
  simp [← T.sq_singularValues_fin]

中文:
定理 hasEigenvalue_adjoint_comp_self_sq_singularValues
  条件: {n : 自然数} (hn : n < finrank 𝕜 E)
  证明: by
  convert! T.isSymmetric_adjoint_comp_self.hasEigenvalue_eigenvalues rfl ⟨n, hn⟩ using 1
  simp [← T.sq_singularValues_fin]

Depends on / 依赖: T.isSymmetric_adjoint_comp_self.hasEigenvalue_eigenvalues, T.sq_singularValues_fin, convert, hasEigenvalue_eigenvalues, isSymmetric_adjoint_comp_self, sq_singularValues_fin
-/
theorem hasEigenvalue_adjoint_comp_self_sq_singularValues {n : Nat} (hn : n < finrank 𝕜 E) :
    End.HasEigenvalue (adjoint T ∘ₗ T) (T.singularValues n ^ 2) := by
  convert! T.isSymmetric_adjoint_comp_self.hasEigenvalue_eigenvalues rfl ⟨n, hn⟩ using 1
  simp [← T.sq_singularValues_fin]

/--
theorem `singularValues_antitone` / 定理 `singularValues_antitone`

English:
theorem singularValues_antitone
  statement: Antitone T.singularValues
  proof: by
  intro i j hij
  by_cases! hj : finrank 𝕜 E <= j
  · simpa [T.singularValues_of_finrank_le hj] using T.singularValues_nonneg i
  have : (T.singularValues j : Real) ^ 2 <= (T.singularValues i : Real) ^ 2 := by
    rw [T.sq_singularValues_fin rfl ⟨j]; rw [hj⟩]; rw [T.sq_singularValues_fin rfl ⟨i];

中文:
定理 singularValues_antitone
  结论: Antitone T.singularValues
  证明: by
  intro i j hij
  by_cases! hj : finrank 𝕜 E <= j
  · simpa [T.singularValues_of_finrank_le hj] using T.singularValues_nonneg i
  have : (T.singularValues j : Real) ^ 2 <= (T.singularValues i : Real) ^ 2 := by
    rw [T.sq_singularValues_fin rfl ⟨j]; rw [hj⟩]; rw [T.sq_singularValues_fin rfl ⟨i];

Depends on / 依赖: T.isSymmetric_adjoint_comp_self.eigenvalues_antitone, T.singularValues, T.singularValues_nonneg, T.singularValues_of_finrank_le, T.sq_singularValues_fin, eigenvalues_antitone, finrank, hij.trans_lt, isSymmetric_adjoint_comp_self, le_of_sq_le_sq, singularValues, singularValues_nonneg, singularValues_of_finrank_le, sq_singularValues_fin, trans_lt
-/
theorem singularValues_antitone : Antitone T.singularValues := by
  intro i j hij
  by_cases! hj : finrank 𝕜 E <= j
  · simpa [T.singularValues_of_finrank_le hj] using T.singularValues_nonneg i
  have : (T.singularValues j : Real) ^ 2 <= (T.singularValues i : Real) ^ 2 := by
    rw [T.sq_singularValues_fin rfl ⟨j]; rw [hj⟩]; rw [T.sq_singularValues_fin rfl ⟨i]; rw [hij.trans_lt hj⟩]
    exact T.isSymmetric_adjoint_comp_self.eigenvalues_antitone rfl hij
  exact le_of_sq_le_sq this (T.singularValues_nonneg i)

/--
theorem `injective_iff_forall_lt_finrank_singularValues_pos` / 定理 `injective_iff_forall_lt_finrank_singularValues_pos`

English:
theorem injective_iff_forall_lt_finrank_singularValues_pos
  proof: by
  have := (adjoint T ∘ₗ T).not_hasEigenvalue_zero_tfae.out 4 0
  rw [← adjoint_comp_self_injective_iff]; rw [← coe_comp]; rw [← ker_eq_bot]; rw [← not_iff_not]; rw [this.not_left]
  push Not
  constructor
  · intro h
    obtain ⟨i, hi⟩ := T.isSymmetric_adjoint_comp_self.exists_eigenvalues_eq rfl 

中文:
定理 injective_iff_forall_lt_finrank_singularValues_pos
  证明: by
  have := (adjoint T ∘ₗ T).not_hasEigenvalue_zero_tfae.out 4 0
  rw [← adjoint_comp_self_injective_iff]; rw [← coe_comp]; rw [← ker_eq_bot]; rw [← not_iff_not]; rw [this.not_left]
  push Not
  constructor
  · intro h
    obtain ⟨i, hi⟩ := T.isSymmetric_adjoint_comp_self.exists_eigenvalues_eq rfl 

Depends on / 依赖: RCLike, RCLike.ofReal_eq_zero.mp, T.isSymmetric_adjoint_comp_self.exists_eigenvalues_eq, T.isSymmetric_adjoint_comp_self.hasEigenvalue_eigenvalues, T.singularValues_fin, adjoint, adjoint_comp_self_injective_iff, coe_comp, convert, exists_eigenvalues_eq, hasEigenvalue_eigenvalues, i.isLt, isSymmetric_adjoint_comp_self, ker_eq_bot, le_a, not_hasEigenvalue_zero_tfae, not_hasEigenvalue_zero_tfae.out, not_iff_not, not_left, ofReal_eq_zero
-/
theorem injective_iff_forall_lt_finrank_singularValues_pos :
    Function.Injective T ↔ forall i < finrank 𝕜 E, 0 < T.singularValues i := by
  have := (adjoint T ∘ₗ T).not_hasEigenvalue_zero_tfae.out 4 0
  rw [← adjoint_comp_self_injective_iff]; rw [← coe_comp]; rw [← ker_eq_bot]; rw [← not_iff_not]; rw [this.not_left]
  push Not
  constructor
  · intro h
    obtain ⟨i, hi⟩ := T.isSymmetric_adjoint_comp_self.exists_eigenvalues_eq rfl h
    use i, i.isLt
    simp [RCLike.ofReal_eq_zero.mp hi, T.singularValues_fin rfl]
  · intro ⟨i, h, hz⟩
    convert! T.isSymmetric_adjoint_comp_self.hasEigenvalue_eigenvalues rfl ⟨i, h⟩
    rw [← sq_singularValues_of_lt]; rw [le_antisymm hz (T.singularValues_nonneg i)]
    simp

/--
theorem `card_support_singularValues` / 定理 `card_support_singularValues`

English:
theorem card_support_singularValues
  statement: T.singularValues.support.card = finrank 𝕜 T.range
  proof: by
  have hS : forall m in T.singularValues.support, m < finrank 𝕜 E := by
    grind [singularValues_of_finrank_le]
  have hT := T.isSymmetric_adjoint_comp_self
  have : T.singularValues.support.attachFin hS = ({i | hT.eigenvalues rfl i = (0 : 𝕜)} : Finset _)ᶜ
    := by ext i; simp [T.singularValues

中文:
定理 card_support_singularValues
  结论: T.singularValues.support.card = finrank 𝕜 T.range
  证明: by
  have hS : forall m in T.singularValues.support, m < finrank 𝕜 E := by
    grind [singularValues_of_finrank_le]
  have hT := T.isSymmetric_adjoint_comp_self
  have : T.singularValues.support.attachFin hS = ({i | hT.eigenvalues rfl i = (0 : 𝕜)} : Finset _)ᶜ
    := by ext i; simp [T.singularValues

Depends on / 依赖: Finset, Finset.card_compl, Fintype, Fintype.card_fin, T.isPositive_adjoint_comp_self.nonneg_eigenvalues, T.isSymmetric_adjoint_comp_self, T.singularValues.support, T.singularValues.support.attachFin, T.singularValues.support.card_attachFin, T.singularValues_fin, attachFin, card_attachFin, card_compl, card_filter_eigenvalues_eq, card_fin, eigenvalues, finrank, hT.card_filter_eigenvalues_eq, hT.eigenvalues, isPositive_adjoint_comp_self
-/
theorem card_support_singularValues : T.singularValues.support.card = finrank 𝕜 T.range := by
  have hS : forall m in T.singularValues.support, m < finrank 𝕜 E := by
    grind [singularValues_of_finrank_le]
  have hT := T.isSymmetric_adjoint_comp_self
  have : T.singularValues.support.attachFin hS = ({i | hT.eigenvalues rfl i = (0 : 𝕜)} : Finset _)ᶜ
    := by ext i; simp [T.singularValues_fin, T.isPositive_adjoint_comp_self.nonneg_eigenvalues]
  rw [← T.singularValues.support.card_attachFin hS]; rw [this]; rw [Finset.card_compl]; rw [Fintype.card_fin]; rw [hT.card_filter_eigenvalues_eq rfl 0]; rw [Module.End.eigenspace_zero]; rw [← (T.adjoint ∘ₗ T).finrank_range_add_finrank_ker]; rw [add_tsub_cancel_right]; rw [T.range_adjoint_comp_self]; rw [finrank_range_adjoint]

/--
theorem `isLowerSet_support_singularValues` / 定理 `isLowerSet_support_singularValues`

English:
theorem isLowerSet_support_singularValues
  statement: IsLowerSet (T.singularValues.support : Set Nat)
  proof: by
  intro a b hl ha
  rw [Finset.mem_coe]; rw [Finsupp.mem_support_iff]; rw [← singularValues_pos_iff_ne_zero] at ⊢ ha
  order [T.singularValues_antitone hl]

@[simp]

中文:
定理 isLowerSet_support_singularValues
  结论: IsLowerSet (T.singularValues.support : Set 自然数)
  证明: by
  intro a b hl ha
  rw [Finset.mem_coe]; rw [Finsupp.mem_support_iff]; rw [← singularValues_pos_iff_ne_zero] at ⊢ ha
  order [T.singularValues_antitone hl]

@[simp]

Depends on / 依赖: Finset, Finset.mem_coe, Finsupp, Finsupp.mem_support_iff, T.singularValues_antitone, mem_coe, mem_support_iff, singularValues_antitone, singularValues_pos_iff_ne_zero
-/
theorem isLowerSet_support_singularValues : IsLowerSet (T.singularValues.support : Set Nat) := by
  intro a b hl ha
  rw [Finset.mem_coe]; rw [Finsupp.mem_support_iff]; rw [← singularValues_pos_iff_ne_zero] at ⊢ ha
  order [T.singularValues_antitone hl]

@[simp]
/--
theorem `support_singularValues` / 定理 `support_singularValues`

English:
theorem support_singularValues
  statement: T.singularValues.support = Finset.range (finrank 𝕜 T.range)
  proof: by
  obtain ⟨n, hn⟩ := T.isLowerSet_support_singularValues.eq_univ_or_Iio.resolve_left
    (fun h => Set.infinite_univ.not_finite (h ▸ Finset.finite_toSet _))
  rw [← Finset.coe_Iio]; rw [Finset.coe_inj]; rw [Nat.Iio_eq_range] at hn
  simp [← card_support_singularValues, hn]

中文:
定理 support_singularValues
  结论: T.singularValues.support = Finset.range (finrank 𝕜 T.range)
  证明: by
  obtain ⟨n, hn⟩ := T.isLowerSet_support_singularValues.eq_univ_or_Iio.resolve_left
    (fun h => Set.infinite_univ.not_finite (h ▸ Finset.finite_toSet _))
  rw [← Finset.coe_Iio]; rw [Finset.coe_inj]; rw [Nat.Iio_eq_range] at hn
  simp [← card_support_singularValues, hn]

Depends on / 依赖: Finset, Finset.coe_Iio, Finset.coe_inj, Finset.finite_toSet, Iio_eq_range, Nat.Iio_eq_range, Set.infinite_univ.not_finite, T.isLowerSet_support_singularValues.eq_univ_or_Iio.resolve_left, card_support_singularValues, coe_Iio, coe_inj, eq_univ_or_Iio, finite_toSet, infinite_univ, isLowerSet_support_singularValues, not_finite, resolve_left
-/
theorem support_singularValues : T.singularValues.support = Finset.range (finrank 𝕜 T.range) := by
  obtain ⟨n, hn⟩ := T.isLowerSet_support_singularValues.eq_univ_or_Iio.resolve_left
    (fun h => Set.infinite_univ.not_finite (h ▸ Finset.finite_toSet _))
  rw [← Finset.coe_Iio]; rw [Finset.coe_inj]; rw [Nat.Iio_eq_range] at hn
  simp [← card_support_singularValues, hn]

/--
theorem `singularValues_pos_iff_lt_finrank_range` / 定理 `singularValues_pos_iff_lt_finrank_range`

English:
theorem singularValues_pos_iff_lt_finrank_range
  given: {n : Nat}
  proof: by
  rw [singularValues_pos_iff_ne_zero]; rw [← Finsupp.mem_support_iff]; rw [support_singularValues]; rw [Finset.mem_range]

中文:
定理 singularValues_pos_iff_lt_finrank_range
  条件: {n : 自然数}
  证明: by
  rw [singularValues_pos_iff_ne_zero]; rw [← Finsupp.mem_support_iff]; rw [support_singularValues]; rw [Finset.mem_range]

Depends on / 依赖: Finset, Finset.mem_range, Finsupp, Finsupp.mem_support_iff, mem_range, mem_support_iff, singularValues_pos_iff_ne_zero, support_singularValues
-/
theorem singularValues_pos_iff_lt_finrank_range {n : Nat} :
    0 < T.singularValues n ↔ n < finrank 𝕜 T.range := by
  rw [singularValues_pos_iff_ne_zero]; rw [← Finsupp.mem_support_iff]; rw [support_singularValues]; rw [Finset.mem_range]

/--
theorem `singularValues_finrank_range_self` / 定理 `singularValues_finrank_range_self`

English:
theorem singularValues_finrank_range_self
  statement: T.singularValues (finrank 𝕜 T.range) = 0
  proof: by
  rw [← Finsupp.notMem_support_iff]; rw [support_singularValues]
  exact Finset.notMem_range_self

中文:
定理 singularValues_finrank_range_self
  结论: T.singularValues (finrank 𝕜 T.range) = 0
  证明: by
  rw [← Finsupp.notMem_support_iff]; rw [support_singularValues]
  exact Finset.notMem_range_self

Depends on / 依赖: Finset, Finset.notMem_range_self, Finsupp, Finsupp.notMem_support_iff, notMem_range_self, notMem_support_iff, support_singularValues
-/
theorem singularValues_finrank_range_self : T.singularValues (finrank 𝕜 T.range) = 0 := by
  rw [← Finsupp.notMem_support_iff]; rw [support_singularValues]
  exact Finset.notMem_range_self

/--
theorem `singularValues_eq_zero_iff_le_finrank_range` / 定理 `singularValues_eq_zero_iff_le_finrank_range`

English:
theorem singularValues_eq_zero_iff_le_finrank_range
  given: {n : Nat}
  proof: by
  rw [← Finsupp.notMem_support_iff]; rw [support_singularValues]; rw [Finset.mem_range]; rw [not_lt]

@[simp]

中文:
定理 singularValues_eq_zero_iff_le_finrank_range
  条件: {n : 自然数}
  证明: by
  rw [← Finsupp.notMem_support_iff]; rw [support_singularValues]; rw [Finset.mem_range]; rw [not_lt]

@[simp]

Depends on / 依赖: Finset, Finset.mem_range, Finsupp, Finsupp.notMem_support_iff, mem_range, notMem_support_iff, not_lt, support_singularValues
-/
theorem singularValues_eq_zero_iff_le_finrank_range {n : Nat} :
    T.singularValues n = 0 ↔ finrank 𝕜 T.range <= n := by
  rw [← Finsupp.notMem_support_iff]; rw [support_singularValues]; rw [Finset.mem_range]; rw [not_lt]

@[simp]
/--
theorem `singularValues_zero` / 定理 `singularValues_zero`

English:
theorem singularValues_zero
  statement: (0 : E ->ₗ[𝕜] F).singularValues = 0
  proof: by
  ext1 i
  rw [Finsupp.zero_apply]; rw [singularValues_eq_zero_iff_le_finrank_range]; rw [range_zero]
  simp

@[simp]

中文:
定理 singularValues_zero
  结论: (0 : E ->ₗ[𝕜] F).singularValues = 0
  证明: by
  ext1 i
  rw [Finsupp.zero_apply]; rw [singularValues_eq_zero_iff_le_finrank_range]; rw [range_zero]
  simp

@[simp]

Depends on / 依赖: Finsupp, Finsupp.zero_apply, range_zero, singularValues_eq_zero_iff_le_finrank_range, zero_apply
-/
theorem singularValues_zero : (0 : E ->ₗ[𝕜] F).singularValues = 0 := by
  ext1 i
  rw [Finsupp.zero_apply]; rw [singularValues_eq_zero_iff_le_finrank_range]; rw [range_zero]
  simp

@[simp]
/--
theorem `singularValues_eq_zero_iff` / 定理 `singularValues_eq_zero_iff`

English:
theorem singularValues_eq_zero_iff
  statement: T.singularValues = 0 ↔ T = 0
  proof: by
  constructor <;> intro h
  · rw [← range_eq_bot, ← Submodule.finrank_eq_zero, ← Nat.le_zero,
      ← singularValues_eq_zero_iff_le_finrank_range, h, Finsupp.zero_apply]
  · exact h ▸ singularValues_zero

中文:
定理 singularValues_eq_zero_iff
  结论: T.singularValues = 0 ↔ T = 0
  证明: by
  constructor <;> intro h
  · rw [← range_eq_bot, ← Submodule.finrank_eq_zero, ← Nat.le_zero,
      ← singularValues_eq_zero_iff_le_finrank_range, h, Finsupp.zero_apply]
  · exact h ▸ singularValues_zero

Depends on / 依赖: Finsupp, Finsupp.zero_apply, Nat.le_zero, Submodule, Submodule.finrank_eq_zero, finrank_eq_zero, le_zero, range_eq_bot, singularValues_eq_zero_iff_le_finrank_range, singularValues_zero, zero_apply
-/
theorem singularValues_eq_zero_iff : T.singularValues = 0 ↔ T = 0 := by
  constructor <;> intro h
  · rw [← range_eq_bot, ← Submodule.finrank_eq_zero, ← Nat.le_zero,
      ← singularValues_eq_zero_iff_le_finrank_range, h, Finsupp.zero_apply]
  · exact h ▸ singularValues_zero

end LinearMap
