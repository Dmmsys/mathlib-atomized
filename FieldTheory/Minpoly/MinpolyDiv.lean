/-
Copyright (c) 2023 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# Results about `minpoly R x / (X - C x)`

## Main definition
- `minpolyDiv`: The polynomial `minpoly R x / (X - C x)`.

We used the contents of this file to describe the dual basis of a power basis under the trace form.
See `traceForm_dualBasis_powerBasis_eq`.

## Main results
- `span_coeff_minpolyDiv`: The coefficients of `minpolyDiv` span `R<x>`.
-/

@[expose] public section

open Polynomial Module Algebra

variable (R K) {L S} [CommRing R] [Field K] [Field L] [CommRing S] [Algebra R S] [Algebra K L]
variable (x : S)

/--
Definition of `minpolyDiv` / `minpolyDiv` 的定义

English:
definition minpolyDiv
  signature: : S[X]
  body: (minpoly R x).map (algebraMap R S) /ₘ (X - C x)

中文:
定义 minpolyDiv
  签名: : S[X]
  定义体: (minpoly R x).map (algebraMap R S) /ₘ (X - C x)

Depends on / 依赖: algebraMap, minpoly
-/
noncomputable def minpolyDiv : S[X] := (minpoly R x).map (algebraMap R S) /ₘ (X - C x)

/--
lemma `minpolyDiv_spec` / 引理 `minpolyDiv_spec`

English:
lemma minpolyDiv_spec
  proof: by
  delta minpolyDiv
  rw [mul_comm]; rw [mul_divByMonic_eq_iff_isRoot]; rw [IsRoot]; rw [eval_map_algebraMap]; rw [minpoly.aeval]

中文:
引理 minpolyDiv_spec
  证明: by
  delta minpolyDiv
  rw [mul_comm]; rw [mul_divByMonic_eq_iff_isRoot]; rw [IsRoot]; rw [eval_map_algebraMap]; rw [minpoly.aeval]

Depends on / 依赖: IsRoot, eval_map_algebraMap, minpoly, minpoly.aeval, minpolyDiv, mul_comm, mul_divByMonic_eq_iff_isRoot
-/
lemma minpolyDiv_spec :
    minpolyDiv R x * (X - C x) = (minpoly R x).map (algebraMap R S) := by
  delta minpolyDiv
  rw [mul_comm]; rw [mul_divByMonic_eq_iff_isRoot]; rw [IsRoot]; rw [eval_map_algebraMap]; rw [minpoly.aeval]

/--
lemma `coeff_minpolyDiv` / 引理 `coeff_minpolyDiv`

English:
lemma coeff_minpolyDiv
  given: (i)
  statement: coeff (minpolyDiv R x) i =
  proof: by
  rw [← coeff_map]; rw [← minpolyDiv_spec R x]; simp [mul_sub]

中文:
引理 coeff_minpolyDiv
  条件: (i)
  结论: coeff (minpolyDiv R x) i =
  证明: by
  rw [← coeff_map]; rw [← minpolyDiv_spec R x]; simp [mul_sub]

Depends on / 依赖: coeff_map, minpolyDiv_spec, mul_sub
-/
lemma coeff_minpolyDiv (i) : coeff (minpolyDiv R x) i =
    algebraMap R S (coeff (minpoly R x) (i + 1)) + coeff (minpolyDiv R x) (i + 1) * x := by
  rw [← coeff_map]; rw [← minpolyDiv_spec R x]; simp [mul_sub]

variable {R x}

/--
lemma `minpolyDiv_eq_zero` / 引理 `minpolyDiv_eq_zero`

English:
lemma minpolyDiv_eq_zero
  given: (hx : ¬IsIntegral R x)
  statement: minpolyDiv R x = 0
  proof: by
  delta minpolyDiv minpoly
  rw [dif_neg hx]; rw [Polynomial.map_zero]; rw [zero_divByMonic]

中文:
引理 minpolyDiv_eq_zero
  条件: (hx : ¬是整 R x)
  结论: minpolyDiv R x = 0
  证明: by
  delta minpolyDiv minpoly
  rw [dif_neg hx]; rw [Polynomial.map_zero]; rw [zero_divByMonic]

Depends on / 依赖: Polynomial, Polynomial.map_zero, dif_neg, map_zero, minpoly, minpolyDiv, zero_divByMonic
-/
lemma minpolyDiv_eq_zero (hx : ¬IsIntegral R x) : minpolyDiv R x = 0 := by
  delta minpolyDiv minpoly
  rw [dif_neg hx]; rw [Polynomial.map_zero]; rw [zero_divByMonic]

/--
lemma `eval_minpolyDiv_self` / 引理 `eval_minpolyDiv_self`

English:
lemma eval_minpolyDiv_self
  statement: (minpolyDiv R x).eval x = aeval x (derivative <| minpoly R x)
  proof: by
  rw [← eval_map_algebraMap]; rw [← derivative_map]; rw [← minpolyDiv_spec R x]; simp

中文:
引理 eval_minpolyDiv_self
  结论: (minpolyDiv R x).eval x = aeval x (derivative <| minpoly R x)
  证明: by
  rw [← eval_map_algebraMap]; rw [← derivative_map]; rw [← minpolyDiv_spec R x]; simp

Depends on / 依赖: derivative_map, eval_map_algebraMap, minpolyDiv_spec
-/
lemma eval_minpolyDiv_self : (minpolyDiv R x).eval x = aeval x (derivative <| minpoly R x) := by
  rw [← eval_map_algebraMap]; rw [← derivative_map]; rw [← minpolyDiv_spec R x]; simp

/--
lemma `minpolyDiv_eval_eq_zero_of_ne_of_aeval_eq_zero` / 引理 `minpolyDiv_eval_eq_zero_of_ne_of_aeval_eq_zero`

English:
lemma minpolyDiv_eval_eq_zero_of_ne_of_aeval_eq_zero
  statement: [IsDomain S]
  proof: by
  rw [← eval_map_algebraMap]; rw [← minpolyDiv_spec R x] at hy
  simp only [eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero] at hy
  exact hy.resolve_right (by rwa [sub_eq_zero])

中文:
引理 minpolyDiv_eval_eq_zero_of_ne_of_aeval_eq_zero
  结论: [是整环 S]
  证明: by
  rw [← eval_map_algebraMap]; rw [← minpolyDiv_spec R x] at hy
  simp only [eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero] at hy
  exact hy.resolve_right (by rwa [sub_eq_zero])

Depends on / 依赖: eval_C, eval_X, eval_map_algebraMap, eval_mul, eval_sub, hy.resolve_right, minpolyDiv_spec, mul_eq_zero, resolve_right, sub_eq_zero
-/
lemma minpolyDiv_eval_eq_zero_of_ne_of_aeval_eq_zero [IsDomain S]
    {y} (hxy : y != x) (hy : aeval y (minpoly R x) = 0) : (minpolyDiv R x).eval y = 0 := by
  rw [← eval_map_algebraMap]; rw [← minpolyDiv_spec R x] at hy
  simp only [eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero] at hy
  exact hy.resolve_right (by rwa [sub_eq_zero])

/--
lemma `eval₂_minpolyDiv_of_eval₂_eq_zero` / 引理 `eval₂_minpolyDiv_of_eval₂_eq_zero`

English:
lemma eval₂_minpolyDiv_of_eval₂_eq_zero
  statement: {T} [CommRing T]
  proof: by
  split_ifs with h
  · rw [← h, eval₂_hom, eval_minpolyDiv_self]
  · rw [← eval₂_map, ← minpolyDiv_spec] at hy
    simpa [sub_eq_zero, Ne.symm h] using hy

中文:
引理 eval₂_minpolyDiv_of_eval₂_eq_zero
  结论: {T} [交换环 T]
  证明: by
  split_ifs with h
  · rw [← h, eval₂_hom, eval_minpolyDiv_self]
  · rw [← eval₂_map, ← minpolyDiv_spec] at hy
    simpa [sub_eq_zero, Ne.symm h] using hy

Depends on / 依赖: Ne.symm, eval_minpolyDiv_self, minpolyDiv_spec, split_ifs, sub_eq_zero
-/
lemma eval₂_minpolyDiv_of_eval₂_eq_zero {T} [CommRing T]
    [IsDomain T] [DecidableEq T] {x y}
    (σ : S ->+* T) (hy : eval₂ (σ.comp (algebraMap R S)) y (minpoly R x) = 0) :
    eval₂ σ y (minpolyDiv R x) =
      if σ x = y then σ (aeval x (derivative <| minpoly R x)) else 0 := by
  split_ifs with h
  · rw [← h, eval₂_hom, eval_minpolyDiv_self]
  · rw [← eval₂_map, ← minpolyDiv_spec] at hy
    simpa [sub_eq_zero, Ne.symm h] using hy

/--
lemma `eval₂_minpolyDiv_self` / 引理 `eval₂_minpolyDiv_self`

English:
lemma eval₂_minpolyDiv_self
  statement: {T} [CommRing T] [Algebra R T] [IsDomain T] [DecidableEq T] (x : S)
  proof: by
  apply eval₂_minpolyDiv_of_eval₂_eq_zero
  rw [AlgHom.comp_algebraMap]; rw [← σ₂.comp_algebraMap]; rw [← eval₂_map]; rw [← RingHom.coe_coe]; rw [eval₂_hom]; rw [eval_map_algebraMap]; rw [minpoly.aeval]; rw [map_zero]

中文:
引理 eval₂_minpolyDiv_self
  结论: {T} [交换环 T] [代数 R T] [是整环 T] [DecidableEq T] (x : S)
  证明: by
  apply eval₂_minpolyDiv_of_eval₂_eq_zero
  rw [AlgHom.comp_algebraMap]; rw [← σ₂.comp_algebraMap]; rw [← eval₂_map]; rw [← RingHom.coe_coe]; rw [eval₂_hom]; rw [eval_map_algebraMap]; rw [minpoly.aeval]; rw [map_zero]

Depends on / 依赖: AlgHom, AlgHom.comp_algebraMap, RingHom, RingHom.coe_coe, coe_coe, comp_algebraMap, eval_map_algebraMap, map_zero, minpoly, minpoly.aeval
-/
lemma eval₂_minpolyDiv_self {T} [CommRing T] [Algebra R T] [IsDomain T] [DecidableEq T] (x : S)
    (σ₁ σ₂ : S ->ₐ[R] T) :
    eval₂ σ₁ (σ₂ x) (minpolyDiv R x) =
      if σ₁ x = σ₂ x then σ₁ (aeval x (derivative <| minpoly R x)) else 0 := by
  apply eval₂_minpolyDiv_of_eval₂_eq_zero
  rw [AlgHom.comp_algebraMap]; rw [← σ₂.comp_algebraMap]; rw [← eval₂_map]; rw [← RingHom.coe_coe]; rw [eval₂_hom]; rw [eval_map_algebraMap]; rw [minpoly.aeval]; rw [map_zero]

/--
lemma `eval_minpolyDiv_of_aeval_eq_zero` / 引理 `eval_minpolyDiv_of_aeval_eq_zero`

English:
lemma eval_minpolyDiv_of_aeval_eq_zero
  statement: [IsDomain S] [DecidableEq S]
  proof: by
  rw [eval]; rw [eval₂_minpolyDiv_of_eval₂_eq_zero]; rw [RingHom.id_apply]; rw [RingHom.id_apply]
  simpa [aeval_def] using hy

中文:
引理 eval_minpolyDiv_of_aeval_eq_zero
  结论: [是整环 S] [DecidableEq S]
  证明: by
  rw [eval]; rw [eval₂_minpolyDiv_of_eval₂_eq_zero]; rw [RingHom.id_apply]; rw [RingHom.id_apply]
  simpa [aeval_def] using hy

Depends on / 依赖: RingHom, RingHom.id_apply, aeval_def, id_apply
-/
lemma eval_minpolyDiv_of_aeval_eq_zero [IsDomain S] [DecidableEq S]
    {y} (hy : aeval y (minpoly R x) = 0) :
    (minpolyDiv R x).eval y = if x = y then aeval x (derivative <| minpoly R x) else 0 := by
  rw [eval]; rw [eval₂_minpolyDiv_of_eval₂_eq_zero]; rw [RingHom.id_apply]; rw [RingHom.id_apply]
  simpa [aeval_def] using hy


/--
lemma `coeff_minpolyDiv_mem_adjoin` / 引理 `coeff_minpolyDiv_mem_adjoin`

English:
lemma coeff_minpolyDiv_mem_adjoin
  given: (x : S) (i)
  proof: by
  by_contra H
  have : forall j, coeff (minpolyDiv R x) (i + j) ∉ R[x] := by
    intro j; induction j with
    | zero => exact H
    | succ j IH =>
      intro H; apply IH
      rw [coeff_minpolyDiv]
      refine add_mem ?_ (mul_mem H (self_mem_adjoin_singleton R x))
      exact Subalgebra.algebr

中文:
引理 coeff_minpolyDiv_mem_adjoin
  条件: (x : S) (i)
  证明: by
  by_contra H
  have : forall j, coeff (minpolyDiv R x) (i + j) ∉ R[x] := by
    intro j; induction j with
    | zero => exact H
    | succ j IH =>
      intro H; apply IH
      rw [coeff_minpolyDiv]
      refine add_mem ?_ (mul_mem H (self_mem_adjoin_singleton R x))
      exact Subalgebra.algebr

Depends on / 依赖: Subalgebra, Subalgebra.algebraMap_mem, add_mem, algebraMap_mem, coeff_eq_zero_of_natDegree_lt, coeff_minpolyDiv, minpolyDiv, mul_mem, natDegree, self_mem_adjoin_singleton, zero_mem
-/
lemma coeff_minpolyDiv_mem_adjoin (x : S) (i) :
    coeff (minpolyDiv R x) i in R[x] := by
  by_contra H
  have : forall j, coeff (minpolyDiv R x) (i + j) ∉ R[x] := by
    intro j; induction j with
    | zero => exact H
    | succ j IH =>
      intro H; apply IH
      rw [coeff_minpolyDiv]
      refine add_mem ?_ (mul_mem H (self_mem_adjoin_singleton R x))
      exact Subalgebra.algebraMap_mem _ _
  apply this (natDegree (minpolyDiv R x) + 1)
  rw [coeff_eq_zero_of_natDegree_lt]
  · exact zero_mem _
  · lia

section IsIntegral
variable (hx : IsIntegral R x)
include hx

/--
lemma `minpolyDiv_ne_zero` / 引理 `minpolyDiv_ne_zero`

English:
lemma minpolyDiv_ne_zero
  given: [Nontrivial S]
  statement: minpolyDiv R x != 0
  proof: by
  intro e
  have := minpolyDiv_spec R x
  rw [e]; rw [zero_mul] at this
  exact ((minpoly.monic hx).map (algebraMap R S)).ne_zero this.symm

中文:
引理 minpolyDiv_ne_zero
  条件: [非平凡 S]
  结论: minpolyDiv R x != 0
  证明: by
  intro e
  have := minpolyDiv_spec R x
  rw [e]; rw [zero_mul] at this
  exact ((minpoly.monic hx).map (algebraMap R S)).ne_zero this.symm

Depends on / 依赖: algebraMap, minpoly, minpoly.monic, minpolyDiv_spec, ne_zero, this.symm, zero_mul
-/
lemma minpolyDiv_ne_zero [Nontrivial S] : minpolyDiv R x != 0 := by
  intro e
  have := minpolyDiv_spec R x
  rw [e]; rw [zero_mul] at this
  exact ((minpoly.monic hx).map (algebraMap R S)).ne_zero this.symm

/--
lemma `minpolyDiv_monic` / 引理 `minpolyDiv_monic`

English:
lemma minpolyDiv_monic
  statement: Monic (minpolyDiv R x)
  proof: by
  nontriviality S
  have := congr_arg leadingCoeff (minpolyDiv_spec R x)
  rw [leadingCoeff_mul']; rw [((minpoly.monic hx).map (algebraMap R S)).leadingCoeff] at this
  · simpa using! this
  · simpa using! minpolyDiv_ne_zero hx

中文:
引理 minpolyDiv_monic
  结论: Monic (minpolyDiv R x)
  证明: by
  nontriviality S
  have := congr_arg leadingCoeff (minpolyDiv_spec R x)
  rw [leadingCoeff_mul']; rw [((minpoly.monic hx).map (algebraMap R S)).leadingCoeff] at this
  · simpa using! this
  · simpa using! minpolyDiv_ne_zero hx

Depends on / 依赖: algebraMap, congr_arg, leadingCoeff, leadingCoeff_mul, minpoly, minpoly.monic, minpolyDiv_ne_zero, minpolyDiv_spec, nontriviality
-/
lemma minpolyDiv_monic : Monic (minpolyDiv R x) := by
  nontriviality S
  have := congr_arg leadingCoeff (minpolyDiv_spec R x)
  rw [leadingCoeff_mul']; rw [((minpoly.monic hx).map (algebraMap R S)).leadingCoeff] at this
  · simpa using! this
  · simpa using! minpolyDiv_ne_zero hx

/--
lemma `natDegree_minpolyDiv_succ` / 引理 `natDegree_minpolyDiv_succ`

English:
lemma natDegree_minpolyDiv_succ
  given: [Nontrivial S]
  proof: by
  rw [← (minpoly.monic hx).natDegree_map (algebraMap R S)]; rw [← minpolyDiv_spec]; rw [natDegree_mul']
  · simp
  · simpa using minpolyDiv_ne_zero hx

中文:
引理 natDegree_minpolyDiv_succ
  条件: [非平凡 S]
  证明: by
  rw [← (minpoly.monic hx).natDegree_map (algebraMap R S)]; rw [← minpolyDiv_spec]; rw [natDegree_mul']
  · simp
  · simpa using minpolyDiv_ne_zero hx

Depends on / 依赖: algebraMap, minpoly, minpoly.monic, minpolyDiv_ne_zero, minpolyDiv_spec, natDegree_map, natDegree_mul
-/
lemma natDegree_minpolyDiv_succ [Nontrivial S] :
    natDegree (minpolyDiv R x) + 1 = natDegree (minpoly R x) := by
  rw [← (minpoly.monic hx).natDegree_map (algebraMap R S)]; rw [← minpolyDiv_spec]; rw [natDegree_mul']
  · simp
  · simpa using minpolyDiv_ne_zero hx

/--
lemma `natDegree_minpolyDiv_lt` / 引理 `natDegree_minpolyDiv_lt`

English:
lemma natDegree_minpolyDiv_lt
  given: [Nontrivial S]
  proof: by
  rw [← natDegree_minpolyDiv_succ hx]
  exact Nat.lt_succ_self _

中文:
引理 natDegree_minpolyDiv_lt
  条件: [非平凡 S]
  证明: by
  rw [← natDegree_minpolyDiv_succ hx]
  exact Nat.lt_succ_self _

Depends on / 依赖: Nat.lt_succ_self, lt_succ_self, natDegree_minpolyDiv_succ
-/
lemma natDegree_minpolyDiv_lt [Nontrivial S] :
    natDegree (minpolyDiv R x) < natDegree (minpoly R x) := by
  rw [← natDegree_minpolyDiv_succ hx]
  exact Nat.lt_succ_self _

/--
lemma `minpolyDiv_eq_of_isIntegrallyClosed` / 引理 `minpolyDiv_eq_of_isIntegrallyClosed`

English:
lemma minpolyDiv_eq_of_isIntegrallyClosed
  statement: [IsDomain R] [IsIntegrallyClosed R] [IsDomain S]
  proof: by
  delta minpolyDiv
  rw [IsScalarTower.algebraMap_eq R K S]; rw [← map_map]; rw [← minpoly.isIntegrallyClosed_eq_field_fractions' _ hx]

中文:
引理 minpolyDiv_eq_of_is整数egrallyClosed
  结论: [是整环 R] [是整闭 R] [是整环 S]
  证明: by
  delta minpolyDiv
  rw [IsScalarTower.algebraMap_eq R K S]; rw [← map_map]; rw [← minpoly.isIntegrallyClosed_eq_field_fractions' _ hx]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, algebraMap_eq, isIntegrallyClosed_eq_field_fractions, map_map, minpoly, minpoly.isIntegrallyClosed_eq_field_fractions, minpolyDiv
-/
lemma minpolyDiv_eq_of_isIntegrallyClosed [IsDomain R] [IsIntegrallyClosed R] [IsDomain S]
    [Algebra R K] [Algebra K S] [IsScalarTower R K S] [IsFractionRing R K] :
    minpolyDiv R x = minpolyDiv K x := by
  delta minpolyDiv
  rw [IsScalarTower.algebraMap_eq R K S]; rw [← map_map]; rw [← minpoly.isIntegrallyClosed_eq_field_fractions' _ hx]

/--
lemma `coeff_minpolyDiv_sub_pow_mem_span` / 引理 `coeff_minpolyDiv_sub_pow_mem_span`

English:
lemma coeff_minpolyDiv_sub_pow_mem_span
  given: {i} (hi : i <= natDegree (minpolyDiv R x))
  proof: by
  induction i with
  | zero => simp [(minpolyDiv_monic hx).leadingCoeff]
  | succ i IH =>
    rw [coeff_minpolyDiv]; rw [add_sub_assoc]; rw [pow_succ]; rw [← sub_mul]; rw [Algebra.algebraMap_eq_smul_one]
    refine add_mem ?_ ?_
    · apply Submodule.smul_mem
      apply Submodule.subset_span
   

中文:
引理 coeff_minpolyDiv_sub_pow_mem_span
  条件: {i} (hi : i <= natDegree (minpolyDiv R x))
  证明: by
  induction i with
  | zero => simp [(minpolyDiv_monic hx).leadingCoeff]
  | succ i IH =>
    rw [coeff_minpolyDiv]; rw [add_sub_assoc]; rw [pow_succ]; rw [← sub_mul]; rw [Algebra.algebraMap_eq_smul_one]
    refine add_mem ?_ ?_
    · apply Submodule.smul_mem
      apply Submodule.subset_span
   

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Nat.le_succ, Nat.zero_lt_succ, SetLike, SetLike.le_def.mp, Submodule, Submodule.mem_span_sing, Submodule.mul_mem_mul, Submodule.smul_mem, Submodule.subset_span, add_mem, add_sub_assoc, algebraMap_eq_smul_one, coeff_minpolyDiv, le_def, le_succ, le_tsub_of_add_le_left, leadingCoeff, mem_span_sing
-/
lemma coeff_minpolyDiv_sub_pow_mem_span {i} (hi : i <= natDegree (minpolyDiv R x)) :
    coeff (minpolyDiv R x) (natDegree (minpolyDiv R x) - i) - x ^ i in
      Submodule.span R ((x ^ ·) '' Set.Iio i) := by
  induction i with
  | zero => simp [(minpolyDiv_monic hx).leadingCoeff]
  | succ i IH =>
    rw [coeff_minpolyDiv]; rw [add_sub_assoc]; rw [pow_succ]; rw [← sub_mul]; rw [Algebra.algebraMap_eq_smul_one]
    refine add_mem ?_ ?_
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨0, Nat.zero_lt_succ _, pow_zero _⟩
    · rw [← tsub_tsub, tsub_add_cancel_of_le (le_tsub_of_add_le_left (b := 1) hi)]
      apply SetLike.le_def.mp ?_
        (Submodule.mul_mem_mul (IH ((Nat.le_succ _).trans hi))
          (Submodule.mem_span_singleton_self x))
      rw [Submodule.span_mul_span]; rw [Set.mul_singleton]; rw [Set.image_image]
      apply Submodule.span_mono
      rintro _ ⟨j, hj, rfl⟩
      rw [Set.mem_Iio] at hj
      exact ⟨j + 1, Nat.add_lt_of_lt_sub hj, pow_succ x j⟩

/--
lemma `span_coeff_minpolyDiv` / 引理 `span_coeff_minpolyDiv`

English:
lemma span_coeff_minpolyDiv
  proof: by
  nontriviality S
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply coeff_minpolyDiv_mem_adjoin
  · rw [← Submodule.span_range_natDegree_eq_adjoin (minpoly.monic hx) (minpoly.aeval _ _),
      Submodule.span_le]
    simp only [Finset.coe_image, Finset.coe_range, Set.i

中文:
引理 span_coeff_minpolyDiv
  证明: by
  nontriviality S
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply coeff_minpolyDiv_mem_adjoin
  · rw [← Submodule.span_range_natDegree_eq_adjoin (minpoly.monic hx) (minpoly.aeval _ _),
      Submodule.span_le]
    simp only [Finset.coe_image, Finset.coe_range, Set.i

Depends on / 依赖: Finset, Finset.coe_image, Finset.coe_range, Nat.strongRecOn, Set.image_subset_iff, Set.range, Submodule, Submodule.span, Submodule.span_le, Submodule.span_range_natDegree_eq_adjoin, Submodule.su, coe_image, coe_range, coeff_minpolyDiv_mem_adjoin, image_subset_iff, le_antisymm, minpoly, minpoly.aeval, minpoly.monic, minpolyDiv
-/
lemma span_coeff_minpolyDiv :
    Submodule.span R (Set.range (coeff (minpolyDiv R x))) =
      Subalgebra.toSubmodule (R[x]) := by
  nontriviality S
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply coeff_minpolyDiv_mem_adjoin
  · rw [← Submodule.span_range_natDegree_eq_adjoin (minpoly.monic hx) (minpoly.aeval _ _),
      Submodule.span_le]
    simp only [Finset.coe_image, Finset.coe_range, Set.image_subset_iff]
    intro i
    induction i using Nat.strongRecOn with | ind i hi => ?_
    intro hi'
    have : coeff (minpolyDiv R x) (natDegree (minpolyDiv R x) - i) in
        Submodule.span R (Set.range (coeff (minpolyDiv R x))) :=
      Submodule.subset_span (Set.mem_range_self _)
    rw [Set.mem_preimage]; rw [SetLike.mem_coe]; rw [← Submodule.sub_mem_iff_right _ this]
    refine SetLike.le_def.mp ?_ (coeff_minpolyDiv_sub_pow_mem_span hx ?_)
    · rw [Submodule.span_le, Set.image_subset_iff]
      intro j (hj : j < i)
      exact hi j hj (lt_trans hj hi')
    · rwa [← natDegree_minpolyDiv_succ hx, Set.mem_Iio, Nat.lt_succ_iff] at hi'

end IsIntegral

/--
lemma `natDegree_minpolyDiv` / 引理 `natDegree_minpolyDiv`

English:
lemma natDegree_minpolyDiv
  proof: by
  nontriviality S
  by_cases hx : IsIntegral R x
  · rw [← natDegree_minpolyDiv_succ hx]; rfl
  · rw [minpolyDiv_eq_zero hx, minpoly.eq_zero hx]; rfl

中文:
引理 natDegree_minpolyDiv
  证明: by
  nontriviality S
  by_cases hx : IsIntegral R x
  · rw [← natDegree_minpolyDiv_succ hx]; rfl
  · rw [minpolyDiv_eq_zero hx, minpoly.eq_zero hx]; rfl

Depends on / 依赖: IsIntegral, eq_zero, minpoly, minpoly.eq_zero, minpolyDiv_eq_zero, natDegree_minpolyDiv_succ, nontriviality
-/
lemma natDegree_minpolyDiv :
    natDegree (minpolyDiv R x) = natDegree (minpoly R x) - 1 := by
  nontriviality S
  by_cases hx : IsIntegral R x
  · rw [← natDegree_minpolyDiv_succ hx]; rfl
  · rw [minpolyDiv_eq_zero hx, minpoly.eq_zero hx]; rfl


section PowerBasis

variable {K}

/--
lemma `sum_smul_minpolyDiv_eq_X_pow` / 引理 `sum_smul_minpolyDiv_eq_X_pow`

English:
lemma sum_smul_minpolyDiv_eq_X_pow
  statement: (E) [Field E] [Algebra K E] [IsAlgClosed E]
  proof: by
  classical
  rw [← sub_eq_zero]
  have : Function.Injective (fun σ : L ->ₐ[K] E => σ x) := fun _ _ h =>
    AlgHom.ext_of_adjoin_eq_top hxL (fun _ hx => hx ▸ h)
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ this
  · intro σ
    simp only [Polynomial.map_smul, map_div₀, map_po

中文:
引理 sum_smul_minpolyDiv_eq_X_pow
  结论: (E) [域 E] [代数 K E] [是代数闭 E]
  证明: by
  classical
  rw [← sub_eq_zero]
  have : Function.Injective (fun σ : L ->ₐ[K] E => σ x) := fun _ _ h =>
    AlgHom.ext_of_adjoin_eq_top hxL (fun _ hx => hx ▸ h)
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ this
  · intro σ
    simp only [Polynomial.map_smul, map_div₀, map_po

Depends on / 依赖: AlgHom, AlgHom.ext_of_adjoin_eq_top, Finset, Finset.mem_univ, Finset.sum_ite_eq, Function, Function.Injective, Injective, Polynomial, Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero, Polynomial.map_smul, RingHom, RingHom.coe_coe, classical, coe_coe, eq_iff, eq_zero_of_natDegree_lt_card_of_eval_eq_zero, eval_X_pow, eval_finsetSum, eval_map
-/
lemma sum_smul_minpolyDiv_eq_X_pow (E) [Field E] [Algebra K E] [IsAlgClosed E]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {x : L} (hxL : K[x] = ⊤) {r : Nat} (hr : r < finrank K L) :
    ∑ σ : L ->ₐ[K] E, ((x ^ r / aeval x (derivative <| minpoly K x)) •
      minpolyDiv K x).map σ = (X ^ r : E[X]) := by
  classical
  rw [← sub_eq_zero]
  have : Function.Injective (fun σ : L ->ₐ[K] E => σ x) := fun _ _ h =>
    AlgHom.ext_of_adjoin_eq_top hxL (fun _ hx => hx ▸ h)
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ this
  · intro σ
    simp only [Polynomial.map_smul, map_div₀, map_pow, RingHom.coe_coe, eval_sub, eval_finsetSum,
      eval_smul, eval_map, eval₂_minpolyDiv_self, this.eq_iff, smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, eval_X_pow]
    rw [sub_eq_zero]; rw [div_mul_cancel₀]
    rw [ne_eq]; rw [map_eq_zero_iff σ σ.toRingHom.injective]
    exact (IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)
  · refine (Polynomial.natDegree_sub_le _ _).trans_lt
      (max_lt ((Polynomial.natDegree_sum_le _ _).trans_lt ?_) ?_)
    · simp only [Polynomial.map_smul,
        map_div₀, map_pow, RingHom.coe_coe, Function.comp_apply,
        Finset.mem_univ, forall_true_left, Finset.fold_max_lt, AlgHom.card]
      refine ⟨finrank_pos, ?_⟩
      intro σ
      exact ((Polynomial.natDegree_smul_le _ _).trans natDegree_map_le).trans_lt
        ((natDegree_minpolyDiv_lt (Algebra.IsIntegral.isIntegral x)).trans_le
          (minpoly.natDegree_le _))
    · rwa [natDegree_pow, natDegree_X, mul_one, AlgHom.card]

end PowerBasis
