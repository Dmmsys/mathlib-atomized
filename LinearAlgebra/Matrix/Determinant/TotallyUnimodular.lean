/-
Copyright (c) 2024 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Vladimir Kolmogorov, Ivan Sergeev, Bhavik Mehta
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Sign.Basic

/-!
# Totally unimodular matrices

This file defines totally unimodular matrices and provides basic API for them.

## Main definitions

- `Matrix.IsTotallyUnimodular`: a matrix is totally unimodular iff every square submatrix
  (not necessarily contiguous) has determinant `0` or `1` or `-1`.

## Main results

- `Matrix.isTotallyUnimodular_iff`: a matrix is totally unimodular iff every square submatrix
  (possibly with repeated rows and/or repeated columns) has determinant `0` or `1` or `-1`.
- `Matrix.IsTotallyUnimodular.apply`: entry in a totally unimodular matrix is `0` or `1` or `-1`.

-/

@[expose] public section

namespace Matrix

variable {m m' n n' R : Type*} [CommRing R]

/--
Definition of `IsTotallyUnimodular` / `IsTotallyUnimodular` 的定义

English:
definition IsTotallyUnimodular
  signature: (A : Matrix m n R)
  body: forall k : Nat, forall f : Fin k -> m, forall g : Fin k -> n, f.Injective -> g.Injective ->
    (A.submatrix f g).det in Set.range SignType.cast

中文:
定义 IsTotallyUnimodular
  签名: (A : Matrix m n R)
  定义体: forall k : Nat, forall f : Fin k -> m, forall g : Fin k -> n, f.Injective -> g.Injective ->
    (A.submatrix f g).det in Set.range SignType.cast

Depends on / 依赖: A.submatrix, Injective, Set.range, SignType, SignType.cast, f.Injective, g.Injective, submatrix
-/
def IsTotallyUnimodular (A : Matrix m n R) : Prop :=
  forall k : Nat, forall f : Fin k -> m, forall g : Fin k -> n, f.Injective -> g.Injective ->
    (A.submatrix f g).det in Set.range SignType.cast

/--
lemma `isTotallyUnimodular_iff` / 引理 `isTotallyUnimodular_iff`

English:
lemma isTotallyUnimodular_iff
  given: (A : Matrix m n R)
  statement: A.IsTotallyUnimodular ↔
  proof: by
  constructor <;> intro hA
  · intro k f g
    by_cases hfg : f.Injective ∧ g.Injective
    · exact hA k f g hfg.1 hfg.2
    · use 0
      rw [SignType.coe_zero]; rw [eq_comm]
      simp_rw [not_and_or, Function.not_injective_iff] at hfg
      obtain ⟨i, j, hfij, hij⟩ | ⟨i, j, hgij, hij⟩ := hfg
 

中文:
引理 isTotallyUnimodular_iff
  条件: (A : Matrix m n R)
  结论: A.IsTotallyUnimodular ↔
  证明: by
  constructor <;> intro hA
  · intro k f g
    by_cases hfg : f.Injective ∧ g.Injective
    · exact hA k f g hfg.1 hfg.2
    · use 0
      rw [SignType.coe_zero]; rw [eq_comm]
      simp_rw [not_and_or, Function.not_injective_iff] at hfg
      obtain ⟨i, j, hfij, hij⟩ | ⟨i, j, hgij, hij⟩ := hfg
 

Depends on / 依赖: Function, Function.not_injective_iff, Injective, SignType, SignType.coe_zero, coe_zero, det_transpose, det_zero_of_column_eq, eq_comm, f.Injective, g.Injective, hij.symm, not_and_or, not_injective_iff, simp_rw, transpose_submatrix
-/
lemma isTotallyUnimodular_iff (A : Matrix m n R) : A.IsTotallyUnimodular ↔
    forall k : Nat, forall f : Fin k -> m, forall g : Fin k -> n,
      (A.submatrix f g).det in Set.range SignType.cast := by
  constructor <;> intro hA
  · intro k f g
    by_cases hfg : f.Injective ∧ g.Injective
    · exact hA k f g hfg.1 hfg.2
    · use 0
      rw [SignType.coe_zero]; rw [eq_comm]
      simp_rw [not_and_or, Function.not_injective_iff] at hfg
      obtain ⟨i, j, hfij, hij⟩ | ⟨i, j, hgij, hij⟩ := hfg
      · rw [← det_transpose, transpose_submatrix]
        apply det_zero_of_column_eq hij.symm
        simp [hfij]
      · apply det_zero_of_column_eq hij
        simp [hgij]
  · intro _ _ _ _ _
    apply hA

/--
lemma `isTotallyUnimodular_iff_fintype.` / 引理 `isTotallyUnimodular_iff_fintype.`

English:
lemma isTotallyUnimodular_iff_fintype.{w}
  given: (A : Matrix m n R)
  statement: A.IsTotallyUnimodular ↔
  proof: by
  rw [isTotallyUnimodular_iff]
  constructor
  · intro hA ι _ _ f g
    specialize hA (Fintype.card ι) (f ∘ (Fintype.equivFin ι).symm) (g ∘ (Fintype.equivFin ι).symm)
    rwa [← submatrix_submatrix, det_submatrix_equiv_self] at hA
  · intro hA k f g
    specialize hA (ULift (Fin k)) (f ∘ Equiv.ul

中文:
引理 isTotallyUnimodular_iff_fintype.{w}
  条件: (A : Matrix m n R)
  结论: A.IsTotallyUnimodular ↔
  证明: by
  rw [isTotallyUnimodular_iff]
  constructor
  · intro hA ι _ _ f g
    specialize hA (Fintype.card ι) (f ∘ (Fintype.equivFin ι).symm) (g ∘ (Fintype.equivFin ι).symm)
    rwa [← submatrix_submatrix, det_submatrix_equiv_self] at hA
  · intro hA k f g
    specialize hA (ULift (Fin k)) (f ∘ Equiv.ul

Depends on / 依赖: Equiv.ulift, Fintype, Fintype.card, Fintype.equivFin, det_submatrix_equiv_self, equivFin, isTotallyUnimodular_iff, specialize, submatrix_submatrix
-/
lemma isTotallyUnimodular_iff_fintype.{w} (A : Matrix m n R) : A.IsTotallyUnimodular ↔
    forall (ι : Type w) [Fintype ι] [DecidableEq ι], forall f : ι -> m, forall g : ι -> n,
      (A.submatrix f g).det in Set.range SignType.cast := by
  rw [isTotallyUnimodular_iff]
  constructor
  · intro hA ι _ _ f g
    specialize hA (Fintype.card ι) (f ∘ (Fintype.equivFin ι).symm) (g ∘ (Fintype.equivFin ι).symm)
    rwa [← submatrix_submatrix, det_submatrix_equiv_self] at hA
  · intro hA k f g
    specialize hA (ULift (Fin k)) (f ∘ Equiv.ulift) (g ∘ Equiv.ulift)
    rwa [← submatrix_submatrix, det_submatrix_equiv_self] at hA

/--
lemma `IsTotallyUnimodular.apply` / 引理 `IsTotallyUnimodular.apply`

English:
lemma IsTotallyUnimodular.apply
  given: {A : Matrix m n R} (hA : A.IsTotallyUnimodular) (i : m) (j : n)
  proof: by
  rw [isTotallyUnimodular_iff] at hA
  simpa using hA 1 (fun _ => i) (fun _ => j)

中文:
引理 IsTotallyUnimodular.apply
  条件: {A : Matrix m n R} (hA : A.IsTotallyUnimodular) (i : m) (j : n)
  证明: by
  rw [isTotallyUnimodular_iff] at hA
  simpa using hA 1 (fun _ => i) (fun _ => j)

Depends on / 依赖: isTotallyUnimodular_iff
-/
lemma IsTotallyUnimodular.apply {A : Matrix m n R} (hA : A.IsTotallyUnimodular) (i : m) (j : n) :
    A i j in Set.range SignType.cast := by
  rw [isTotallyUnimodular_iff] at hA
  simpa using hA 1 (fun _ => i) (fun _ => j)

/--
lemma `IsTotallyUnimodular.submatrix` / 引理 `IsTotallyUnimodular.submatrix`

English:
lemma IsTotallyUnimodular.submatrix
  statement: {A : Matrix m n R} (f : m' -> m) (g : n' -> n)
  proof: by
  simp only [isTotallyUnimodular_iff, submatrix_submatrix] at hA ⊢
  intro _ _ _
  apply hA

中文:
引理 IsTotallyUnimodular.submatrix
  结论: {A : Matrix m n R} (f : m' -> m) (g : n' -> n)
  证明: by
  simp only [isTotallyUnimodular_iff, submatrix_submatrix] at hA ⊢
  intro _ _ _
  apply hA

Depends on / 依赖: isTotallyUnimodular_iff, submatrix_submatrix
-/
lemma IsTotallyUnimodular.submatrix {A : Matrix m n R} (f : m' -> m) (g : n' -> n)
    (hA : A.IsTotallyUnimodular) :
    (A.submatrix f g).IsTotallyUnimodular := by
  simp only [isTotallyUnimodular_iff, submatrix_submatrix] at hA ⊢
  intro _ _ _
  apply hA

/--
lemma `IsTotallyUnimodular.transpose` / 引理 `IsTotallyUnimodular.transpose`

English:
lemma IsTotallyUnimodular.transpose
  given: {A : Matrix m n R} (hA : A.IsTotallyUnimodular)
  proof: by
  simp only [isTotallyUnimodular_iff, ← transpose_submatrix, det_transpose] at hA ⊢
  intro _ _ _
  apply hA

中文:
引理 IsTotallyUnimodular.transpose
  条件: {A : Matrix m n R} (hA : A.IsTotallyUnimodular)
  证明: by
  simp only [isTotallyUnimodular_iff, ← transpose_submatrix, det_transpose] at hA ⊢
  intro _ _ _
  apply hA

Depends on / 依赖: det_transpose, isTotallyUnimodular_iff, transpose_submatrix
-/
lemma IsTotallyUnimodular.transpose {A : Matrix m n R} (hA : A.IsTotallyUnimodular) :
    Aᵀ.IsTotallyUnimodular := by
  simp only [isTotallyUnimodular_iff, ← transpose_submatrix, det_transpose] at hA ⊢
  intro _ _ _
  apply hA

/--
lemma `transpose_isTotallyUnimodular_iff` / 引理 `transpose_isTotallyUnimodular_iff`

English:
lemma transpose_isTotallyUnimodular_iff
  given: (A : Matrix m n R)
  proof: by
  constructor <;> apply IsTotallyUnimodular.transpose

中文:
引理 transpose_isTotallyUnimodular_iff
  条件: (A : Matrix m n R)
  证明: by
  constructor <;> apply IsTotallyUnimodular.transpose

Depends on / 依赖: IsTotallyUnimodular, IsTotallyUnimodular.transpose, transpose
-/
lemma transpose_isTotallyUnimodular_iff (A : Matrix m n R) :
    Aᵀ.IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  constructor <;> apply IsTotallyUnimodular.transpose

/--
lemma `IsTotallyUnimodular.reindex` / 引理 `IsTotallyUnimodular.reindex`

English:
lemma IsTotallyUnimodular.reindex
  statement: {A : Matrix m n R} (em : m ≃ m') (en : n ≃ n')
  proof: hA.submatrix _ _

中文:
引理 IsTotallyUnimodular.reindex
  结论: {A : Matrix m n R} (em : m ≃ m') (en : n ≃ n')
  证明: hA.submatrix _ _

Depends on / 依赖: hA.submatrix, submatrix
-/
lemma IsTotallyUnimodular.reindex {A : Matrix m n R} (em : m ≃ m') (en : n ≃ n')
    (hA : A.IsTotallyUnimodular) :
    (A.reindex em en).IsTotallyUnimodular :=
  hA.submatrix _ _

/--
lemma `reindex_isTotallyUnimodular` / 引理 `reindex_isTotallyUnimodular`

English:
lemma reindex_isTotallyUnimodular
  given: (A : Matrix m n R) (em : m ≃ m') (en : n ≃ n')
  proof: ⟨fun hA => by simpa [Equiv.symm_apply_eq] using hA.reindex em.symm en.symm,
   fun hA => hA.reindex _ _⟩

中文:
引理 reindex_isTotallyUnimodular
  条件: (A : Matrix m n R) (em : m ≃ m') (en : n ≃ n')
  证明: ⟨fun hA => by simpa [Equiv.symm_apply_eq] using hA.reindex em.symm en.symm,
   fun hA => hA.reindex _ _⟩

Depends on / 依赖: Equiv.symm_apply_eq, em.symm, en.symm, hA.reindex, reindex, symm_apply_eq
-/
lemma reindex_isTotallyUnimodular (A : Matrix m n R) (em : m ≃ m') (en : n ≃ n') :
    (A.reindex em en).IsTotallyUnimodular ↔ A.IsTotallyUnimodular :=
  ⟨fun hA => by simpa [Equiv.symm_apply_eq] using hA.reindex em.symm en.symm,
   fun hA => hA.reindex _ _⟩

set_option backward.isDefEq.respectTransparency false in
/-- If `A` has no rows, then it is totally unimodular. -/
@[simp]
/--
lemma `emptyRows_isTotallyUnimodular` / 引理 `emptyRows_isTotallyUnimodular`

English:
lemma emptyRows_isTotallyUnimodular
  given: [IsEmpty m] (A : Matrix m n R)
  proof: by
  intro k f _ _ _
  cases k with
  | zero => use 1; rw [submatrix_empty, det_fin_zero, SignType.coe_one]
  | succ => exact (IsEmpty.false (f 0)).elim

中文:
引理 emptyRows_isTotallyUnimodular
  条件: [IsEmpty m] (A : Matrix m n R)
  证明: by
  intro k f _ _ _
  cases k with
  | zero => use 1; rw [submatrix_empty, det_fin_zero, SignType.coe_one]
  | succ => exact (IsEmpty.false (f 0)).elim

Depends on / 依赖: IsEmpty, IsEmpty.false, SignType, SignType.coe_one, coe_one, det_fin_zero, submatrix_empty
-/
lemma emptyRows_isTotallyUnimodular [IsEmpty m] (A : Matrix m n R) :
    A.IsTotallyUnimodular := by
  intro k f _ _ _
  cases k with
  | zero => use 1; rw [submatrix_empty, det_fin_zero, SignType.coe_one]
  | succ => exact (IsEmpty.false (f 0)).elim

/-- If `A` has no columns, then it is totally unimodular. -/
@[simp]
/--
lemma `emptyCols_isTotallyUnimodular` / 引理 `emptyCols_isTotallyUnimodular`

English:
lemma emptyCols_isTotallyUnimodular
  given: [IsEmpty n] (A : Matrix m n R)
  proof: A.transpose.emptyRows_isTotallyUnimodular.transpose

中文:
引理 emptyCols_isTotallyUnimodular
  条件: [IsEmpty n] (A : Matrix m n R)
  证明: A.transpose.emptyRows_isTotallyUnimodular.transpose

Depends on / 依赖: A.transpose.emptyRows_isTotallyUnimodular.transpose, emptyRows_isTotallyUnimodular, transpose
-/
lemma emptyCols_isTotallyUnimodular [IsEmpty n] (A : Matrix m n R) :
    A.IsTotallyUnimodular :=
  A.transpose.emptyRows_isTotallyUnimodular.transpose

set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsTotallyUnimodular.fromRows_unitlike` / 引理 `IsTotallyUnimodular.fromRows_unitlike`

English:
lemma IsTotallyUnimodular.fromRows_unitlike
  statement: [DecidableEq n] {A : Matrix m n R} {B : Matrix m' n R}
  proof: by
  intro k f g hf hg
  induction k with
  | zero => use 1; simp
  | succ k ih =>
    specialize hB ⟨g 0⟩
    -- Either `f` is `inr` somewhere or `inl` everywhere
    obtain ⟨i, j, hfi⟩ | ⟨f', rfl⟩ : (exists i j, f i = .inr j) ∨ (exists f', f = .inl ∘ f') := by
      simp_rw [← Sum.isRight_iff, or_

中文:
引理 IsTotallyUnimodular.fromRows_unitlike
  结论: [DecidableEq n] {A : Matrix m n R} {B : Matrix m' n R}
  证明: by
  intro k f g hf hg
  induction k with
  | zero => use 1; simp
  | succ k ih =>
    specialize hB ⟨g 0⟩
    -- Either `f` is `inr` somewhere or `inl` everywhere
    obtain ⟨i, j, hfi⟩ | ⟨f', rfl⟩ : (exists i j, f i = .inr j) ∨ (exists f', f = .inl ∘ f') := by
      simp_rw [← Sum.isRight_iff, or_

Depends on / 依赖: specialize
-/
lemma IsTotallyUnimodular.fromRows_unitlike [DecidableEq n] {A : Matrix m n R} {B : Matrix m' n R}
    (hA : A.IsTotallyUnimodular)
    (hB : Nonempty n -> forall i : m', exists j : n, exists s : SignType, B i = Pi.single j s.cast) :
    (fromRows A B).IsTotallyUnimodular := by
  intro k f g hf hg
  induction k with
  | zero => use 1; simp
  | succ k ih =>
    specialize hB ⟨g 0⟩
    -- Either `f` is `inr` somewhere or `inl` everywhere
    obtain ⟨i, j, hfi⟩ | ⟨f', rfl⟩ : (exists i j, f i = .inr j) ∨ (exists f', f = .inl ∘ f') := by
      simp_rw [← Sum.isRight_iff, or_iff_not_imp_left, not_exists, Bool.not_eq_true,
        Sum.isRight_eq_false, Sum.isLeft_iff]
      intro hfr
      choose f' hf' using hfr
      exact ⟨f', funext hf'⟩
    · have hAB := det_succ_row ((fromRows A B).submatrix f g) i
      simp only [submatrix_apply, hfi, fromRows_apply_inr] at hAB
      obtain ⟨j', s, hj'⟩ := hB j
      · simp only [hj'] at hAB
        by_cases hj'' : exists x, g x = j'
        · obtain ⟨x, rfl⟩ := hj''
          rw [Fintype.sum_eq_single x fun y hxy => ?_]; rw [Pi.single_eq_same] at hAB
          · rw [hAB]
            change _ in MonoidHom.mrange SignType.castHom.toMonoidHom
            refine mul_mem (mul_mem ?_ (Set.mem_range_self s)) ?_
            · apply pow_mem
              exact ⟨-1, by simp⟩
            · exact ih _ _
                (hf.comp Fin.succAbove_right_injective)
                (hg.comp Fin.succAbove_right_injective)
          · simp [Pi.single_eq_of_ne, hg.ne_iff.mpr hxy]
        · rw [not_exists] at hj''
          use 0
          simpa [hj''] using hAB.symm
    · rw [isTotallyUnimodular_iff] at hA
      apply hA

/--
lemma `fromRows_isTotallyUnimodular_iff_rows` / 引理 `fromRows_isTotallyUnimodular_iff_rows`

English:
lemma fromRows_isTotallyUnimodular_iff_rows
  statement: [DecidableEq n] {A : Matrix m n R} {B : Matrix m' n R}
  proof: ⟨.submatrix Sum.inl id, fun hA => hA.fromRows_unitlike hB⟩

中文:
引理 fromRows_isTotallyUnimodular_iff_rows
  结论: [DecidableEq n] {A : Matrix m n R} {B : Matrix m' n R}
  证明: ⟨.submatrix Sum.inl id, fun hA => hA.fromRows_unitlike hB⟩

Depends on / 依赖: Sum.inl, fromRows_unitlike, hA.fromRows_unitlike, submatrix
-/
lemma fromRows_isTotallyUnimodular_iff_rows [DecidableEq n] {A : Matrix m n R} {B : Matrix m' n R}
    (hB : Nonempty n -> forall i : m', exists j : n, exists s : SignType, B i = Pi.single j s.cast) :
    (fromRows A B).IsTotallyUnimodular ↔ A.IsTotallyUnimodular :=
  ⟨.submatrix Sum.inl id, fun hA => hA.fromRows_unitlike hB⟩

/--
lemma `fromRows_one_isTotallyUnimodular_iff` / 引理 `fromRows_one_isTotallyUnimodular_iff`

English:
lemma fromRows_one_isTotallyUnimodular_iff
  given: [DecidableEq n] (A : Matrix m n R)
  proof: fromRows_isTotallyUnimodular_iff_rows fun h i =>
    ⟨i, 1, funext fun j => by simp [one_apply, Pi.single_apply, eq_comm]⟩

中文:
引理 fromRows_one_isTotallyUnimodular_iff
  条件: [DecidableEq n] (A : Matrix m n R)
  证明: fromRows_isTotallyUnimodular_iff_rows fun h i =>
    ⟨i, 1, funext fun j => by simp [one_apply, Pi.single_apply, eq_comm]⟩

Depends on / 依赖: Pi.single_apply, eq_comm, fromRows_isTotallyUnimodular_iff_rows, one_apply, single_apply
-/
lemma fromRows_one_isTotallyUnimodular_iff [DecidableEq n] (A : Matrix m n R) :
    (fromRows A (1 : Matrix n n R)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular :=
fromRows_isTotallyUnimodular_iff_rows fun h i =>
    ⟨i, 1, funext fun j => by simp [one_apply, Pi.single_apply, eq_comm]⟩

/--
lemma `one_fromRows_isTotallyUnimodular_iff` / 引理 `one_fromRows_isTotallyUnimodular_iff`

English:
lemma one_fromRows_isTotallyUnimodular_iff
  given: [DecidableEq n] (A : Matrix m n R)
  proof: by
  have hA :
    fromRows (1 : Matrix n n R) A =
      (fromRows A (1 : Matrix n n R)).reindex (Equiv.sumComm m n) (Equiv.refl n) := by
    aesop
  rw [hA]; rw [reindex_isTotallyUnimodular]; rw [fromRows_one_isTotallyUnimodular_iff]

中文:
引理 one_fromRows_isTotallyUnimodular_iff
  条件: [DecidableEq n] (A : Matrix m n R)
  证明: by
  have hA :
    fromRows (1 : Matrix n n R) A =
      (fromRows A (1 : Matrix n n R)).reindex (Equiv.sumComm m n) (Equiv.refl n) := by
    aesop
  rw [hA]; rw [reindex_isTotallyUnimodular]; rw [fromRows_one_isTotallyUnimodular_iff]

Depends on / 依赖: Equiv.refl, Equiv.sumComm, Matrix, fromRows, fromRows_one_isTotallyUnimodular_iff, reindex, reindex_isTotallyUnimodular, sumComm
-/
lemma one_fromRows_isTotallyUnimodular_iff [DecidableEq n] (A : Matrix m n R) :
    (fromRows (1 : Matrix n n R) A).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  have hA :
    fromRows (1 : Matrix n n R) A =
      (fromRows A (1 : Matrix n n R)).reindex (Equiv.sumComm m n) (Equiv.refl n) := by
    aesop
  rw [hA]; rw [reindex_isTotallyUnimodular]; rw [fromRows_one_isTotallyUnimodular_iff]

/--
lemma `fromCols_one_isTotallyUnimodular_iff` / 引理 `fromCols_one_isTotallyUnimodular_iff`

English:
lemma fromCols_one_isTotallyUnimodular_iff
  given: [DecidableEq m] (A : Matrix m n R)
  proof: by
  rw [← transpose_isTotallyUnimodular_iff]; rw [transpose_fromCols]; rw [transpose_one]; rw [fromRows_one_isTotallyUnimodular_iff]; rw [transpose_isTotallyUnimodular_iff]

中文:
引理 fromCols_one_isTotallyUnimodular_iff
  条件: [DecidableEq m] (A : Matrix m n R)
  证明: by
  rw [← transpose_isTotallyUnimodular_iff]; rw [transpose_fromCols]; rw [transpose_one]; rw [fromRows_one_isTotallyUnimodular_iff]; rw [transpose_isTotallyUnimodular_iff]

Depends on / 依赖: fromRows_one_isTotallyUnimodular_iff, transpose_fromCols, transpose_isTotallyUnimodular_iff, transpose_one
-/
lemma fromCols_one_isTotallyUnimodular_iff [DecidableEq m] (A : Matrix m n R) :
    (fromCols A (1 : Matrix m m R)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  rw [← transpose_isTotallyUnimodular_iff]; rw [transpose_fromCols]; rw [transpose_one]; rw [fromRows_one_isTotallyUnimodular_iff]; rw [transpose_isTotallyUnimodular_iff]

/--
lemma `one_fromCols_isTotallyUnimodular_iff` / 引理 `one_fromCols_isTotallyUnimodular_iff`

English:
lemma one_fromCols_isTotallyUnimodular_iff
  given: [DecidableEq m] (A : Matrix m n R)
  proof: by
  rw [← transpose_isTotallyUnimodular_iff]; rw [transpose_fromCols]; rw [transpose_one]; rw [one_fromRows_isTotallyUnimodular_iff]; rw [transpose_isTotallyUnimodular_iff]

alias ⟨_, IsTotallyUnimodular.fromRows_one⟩ := fromRows_one_isTotallyUnimodular_iff
alias ⟨_, IsTotallyUnimodular.one_fromRow

中文:
引理 one_fromCols_isTotallyUnimodular_iff
  条件: [DecidableEq m] (A : Matrix m n R)
  证明: by
  rw [← transpose_isTotallyUnimodular_iff]; rw [transpose_fromCols]; rw [transpose_one]; rw [one_fromRows_isTotallyUnimodular_iff]; rw [transpose_isTotallyUnimodular_iff]

alias ⟨_, IsTotallyUnimodular.fromRows_one⟩ := fromRows_one_isTotallyUnimodular_iff
alias ⟨_, IsTotallyUnimodular.one_fromRow

Depends on / 依赖: one_fromRows_isTotallyUnimodular_iff, transpose_fromCols, transpose_isTotallyUnimodular_iff, transpose_one
-/
lemma one_fromCols_isTotallyUnimodular_iff [DecidableEq m] (A : Matrix m n R) :
    (fromCols (1 : Matrix m m R) A).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  rw [← transpose_isTotallyUnimodular_iff]; rw [transpose_fromCols]; rw [transpose_one]; rw [one_fromRows_isTotallyUnimodular_iff]; rw [transpose_isTotallyUnimodular_iff]

alias ⟨_, IsTotallyUnimodular.fromRows_one⟩ := fromRows_one_isTotallyUnimodular_iff
alias ⟨_, IsTotallyUnimodular.one_fromRows⟩ := one_fromRows_isTotallyUnimodular_iff
alias ⟨_, IsTotallyUnimodular.fromCols_one⟩ := fromCols_one_isTotallyUnimodular_iff
alias ⟨_, IsTotallyUnimodular.one_fromCols⟩ := one_fromCols_isTotallyUnimodular_iff

/--
lemma `fromRows_replicateRow0_isTotallyUnimodular_iff` / 引理 `fromRows_replicateRow0_isTotallyUnimodular_iff`

English:
lemma fromRows_replicateRow0_isTotallyUnimodular_iff
  given: (A : Matrix m n R)
  proof: by
  classical
refine fromRows_isTotallyUnimodular_iff_rows fun _ _ => ?_
  inhabit n
  refine ⟨default, 0, ?_⟩
  ext x
  simp [Pi.single_apply]

中文:
引理 fromRows_replicateRow0_isTotallyUnimodular_iff
  条件: (A : Matrix m n R)
  证明: by
  classical
refine fromRows_isTotallyUnimodular_iff_rows fun _ _ => ?_
  inhabit n
  refine ⟨default, 0, ?_⟩
  ext x
  simp [Pi.single_apply]

Depends on / 依赖: Pi.single_apply, classical, fromRows_isTotallyUnimodular_iff_rows, inhabit, single_apply
-/
lemma fromRows_replicateRow0_isTotallyUnimodular_iff (A : Matrix m n R) :
    (fromRows A (replicateRow m' 0)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  classical
refine fromRows_isTotallyUnimodular_iff_rows fun _ _ => ?_
  inhabit n
  refine ⟨default, 0, ?_⟩
  ext x
  simp [Pi.single_apply]

/--
lemma `fromCols_replicateCol0_isTotallyUnimodular_iff` / 引理 `fromCols_replicateCol0_isTotallyUnimodular_iff`

English:
lemma fromCols_replicateCol0_isTotallyUnimodular_iff
  given: (A : Matrix m n R)
  proof: by
  rw [← transpose_isTotallyUnimodular_iff]; rw [transpose_fromCols]; rw [transpose_replicateCol]; rw [fromRows_replicateRow0_isTotallyUnimodular_iff]; rw [transpose_isTotallyUnimodular_iff]

中文:
引理 fromCols_replicateCol0_isTotallyUnimodular_iff
  条件: (A : Matrix m n R)
  证明: by
  rw [← transpose_isTotallyUnimodular_iff]; rw [transpose_fromCols]; rw [transpose_replicateCol]; rw [fromRows_replicateRow0_isTotallyUnimodular_iff]; rw [transpose_isTotallyUnimodular_iff]

Depends on / 依赖: fromRows_replicateRow0_isTotallyUnimodular_iff, transpose_fromCols, transpose_isTotallyUnimodular_iff, transpose_replicateCol
-/
lemma fromCols_replicateCol0_isTotallyUnimodular_iff (A : Matrix m n R) :
    (fromCols A (replicateCol n' 0)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  rw [← transpose_isTotallyUnimodular_iff]; rw [transpose_fromCols]; rw [transpose_replicateCol]; rw [fromRows_replicateRow0_isTotallyUnimodular_iff]; rw [transpose_isTotallyUnimodular_iff]

end Matrix
