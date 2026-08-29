/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.NumberTheory.ClassNumber.AdmissibleAbsoluteValue
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Norm.Basic

/-!
# Class numbers of global fields

In this file, we use the notion of "admissible absolute value" to prove
finiteness of the class group for number fields and function fields.

## Main definitions
- `ClassGroup.fintypeOfAdmissibleOfAlgebraic`: if `R` has an admissible absolute value,
  its integral closure has a finite class group
-/

@[expose] public section

open Module Ring
open scoped nonZeroDivisors

namespace ClassGroup
section EuclideanDomain

variable {R S : Type*} (K L : Type*) [EuclideanDomain R] [CommRing S] [IsDomain S]
variable [Field K] [Field L]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [algRL : Algebra R L] [IsScalarTower R K L]
variable [Algebra R S] [Algebra S L]
variable [ist : IsScalarTower R S L]
variable (abv : AbsoluteValue R Int)
variable {ι : Type*} [DecidableEq ι] [Fintype ι] (bS : Basis ι R S)

/--
Definition of `normBound` / `normBound` 的定义

English:
definition normBound
  signature: : Int
  body: let n := Fintype.card ι
  let i : ι := Nonempty.some bS.index_nonempty
  let m : Int :=
    Finset.max'
      (Finset.univ.image fun ijk : ι × ι × ι =>
        abv (Algebra.leftMulMatrix bS (bS ijk.1) ijk.2.1 ijk.2.2))
      ⟨_, Finset.mem_image.mpr ⟨⟨i, i, i⟩, Finset.mem_univ _, rfl⟩⟩
  Nat.factorial n • (n • m) ^ n

中文:
定义 normBound
  签名: : 整数
  定义体: let n := Fintype.card ι
  let i : ι := Nonempty.some bS.index_nonempty
  let m : Int :=
    Finset.max'
      (Finset.univ.image fun ijk : ι × ι × ι =>
        abv (Algebra.leftMulMatrix bS (bS ijk.1) ijk.2.1 ijk.2.2))
      ⟨_, Finset.mem_image.mpr ⟨⟨i, i, i⟩, Finset.mem_univ _, rfl⟩⟩
  Nat.factorial n • (n • m) ^ n

Depends on / 依赖: Algebra, Algebra.leftMulMatrix, Finset, Finset.max, Finset.mem_image.mpr, Finset.mem_univ, Finset.univ.image, Fintype, Fintype.card, Nat.factorial, Nonempty, Nonempty.some, bS.index_nonempty, factorial, index_nonempty, leftMulMatrix, mem_image, mem_univ
-/
noncomputable def normBound : Int :=
  let n := Fintype.card ι
  let i : ι := Nonempty.some bS.index_nonempty
  let m : Int :=
    Finset.max'
      (Finset.univ.image fun ijk : ι × ι × ι =>
        abv (Algebra.leftMulMatrix bS (bS ijk.1) ijk.2.1 ijk.2.2))
      ⟨_, Finset.mem_image.mpr ⟨⟨i, i, i⟩, Finset.mem_univ _, rfl⟩⟩
  Nat.factorial n • (n • m) ^ n

/--
theorem `normBound_pos` / 定理 `normBound_pos`

English:
theorem normBound_pos
  statement: 0 < normBound abv bS
  proof: by
  obtain ⟨i, j, k, hijk⟩ : exists i j k, Algebra.leftMulMatrix bS (bS i) j k != 0 := by
    by_contra! h
    obtain ⟨i⟩ := bS.index_nonempty
    apply bS.ne_zero i
    apply
      (injective_iff_map_eq_zero (Algebra.leftMulMatrix bS)).mp (Algebra.leftMulMatrix_injective bS)
    ext j k
    simp [h]
  simp only [normBound, Algebra.smul_def, eq_natCast]
  apply mul_pos (Int.natCast_pos.mpr (Nat.factorial_pos _))
  refine pow_pos (mul_pos (Int.natCast_pos.mpr (Fintype.card_pos_iff.mpr ⟨i⟩)) ?_) _
  refine lt_of_lt_of_le (abv.pos hijk) (Finset.le_max' _ _ ?_)
  exact Finset.mem_image.mpr ⟨⟨i, j, k⟩, Finset.mem_univ _, rfl⟩

中文:
定理 normBound_pos
  结论: 0 < normBound abv bS
  证明: by
  obtain ⟨i, j, k, hijk⟩ : exists i j k, Algebra.leftMulMatrix bS (bS i) j k != 0 := by
    by_contra! h
    obtain ⟨i⟩ := bS.index_nonempty
    apply bS.ne_zero i
    apply
      (injective_iff_map_eq_zero (Algebra.leftMulMatrix bS)).mp (Algebra.leftMulMatrix_injective bS)
    ext j k
    simp [h]
  simp only [normBound, Algebra.smul_def, eq_natCast]
  apply mul_pos (Int.natCast_pos.mpr (Nat.factorial_pos _))
  refine pow_pos (mul_pos (Int.natCast_pos.mpr (Fintype.card_pos_iff.mpr ⟨i⟩)) ?_) _
  refine lt_of_lt_of_le (abv.pos hijk) (Finset.le_max' _ _ ?_)
  exact Finset.mem_image.mpr ⟨⟨i, j, k⟩, Finset.mem_univ _, rfl⟩

Depends on / 依赖: Algebra, Algebra.leftMulMatrix, Algebra.leftMulMatrix_injective, Algebra.smul_def, Fintype, Fintype.card_pos_iff.mpr, Int.natCast_pos.mpr, Nat.factorial_pos, abv.pos, bS.index_nonempty, bS.ne_zero, card_pos_iff, eq_natCast, factorial_pos, index_nonempty, injective_iff_map_eq_zero, leftMulMatrix, leftMulMatrix_injective, lt_of_lt_of_le, mul_pos
-/
theorem normBound_pos : 0 < normBound abv bS := by
  obtain ⟨i, j, k, hijk⟩ : exists i j k, Algebra.leftMulMatrix bS (bS i) j k != 0 := by
    by_contra! h
    obtain ⟨i⟩ := bS.index_nonempty
    apply bS.ne_zero i
    apply
      (injective_iff_map_eq_zero (Algebra.leftMulMatrix bS)).mp (Algebra.leftMulMatrix_injective bS)
    ext j k
    simp [h]
  simp only [normBound, Algebra.smul_def, eq_natCast]
  apply mul_pos (Int.natCast_pos.mpr (Nat.factorial_pos _))
  refine pow_pos (mul_pos (Int.natCast_pos.mpr (Fintype.card_pos_iff.mpr ⟨i⟩)) ?_) _
  refine lt_of_lt_of_le (abv.pos hijk) (Finset.le_max' _ _ ?_)
  exact Finset.mem_image.mpr ⟨⟨i, j, k⟩, Finset.mem_univ _, rfl⟩

/--
theorem `norm_le` / 定理 `norm_le`

English:
theorem norm_le
  given: (a : S) {y : Int} (hy : forall k, abv (bS.repr a k) <= y)
  proof: by
  conv_lhs => rw [← bS.sum_repr a]
  rw [Algebra.norm_apply]; rw [← LinearMap.det_toMatrix bS]
  simp only [map_sum, map_smul, map_sum, map_smul,
    normBound, smul_mul_assoc, ← mul_pow]
  convert! Matrix.det_sum_smul_le Finset.univ _ hy using 3
  · rw [Finset.card_univ, smul_mul_assoc, mul_comm]
  · intro i j k
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨⟨i, j, k⟩, Finset.mem_univ _, rfl⟩

中文:
定理 norm_le
  条件: (a : S) {y : 整数} (hy : 对任意 k, abv (bS.repr a k) <= y)
  证明: by
  conv_lhs => rw [← bS.sum_repr a]
  rw [Algebra.norm_apply]; rw [← LinearMap.det_toMatrix bS]
  simp only [map_sum, map_smul, map_sum, map_smul,
    normBound, smul_mul_assoc, ← mul_pow]
  convert! Matrix.det_sum_smul_le Finset.univ _ hy using 3
  · rw [Finset.card_univ, smul_mul_assoc, mul_comm]
  · intro i j k
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨⟨i, j, k⟩, Finset.mem_univ _, rfl⟩

Depends on / 依赖: Algebra, Algebra.norm_apply, Finset, Finset.card_univ, Finset.le_max, Finset.mem_image.mpr, Finset.mem_univ, Finset.univ, LinearMap, LinearMap.det_toMatrix, Matrix, Matrix.det_sum_smul_le, bS.sum_repr, card_univ, conv_lhs, convert, det_sum_smul_le, det_toMatrix, le_max, map_smul
-/
theorem norm_le (a : S) {y : Int} (hy : forall k, abv (bS.repr a k) <= y) :
    abv (Algebra.norm R a) <= normBound abv bS * y ^ Fintype.card ι := by
  conv_lhs => rw [← bS.sum_repr a]
  rw [Algebra.norm_apply]; rw [← LinearMap.det_toMatrix bS]
  simp only [map_sum, map_smul, map_sum, map_smul,
    normBound, smul_mul_assoc, ← mul_pow]
  convert! Matrix.det_sum_smul_le Finset.univ _ hy using 3
  · rw [Finset.card_univ, smul_mul_assoc, mul_comm]
  · intro i j k
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨⟨i, j, k⟩, Finset.mem_univ _, rfl⟩

/--
theorem `norm_lt` / 定理 `norm_lt`

English:
theorem norm_lt
  statement: {T : Type*} [Ring T] [LinearOrder T] [IsStrictOrderedRing T] (a : S) {y : T}
  proof: by
  obtain ⟨i⟩ := bS.index_nonempty
  have him : (Finset.univ.image fun k => abv (bS.repr a k)).Nonempty :=
    ⟨_, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  set y' : Int := Finset.max' _ him with y'_def
  have hy' : forall k, abv (bS.repr a k) <= y' := by
    intro k
    exact @Finset.le_max' Int _ _ _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  have : (y' : T) < y := by
    rw [y'_def]; rw [← Finset.max'_image (show Monotone (_ : Int -> T) from fun x y h => Int.cast_le.mpr h)
          _ (him.image _)]
    apply (Finset.max'_lt_iff _ (him.image _)).mpr
    simp only [Finset.mem_image]
    rintro _ ⟨x, ⟨k, -, rfl⟩, rfl⟩
    exact hy k
  have y'_nonneg : 0 <= y' := le_trans (abv.nonneg _) (hy' i)
  apply (Int.cast_le.mpr (norm_le abv bS a hy')).trans_lt
  simp only [Int.cast_mul, Int.cast_pow]
  apply mul_lt_mul' le_rfl
  · exact pow_lt_pow_left₀ this (by positivity) (@Fintype.card_ne_zero _ _ ⟨i⟩)
  · positivity
  · exact Int.cast_pos.mpr (normBound_pos abv bS)

中文:
定理 norm_lt
  结论: {T : 类型} [环 T] [线性序 T] [是StrictOrdered环 T] (a : S) {y : T}
  证明: by
  obtain ⟨i⟩ := bS.index_nonempty
  have him : (Finset.univ.image fun k => abv (bS.repr a k)).Nonempty :=
    ⟨_, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  set y' : Int := Finset.max' _ him with y'_def
  have hy' : forall k, abv (bS.repr a k) <= y' := by
    intro k
    exact @Finset.le_max' Int _ _ _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  have : (y' : T) < y := by
    rw [y'_def]; rw [← Finset.max'_image (show Monotone (_ : Int -> T) from fun x y h => Int.cast_le.mpr h)
          _ (him.image _)]
    apply (Finset.max'_lt_iff _ (him.image _)).mpr
    simp only [Finset.mem_image]
    rintro _ ⟨x, ⟨k, -, rfl⟩, rfl⟩
    exact hy k
  have y'_nonneg : 0 <= y' := le_trans (abv.nonneg _) (hy' i)
  apply (Int.cast_le.mpr (norm_le abv bS a hy')).trans_lt
  simp only [Int.cast_mul, Int.cast_pow]
  apply mul_lt_mul' le_rfl
  · exact pow_lt_pow_left₀ this (by positivity) (@Fintype.card_ne_zero _ _ ⟨i⟩)
  · positivity
  · exact Int.cast_pos.mpr (normBound_pos abv bS)

Depends on / 依赖: Finset, Finset.le_max, Finset.max, Finset.mem_image.mpr, Finset.mem_univ, Finset.univ.image, Int.cast_le.mpr, Monotone, Nonempty, _def, _image, bS.index_nonempty, bS.repr, cast_le, him.image, index_nonempty, le_max, mem_image, mem_univ
-/
theorem norm_lt {T : Type*} [Ring T] [LinearOrder T] [IsStrictOrderedRing T] (a : S) {y : T}
    (hy : forall k, (abv (bS.repr a k) : T) < y) :
    (abv (Algebra.norm R a) : T) < normBound abv bS * y ^ Fintype.card ι := by
  obtain ⟨i⟩ := bS.index_nonempty
  have him : (Finset.univ.image fun k => abv (bS.repr a k)).Nonempty :=
    ⟨_, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  set y' : Int := Finset.max' _ him with y'_def
  have hy' : forall k, abv (bS.repr a k) <= y' := by
    intro k
    exact @Finset.le_max' Int _ _ _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  have : (y' : T) < y := by
    rw [y'_def]; rw [← Finset.max'_image (show Monotone (_ : Int -> T) from fun x y h => Int.cast_le.mpr h)
          _ (him.image _)]
    apply (Finset.max'_lt_iff _ (him.image _)).mpr
    simp only [Finset.mem_image]
    rintro _ ⟨x, ⟨k, -, rfl⟩, rfl⟩
    exact hy k
  have y'_nonneg : 0 <= y' := le_trans (abv.nonneg _) (hy' i)
  apply (Int.cast_le.mpr (norm_le abv bS a hy')).trans_lt
  simp only [Int.cast_mul, Int.cast_pow]
  apply mul_lt_mul' le_rfl
  · exact pow_lt_pow_left₀ this (by positivity) (@Fintype.card_ne_zero _ _ ⟨i⟩)
  · positivity
  · exact Int.cast_pos.mpr (normBound_pos abv bS)


/--
theorem `exists_min` / 定理 `exists_min`

English:
theorem exists_min
  given: (I : (Ideal S)⁰)
  proof: by
  obtain ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩, min⟩ := @Int.exists_least_of_bdd
      (fun a => exists b in (I : Ideal S), b != (0 : S) ∧ abv (Algebra.norm R b) = a)
    (by
      use 0
      rintro _ ⟨b, _, _, rfl⟩
      apply abv.nonneg)
    (by
      obtain ⟨b, b_mem, b_ne_zero⟩ := (I : Ideal S).ne_bot_iff.mp (nonZeroDivisors.coe_ne_zero I)
      exact ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩⟩)
  refine ⟨b, b_mem, b_ne_zero, ?_⟩
  intro c hc lt
  contrapose! lt with c_ne_zero
  exact min _ ⟨c, hc, c_ne_zero, rfl⟩

中文:
定理 存在_min
  条件: (I : (理想 S)⁰)
  证明: by
  obtain ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩, min⟩ := @Int.exists_least_of_bdd
      (fun a => exists b in (I : Ideal S), b != (0 : S) ∧ abv (Algebra.norm R b) = a)
    (by
      use 0
      rintro _ ⟨b, _, _, rfl⟩
      apply abv.nonneg)
    (by
      obtain ⟨b, b_mem, b_ne_zero⟩ := (I : Ideal S).ne_bot_iff.mp (nonZeroDivisors.coe_ne_zero I)
      exact ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩⟩)
  refine ⟨b, b_mem, b_ne_zero, ?_⟩
  intro c hc lt
  contrapose! lt with c_ne_zero
  exact min _ ⟨c, hc, c_ne_zero, rfl⟩

Depends on / 依赖: Algebra, Algebra.norm, Int.exists_least_of_bdd, abv.nonneg, b_mem, b_ne_zero, c_ne_zero, coe_ne_zero, contrapose, exists_least_of_bdd, ne_bot_iff, ne_bot_iff.mp, nonZeroDivisors, nonZeroDivisors.coe_ne_zero, nonneg
-/
theorem exists_min (I : (Ideal S)⁰) :
    exists b in (I : Ideal S),
      b != 0 ∧ forall c in (I : Ideal S), abv (Algebra.norm R c) < abv (Algebra.norm R b) -> c =
      (0 : S) := by
  obtain ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩, min⟩ := @Int.exists_least_of_bdd
      (fun a => exists b in (I : Ideal S), b != (0 : S) ∧ abv (Algebra.norm R b) = a)
    (by
      use 0
      rintro _ ⟨b, _, _, rfl⟩
      apply abv.nonneg)
    (by
      obtain ⟨b, b_mem, b_ne_zero⟩ := (I : Ideal S).ne_bot_iff.mp (nonZeroDivisors.coe_ne_zero I)
      exact ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩⟩)
  refine ⟨b, b_mem, b_ne_zero, ?_⟩
  intro c hc lt
  contrapose! lt with c_ne_zero
  exact min _ ⟨c, hc, c_ne_zero, rfl⟩

section IsAdmissible

variable {abv}
variable (adm : abv.IsAdmissible)

/--
Definition of `cardM` / `cardM` 的定义

English:
definition cardM
  signature: : Nat
  body: adm.card (normBound abv bS ^ (-1 / Fintype.card ι : Real)) ^ Fintype.card ι

中文:
定义 cardM
  签名: : 自然数
  定义体: adm.card (normBound abv bS ^ (-1 / Fintype.card ι : Real)) ^ Fintype.card ι

Depends on / 依赖: Fintype, Fintype.card, adm.card, normBound
-/
noncomputable def cardM : Nat :=
  adm.card (normBound abv bS ^ (-1 / Fintype.card ι : Real)) ^ Fintype.card ι

variable [Infinite R]

/--
Definition of `distinctElems` / `distinctElems` 的定义

English:
definition distinctElems
  signature: : Fin (cardM bS adm).succ ↪ R
  body: Fin.valEmbedding.trans (Infinite.natEmbedding R)

中文:
定义 distinctElems
  签名: : 有限集 (cardM bS adm).succ ↪ R
  定义体: Fin.valEmbedding.trans (Infinite.natEmbedding R)

Depends on / 依赖: Fin.valEmbedding.trans, Infinite, Infinite.natEmbedding, natEmbedding, valEmbedding
-/
noncomputable def distinctElems : Fin (cardM bS adm).succ ↪ R :=
  Fin.valEmbedding.trans (Infinite.natEmbedding R)

variable [DecidableEq R]

/--
Definition of `finsetApprox` / `finsetApprox` 的定义

English:
definition finsetApprox
  signature: : Finset R
  body: (Finset.univ.image fun xy : _ × _ => distinctElems bS adm xy.1 - distinctElems bS adm xy.2).erase
    0

中文:
定义 finsetApprox
  签名: : 有限集 R
  定义体: (Finset.univ.image fun xy : _ × _ => distinctElems bS adm xy.1 - distinctElems bS adm xy.2).erase
    0

Depends on / 依赖: Finset, Finset.univ.image, distinctElems
-/
noncomputable def finsetApprox : Finset R :=
  (Finset.univ.image fun xy : _ × _ => distinctElems bS adm xy.1 - distinctElems bS adm xy.2).erase
    0

/--
theorem `finsetApprox.zero_notMem` / 定理 `finsetApprox.zero_notMem`

English:
theorem finsetApprox.zero_notMem
  statement: (0 : R) ∉ finsetApprox bS adm
  proof: Finset.notMem_erase _ _

@[simp]

中文:
定理 finsetApprox.zero_notMem
  结论: (0 : R) ∉ finsetApprox bS adm
  证明: Finset.notMem_erase _ _

@[simp]

Depends on / 依赖: Finset, Finset.notMem_erase, notMem_erase
-/
theorem finsetApprox.zero_notMem : (0 : R) ∉ finsetApprox bS adm :=
  Finset.notMem_erase _ _

@[simp]
/--
theorem `mem_finsetApprox` / 定理 `mem_finsetApprox`

English:
theorem mem_finsetApprox
  given: {x : R}
  proof: by
  simp only [finsetApprox, Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hx, ⟨i, j⟩, _, rfl⟩
    refine ⟨i, j, ?_, rfl⟩
    rintro rfl
    simp at hx
  · rintro ⟨i, j, hij, rfl⟩
    refine ⟨?_, ⟨i, j⟩, Finset.mem_univ _, rfl⟩
    rw [Ne]; rw [sub_eq_zero]
    exact fun h => hij ((distinctElems bS adm).injective h)

中文:
定理 mem_finsetApprox
  条件: {x : R}
  证明: by
  simp only [finsetApprox, Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hx, ⟨i, j⟩, _, rfl⟩
    refine ⟨i, j, ?_, rfl⟩
    rintro rfl
    simp at hx
  · rintro ⟨i, j, hij, rfl⟩
    refine ⟨?_, ⟨i, j⟩, Finset.mem_univ _, rfl⟩
    rw [Ne]; rw [sub_eq_zero]
    exact fun h => hij ((distinctElems bS adm).injective h)

Depends on / 依赖: Finset, Finset.mem_erase, Finset.mem_image, Finset.mem_univ, distinctElems, finsetApprox, injective, mem_erase, mem_image, mem_univ, sub_eq_zero
-/
theorem mem_finsetApprox {x : R} :
    x in finsetApprox bS adm ↔ exists i j, i != j ∧ distinctElems bS adm i - distinctElems bS adm j =
    x := by
  simp only [finsetApprox, Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hx, ⟨i, j⟩, _, rfl⟩
    refine ⟨i, j, ?_, rfl⟩
    rintro rfl
    simp at hx
  · rintro ⟨i, j, hij, rfl⟩
    refine ⟨?_, ⟨i, j⟩, Finset.mem_univ _, rfl⟩
    rw [Ne]; rw [sub_eq_zero]
    exact fun h => hij ((distinctElems bS adm).injective h)

section Real

open Real

attribute [-instance] Real.decidableEq

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `exists_mem_finsetApprox` / 定理 `exists_mem_finsetApprox`

English:
theorem exists_mem_finsetApprox
  given: (a : S) {b} (hb : b != (0 : R))
  proof: by
  have dim_pos := Fintype.card_pos_iff.mpr bS.index_nonempty
  set ε : Real := normBound abv bS ^ (-1 / Fintype.card ι : Real) with ε_eq
  have hε : 0 < ε := Real.rpow_pos_of_pos (Int.cast_pos.mpr (normBound_pos abv bS)) _
  have ε_le : (normBound abv bS : Real) * (abv b • ε) ^ (Fintype.card ι : Real)
                <= abv b ^ (Fintype.card ι : Real) := by
    have := normBound_pos abv bS
    have := abv.nonneg b
    rw [ε_eq]; rw [Algebra.smul_def]; rw [eq_intCast]; rw [mul_rpow]; rw [← rpow_mul]; rw [div_mul_cancel₀]; rw [rpow_neg_one]; rw [mul_left_comm]; rw [mul_inv_cancel₀]; rw [mul_one]; rw [rpow_natCast] <;>
      try norm_cast; lia
    · exact Int.cast_nonneg this
    · linarith
  set μ : Fin (cardM bS adm).succ ↪ R := distinctElems bS adm
  let s : ι ->₀ R := bS.repr a
  have s_eq : forall i, s i = bS.repr a i := fun i => rfl
  let qs : Fin (cardM bS adm).succ -> ι -> R := fun j i => μ j * s i / b
  let rs : Fin (cardM bS adm).succ -> ι -> R := fun j i => μ j * s i % b
  have r_eq : forall j i, rs j i = μ j * s i % b := fun i j => rfl
  have μ_eq : forall i j, μ j * s i = b * qs j i + rs j i := by
    intro i j
    rw [r_eq]; rw [EuclideanDomain.div_add_mod]
  have μ_mul_a_eq : forall j, μ j • a = b • ∑ i, qs j i • bS i + ∑ i, rs j i • bS i := by
    intro j
    rw [← bS.sum_repr a]
    simp only [μ, qs, rs, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← s_eq]; rw [← mul_smul]; rw [μ_eq]; rw [add_smul]; rw [mul_smul]; rw [← μ_eq]
  obtain ⟨j, k, j_ne_k, hjk⟩ := adm.exists_approx hε hb fun j i => μ j * s i
  have hjk' : forall i, (abv (rs k i - rs j i) : Real) < abv b • ε := by simpa only [r_eq] using hjk
  let q := ∑ i, (qs k i - qs j i) • bS i
  set r := μ k - μ j with r_eq
  refine ⟨q, r, (mem_finsetApprox bS adm).mpr ?_, ?_⟩
  · exact ⟨k, j, j_ne_k.symm, rfl⟩
  have : r • a - b • q = ∑ x : ι, (rs k x • bS x - rs j x • bS x) := by
    simp only [q, r_eq, sub_smul, μ_mul_a_eq, Finset.smul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, smul_sub]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [this]; rw [Algebra.norm_algebraMap_of_basis bS]; rw [abv.map_pow]
  refine Int.cast_lt.mp ((norm_lt abv bS _ fun i => lt_of_le_of_lt ?_ (hjk' i)).trans_le ?_)
  · apply le_of_eq
    congr
    simp_rw [map_sum, map_sub, map_smul, Finset.sum_apply',
      Finsupp.sub_apply, Finsupp.smul_apply, Finset.sum_sub_distrib, Basis.repr_self_apply,
      smul_eq_mul, mul_boole, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · exact mod_cast ε_le

中文:
定理 存在_mem_finsetApprox
  条件: (a : S) {b} (hb : b != (0 : R))
  证明: by
  have dim_pos := Fintype.card_pos_iff.mpr bS.index_nonempty
  set ε : Real := normBound abv bS ^ (-1 / Fintype.card ι : Real) with ε_eq
  have hε : 0 < ε := Real.rpow_pos_of_pos (Int.cast_pos.mpr (normBound_pos abv bS)) _
  have ε_le : (normBound abv bS : Real) * (abv b • ε) ^ (Fintype.card ι : Real)
                <= abv b ^ (Fintype.card ι : Real) := by
    have := normBound_pos abv bS
    have := abv.nonneg b
    rw [ε_eq]; rw [Algebra.smul_def]; rw [eq_intCast]; rw [mul_rpow]; rw [← rpow_mul]; rw [div_mul_cancel₀]; rw [rpow_neg_one]; rw [mul_left_comm]; rw [mul_inv_cancel₀]; rw [mul_one]; rw [rpow_natCast] <;>
      try norm_cast; lia
    · exact Int.cast_nonneg this
    · linarith
  set μ : Fin (cardM bS adm).succ ↪ R := distinctElems bS adm
  let s : ι ->₀ R := bS.repr a
  have s_eq : forall i, s i = bS.repr a i := fun i => rfl
  let qs : Fin (cardM bS adm).succ -> ι -> R := fun j i => μ j * s i / b
  let rs : Fin (cardM bS adm).succ -> ι -> R := fun j i => μ j * s i % b
  have r_eq : forall j i, rs j i = μ j * s i % b := fun i j => rfl
  have μ_eq : forall i j, μ j * s i = b * qs j i + rs j i := by
    intro i j
    rw [r_eq]; rw [EuclideanDomain.div_add_mod]
  have μ_mul_a_eq : forall j, μ j • a = b • ∑ i, qs j i • bS i + ∑ i, rs j i • bS i := by
    intro j
    rw [← bS.sum_repr a]
    simp only [μ, qs, rs, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← s_eq]; rw [← mul_smul]; rw [μ_eq]; rw [add_smul]; rw [mul_smul]; rw [← μ_eq]
  obtain ⟨j, k, j_ne_k, hjk⟩ := adm.exists_approx hε hb fun j i => μ j * s i
  have hjk' : forall i, (abv (rs k i - rs j i) : Real) < abv b • ε := by simpa only [r_eq] using hjk
  let q := ∑ i, (qs k i - qs j i) • bS i
  set r := μ k - μ j with r_eq
  refine ⟨q, r, (mem_finsetApprox bS adm).mpr ?_, ?_⟩
  · exact ⟨k, j, j_ne_k.symm, rfl⟩
  have : r • a - b • q = ∑ x : ι, (rs k x • bS x - rs j x • bS x) := by
    simp only [q, r_eq, sub_smul, μ_mul_a_eq, Finset.smul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, smul_sub]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [this]; rw [Algebra.norm_algebraMap_of_basis bS]; rw [abv.map_pow]
  refine Int.cast_lt.mp ((norm_lt abv bS _ fun i => lt_of_le_of_lt ?_ (hjk' i)).trans_le ?_)
  · apply le_of_eq
    congr
    simp_rw [map_sum, map_sub, map_smul, Finset.sum_apply',
      Finsupp.sub_apply, Finsupp.smul_apply, Finset.sum_sub_distrib, Basis.repr_self_apply,
      smul_eq_mul, mul_boole, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · exact mod_cast ε_le

Depends on / 依赖: Algebra, Algebra.smul_def, Fintype, Fintype.card, Fintype.card_pos_iff.mpr, Int.cast_pos.mpr, Real.rpow_pos_of_pos, abv.nonneg, bS.index_nonempty, card_pos_iff, cast_pos, dim_pos, eq_intCast, index_nonempty, mul_rpow, nonneg, normBound, normBound_pos, rpow_mul, rpow_pos_of_pos
-/
theorem exists_mem_finsetApprox (a : S) {b} (hb : b != (0 : R)) :
    exists q : S,
      exists r in finsetApprox bS adm, abv (Algebra.norm R (r • a - b • q)) <
      abv (Algebra.norm R (algebraMap R S b)) := by
  have dim_pos := Fintype.card_pos_iff.mpr bS.index_nonempty
  set ε : Real := normBound abv bS ^ (-1 / Fintype.card ι : Real) with ε_eq
  have hε : 0 < ε := Real.rpow_pos_of_pos (Int.cast_pos.mpr (normBound_pos abv bS)) _
  have ε_le : (normBound abv bS : Real) * (abv b • ε) ^ (Fintype.card ι : Real)
                <= abv b ^ (Fintype.card ι : Real) := by
    have := normBound_pos abv bS
    have := abv.nonneg b
    rw [ε_eq]; rw [Algebra.smul_def]; rw [eq_intCast]; rw [mul_rpow]; rw [← rpow_mul]; rw [div_mul_cancel₀]; rw [rpow_neg_one]; rw [mul_left_comm]; rw [mul_inv_cancel₀]; rw [mul_one]; rw [rpow_natCast] <;>
      try norm_cast; lia
    · exact Int.cast_nonneg this
    · linarith
  set μ : Fin (cardM bS adm).succ ↪ R := distinctElems bS adm
  let s : ι ->₀ R := bS.repr a
  have s_eq : forall i, s i = bS.repr a i := fun i => rfl
  let qs : Fin (cardM bS adm).succ -> ι -> R := fun j i => μ j * s i / b
  let rs : Fin (cardM bS adm).succ -> ι -> R := fun j i => μ j * s i % b
  have r_eq : forall j i, rs j i = μ j * s i % b := fun i j => rfl
  have μ_eq : forall i j, μ j * s i = b * qs j i + rs j i := by
    intro i j
    rw [r_eq]; rw [EuclideanDomain.div_add_mod]
  have μ_mul_a_eq : forall j, μ j • a = b • ∑ i, qs j i • bS i + ∑ i, rs j i • bS i := by
    intro j
    rw [← bS.sum_repr a]
    simp only [μ, qs, rs, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← s_eq]; rw [← mul_smul]; rw [μ_eq]; rw [add_smul]; rw [mul_smul]; rw [← μ_eq]
  obtain ⟨j, k, j_ne_k, hjk⟩ := adm.exists_approx hε hb fun j i => μ j * s i
  have hjk' : forall i, (abv (rs k i - rs j i) : Real) < abv b • ε := by simpa only [r_eq] using hjk
  let q := ∑ i, (qs k i - qs j i) • bS i
  set r := μ k - μ j with r_eq
  refine ⟨q, r, (mem_finsetApprox bS adm).mpr ?_, ?_⟩
  · exact ⟨k, j, j_ne_k.symm, rfl⟩
  have : r • a - b • q = ∑ x : ι, (rs k x • bS x - rs j x • bS x) := by
    simp only [q, r_eq, sub_smul, μ_mul_a_eq, Finset.smul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, smul_sub]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [this]; rw [Algebra.norm_algebraMap_of_basis bS]; rw [abv.map_pow]
  refine Int.cast_lt.mp ((norm_lt abv bS _ fun i => lt_of_le_of_lt ?_ (hjk' i)).trans_le ?_)
  · apply le_of_eq
    congr
    simp_rw [map_sum, map_sub, map_smul, Finset.sum_apply',
      Finsupp.sub_apply, Finsupp.smul_apply, Finset.sum_sub_distrib, Basis.repr_self_apply,
      smul_eq_mul, mul_boole, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · exact mod_cast ε_le

/--
theorem `exists_mem_finset_approx'` / 定理 `exists_mem_finset_approx'`

English:
theorem exists_mem_finset_approx'
  given: [Algebra.IsAlgebraic R S] (a : S) {b : S} (hb : b != 0)
  proof: by
  obtain ⟨a', b', hb', h⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul R a hb
  obtain ⟨q, r, hr, hqr⟩ := exists_mem_finsetApprox bS adm a' hb'
  refine ⟨q, r, hr, ?_⟩
  refine
    lt_of_mul_lt_mul_left ?_ (show 0 <= abv (Algebra.norm R (algebraMap R S b')) from abv.nonneg _)
  refine
    lt_of_le_of_lt (le_of_eq ?_)
      (mul_lt_mul hqr le_rfl (abv.pos ((Algebra.norm_ne_zero_iff_of_basis bS).mpr hb))
        (abv.nonneg _))
  rw [← abv.map_mul]; rw [← map_mul]; rw [← abv.map_mul]; rw [← map_mul]; rw [← Algebra.smul_def]; rw [smul_sub b']; rw [sub_mul]; rw [smul_comm]; rw [h]; rw [mul_comm b a']; rw [Algebra.smul_mul_assoc r a' b]; rw [Algebra.smul_mul_assoc b' q b]

中文:
定理 存在_mem_finset_approx'
  条件: [代数.是代数 R S] (a : S) {b : S} (hb : b != 0)
  证明: by
  obtain ⟨a', b', hb', h⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul R a hb
  obtain ⟨q, r, hr, hqr⟩ := exists_mem_finsetApprox bS adm a' hb'
  refine ⟨q, r, hr, ?_⟩
  refine
    lt_of_mul_lt_mul_left ?_ (show 0 <= abv (Algebra.norm R (algebraMap R S b')) from abv.nonneg _)
  refine
    lt_of_le_of_lt (le_of_eq ?_)
      (mul_lt_mul hqr le_rfl (abv.pos ((Algebra.norm_ne_zero_iff_of_basis bS).mpr hb))
        (abv.nonneg _))
  rw [← abv.map_mul]; rw [← map_mul]; rw [← abv.map_mul]; rw [← map_mul]; rw [← Algebra.smul_def]; rw [smul_sub b']; rw [sub_mul]; rw [smul_comm]; rw [h]; rw [mul_comm b a']; rw [Algebra.smul_mul_assoc r a' b]; rw [Algebra.smul_mul_assoc b' q b]

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.exists_smul_eq_mul, Algebra.norm, Algebra.norm_ne_zero_iff_of_basis, Algebra.smul_def, IsAlgebraic, abv.map_mul, abv.nonneg, abv.pos, algebraMap, exists_mem_finsetApprox, exists_smul_eq_mul, le_of_eq, le_rfl, lt_of_le_of_lt, lt_of_mul_lt_mul_left, map_mul, mul_lt_mul, nonneg, norm_ne_zero_iff_of_basis
-/
theorem exists_mem_finset_approx' [Algebra.IsAlgebraic R S] (a : S) {b : S} (hb : b != 0) :
    exists q : S,
      exists r in finsetApprox bS adm, abv (Algebra.norm R (r • a - q * b)) < abv (Algebra.norm R b) := by
  obtain ⟨a', b', hb', h⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul R a hb
  obtain ⟨q, r, hr, hqr⟩ := exists_mem_finsetApprox bS adm a' hb'
  refine ⟨q, r, hr, ?_⟩
  refine
    lt_of_mul_lt_mul_left ?_ (show 0 <= abv (Algebra.norm R (algebraMap R S b')) from abv.nonneg _)
  refine
    lt_of_le_of_lt (le_of_eq ?_)
      (mul_lt_mul hqr le_rfl (abv.pos ((Algebra.norm_ne_zero_iff_of_basis bS).mpr hb))
        (abv.nonneg _))
  rw [← abv.map_mul]; rw [← map_mul]; rw [← abv.map_mul]; rw [← map_mul]; rw [← Algebra.smul_def]; rw [smul_sub b']; rw [sub_mul]; rw [smul_comm]; rw [h]; rw [mul_comm b a']; rw [Algebra.smul_mul_assoc r a' b]; rw [Algebra.smul_mul_assoc b' q b]

end Real

/--
theorem `prod_finsetApprox_ne_zero` / 定理 `prod_finsetApprox_ne_zero`

English:
theorem prod_finsetApprox_ne_zero
  statement: algebraMap R S (∏ m in finsetApprox bS adm, m) != 0
  proof: by
  refine mt ((injective_iff_map_eq_zero _).mp bS.algebraMap_injective _) ?_
  simp only [Finset.prod_eq_zero_iff, not_exists]
  rintro x ⟨hx, rfl⟩
  exact finsetApprox.zero_notMem bS adm hx

中文:
定理 prod_finsetApprox_ne_zero
  结论: algebraMap R S (∏ m in finsetApprox bS adm, m) != 0
  证明: by
  refine mt ((injective_iff_map_eq_zero _).mp bS.algebraMap_injective _) ?_
  simp only [Finset.prod_eq_zero_iff, not_exists]
  rintro x ⟨hx, rfl⟩
  exact finsetApprox.zero_notMem bS adm hx

Depends on / 依赖: Finset, Finset.prod_eq_zero_iff, algebraMap_injective, bS.algebraMap_injective, finsetApprox, finsetApprox.zero_notMem, injective_iff_map_eq_zero, not_exists, prod_eq_zero_iff, zero_notMem
-/
theorem prod_finsetApprox_ne_zero : algebraMap R S (∏ m in finsetApprox bS adm, m) != 0 := by
  refine mt ((injective_iff_map_eq_zero _).mp bS.algebraMap_injective _) ?_
  simp only [Finset.prod_eq_zero_iff, not_exists]
  rintro x ⟨hx, rfl⟩
  exact finsetApprox.zero_notMem bS adm hx

/--
theorem `ne_bot_of_prod_finsetApprox_mem` / 定理 `ne_bot_of_prod_finsetApprox_mem`

English:
theorem ne_bot_of_prod_finsetApprox_mem
  statement: (J : Ideal S)
  proof: (Submodule.ne_bot_iff _).mpr ⟨_, h, prod_finsetApprox_ne_zero _ _⟩

中文:
定理 ne_bot_of_prod_finsetApprox_mem
  结论: (J : 理想 S)
  证明: (Submodule.ne_bot_iff _).mpr ⟨_, h, prod_finsetApprox_ne_zero _ _⟩

Depends on / 依赖: Submodule, Submodule.ne_bot_iff, ne_bot_iff, prod_finsetApprox_ne_zero
-/
theorem ne_bot_of_prod_finsetApprox_mem (J : Ideal S)
    (h : algebraMap _ _ (∏ m in finsetApprox bS adm, m) in J) : J != ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, h, prod_finsetApprox_ne_zero _ _⟩

set_option linter.overlappingInstances false

/--
theorem `exists_mk0_eq_mk0` / 定理 `exists_mk0_eq_mk0`

English:
theorem exists_mk0_eq_mk0
  given: [IsDedekindDomain S] [Algebra.IsAlgebraic R S] (I : (Ideal S)⁰)
  proof: by
  set M := ∏ m in finsetApprox bS adm, m
  have hM : algebraMap R S M != 0 := prod_finsetApprox_ne_zero bS adm
  obtain ⟨b, b_mem, b_ne_zero, b_min⟩ := exists_min abv I
  suffices Ideal.span {b} ∣ Ideal.span {algebraMap _ _ M} * I.1 by
    obtain ⟨J, hJ⟩ := this
    refine ⟨⟨J, ?_⟩, ?_, ?_⟩
    · rw [mem_nonZeroDivisors_iff_ne_zero]
      rintro rfl
      rw [Ideal.zero_eq_bot]; rw [Ideal.mul_bot] at hJ
      exact hM (Ideal.span_singleton_eq_bot.mp (I.2.2 _ hJ))
    · rw [ClassGroup.mk0_eq_mk0_iff]
      exact ⟨algebraMap _ _ M, b, hM, b_ne_zero, hJ⟩
    rw [← SetLike.mem_coe]; rw [← Set.singleton_subset_iff]; rw [← Ideal.span_le]; rw [← Ideal.dvd_iff_le]
    apply (mul_dvd_mul_iff_left _).mp _
    swap; · exact mt Ideal.span_singleton_eq_bot.mp b_ne_zero
    rw [Subtype.coe_mk]; rw [Ideal.dvd_iff_le]; rw [← hJ]; rw [mul_comm]
    apply Ideal.mul_mono le_rfl
    rw [Ideal.span_le]; rw [Set.singleton_subset_iff]
    exact b_mem
  rw [Ideal.dvd_iff_le]; rw [Ideal.mul_le]
  intro r' hr' a ha
  rw [Ideal.mem_span_singleton] at hr' ⊢
  obtain ⟨q, r, r_mem, lt⟩ := exists_mem_finset_approx' bS adm a b_ne_zero
  apply @dvd_of_mul_left_dvd _ _ q
  simp only [Algebra.smul_def] at lt
  rw [←
    sub_eq_zero.mp (b_min _ (I.1.sub_mem (I.1.mul_mem_left _ ha) (I.1.mul_mem_left _ b_mem)) lt)]
  refine mul_dvd_mul_right (dvd_trans (map_dvd _ ?_) hr') _
  exact Multiset.dvd_prod (Multiset.mem_map.mpr ⟨_, r_mem, rfl⟩)

中文:
定理 存在_mk0_eq_mk0
  条件: [是Dedekind整环 S] [代数.是代数 R S] (I : (理想 S)⁰)
  证明: by
  set M := ∏ m in finsetApprox bS adm, m
  have hM : algebraMap R S M != 0 := prod_finsetApprox_ne_zero bS adm
  obtain ⟨b, b_mem, b_ne_zero, b_min⟩ := exists_min abv I
  suffices Ideal.span {b} ∣ Ideal.span {algebraMap _ _ M} * I.1 by
    obtain ⟨J, hJ⟩ := this
    refine ⟨⟨J, ?_⟩, ?_, ?_⟩
    · rw [mem_nonZeroDivisors_iff_ne_zero]
      rintro rfl
      rw [Ideal.zero_eq_bot]; rw [Ideal.mul_bot] at hJ
      exact hM (Ideal.span_singleton_eq_bot.mp (I.2.2 _ hJ))
    · rw [ClassGroup.mk0_eq_mk0_iff]
      exact ⟨algebraMap _ _ M, b, hM, b_ne_zero, hJ⟩
    rw [← SetLike.mem_coe]; rw [← Set.singleton_subset_iff]; rw [← Ideal.span_le]; rw [← Ideal.dvd_iff_le]
    apply (mul_dvd_mul_iff_left _).mp _
    swap; · exact mt Ideal.span_singleton_eq_bot.mp b_ne_zero
    rw [Subtype.coe_mk]; rw [Ideal.dvd_iff_le]; rw [← hJ]; rw [mul_comm]
    apply Ideal.mul_mono le_rfl
    rw [Ideal.span_le]; rw [Set.singleton_subset_iff]
    exact b_mem
  rw [Ideal.dvd_iff_le]; rw [Ideal.mul_le]
  intro r' hr' a ha
  rw [Ideal.mem_span_singleton] at hr' ⊢
  obtain ⟨q, r, r_mem, lt⟩ := exists_mem_finset_approx' bS adm a b_ne_zero
  apply @dvd_of_mul_left_dvd _ _ q
  simp only [Algebra.smul_def] at lt
  rw [←
    sub_eq_zero.mp (b_min _ (I.1.sub_mem (I.1.mul_mem_left _ ha) (I.1.mul_mem_left _ b_mem)) lt)]
  refine mul_dvd_mul_right (dvd_trans (map_dvd _ ?_) hr') _
  exact Multiset.dvd_prod (Multiset.mem_map.mpr ⟨_, r_mem, rfl⟩)

Depends on / 依赖: ClassGroup, ClassGroup.mk0_eq_mk0_iff, Ideal.mul_bot, Ideal.span, Ideal.span_singleton_eq_bot.mp, Ideal.zero_eq_bot, algebraMap, b_mem, b_min, b_ne_zero, exists_min, finsetApprox, mem_nonZeroDivisors_iff_ne_zero, mk0_eq_mk0_iff, mul_bot, prod_finsetApprox_ne_zero, span_singleton_eq_bot, zero_eq_bot
-/
theorem exists_mk0_eq_mk0 [IsDedekindDomain S] [Algebra.IsAlgebraic R S] (I : (Ideal S)⁰) :
    exists J : (Ideal S)⁰,
      ClassGroup.mk0 I = ClassGroup.mk0 J ∧
        algebraMap _ _ (∏ m in finsetApprox bS adm, m) in (J : Ideal S) := by
  set M := ∏ m in finsetApprox bS adm, m
  have hM : algebraMap R S M != 0 := prod_finsetApprox_ne_zero bS adm
  obtain ⟨b, b_mem, b_ne_zero, b_min⟩ := exists_min abv I
  suffices Ideal.span {b} ∣ Ideal.span {algebraMap _ _ M} * I.1 by
    obtain ⟨J, hJ⟩ := this
    refine ⟨⟨J, ?_⟩, ?_, ?_⟩
    · rw [mem_nonZeroDivisors_iff_ne_zero]
      rintro rfl
      rw [Ideal.zero_eq_bot]; rw [Ideal.mul_bot] at hJ
      exact hM (Ideal.span_singleton_eq_bot.mp (I.2.2 _ hJ))
    · rw [ClassGroup.mk0_eq_mk0_iff]
      exact ⟨algebraMap _ _ M, b, hM, b_ne_zero, hJ⟩
    rw [← SetLike.mem_coe]; rw [← Set.singleton_subset_iff]; rw [← Ideal.span_le]; rw [← Ideal.dvd_iff_le]
    apply (mul_dvd_mul_iff_left _).mp _
    swap; · exact mt Ideal.span_singleton_eq_bot.mp b_ne_zero
    rw [Subtype.coe_mk]; rw [Ideal.dvd_iff_le]; rw [← hJ]; rw [mul_comm]
    apply Ideal.mul_mono le_rfl
    rw [Ideal.span_le]; rw [Set.singleton_subset_iff]
    exact b_mem
  rw [Ideal.dvd_iff_le]; rw [Ideal.mul_le]
  intro r' hr' a ha
  rw [Ideal.mem_span_singleton] at hr' ⊢
  obtain ⟨q, r, r_mem, lt⟩ := exists_mem_finset_approx' bS adm a b_ne_zero
  apply @dvd_of_mul_left_dvd _ _ q
  simp only [Algebra.smul_def] at lt
  rw [←
    sub_eq_zero.mp (b_min _ (I.1.sub_mem (I.1.mul_mem_left _ ha) (I.1.mul_mem_left _ b_mem)) lt)]
  refine mul_dvd_mul_right (dvd_trans (map_dvd _ ?_) hr') _
  exact Multiset.dvd_prod (Multiset.mem_map.mpr ⟨_, r_mem, rfl⟩)

/--
Definition of `mkMMem` / `mkMMem` 的定义

English:
definition mkMMem
  signature: [IsDedekindDomain S]
  body: ClassGroup.mk0
    ⟨J.1, mem_nonZeroDivisors_iff_ne_zero.mpr (ne_bot_of_prod_finsetApprox_mem bS adm J.1 J.2)⟩

中文:
定义 mkMMem
  签名: [是Dedekind整环 S]
  定义体: ClassGroup.mk0
    ⟨J.1, mem_nonZeroDivisors_iff_ne_zero.mpr (ne_bot_of_prod_finsetApprox_mem bS adm J.1 J.2)⟩

Depends on / 依赖: ClassGroup, ClassGroup.mk0, mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero.mpr, ne_bot_of_prod_finsetApprox_mem
-/
noncomputable def mkMMem [IsDedekindDomain S]
    (J : { J : Ideal S // algebraMap _ _ (∏ m in finsetApprox bS adm, m) in J }) : ClassGroup S :=
  ClassGroup.mk0
    ⟨J.1, mem_nonZeroDivisors_iff_ne_zero.mpr (ne_bot_of_prod_finsetApprox_mem bS adm J.1 J.2)⟩

/--
theorem `mkMMem_surjective` / 定理 `mkMMem_surjective`

English:
theorem mkMMem_surjective
  given: [IsDedekindDomain S] [Algebra.IsAlgebraic R S]
  proof: by
  intro I'
  obtain ⟨⟨I, hI⟩, rfl⟩ := ClassGroup.mk0_surjective I'
  obtain ⟨J, mk0_eq_mk0, J_dvd⟩ := exists_mk0_eq_mk0 bS adm ⟨I, hI⟩
  exact ⟨⟨J, J_dvd⟩, mk0_eq_mk0.symm⟩

中文:
定理 mkMMem_surjective
  条件: [是Dedekind整环 S] [代数.是代数 R S]
  证明: by
  intro I'
  obtain ⟨⟨I, hI⟩, rfl⟩ := ClassGroup.mk0_surjective I'
  obtain ⟨J, mk0_eq_mk0, J_dvd⟩ := exists_mk0_eq_mk0 bS adm ⟨I, hI⟩
  exact ⟨⟨J, J_dvd⟩, mk0_eq_mk0.symm⟩

Depends on / 依赖: ClassGroup, ClassGroup.mk0_surjective, J_dvd, exists_mk0_eq_mk0, mk0_eq_mk0, mk0_eq_mk0.symm, mk0_surjective
-/
theorem mkMMem_surjective [IsDedekindDomain S] [Algebra.IsAlgebraic R S] :
    Function.Surjective (ClassGroup.mkMMem bS adm) := by
  intro I'
  obtain ⟨⟨I, hI⟩, rfl⟩ := ClassGroup.mk0_surjective I'
  obtain ⟨J, mk0_eq_mk0, J_dvd⟩ := exists_mk0_eq_mk0 bS adm ⟨I, hI⟩
  exact ⟨⟨J, J_dvd⟩, mk0_eq_mk0.symm⟩

open scoped Classical in
/-- The **class number theorem**: the class group of an integral closure `S` of `R` in an
algebraic extension `L` is finite if there is an admissible absolute value.

See also `ClassGroup.fintypeOfAdmissibleOfFinite` where `L` is a finite
extension of `K = Frac(R)`, supplying most of the required assumptions automatically.
-/
@[instance_reducible]
/--
Definition of `fintypeOfAdmissibleOfAlgebraic` / `fintypeOfAdmissibleOfAlgebraic` 的定义

English:
definition fintypeOfAdmissibleOfAlgebraic
  signature: [IsDedekindDomain S]
  body: @Fintype.ofSurjective _ _ _
    (@Fintype.ofEquiv _
      { J // J ∣ Ideal.span ({algebraMap R S (∏ m in finsetApprox bS adm, m)} : Set S) }
      (UniqueFactorizationMonoid.fintypeSubtypeDvd _
        (by
          rw [Ne]; rw [Ideal.zero_eq_bot]; rw [Ideal.span_singleton_eq_bot]
          exact prod_finsetApprox_ne_zero bS adm))
      ((Equiv.refl _).subtypeEquiv fun I =>
        Ideal.dvd_iff_le.trans (by
          rw [Equiv.refl_apply]; rw [Ideal.span_le]; rw [Set.singleton_subset_iff]; rfl)))
    (ClassGroup.mkMMem bS adm) (ClassGroup.mkMMem_surjective bS adm)

中文:
定义 fintypeOfAdmissibleOfAlgebraic
  签名: [是Dedekind整环 S]
  定义体: @Fintype.ofSurjective _ _ _
    (@Fintype.ofEquiv _
      { J // J ∣ Ideal.span ({algebraMap R S (∏ m in finsetApprox bS adm, m)} : Set S) }
      (UniqueFactorizationMonoid.fintypeSubtypeDvd _
        (by
          rw [Ne]; rw [Ideal.zero_eq_bot]; rw [Ideal.span_singleton_eq_bot]
          exact prod_finsetApprox_ne_zero bS adm))
      ((Equiv.refl _).subtypeEquiv fun I =>
        Ideal.dvd_iff_le.trans (by
          rw [Equiv.refl_apply]; rw [Ideal.span_le]; rw [Set.singleton_subset_iff]; rfl)))
    (ClassGroup.mkMMem bS adm) (ClassGroup.mkMMem_surjective bS adm)

Depends on / 依赖: ClassGroup, ClassGroup.mkMMem, ClassGroup.mkMMem_surjective, Equiv.refl, Equiv.refl_apply, Fintype, Fintype.ofEquiv, Fintype.ofSurjective, Ideal.dvd_iff_le.trans, Ideal.span, Ideal.span_le, Ideal.span_singleton_eq_bot, Ideal.zero_eq_bot, Set.singleton_subset_iff, UniqueFactorizationMonoid, UniqueFactorizationMonoid.fintypeSubtypeDvd, algebraMap, dvd_iff_le, finsetApprox, fintypeSubtypeDvd
-/
noncomputable def fintypeOfAdmissibleOfAlgebraic [IsDedekindDomain S]
    [Algebra.IsAlgebraic R S] : Fintype (ClassGroup S) :=
  @Fintype.ofSurjective _ _ _
    (@Fintype.ofEquiv _
      { J // J ∣ Ideal.span ({algebraMap R S (∏ m in finsetApprox bS adm, m)} : Set S) }
      (UniqueFactorizationMonoid.fintypeSubtypeDvd _
        (by
          rw [Ne]; rw [Ideal.zero_eq_bot]; rw [Ideal.span_singleton_eq_bot]
          exact prod_finsetApprox_ne_zero bS adm))
      ((Equiv.refl _).subtypeEquiv fun I =>
        Ideal.dvd_iff_le.trans (by
          rw [Equiv.refl_apply]; rw [Ideal.span_le]; rw [Set.singleton_subset_iff]; rfl)))
    (ClassGroup.mkMMem bS adm) (ClassGroup.mkMMem_surjective bS adm)

/-- The main theorem: the class group of an integral closure `S` of `R` in a
finite extension `L` of `K = Frac(R)` is finite if there is an admissible
absolute value.

See also `ClassGroup.fintypeOfAdmissibleOfAlgebraic` where `L` is an
algebraic extension of `R`, that includes some extra assumptions.
-/
@[instance_reducible]
/--
Definition of `fintypeOfAdmissibleOfFinite` / `fintypeOfAdmissibleOfFinite` 的定义

English:
definition fintypeOfAdmissibleOfFinite
  signature: [IsIntegralClosure S R L]
  body: by
  letI := Classical.decEq L
  letI := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  letI := IsIntegralClosure.isDedekindDomain R K L S
  choose s b hb_int using FiniteDimensional.exists_is_basis_integral R K L
  have : LinearIndependent R ((Algebra.traceForm K L).dualBasis
      (traceForm_nondegenerate K L) b) := by
    apply (Basis.linearIndependent _).restrict_scalars
    simp only [Algebra.smul_def, mul_one]
    apply IsFractionRing.injective
  obtain ⟨n, b⟩ :=
    Submodule.basisOfPidOfLESpan this (IsIntegralClosure.range_le_span_dualBasis S b hb_int)
  let f : (S ⧸ LinearMap.ker (LinearMap.restrictScalars R (Algebra.linearMap S L))) ≃ₗ[R] S := by
    rw [LinearMap.ker_eq_bot.mpr]
    · exact Submodule.quotEquivOfEqBot _ rfl
    · exact IsIntegralClosure.algebraMap_injective _ R _
  let bS := b.map ((LinearMap.quotKerEquivRange _).symm ≪≫ₗ f)
  have : Algebra.IsIntegral R S := IsIntegralClosure.isIntegral_algebra R L
  exact fintypeOfAdmissibleOfAlgebraic bS adm

中文:
定义 fintypeOfAdmissibleOfFinite
  签名: [是整闭包 S R L]
  定义体: by
  letI := Classical.decEq L
  letI := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  letI := IsIntegralClosure.isDedekindDomain R K L S
  choose s b hb_int using FiniteDimensional.exists_is_basis_integral R K L
  have : LinearIndependent R ((Algebra.traceForm K L).dualBasis
      (traceForm_nondegenerate K L) b) := by
    apply (Basis.linearIndependent _).restrict_scalars
    simp only [Algebra.smul_def, mul_one]
    apply IsFractionRing.injective
  obtain ⟨n, b⟩ :=
    Submodule.basisOfPidOfLESpan this (IsIntegralClosure.range_le_span_dualBasis S b hb_int)
  let f : (S ⧸ LinearMap.ker (LinearMap.restrictScalars R (Algebra.linearMap S L))) ≃ₗ[R] S := by
    rw [LinearMap.ker_eq_bot.mpr]
    · exact Submodule.quotEquivOfEqBot _ rfl
    · exact IsIntegralClosure.algebraMap_injective _ R _
  let bS := b.map ((LinearMap.quotKerEquivRange _).symm ≪≫ₗ f)
  have : Algebra.IsIntegral R S := IsIntegralClosure.isIntegral_algebra R L
  exact fintypeOfAdmissibleOfAlgebraic bS adm

Depends on / 依赖: Algebra, Algebra.smul_def, Algebra.traceForm, Basis.linearIndependent, Classical, Classical.decEq, FiniteDimensional, FiniteDimensional.exists_is_basis_integral, IsFractionRing, IsFractionRing.injective, IsIntegralClosure, IsIntegralClosure.isDedekindDomain, IsIntegralClosure.isFractionRing_of_finite_extension, LinearIndependent, Submodule, Submodule.basisOfPidOfLESpan, basisOfPidOfLESpan, dualBasis, exists_is_basis_integral, hb_int
-/
noncomputable def fintypeOfAdmissibleOfFinite [IsIntegralClosure S R L] :
    Fintype (ClassGroup S) := by
  letI := Classical.decEq L
  letI := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  letI := IsIntegralClosure.isDedekindDomain R K L S
  choose s b hb_int using FiniteDimensional.exists_is_basis_integral R K L
  have : LinearIndependent R ((Algebra.traceForm K L).dualBasis
      (traceForm_nondegenerate K L) b) := by
    apply (Basis.linearIndependent _).restrict_scalars
    simp only [Algebra.smul_def, mul_one]
    apply IsFractionRing.injective
  obtain ⟨n, b⟩ :=
    Submodule.basisOfPidOfLESpan this (IsIntegralClosure.range_le_span_dualBasis S b hb_int)
  let f : (S ⧸ LinearMap.ker (LinearMap.restrictScalars R (Algebra.linearMap S L))) ≃ₗ[R] S := by
    rw [LinearMap.ker_eq_bot.mpr]
    · exact Submodule.quotEquivOfEqBot _ rfl
    · exact IsIntegralClosure.algebraMap_injective _ R _
  let bS := b.map ((LinearMap.quotKerEquivRange _).symm ≪≫ₗ f)
  have : Algebra.IsIntegral R S := IsIntegralClosure.isIntegral_algebra R L
  exact fintypeOfAdmissibleOfAlgebraic bS adm

end IsAdmissible

end EuclideanDomain

end ClassGroup
