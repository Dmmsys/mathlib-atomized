/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Rank of matrices

The rank of a matrix `A` is defined to be the rank of range of the linear map corresponding to `A`.
This definition does not depend on the choice of basis, see `Matrix.rank_eq_finrank_range_toLin`.

## Main declarations

* `Matrix.rank`: the rank of a matrix
* `Matrix.cRank`: the rank of a matrix as a cardinal
* `Matrix.eRank`: the rank of a matrix as a term in `ℕ∞`.

## Main results

* `Matrix.rank_eq_finrank_range_toLin`: the rank equals the dimension of the range of the
corresponding linear map, and is therefore independent of the choice of bases.
* `Matrix.rank_eq_finrank_span_cols`, `Matrix.rank_eq_finrank_span_row`: the rank equals the
dimension of the space spanned by the columns (resp. rows).
* `Matrix.rank_transpose`: transposing a matrix does not change its rank.
* `Matrix.rank_mul_le`: the rank of `A * B` is at most the rank of `A` and at most the rank of `B`.
* `Matrix.rank_mul_eq_left_of_isUnit_det`, `Matrix.rank_mul_eq_right_of_isUnit_det`: multiplying by
an invertible matrix does not change the rank.
* `Matrix.exists_rank_normal_form`: every square matrix over a field can be brought, by left and
right multiplication by invertible matrices, into the block form `fromBlocks 1 0 0 0`, where the
identity block has size equal to the rank of the matrix.
-/

@[expose] public section

open Matrix

namespace Matrix

open Module Cardinal Set Submodule

universe ul um um₀ un un₀ uo uR
variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}
variable {R : Type uR}

section Infinite

variable [Semiring R]

/--
Definition of `cRank` / `cRank` 的定义

English:
definition cRank
  signature: (A : Matrix m n R)
  body: Module.rank R span R range A.col

@[simp]

中文:
定义 cRank
  签名: (A : 矩阵 m n R)
  定义体: Module.rank R span R range A.col

@[simp]

Depends on / 依赖: A.col, Module, Module.rank
-/
noncomputable def cRank (A : Matrix m n R) : Cardinal := Module.rank R span R range A.col

@[simp]
/--
theorem `cRank_subsingleton` / 定理 `cRank_subsingleton`

English:
theorem cRank_subsingleton
  given: [Subsingleton R] (A : Matrix m n R)
  statement: A.cRank = 1
  proof: rank_subsingleton _ _

中文:
定理 cRank_subsingleton
  条件: [子单例 R] (A : 矩阵 m n R)
  结论: A.cRank = 1
  证明: rank_subsingleton _ _

Depends on / 依赖: rank_subsingleton
-/
theorem cRank_subsingleton [Subsingleton R] (A : Matrix m n R) : A.cRank = 1 :=
  rank_subsingleton _ _

/--
lemma `cRank_toNat_eq_finrank` / 引理 `cRank_toNat_eq_finrank`

English:
lemma cRank_toNat_eq_finrank
  given: (A : Matrix m n R)
  proof: rfl

中文:
引理 cRank_to自然数_eq_finrank
  条件: (A : 矩阵 m n R)
  证明: rfl
-/
lemma cRank_toNat_eq_finrank (A : Matrix m n R) :
    A.cRank.toNat = Module.finrank R (span R (range A.col)) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `lift_cRank_submatrix_le` / 引理 `lift_cRank_submatrix_le`

English:
lemma lift_cRank_submatrix_le
  given: (A : Matrix m n R) (r : m₀ -> m) (c : n₀ -> n)
  proof: by
  have h : ((A.submatrix r id).submatrix id c).cRank <= (A.submatrix r id).cRank :=
Submodule.rank_mono span_mono by rintro _ ⟨x, rfl⟩; exact ⟨c x, rfl⟩
  refine (Cardinal.lift_monotone h).trans ?_
  let f : (m -> R) ->ₗ[R] (m₀ -> R) := LinearMap.funLeft R R r
  have h_eq : Submodule.map f (span 

中文:
引理 lift_cRank_submatrix_le
  条件: (A : 矩阵 m n R) (r : m₀ -> m) (c : n₀ -> n)
  证明: by
  have h : ((A.submatrix r id).submatrix id c).cRank <= (A.submatrix r id).cRank :=
Submodule.rank_mono span_mono by rintro _ ⟨x, rfl⟩; exact ⟨c x, rfl⟩
  refine (Cardinal.lift_monotone h).trans ?_
  let f : (m -> R) ->ₗ[R] (m₀ -> R) := LinearMap.funLeft R R r
  have h_eq : Submodule.map f (span 

Depends on / 依赖: A.col, A.submatrix, Cardinal, Cardinal.lift_monotone, LinearMap, LinearMap.funLeft, LinearMap.map_span, Submodule, Submodule.map, Submodule.rank_mono, col_eq_transpose, funLeft, h_eq, image_image, image_univ, lift_monotone, lift_ra, map_span, rank_mono, simp_rw
-/
lemma lift_cRank_submatrix_le (A : Matrix m n R) (r : m₀ -> m) (c : n₀ -> n) :
    lift.{um} (A.submatrix r c).cRank <= lift.{um₀} A.cRank := by
  have h : ((A.submatrix r id).submatrix id c).cRank <= (A.submatrix r id).cRank :=
Submodule.rank_mono span_mono by rintro _ ⟨x, rfl⟩; exact ⟨c x, rfl⟩
  refine (Cardinal.lift_monotone h).trans ?_
  let f : (m -> R) ->ₗ[R] (m₀ -> R) := LinearMap.funLeft R R r
  have h_eq : Submodule.map f (span R (range A.col)) = span R (range (A.submatrix r id).col) := by
    simp_rw [LinearMap.map_span, ← image_univ, image_image, col_eq_transpose, transpose_submatrix]
    aesop
  rw [cRank]; rw [← h_eq]
  have hwin := lift_rank_map_le f (span R (range Aᵀ))
  simp_rw [← lift_umax] at hwin ⊢
  exact hwin

/--
lemma `cRank_submatrix_le` / 引理 `cRank_submatrix_le`

English:
lemma cRank_submatrix_le
  given: {m m₀ : Type um} (A : Matrix m n R) (r : m₀ -> m) (c : n₀ -> n)
  proof: by
  simpa using lift_cRank_submatrix_le A r c

中文:
引理 cRank_submatrix_le
  条件: {m m₀ : 类型um} (A : 矩阵 m n R) (r : m₀ -> m) (c : n₀ -> n)
  证明: by
  simpa using lift_cRank_submatrix_le A r c

Depends on / 依赖: lift_cRank_submatrix_le
-/
lemma cRank_submatrix_le {m m₀ : Type um} (A : Matrix m n R) (r : m₀ -> m) (c : n₀ -> n) :
    (A.submatrix r c).cRank <= A.cRank := by
  simpa using lift_cRank_submatrix_le A r c

/--
lemma `cRank_le_card_height` / 引理 `cRank_le_card_height`

English:
lemma cRank_le_card_height
  given: [StrongRankCondition R] [Fintype m] (A : Matrix m n R)
  proof: (Submodule.rank_le (span R (range Aᵀ))).trans by rw [rank_fun']

中文:
引理 cRank_le_card_height
  条件: [StrongRankCondition R] [有限类型 m] (A : 矩阵 m n R)
  证明: (Submodule.rank_le (span R (range Aᵀ))).trans by rw [rank_fun']

Depends on / 依赖: Submodule, Submodule.rank_le, rank_fun, rank_le
-/
lemma cRank_le_card_height [StrongRankCondition R] [Fintype m] (A : Matrix m n R) :
    A.cRank <= Fintype.card m :=
(Submodule.rank_le (span R (range Aᵀ))).trans by rw [rank_fun']

/--
lemma `cRank_le_card_width` / 引理 `cRank_le_card_width`

English:
lemma cRank_le_card_width
  given: [StrongRankCondition R] [Fintype n] (A : Matrix m n R)
  proof: (rank_span_le ..).trans
    by simpa [col_eq_transpose] using Cardinal.mk_range_le_lift (f := A.col)

中文:
引理 cRank_le_card_width
  条件: [StrongRankCondition R] [有限类型 n] (A : 矩阵 m n R)
  证明: (rank_span_le ..).trans
    by simpa [col_eq_transpose] using Cardinal.mk_range_le_lift (f := A.col)

Depends on / 依赖: A.col, Cardinal, Cardinal.mk_range_le_lift, col_eq_transpose, mk_range_le_lift, rank_span_le
-/
lemma cRank_le_card_width [StrongRankCondition R] [Fintype n] (A : Matrix m n R) :
    A.cRank <= Fintype.card n :=
(rank_span_le ..).trans
    by simpa [col_eq_transpose] using Cardinal.mk_range_le_lift (f := A.col)

/--
Definition of `eRank` / `eRank` 的定义

English:
definition eRank
  signature: (A : Matrix m n R)
  body: A.cRank.toENat

@[simp]

中文:
定义 eRank
  签名: (A : 矩阵 m n R)
  定义体: A.cRank.toENat

@[simp]

Depends on / 依赖: A.cRank.toENat, toENat
-/
noncomputable def eRank (A : Matrix m n R) : Nat∞ := A.cRank.toENat

@[simp]
/--
theorem `eRank_subsingleton` / 定理 `eRank_subsingleton`

English:
theorem eRank_subsingleton
  given: [Subsingleton R] (A : Matrix m n R)
  statement: A.eRank = 1
  proof: by
  simp [eRank]

中文:
定理 eRank_subsingleton
  条件: [子单例 R] (A : 矩阵 m n R)
  结论: A.eRank = 1
  证明: by
  simp [eRank]
-/
theorem eRank_subsingleton [Subsingleton R] (A : Matrix m n R) : A.eRank = 1 := by
  simp [eRank]

/--
lemma `eRank_toNat_eq_finrank` / 引理 `eRank_toNat_eq_finrank`

English:
lemma eRank_toNat_eq_finrank
  given: (A : Matrix m n R)
  proof: toNat_toENat ..

中文:
引理 eRank_to自然数_eq_finrank
  条件: (A : 矩阵 m n R)
  证明: toNat_toENat ..

Depends on / 依赖: toNat_toENat
-/
lemma eRank_toNat_eq_finrank (A : Matrix m n R) :
    A.eRank.toNat = Module.finrank R (span R (range A.col)) :=
  toNat_toENat ..

/--
lemma `eRank_submatrix_le` / 引理 `eRank_submatrix_le`

English:
lemma eRank_submatrix_le
  given: (A : Matrix m n R) (r : m₀ -> m) (c : n₀ -> n)
  proof: by
simpa using! OrderHom.mono (β := Nat∞) Cardinal.toENat lift_cRank_submatrix_le A r c

中文:
引理 eRank_submatrix_le
  条件: (A : 矩阵 m n R) (r : m₀ -> m) (c : n₀ -> n)
  证明: by
simpa using! OrderHom.mono (β := Nat∞) Cardinal.toENat lift_cRank_submatrix_le A r c

Depends on / 依赖: Cardinal, Cardinal.toENat, OrderHom, OrderHom.mono, lift_cRank_submatrix_le, toENat
-/
lemma eRank_submatrix_le (A : Matrix m n R) (r : m₀ -> m) (c : n₀ -> n) :
    (A.submatrix r c).eRank <= A.eRank := by
simpa using! OrderHom.mono (β := Nat∞) Cardinal.toENat lift_cRank_submatrix_le A r c

/--
lemma `eRank_le_card_width` / 引理 `eRank_le_card_width`

English:
lemma eRank_le_card_width
  given: [StrongRankCondition R] (A : Matrix m n R)
  statement: A.eRank <= ENat.card n
  proof: by
  wlog hfin : Finite n
  · simp [ENat.card_eq_top.2 (by simpa using hfin)]
  have _ := Fintype.ofFinite n
  rw [ENat.card_eq_coe_fintype_card]; rw [eRank]; rw [toENat_le_natCast]
  exact A.cRank_le_card_width

中文:
引理 eRank_le_card_width
  条件: [StrongRankCondition R] (A : 矩阵 m n R)
  结论: A.eRank <= E自然数.card n
  证明: by
  wlog hfin : Finite n
  · simp [ENat.card_eq_top.2 (by simpa using hfin)]
  have _ := Fintype.ofFinite n
  rw [ENat.card_eq_coe_fintype_card]; rw [eRank]; rw [toENat_le_natCast]
  exact A.cRank_le_card_width

Depends on / 依赖: A.cRank_le_card_width, ENat.card_eq_coe_fintype_card, ENat.card_eq_top, Finite, Fintype, Fintype.ofFinite, cRank_le_card_width, card_eq_coe_fintype_card, card_eq_top, ofFinite, toENat_le_natCast
-/
lemma eRank_le_card_width [StrongRankCondition R] (A : Matrix m n R) : A.eRank <= ENat.card n := by
  wlog hfin : Finite n
  · simp [ENat.card_eq_top.2 (by simpa using hfin)]
  have _ := Fintype.ofFinite n
  rw [ENat.card_eq_coe_fintype_card]; rw [eRank]; rw [toENat_le_natCast]
  exact A.cRank_le_card_width

/--
lemma `eRank_le_card_height` / 引理 `eRank_le_card_height`

English:
lemma eRank_le_card_height
  given: [StrongRankCondition R] (A : Matrix m n R)
  statement: A.eRank <= ENat.card m
  proof: by
  wlog hfin : Finite m
  · simp [ENat.card_eq_top.2 (by simpa using hfin)]
  have _ := Fintype.ofFinite m
  rw [ENat.card_eq_coe_fintype_card]; rw [eRank]; rw [toENat_le_natCast]
  exact A.cRank_le_card_height

中文:
引理 eRank_le_card_height
  条件: [StrongRankCondition R] (A : 矩阵 m n R)
  结论: A.eRank <= E自然数.card m
  证明: by
  wlog hfin : Finite m
  · simp [ENat.card_eq_top.2 (by simpa using hfin)]
  have _ := Fintype.ofFinite m
  rw [ENat.card_eq_coe_fintype_card]; rw [eRank]; rw [toENat_le_natCast]
  exact A.cRank_le_card_height

Depends on / 依赖: A.cRank_le_card_height, ENat.card_eq_coe_fintype_card, ENat.card_eq_top, Finite, Fintype, Fintype.ofFinite, cRank_le_card_height, card_eq_coe_fintype_card, card_eq_top, ofFinite, toENat_le_natCast
-/
lemma eRank_le_card_height [StrongRankCondition R] (A : Matrix m n R) : A.eRank <= ENat.card m := by
  wlog hfin : Finite m
  · simp [ENat.card_eq_top.2 (by simpa using hfin)]
  have _ := Fintype.ofFinite m
  rw [ENat.card_eq_coe_fintype_card]; rw [eRank]; rw [toENat_le_natCast]
  exact A.cRank_le_card_height

end Infinite

variable [Fintype n] [Fintype o]

/--
Definition of `rank` / `rank` 的定义

English:
definition rank
  signature: [CommSemiring R] (A : Matrix m n R)
  body: finrank R LinearMap.range A.mulVecLin

@[simp]

中文:
定义 rank
  签名: [交换半环 R] (A : 矩阵 m n R)
  定义体: finrank R LinearMap.range A.mulVecLin

@[simp]

Depends on / 依赖: A.mulVecLin, LinearMap, LinearMap.range, finrank, mulVecLin
-/
noncomputable def rank [CommSemiring R] (A : Matrix m n R) : Nat :=
finrank R LinearMap.range A.mulVecLin

@[simp]
/--
theorem `rank_subsingleton` / 定理 `rank_subsingleton`

English:
theorem rank_subsingleton
  given: [CommSemiring R] [Subsingleton R] (A : Matrix m n R)
  statement: A.rank = 1
  proof: finrank_subsingleton

中文:
定理 rank_subsingleton
  条件: [交换半环 R] [子单例 R] (A : 矩阵 m n R)
  结论: A.rank = 1
  证明: finrank_subsingleton

Depends on / 依赖: finrank_subsingleton
-/
theorem rank_subsingleton [CommSemiring R] [Subsingleton R] (A : Matrix m n R) : A.rank = 1 :=
  finrank_subsingleton

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `cRank_one` / 定理 `cRank_one`

English:
theorem cRank_one
  given: [Semiring R] [Nontrivial R] [DecidableEq m] [StrongRankCondition R]
  proof: by
  have h : LinearIndependent R (1 : Matrix m m R).col := by
    convert! Pi.linearIndependent_single_one m R
    simp [funext_iff, one_apply, Pi.single_apply]
  rw [cRank]; rw [rank_span h]; rw [← lift_umax]; rw [← Cardinal.mk_range_eq_of_injective h.injective]; rw [lift_id']

中文:
定理 cRank_one
  条件: [半环 R] [非平凡 R] [DecidableEq m] [StrongRankCondition R]
  证明: by
  have h : LinearIndependent R (1 : Matrix m m R).col := by
    convert! Pi.linearIndependent_single_one m R
    simp [funext_iff, one_apply, Pi.single_apply]
  rw [cRank]; rw [rank_span h]; rw [← lift_umax]; rw [← Cardinal.mk_range_eq_of_injective h.injective]; rw [lift_id']

Depends on / 依赖: Cardinal, Cardinal.mk_range_eq_of_injective, LinearIndependent, Matrix, Pi.linearIndependent_single_one, Pi.single_apply, convert, funext_iff, h.injective, injective, lift_id, lift_umax, linearIndependent_single_one, mk_range_eq_of_injective, one_apply, rank_span, single_apply
-/
theorem cRank_one [Semiring R] [Nontrivial R] [DecidableEq m] [StrongRankCondition R] :
    (cRank (1 : Matrix m m R)) = lift.{uR} #m := by
  have h : LinearIndependent R (1 : Matrix m m R).col := by
    convert! Pi.linearIndependent_single_one m R
    simp [funext_iff, one_apply, Pi.single_apply]
  rw [cRank]; rw [rank_span h]; rw [← lift_umax]; rw [← Cardinal.mk_range_eq_of_injective h.injective]; rw [lift_id']

/--
theorem `eRank_one` / 定理 `eRank_one`

English:
theorem eRank_one
  given: [Semiring R] [Nontrivial R] [DecidableEq m] [StrongRankCondition R]
  proof: by
  rw [eRank]; rw [cRank_one]; rw [toENat_lift]; rw [ENat.card]

@[simp]

中文:
定理 eRank_one
  条件: [半环 R] [非平凡 R] [DecidableEq m] [StrongRankCondition R]
  证明: by
  rw [eRank]; rw [cRank_one]; rw [toENat_lift]; rw [ENat.card]

@[simp]
-/
@[simp] theorem eRank_one [Semiring R] [Nontrivial R] [DecidableEq m] [StrongRankCondition R] :
    (eRank (1 : Matrix m m R)) = ENat.card m := by
  rw [eRank]; rw [cRank_one]; rw [toENat_lift]; rw [ENat.card]

@[simp]
/--
theorem `rank_one` / 定理 `rank_one`

English:
theorem rank_one
  given: [CommSemiring R] [DecidableEq n] [StrongRankCondition R]
  proof: by
  rw [rank]; rw [mulVecLin_one]; rw [LinearMap.range_id]; rw [finrank_top]; rw [finrank_pi]

@[simp]

中文:
定理 rank_one
  条件: [交换半环 R] [DecidableEq n] [StrongRankCondition R]
  证明: by
  rw [rank]; rw [mulVecLin_one]; rw [LinearMap.range_id]; rw [finrank_top]; rw [finrank_pi]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.range_id, finrank_pi, finrank_top, mulVecLin_one, range_id
-/
theorem rank_one [CommSemiring R] [DecidableEq n] [StrongRankCondition R] :
    rank (1 : Matrix n n R) = Fintype.card n := by
  rw [rank]; rw [mulVecLin_one]; rw [LinearMap.range_id]; rw [finrank_top]; rw [finrank_pi]

@[simp]
/--
theorem `rank_zero` / 定理 `rank_zero`

English:
theorem rank_zero
  given: [CommSemiring R] [Nontrivial R]
  statement: rank (0 : Matrix m n R) = 0
  proof: by
  rw [rank]; rw [mulVecLin_zero]; rw [LinearMap.range_zero]; rw [finrank_bot]

@[simp]

中文:
定理 rank_zero
  条件: [交换半环 R] [非平凡 R]
  结论: rank (0 : 矩阵 m n R) = 0
  证明: by
  rw [rank]; rw [mulVecLin_zero]; rw [LinearMap.range_zero]; rw [finrank_bot]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.range_zero, finrank_bot, mulVecLin_zero, range_zero
-/
theorem rank_zero [CommSemiring R] [Nontrivial R] : rank (0 : Matrix m n R) = 0 := by
  rw [rank]; rw [mulVecLin_zero]; rw [LinearMap.range_zero]; rw [finrank_bot]

@[simp]
/--
theorem `cRank_zero` / 定理 `cRank_zero`

English:
theorem cRank_zero
  given: {m n : Type*} [Semiring R] [Nontrivial R]
  statement: cRank (0 : Matrix m n R) = 0
  proof: by
  obtain hn | hn := isEmpty_or_nonempty n
  · rw [cRank, range_eq_empty, span_empty, rank_bot]
  rw [cRank]; rw [col_eq_transpose]; rw [transpose_zero]; rw [of_symm_zero]; rw [range_zero]; rw [span_zero_singleton]; rw [rank_bot]

@[simp]

中文:
定理 cRank_zero
  条件: {m n : 类型} [半环 R] [非平凡 R]
  结论: cRank (0 : 矩阵 m n R) = 0
  证明: by
  obtain hn | hn := isEmpty_or_nonempty n
  · rw [cRank, range_eq_empty, span_empty, rank_bot]
  rw [cRank]; rw [col_eq_transpose]; rw [transpose_zero]; rw [of_symm_zero]; rw [range_zero]; rw [span_zero_singleton]; rw [rank_bot]

@[simp]

Depends on / 依赖: col_eq_transpose, isEmpty_or_nonempty, of_symm_zero, range_eq_empty, range_zero, rank_bot, span_empty, span_zero_singleton, transpose_zero
-/
theorem cRank_zero {m n : Type*} [Semiring R] [Nontrivial R] : cRank (0 : Matrix m n R) = 0 := by
  obtain hn | hn := isEmpty_or_nonempty n
  · rw [cRank, range_eq_empty, span_empty, rank_bot]
  rw [cRank]; rw [col_eq_transpose]; rw [transpose_zero]; rw [of_symm_zero]; rw [range_zero]; rw [span_zero_singleton]; rw [rank_bot]

@[simp]
/--
theorem `eRank_zero` / 定理 `eRank_zero`

English:
theorem eRank_zero
  given: {m n : Type*} [Semiring R] [Nontrivial R]
  statement: eRank (0 : Matrix m n R) = 0
  proof: by
  simp [eRank]

中文:
定理 eRank_zero
  条件: {m n : 类型} [半环 R] [非平凡 R]
  结论: eRank (0 : 矩阵 m n R) = 0
  证明: by
  simp [eRank]
-/
theorem eRank_zero {m n : Type*} [Semiring R] [Nontrivial R] : eRank (0 : Matrix m n R) = 0 := by
  simp [eRank]

/--
theorem `rank_le_card_width` / 定理 `rank_le_card_width`

English:
theorem rank_le_card_width
  given: [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R)
  proof: A.mulVecLin.finrank_range_le.trans_eq finrank_pi R

中文:
定理 rank_le_card_width
  条件: [交换半环 R] [StrongRankCondition R] (A : 矩阵 m n R)
  证明: A.mulVecLin.finrank_range_le.trans_eq finrank_pi R

Depends on / 依赖: A.mulVecLin.finrank_range_le.trans_eq, finrank_pi, finrank_range_le, mulVecLin, trans_eq
-/
theorem rank_le_card_width [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R) :
    A.rank <= Fintype.card n :=
A.mulVecLin.finrank_range_le.trans_eq finrank_pi R

/--
theorem `rank_le_width` / 定理 `rank_le_width`

English:
theorem rank_le_width
  statement: [CommSemiring R] [StrongRankCondition R] {m n : Nat}
  proof: A.rank_le_card_width.trans (Fintype.card_fin n).le

中文:
定理 rank_le_width
  结论: [交换半环 R] [StrongRankCondition R] {m n : 自然数}
  证明: A.rank_le_card_width.trans (Fintype.card_fin n).le

Depends on / 依赖: A.rank_le_card_width.trans, Fintype, Fintype.card_fin, card_fin, rank_le_card_width
-/
theorem rank_le_width [CommSemiring R] [StrongRankCondition R] {m n : Nat}
    (A : Matrix (Fin m) (Fin n) R) : A.rank <= n :=
A.rank_le_card_width.trans (Fintype.card_fin n).le

/--
theorem `rank_mul_le_left` / 定理 `rank_mul_le_left`

English:
theorem rank_mul_le_left
  statement: [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R)
  proof: by
  nontriviality R
  rw [rank]; rw [rank]; rw [mulVecLin_mul]
  exact Cardinal.toNat_le_toNat (LinearMap.rank_comp_le_left ..) (rank_lt_aleph0 R _)

中文:
定理 rank_mul_le_left
  结论: [交换半环 R] [StrongRankCondition R] (A : 矩阵 m n R)
  证明: by
  nontriviality R
  rw [rank]; rw [rank]; rw [mulVecLin_mul]
  exact Cardinal.toNat_le_toNat (LinearMap.rank_comp_le_left ..) (rank_lt_aleph0 R _)

Depends on / 依赖: Cardinal, Cardinal.toNat_le_toNat, LinearMap, LinearMap.rank_comp_le_left, MeasurableSingletonClass, MeasurableSingletonClass.toDiscreteMeasurableSpace, MeasurableSpace, mulVecLin_mul, nontriviality, rank_comp_le_left, rank_lt_aleph0, toDiscreteMeasurableSpace, toNat_le_toNat
-/
theorem rank_mul_le_left [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R)
    (B : Matrix n o R) : (A * B).rank <= A.rank := by
  nontriviality R
  rw [rank]; rw [rank]; rw [mulVecLin_mul]
  exact Cardinal.toNat_le_toNat (LinearMap.rank_comp_le_left ..) (rank_lt_aleph0 R _)

/--
theorem `rank_mul_le_right` / 定理 `rank_mul_le_right`

English:
theorem rank_mul_le_right
  statement: [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R)
  proof: by
  nontriviality R
  rw [rank]; rw [rank]; rw [mulVecLin_mul]
  exact finrank_le_finrank_of_rank_le_rank (LinearMap.lift_rank_comp_le_right _ _)
    (rank_lt_aleph0 _ _)

中文:
定理 rank_mul_le_right
  结论: [交换半环 R] [StrongRankCondition R] (A : 矩阵 m n R)
  证明: by
  nontriviality R
  rw [rank]; rw [rank]; rw [mulVecLin_mul]
  exact finrank_le_finrank_of_rank_le_rank (LinearMap.lift_rank_comp_le_right _ _)
    (rank_lt_aleph0 _ _)

Depends on / 依赖: DiscreteMeasurableSpace, DiscreteMeasurableSpace.toMeasurableSingletonClass, LinearMap, LinearMap.lift_rank_comp_le_right, finrank_le_finrank_of_rank_le_rank, lift_rank_comp_le_right, mulVecLin_mul, nontriviality, rank_lt_aleph0, toMeasurableSingletonClass
-/
theorem rank_mul_le_right [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R)
    (B : Matrix n o R) : (A * B).rank <= B.rank := by
  nontriviality R
  rw [rank]; rw [rank]; rw [mulVecLin_mul]
  exact finrank_le_finrank_of_rank_le_rank (LinearMap.lift_rank_comp_le_right _ _)
    (rank_lt_aleph0 _ _)

/--
theorem `rank_mul_le` / 定理 `rank_mul_le`

English:
theorem rank_mul_le
  given: [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R) (B : Matrix n o R)
  proof: le_min (rank_mul_le_left _ _) (rank_mul_le_right _ _)

中文:
定理 rank_mul_le
  条件: [交换半环 R] [StrongRankCondition R] (A : 矩阵 m n R) (B : 矩阵 n o R)
  证明: le_min (rank_mul_le_left _ _) (rank_mul_le_right _ _)

Depends on / 依赖: le_min, rank_mul_le_left, rank_mul_le_right
-/
theorem rank_mul_le [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R) (B : Matrix n o R) :
    (A * B).rank <= min A.rank B.rank :=
  le_min (rank_mul_le_left _ _) (rank_mul_le_right _ _)

/--
theorem `rank_vecMulVec_le` / 定理 `rank_vecMulVec_le`

English:
theorem rank_vecMulVec_le
  given: [CommSemiring R] [StrongRankCondition R] (w : m -> R) (v : n -> R)
  proof: by
  rw [Matrix.vecMulVec_eq Unit]
  refine le_trans (rank_mul_le_left _ _) ?_
  nontriviality R
  exact rank_le_card_width _

中文:
定理 rank_vecMulVec_le
  条件: [交换半环 R] [StrongRankCondition R] (w : m -> R) (v : n -> R)
  证明: by
  rw [Matrix.vecMulVec_eq Unit]
  refine le_trans (rank_mul_le_left _ _) ?_
  nontriviality R
  exact rank_le_card_width _

Depends on / 依赖: Matrix, Matrix.vecMulVec_eq, le_trans, nontriviality, rank_le_card_width, rank_mul_le_left, vecMulVec_eq
-/
theorem rank_vecMulVec_le [CommSemiring R] [StrongRankCondition R] (w : m -> R) (v : n -> R) :
    (Matrix.vecMulVec w v).rank <= 1 := by
  rw [Matrix.vecMulVec_eq Unit]
  refine le_trans (rank_mul_le_left _ _) ?_
  nontriviality R
  exact rank_le_card_width _

/--
theorem `rank_unit` / 定理 `rank_unit`

English:
theorem rank_unit
  given: [DecidableEq n] [CommSemiring R] [StrongRankCondition R] (A : (Matrix n n R)ˣ)
  proof: by
  apply le_antisymm (rank_le_card_width (A : Matrix n n R)) _
  have := rank_mul_le_left (A : Matrix n n R) (↑A⁻¹ : Matrix n n R)
  rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, rank_one] at this

中文:
定理 rank_unit
  条件: [DecidableEq n] [交换半环 R] [StrongRankCondition R] (A : (矩阵 n n R)ˣ)
  证明: by
  apply le_antisymm (rank_le_card_width (A : Matrix n n R)) _
  have := rank_mul_le_left (A : Matrix n n R) (↑A⁻¹ : Matrix n n R)
  rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, rank_one] at this

Depends on / 依赖: Matrix, Units.val_mul, Units.val_one, le_antisymm, mul_inv_cancel, rank_le_card_width, rank_mul_le_left, rank_one, val_mul, val_one
-/
theorem rank_unit [DecidableEq n] [CommSemiring R] [StrongRankCondition R] (A : (Matrix n n R)ˣ) :
    (A : Matrix n n R).rank = Fintype.card n := by
  apply le_antisymm (rank_le_card_width (A : Matrix n n R)) _
  have := rank_mul_le_left (A : Matrix n n R) (↑A⁻¹ : Matrix n n R)
  rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, rank_one] at this

/--
theorem `rank_of_isUnit` / 定理 `rank_of_isUnit`

English:
theorem rank_of_isUnit
  statement: [DecidableEq n] [CommSemiring R] [StrongRankCondition R] (A : Matrix n n R)
  proof: by
  obtain ⟨A, rfl⟩ := h
  exact rank_unit A

中文:
定理 rank_of_isUnit
  结论: [DecidableEq n] [交换半环 R] [StrongRankCondition R] (A : 矩阵 n n R)
  证明: by
  obtain ⟨A, rfl⟩ := h
  exact rank_unit A

Depends on / 依赖: rank_unit
-/
theorem rank_of_isUnit [DecidableEq n] [CommSemiring R] [StrongRankCondition R] (A : Matrix n n R)
    (h : IsUnit A) : A.rank = Fintype.card n := by
  obtain ⟨A, rfl⟩ := h
  exact rank_unit A

/--
theorem `rank_of_det_mem_nonZeroDivisors` / 定理 `rank_of_det_mem_nonZeroDivisors`

English:
theorem rank_of_det_mem_nonZeroDivisors
  statement: {R : Type*} [CommRing R] [Nontrivial R]
  proof: by
  rw [rank]; rw [LinearMap.finrank_range_of_inj (mulVec_injective_of_det_mem_nonZeroDivisors hA)]; rw [Module.finrank_eq_card_basis (Pi.basisFun R m)]

中文:
定理 rank_of_det_mem_nonZeroDivisors
  结论: {R : 类型} [交换环 R] [非平凡 R]
  证明: by
  rw [rank]; rw [LinearMap.finrank_range_of_inj (mulVec_injective_of_det_mem_nonZeroDivisors hA)]; rw [Module.finrank_eq_card_basis (Pi.basisFun R m)]

Depends on / 依赖: LinearMap, LinearMap.finrank_range_of_inj, Module, Module.finrank_eq_card_basis, Pi.basisFun, basisFun, finrank_eq_card_basis, finrank_range_of_inj, mulVec_injective_of_det_mem_nonZeroDivisors
-/
theorem rank_of_det_mem_nonZeroDivisors {R : Type*} [CommRing R] [Nontrivial R]
    [Fintype m] [DecidableEq m] {A : Matrix m m R} (hA : A.det in nonZeroDivisors R) :
    A.rank = Fintype.card m := by
  rw [rank]; rw [LinearMap.finrank_range_of_inj (mulVec_injective_of_det_mem_nonZeroDivisors hA)]; rw [Module.finrank_eq_card_basis (Pi.basisFun R m)]

/--
theorem `rank_of_det_ne_zero` / 定理 `rank_of_det_ne_zero`

English:
theorem rank_of_det_ne_zero
  statement: {R : Type*} [CommRing R] [IsDomain R] [Fintype m] [DecidableEq m]
  proof: rank_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero h)

中文:
定理 rank_of_det_ne_zero
  结论: {R : 类型} [交换环 R] [是整环 R] [有限类型 m] [DecidableEq m]
  证明: rank_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero h)

Depends on / 依赖: mem_nonZeroDivisors_of_ne_zero, rank_of_det_mem_nonZeroDivisors
-/
theorem rank_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R] [Fintype m] [DecidableEq m]
    {A : Matrix m m R} (h : A.det != 0) : A.rank = Fintype.card m :=
  rank_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero h)

/--
lemma `rank_smul_of_mem_nonZeroDivisors` / 引理 `rank_smul_of_mem_nonZeroDivisors`

English:
lemma rank_smul_of_mem_nonZeroDivisors
  statement: {R : Type*} [CommRing R] {c : R} (B : Matrix m n R)
  proof: by
  have hc' : IsSMulRegular R c := isSMulRegular_iff_mem_nonZeroSMulDivisors.mpr hc.1
  have hreg : IsSMulRegular (m -> R) c := IsSMulRegular.pi fun _ => hc'
  let f := LinearMap.lsmul R (m -> R) c
  have hcomp : (c • B).mulVecLin = f.comp B.mulVecLin := by aesop
  rw [rank]; rw [rank]; rw [hcomp]

中文:
引理 rank_smul_of_mem_nonZeroDivisors
  结论: {R : 类型} [交换环 R] {c : R} (B : 矩阵 m n R)
  证明: by
  have hc' : IsSMulRegular R c := isSMulRegular_iff_mem_nonZeroSMulDivisors.mpr hc.1
  have hreg : IsSMulRegular (m -> R) c := IsSMulRegular.pi fun _ => hc'
  let f := LinearMap.lsmul R (m -> R) c
  have hcomp : (c • B).mulVecLin = f.comp B.mulVecLin := by aesop
  rw [rank]; rw [rank]; rw [hcomp]

Depends on / 依赖: B.mulVecLin, IsSMulRegular, IsSMulRegular.pi, LinearMap, LinearMap.lsmul, LinearMap.range_comp, Submodule, Submodule.equivMapOfInjective, equivMapOfInjective, f.comp, finrank_eq, finrank_eq.symm, isSMulRegular_iff_mem_nonZeroSMulDivisors, isSMulRegular_iff_mem_nonZeroSMulDivisors.mpr, mulVecLin, range_comp
-/
lemma rank_smul_of_mem_nonZeroDivisors {R : Type*} [CommRing R] {c : R} (B : Matrix m n R)
    (hc : c in nonZeroDivisors R) : (c • B).rank = B.rank := by
  have hc' : IsSMulRegular R c := isSMulRegular_iff_mem_nonZeroSMulDivisors.mpr hc.1
  have hreg : IsSMulRegular (m -> R) c := IsSMulRegular.pi fun _ => hc'
  let f := LinearMap.lsmul R (m -> R) c
  have hcomp : (c • B).mulVecLin = f.comp B.mulVecLin := by aesop
  rw [rank]; rw [rank]; rw [hcomp]; rw [LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective f hreg _).finrank_eq.symm

/--
lemma `rank_mul_eq_left_of_det_mem_nonZeroDivisors` / 引理 `rank_mul_eq_left_of_det_mem_nonZeroDivisors`

English:
lemma rank_mul_eq_left_of_det_mem_nonZeroDivisors
  statement: {R : Type*} [CommRing R] [DecidableEq n]
  proof: by
  nontriviality R
  refine le_antisymm (rank_mul_le_left B A) ?_
  have key : (B * A) * A.adjugate = A.det • B := by
    rw [Matrix.mul_assoc]; rw [Matrix.mul_adjugate]; rw [Matrix.mul_smul]; rw [Matrix.mul_one]
  calc B.rank = (A.det • B).rank := (rank_smul_of_mem_nonZeroDivisors B hA).symm
    

中文:
引理 rank_mul_eq_left_of_det_mem_nonZeroDivisors
  结论: {R : 类型} [交换环 R] [DecidableEq n]
  证明: by
  nontriviality R
  refine le_antisymm (rank_mul_le_left B A) ?_
  have key : (B * A) * A.adjugate = A.det • B := by
    rw [Matrix.mul_assoc]; rw [Matrix.mul_adjugate]; rw [Matrix.mul_smul]; rw [Matrix.mul_one]
  calc B.rank = (A.det • B).rank := (rank_smul_of_mem_nonZeroDivisors B hA).symm
    

Depends on / 依赖: A.adjugate, A.det, B.rank, Matrix, Matrix.mul_adjugate, Matrix.mul_assoc, Matrix.mul_one, Matrix.mul_smul, adjugate, le_antisymm, mul_adjugate, mul_assoc, mul_one, mul_smul, nontriviality, rank_mul_le_left, rank_smul_of_mem_nonZeroDivisors
-/
lemma rank_mul_eq_left_of_det_mem_nonZeroDivisors {R : Type*} [CommRing R] [DecidableEq n]
    (A : Matrix n n R) (B : Matrix m n R) (hA : A.det in nonZeroDivisors R) :
    (B * A).rank = B.rank := by
  nontriviality R
  refine le_antisymm (rank_mul_le_left B A) ?_
  have key : (B * A) * A.adjugate = A.det • B := by
    rw [Matrix.mul_assoc]; rw [Matrix.mul_adjugate]; rw [Matrix.mul_smul]; rw [Matrix.mul_one]
  calc B.rank = (A.det • B).rank := (rank_smul_of_mem_nonZeroDivisors B hA).symm
    _ = ((B * A) * A.adjugate).rank := by rw [key]
    _ <= (B * A).rank := rank_mul_le_left _ _

/--
lemma `rank_mul_eq_left_of_det_ne_zero` / 引理 `rank_mul_eq_left_of_det_ne_zero`

English:
lemma rank_mul_eq_left_of_det_ne_zero
  statement: {R : Type*} [CommRing R] [IsDomain R] [DecidableEq n]
  proof: rank_mul_eq_left_of_det_mem_nonZeroDivisors A B (mem_nonZeroDivisors_of_ne_zero h)

中文:
引理 rank_mul_eq_left_of_det_ne_zero
  结论: {R : 类型} [交换环 R] [是整环 R] [DecidableEq n]
  证明: rank_mul_eq_left_of_det_mem_nonZeroDivisors A B (mem_nonZeroDivisors_of_ne_zero h)

Depends on / 依赖: mem_nonZeroDivisors_of_ne_zero, rank_mul_eq_left_of_det_mem_nonZeroDivisors
-/
lemma rank_mul_eq_left_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R] [DecidableEq n]
    (A : Matrix n n R) (B : Matrix m n R) (h : A.det != 0) : (B * A).rank = B.rank :=
  rank_mul_eq_left_of_det_mem_nonZeroDivisors A B (mem_nonZeroDivisors_of_ne_zero h)

/-- Right multiplying by an invertible matrix does not change the rank -/
@[simp]
/--
lemma `rank_mul_eq_left_of_isUnit_det` / 引理 `rank_mul_eq_left_of_isUnit_det`

English:
lemma rank_mul_eq_left_of_isUnit_det
  statement: {R : Type*} [CommRing R] [DecidableEq n] (A : Matrix n n R)
  proof: rank_mul_eq_left_of_det_mem_nonZeroDivisors A B hA.mem_nonZeroDivisors

中文:
引理 rank_mul_eq_left_of_isUnit_det
  结论: {R : 类型} [交换环 R] [DecidableEq n] (A : 矩阵 n n R)
  证明: rank_mul_eq_left_of_det_mem_nonZeroDivisors A B hA.mem_nonZeroDivisors

Depends on / 依赖: hA.mem_nonZeroDivisors, mem_nonZeroDivisors, rank_mul_eq_left_of_det_mem_nonZeroDivisors
-/
lemma rank_mul_eq_left_of_isUnit_det {R : Type*} [CommRing R] [DecidableEq n] (A : Matrix n n R)
    (B : Matrix m n R) (hA : IsUnit A.det) : (B * A).rank = B.rank :=
  rank_mul_eq_left_of_det_mem_nonZeroDivisors A B hA.mem_nonZeroDivisors

/--
lemma `rank_mul_eq_right_of_det_mem_nonZeroDivisors` / 引理 `rank_mul_eq_right_of_det_mem_nonZeroDivisors`

English:
lemma rank_mul_eq_right_of_det_mem_nonZeroDivisors
  statement: {R : Type*} [CommRing R]
  proof: by
  rw [rank]; rw [rank]; rw [mulVecLin_mul]; rw [LinearMap.range_comp]; rw [← (Submodule.equivMapOfInjective A.mulVecLin
      (mulVec_injective_of_det_mem_nonZeroDivisors hA) _).finrank_eq]

中文:
引理 rank_mul_eq_right_of_det_mem_nonZeroDivisors
  结论: {R : 类型} [交换环 R]
  证明: by
  rw [rank]; rw [rank]; rw [mulVecLin_mul]; rw [LinearMap.range_comp]; rw [← (Submodule.equivMapOfInjective A.mulVecLin
      (mulVec_injective_of_det_mem_nonZeroDivisors hA) _).finrank_eq]

Depends on / 依赖: A.mulVecLin, LinearMap, LinearMap.range_comp, Submodule, Submodule.equivMapOfInjective, equivMapOfInjective, finrank_eq, mulVecLin, mulVecLin_mul, mulVec_injective_of_det_mem_nonZeroDivisors, range_comp
-/
lemma rank_mul_eq_right_of_det_mem_nonZeroDivisors {R : Type*} [CommRing R]
    [Fintype m] [DecidableEq m] (A : Matrix m m R) (B : Matrix m n R)
    (hA : A.det in nonZeroDivisors R) : (A * B).rank = B.rank := by
  rw [rank]; rw [rank]; rw [mulVecLin_mul]; rw [LinearMap.range_comp]; rw [← (Submodule.equivMapOfInjective A.mulVecLin
      (mulVec_injective_of_det_mem_nonZeroDivisors hA) _).finrank_eq]

/--
lemma `rank_mul_eq_right_of_det_ne_zero` / 引理 `rank_mul_eq_right_of_det_ne_zero`

English:
lemma rank_mul_eq_right_of_det_ne_zero
  statement: {R : Type*} [CommRing R] [IsDomain R]
  proof: rank_mul_eq_right_of_det_mem_nonZeroDivisors A B (mem_nonZeroDivisors_of_ne_zero h)

中文:
引理 rank_mul_eq_right_of_det_ne_zero
  结论: {R : 类型} [交换环 R] [是整环 R]
  证明: rank_mul_eq_right_of_det_mem_nonZeroDivisors A B (mem_nonZeroDivisors_of_ne_zero h)

Depends on / 依赖: mem_nonZeroDivisors_of_ne_zero, rank_mul_eq_right_of_det_mem_nonZeroDivisors
-/
lemma rank_mul_eq_right_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    [Fintype m] [DecidableEq m] (A : Matrix m m R) (B : Matrix m n R) (h : A.det != 0) :
    (A * B).rank = B.rank :=
  rank_mul_eq_right_of_det_mem_nonZeroDivisors A B (mem_nonZeroDivisors_of_ne_zero h)

/-- Left multiplying by an invertible matrix does not change the rank -/
@[simp]
/--
lemma `rank_mul_eq_right_of_isUnit_det` / 引理 `rank_mul_eq_right_of_isUnit_det`

English:
lemma rank_mul_eq_right_of_isUnit_det
  statement: {R : Type*} [CommRing R] [Fintype m] [DecidableEq m]
  proof: rank_mul_eq_right_of_det_mem_nonZeroDivisors A B hA.mem_nonZeroDivisors

中文:
引理 rank_mul_eq_right_of_isUnit_det
  结论: {R : 类型} [交换环 R] [有限类型 m] [DecidableEq m]
  证明: rank_mul_eq_right_of_det_mem_nonZeroDivisors A B hA.mem_nonZeroDivisors

Depends on / 依赖: hA.mem_nonZeroDivisors, mem_nonZeroDivisors, rank_mul_eq_right_of_det_mem_nonZeroDivisors
-/
lemma rank_mul_eq_right_of_isUnit_det {R : Type*} [CommRing R] [Fintype m] [DecidableEq m]
    (A : Matrix m m R) (B : Matrix m n R) (hA : IsUnit A.det) : (A * B).rank = B.rank :=
  rank_mul_eq_right_of_det_mem_nonZeroDivisors A B hA.mem_nonZeroDivisors

/--
lemma `rank_mul_eq_right_of_isLowerTriangular` / 引理 `rank_mul_eq_right_of_isLowerTriangular`

English:
lemma rank_mul_eq_right_of_isLowerTriangular
  statement: {R : Type*} [CommRing R] [IsDomain R]
  proof: by
  have hdet : A.det != 0 := by simpa [det_of_isLowerTriangular A hA, Finset.prod_ne_zero_iff]
  exact rank_mul_eq_right_of_det_ne_zero A B hdet

中文:
引理 rank_mul_eq_right_of_isLowerTriangular
  结论: {R : 类型} [交换环 R] [是整环 R]
  证明: by
  have hdet : A.det != 0 := by simpa [det_of_isLowerTriangular A hA, Finset.prod_ne_zero_iff]
  exact rank_mul_eq_right_of_det_ne_zero A B hdet

Depends on / 依赖: A.det, Finset, Finset.prod_ne_zero_iff, det_of_isLowerTriangular, prod_ne_zero_iff, rank_mul_eq_right_of_det_ne_zero
-/
lemma rank_mul_eq_right_of_isLowerTriangular {R : Type*} [CommRing R] [IsDomain R]
    [Fintype m] [LinearOrder m] (A : Matrix m m R) (B : Matrix m n R)
    (hA : A.IsLowerTriangular) (hd : forall i, A.diag i != 0) : (A * B).rank = B.rank := by
  have hdet : A.det != 0 := by simpa [det_of_isLowerTriangular A hA, Finset.prod_ne_zero_iff]
  exact rank_mul_eq_right_of_det_ne_zero A B hdet

/--
lemma `rank_mul_eq_right_of_isUpperTriangular` / 引理 `rank_mul_eq_right_of_isUpperTriangular`

English:
lemma rank_mul_eq_right_of_isUpperTriangular
  statement: {R : Type*} [CommRing R] [IsDomain R]
  proof: by
  have hdet : A.det != 0 := by simpa [det_of_isUpperTriangular hA, Finset.prod_ne_zero_iff]
  exact rank_mul_eq_right_of_det_ne_zero A B hdet

中文:
引理 rank_mul_eq_right_of_isUpperTriangular
  结论: {R : 类型} [交换环 R] [是整环 R]
  证明: by
  have hdet : A.det != 0 := by simpa [det_of_isUpperTriangular hA, Finset.prod_ne_zero_iff]
  exact rank_mul_eq_right_of_det_ne_zero A B hdet

Depends on / 依赖: A.det, Finset, Finset.prod_ne_zero_iff, det_of_isUpperTriangular, prod_ne_zero_iff, rank_mul_eq_right_of_det_ne_zero
-/
lemma rank_mul_eq_right_of_isUpperTriangular {R : Type*} [CommRing R] [IsDomain R]
    [Fintype m] [LinearOrder m] (A : Matrix m m R) (B : Matrix m n R)
    (hA : A.IsUpperTriangular) (hd : forall i, A.diag i != 0) : (A * B).rank = B.rank := by
  have hdet : A.det != 0 := by simpa [det_of_isUpperTriangular hA, Finset.prod_ne_zero_iff]
  exact rank_mul_eq_right_of_det_ne_zero A B hdet

/--
theorem `rank_submatrix_le` / 定理 `rank_submatrix_le`

English:
theorem rank_submatrix_le
  statement: [CommSemiring R] [StrongRankCondition R] [Fintype n₀] (A : Matrix m n R)
  proof: by
  nontriviality R
  have := Module.Finite.span_of_finite R (Set.finite_range (A.submatrix r id).col)
  calc
    _ = (((A.submatrix r id)ᵀᵀ.submatrix id c)ᵀᵀ).rank := by simp
    _ <= finrank R (span R (range (A.submatrix r id).col)) := by
      rw [rank]; rw [Matrix.mulVecLin_transpose]; rw [Matr

中文:
定理 rank_submatrix_le
  结论: [交换半环 R] [StrongRankCondition R] [有限类型 n₀] (A : 矩阵 m n R)
  证明: by
  nontriviality R
  have := Module.Finite.span_of_finite R (Set.finite_range (A.submatrix r id).col)
  calc
    _ = (((A.submatrix r id)ᵀᵀ.submatrix id c)ᵀᵀ).rank := by simp
    _ <= finrank R (span R (range (A.submatrix r id).col)) := by
      rw [rank]; rw [Matrix.mulVecLin_transpose]; rw [Matr

Depends on / 依赖: A.sub, A.submatrix, Finite, Matrix, Matrix.mulVecLin_transpose, Matrix.transpose_submatrix, Module, Module.Finite.span_of_finite, Set.finite_range, Submodule, Submodule.finrank_mono, Submodule.span_mono, finite_range, finrank, finrank_mono, mulVecLin_transpose, nontriviality, range_vecMulLinear, row_transpose, span_mono
-/
theorem rank_submatrix_le [CommSemiring R] [StrongRankCondition R] [Fintype n₀] (A : Matrix m n R)
    (r : m₀ -> m) (c : n₀ -> n) : (A.submatrix r c).rank <= A.rank := by
  nontriviality R
  have := Module.Finite.span_of_finite R (Set.finite_range (A.submatrix r id).col)
  calc
    _ = (((A.submatrix r id)ᵀᵀ.submatrix id c)ᵀᵀ).rank := by simp
    _ <= finrank R (span R (range (A.submatrix r id).col)) := by
      rw [rank]; rw [Matrix.mulVecLin_transpose]; rw [Matrix.transpose_submatrix]; rw [transpose_transpose]; rw [range_vecMulLinear]; rw [← Matrix.transpose_submatrix]; rw [row_transpose]
      exact Submodule.finrank_mono (Submodule.span_mono (fun v ⟨j, hj⟩ => ⟨c j, hj⟩))
    _ = (A.submatrix r id)ᵀᵀ.rank := by
      rw [rank]; rw [Matrix.mulVecLin_transpose]; rw [range_vecMulLinear]
      rfl
    _ = (A.submatrix r (Equiv.refl n)).rank := by simp
  rw [rank]; rw [rank]; rw [mulVecLin_submatrix]; rw [LinearMap.range_comp]; rw [LinearMap.range_comp]; rw [show LinearMap.funLeft R R (Equiv.refl n).symm = LinearEquiv.funCongrLeft R R
      (Equiv.refl n).symm from rfl]; rw [LinearEquiv.range]; rw [Submodule.map_top]
  exact Submodule.finrank_map_le _ _

/--
theorem `rank_reindex` / 定理 `rank_reindex`

English:
theorem rank_reindex
  given: [Fintype n₀] [CommSemiring R] (em : m ≃ m₀) (en : n ≃ n₀) (A : Matrix m n R)
  proof: by
  rw [rank]; rw [rank]; rw [mulVecLin_reindex]; rw [LinearMap.range_comp]; rw [LinearMap.range_comp]; rw [LinearEquiv.range]; rw [Submodule.map_top]; rw [LinearEquiv.finrank_map_eq]

@[simp]

中文:
定理 rank_reindex
  条件: [有限类型 n₀] [交换半环 R] (em : m ≃ m₀) (en : n ≃ n₀) (A : 矩阵 m n R)
  证明: by
  rw [rank]; rw [rank]; rw [mulVecLin_reindex]; rw [LinearMap.range_comp]; rw [LinearMap.range_comp]; rw [LinearEquiv.range]; rw [Submodule.map_top]; rw [LinearEquiv.finrank_map_eq]

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.finrank_map_eq, LinearEquiv.range, LinearMap, LinearMap.range_comp, Submodule, Submodule.map_top, finrank_map_eq, map_top, mulVecLin_reindex, range_comp
-/
theorem rank_reindex [Fintype n₀] [CommSemiring R] (em : m ≃ m₀) (en : n ≃ n₀) (A : Matrix m n R) :
    rank (A.reindex em en) = rank A := by
  rw [rank]; rw [rank]; rw [mulVecLin_reindex]; rw [LinearMap.range_comp]; rw [LinearMap.range_comp]; rw [LinearEquiv.range]; rw [Submodule.map_top]; rw [LinearEquiv.finrank_map_eq]

@[simp]
/--
theorem `rank_submatrix` / 定理 `rank_submatrix`

English:
theorem rank_submatrix
  statement: [Fintype n₀] [CommSemiring R] (A : Matrix m n R) (em : m₀ ≃ m)
  proof: by
  simpa only [reindex_apply] using! rank_reindex em.symm en.symm A

@[simp]

中文:
定理 rank_submatrix
  结论: [有限类型 n₀] [交换半环 R] (A : 矩阵 m n R) (em : m₀ ≃ m)
  证明: by
  simpa only [reindex_apply] using! rank_reindex em.symm en.symm A

@[simp]

Depends on / 依赖: em.symm, en.symm, rank_reindex, reindex_apply
-/
theorem rank_submatrix [Fintype n₀] [CommSemiring R] (A : Matrix m n R) (em : m₀ ≃ m)
    (en : n₀ ≃ n) : rank (A.submatrix em en) = rank A := by
  simpa only [reindex_apply] using! rank_reindex em.symm en.symm A

@[simp]
/--
theorem `lift_cRank_submatrix` / 定理 `lift_cRank_submatrix`

English:
theorem lift_cRank_submatrix
  statement: {n : Type un} [Semiring R] (A : Matrix m n R) (em : m₀ ≃ m)
  proof: (A.lift_cRank_submatrix_le em en).antisymm
 by simpa using ((A.reindex em.symm en.symm).lift_cRank_submatrix_le em.symm en.symm)

中文:
定理 lift_cRank_submatrix
  结论: {n : 类型un} [半环 R] (A : 矩阵 m n R) (em : m₀ ≃ m)
  证明: (A.lift_cRank_submatrix_le em en).antisymm
 by simpa using ((A.reindex em.symm en.symm).lift_cRank_submatrix_le em.symm en.symm)

Depends on / 依赖: A.lift_cRank_submatrix_le, A.reindex, antisymm, em.symm, en.symm, lift_cRank_submatrix_le, reindex
-/
theorem lift_cRank_submatrix {n : Type un} [Semiring R] (A : Matrix m n R) (em : m₀ ≃ m)
    (en : n₀ ≃ n) : lift.{um} (cRank (A.submatrix em en)) = lift.{um₀} (cRank A) :=
  (A.lift_cRank_submatrix_le em en).antisymm
 by simpa using ((A.reindex em.symm en.symm).lift_cRank_submatrix_le em.symm en.symm)

/-- A special case of `lift_cRank_submatrix` for when the row types are in the same universe. -/
@[simp]
/--
theorem `cRank_submatrix` / 定理 `cRank_submatrix`

English:
theorem cRank_submatrix
  statement: {m₀ : Type um} {n : Type un} [Semiring R] (A : Matrix m n R) (em : m₀ ≃ m)
  proof: by
  simpa [-lift_cRank_submatrix] using A.lift_cRank_submatrix em en

中文:
定理 cRank_submatrix
  结论: {m₀ : 类型um} {n : 类型un} [半环 R] (A : 矩阵 m n R) (em : m₀ ≃ m)
  证明: by
  simpa [-lift_cRank_submatrix] using A.lift_cRank_submatrix em en

Depends on / 依赖: A.lift_cRank_submatrix, lift_cRank_submatrix
-/
theorem cRank_submatrix {m₀ : Type um} {n : Type un} [Semiring R] (A : Matrix m n R) (em : m₀ ≃ m)
    (en : n₀ ≃ n) : cRank (A.submatrix em en) = cRank A := by
  simpa [-lift_cRank_submatrix] using A.lift_cRank_submatrix em en

/--
theorem `lift_cRank_reindex` / 定理 `lift_cRank_reindex`

English:
theorem lift_cRank_reindex
  statement: {n : Type un} [Semiring R] (A : Matrix m n R) (em : m ≃ m₀)
  proof: lift_cRank_submatrix ..

中文:
定理 lift_cRank_reindex
  结论: {n : 类型un} [半环 R] (A : 矩阵 m n R) (em : m ≃ m₀)
  证明: lift_cRank_submatrix ..

Depends on / 依赖: lift_cRank_submatrix
-/
theorem lift_cRank_reindex {n : Type un} [Semiring R] (A : Matrix m n R) (em : m ≃ m₀)
    (en : n ≃ n₀) : lift.{um} (cRank (A.reindex em en)) = lift.{um₀} (cRank A) :=
  lift_cRank_submatrix ..

/--
theorem `cRank_reindex` / 定理 `cRank_reindex`

English:
theorem cRank_reindex
  statement: {m₀ : Type um} {n : Type un} [Semiring R] (A : Matrix m n R) (em : m ≃ m₀)
  proof: cRank_submatrix ..

@[simp]

中文:
定理 cRank_reindex
  结论: {m₀ : 类型um} {n : 类型un} [半环 R] (A : 矩阵 m n R) (em : m ≃ m₀)
  证明: cRank_submatrix ..

@[simp]

Depends on / 依赖: cRank_submatrix
-/
theorem cRank_reindex {m₀ : Type um} {n : Type un} [Semiring R] (A : Matrix m n R) (em : m ≃ m₀)
    (en : n ≃ n₀) : cRank (A.reindex em en) = cRank A :=
  cRank_submatrix ..

@[simp]
/--
theorem `eRank_submatrix` / 定理 `eRank_submatrix`

English:
theorem eRank_submatrix
  given: {n : Type un} [Semiring R] (A : Matrix m n R) (em : m₀ ≃ m) (en : n₀ ≃ n)
  proof: by
simpa [-lift_cRank_submatrix] using! congr_arg Cardinal.toENat A.lift_cRank_submatrix em en

中文:
定理 eRank_submatrix
  条件: {n : 类型un} [半环 R] (A : 矩阵 m n R) (em : m₀ ≃ m) (en : n₀ ≃ n)
  证明: by
simpa [-lift_cRank_submatrix] using! congr_arg Cardinal.toENat A.lift_cRank_submatrix em en

Depends on / 依赖: A.lift_cRank_submatrix, Cardinal, Cardinal.toENat, congr_arg, lift_cRank_submatrix, toENat
-/
theorem eRank_submatrix {n : Type un} [Semiring R] (A : Matrix m n R) (em : m₀ ≃ m) (en : n₀ ≃ n) :
    eRank (A.submatrix em en) = eRank A := by
simpa [-lift_cRank_submatrix] using! congr_arg Cardinal.toENat A.lift_cRank_submatrix em en

/--
theorem `eRank_reindex` / 定理 `eRank_reindex`

English:
theorem eRank_reindex
  statement: {m₀ : Type um} {n : Type un} [Semiring R] (A : Matrix m n R) (em : m ≃ m₀)
  proof: eRank_submatrix ..

中文:
定理 eRank_reindex
  结论: {m₀ : 类型um} {n : 类型un} [半环 R] (A : 矩阵 m n R) (em : m ≃ m₀)
  证明: eRank_submatrix ..

Depends on / 依赖: eRank_submatrix
-/
theorem eRank_reindex {m₀ : Type um} {n : Type un} [Semiring R] (A : Matrix m n R) (em : m ≃ m₀)
    (en : n ≃ n₀) : eRank (A.reindex em en) = eRank A :=
  eRank_submatrix ..

set_option backward.isDefEq.respectTransparency false in
/--
theorem `rank_eq_finrank_range_toLin` / 定理 `rank_eq_finrank_range_toLin`

English:
theorem rank_eq_finrank_range_toLin
  statement: [Finite m] [DecidableEq n] {M₁ M₂ : Type*} [CommSemiring R]
  proof: by
  cases nonempty_fintype m
  let e₁ := (Pi.basisFun R m).equiv v₁ (Equiv.refl _)
  let e₂ := (Pi.basisFun R n).equiv v₂ (Equiv.refl _)
  refine LinearEquiv.finrank_eq (e₁.ofSubmodules _ _ ?_)
  rw [← LinearMap.range_comp]; rw [← LinearMap.range_comp_of_range_eq_top (toLin v₂ v₁ A) e₂.range]
  con

中文:
定理 rank_eq_finrank_range_toLin
  结论: [有限 m] [DecidableEq n] {M₁ M₂ : 类型} [交换半环 R]
  证明: by
  cases nonempty_fintype m
  let e₁ := (Pi.basisFun R m).equiv v₁ (Equiv.refl _)
  let e₂ := (Pi.basisFun R n).equiv v₂ (Equiv.refl _)
  refine LinearEquiv.finrank_eq (e₁.ofSubmodules _ _ ?_)
  rw [← LinearMap.range_comp]; rw [← LinearMap.range_comp_of_range_eq_top (toLin v₂ v₁ A) e₂.range]
  con

Depends on / 依赖: Basis.equiv_apply, Equiv.refl, LinearEquiv, LinearEquiv.finrank_eq, LinearMap, LinearMap.ext_ring, LinearMap.pi_ext, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top, Pi.basisFun, basisFun, equiv_apply, ext_ring, finrank_eq, nonempty_fintype, ofSubmodules, pi_ext, range_comp, range_comp_of_range_eq_top, toLin_eq_toLin
-/
theorem rank_eq_finrank_range_toLin [Finite m] [DecidableEq n] {M₁ M₂ : Type*} [CommSemiring R]
    [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂] (A : Matrix m n R)
    (v₁ : Basis m R M₁) (v₂ : Basis n R M₂) :
    A.rank = finrank R (LinearMap.range (toLin v₂ v₁ A)) := by
  cases nonempty_fintype m
  let e₁ := (Pi.basisFun R m).equiv v₁ (Equiv.refl _)
  let e₂ := (Pi.basisFun R n).equiv v₂ (Equiv.refl _)
  refine LinearEquiv.finrank_eq (e₁.ofSubmodules _ _ ?_)
  rw [← LinearMap.range_comp]; rw [← LinearMap.range_comp_of_range_eq_top (toLin v₂ v₁ A) e₂.range]
  congr 1
  apply LinearMap.pi_ext'
  rintro i
  apply LinearMap.ext_ring
  have aux₁ := toLin_self (Pi.basisFun R n) (Pi.basisFun R m) A i
  have aux₂ := Basis.equiv_apply (Pi.basisFun R n) i v₂
  rw [toLin_eq_toLin']; rw [toLin'_apply'] at aux₁
  rw [Pi.basisFun_apply] at aux₁ aux₂
  simp only [e₁, e₂, LinearMap.comp_apply, LinearEquiv.coe_coe, Equiv.refl_apply,
    aux₁, aux₂, LinearMap.coe_single, toLin_self, map_sum, map_smul, Basis.equiv_apply]

/--
theorem `rank_le_card_height` / 定理 `rank_le_card_height`

English:
theorem rank_le_card_height
  statement: [Fintype m] [CommSemiring R] [StrongRankCondition R]
  proof: (Submodule.finrank_le _).trans (finrank_pi R).le

中文:
定理 rank_le_card_height
  结论: [有限类型 m] [交换半环 R] [StrongRankCondition R]
  证明: (Submodule.finrank_le _).trans (finrank_pi R).le

Depends on / 依赖: Submodule, Submodule.finrank_le, finrank_le, finrank_pi
-/
theorem rank_le_card_height [Fintype m] [CommSemiring R] [StrongRankCondition R]
    (A : Matrix m n R) : A.rank <= Fintype.card m :=
  (Submodule.finrank_le _).trans (finrank_pi R).le

/--
theorem `rank_le_card_of_support_subset` / 定理 `rank_le_card_of_support_subset`

English:
theorem rank_le_card_of_support_subset
  statement: [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R)
  proof: by
  rw [Function.support_subset_iff'] at hz
  classical
  set B : Matrix m {x // x in s} R := Matrix.of fun i a => if (a : m) = i then 1 else 0 with hBdef
  have hB : B * A.submatrix Subtype.val id = A := by
    ext i j
    simp only [hBdef, mul_apply, of_apply, submatrix_apply, id_eq]
    by_cases

中文:
定理 rank_le_card_of_support_subset
  结论: [交换半环 R] [StrongRankCondition R] (A : 矩阵 m n R)
  证明: by
  rw [Function.support_subset_iff'] at hz
  classical
  set B : Matrix m {x // x in s} R := Matrix.of fun i a => if (a : m) = i then 1 else 0 with hBdef
  have hB : B * A.submatrix Subtype.val id = A := by
    ext i j
    simp only [hBdef, mul_apply, of_apply, submatrix_apply, id_eq]
    by_cases

Depends on / 依赖: A.rank, A.submat, A.submatrix, Fintype, Fintype.sum_eq_single, Function, Function.support_subset_iff, Matrix, Matrix.of, Subtype, Subtype.ext, Subtype.val, classical, id_eq, if_neg, if_pos, mul_apply, of_apply, one_mul, submat
-/
theorem rank_le_card_of_support_subset [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R)
    (s : Finset m) (hz : Function.support A.row subseteq s) : A.rank <= s.card := by
  rw [Function.support_subset_iff'] at hz
  classical
  set B : Matrix m {x // x in s} R := Matrix.of fun i a => if (a : m) = i then 1 else 0 with hBdef
  have hB : B * A.submatrix Subtype.val id = A := by
    ext i j
    simp only [hBdef, mul_apply, of_apply, submatrix_apply, id_eq]
    by_cases hi : i in s
    · rw [Fintype.sum_eq_single (⟨i, hi⟩ : {x // x in s})
        fun a ha => by rw [if_neg fun he => ha (Subtype.ext he), zero_mul], if_pos rfl, one_mul]
    · have h0 : A i = 0 := hz i hi
      aesop
  calc A.rank = (B * A.submatrix Subtype.val id).rank := by rw [hB]
    _ <= (A.submatrix Subtype.val id).rank := rank_mul_le_right _ _
    _ <= Fintype.card {x // x in s} := rank_le_card_height _
    _ = s.card := Fintype.card_coe s

/--
theorem `rank_le_height` / 定理 `rank_le_height`

English:
theorem rank_le_height
  statement: [CommSemiring R] [StrongRankCondition R] {m n : Nat}
  proof: A.rank_le_card_height.trans (Fintype.card_fin m).le

中文:
定理 rank_le_height
  结论: [交换半环 R] [StrongRankCondition R] {m n : 自然数}
  证明: A.rank_le_card_height.trans (Fintype.card_fin m).le

Depends on / 依赖: A.rank_le_card_height.trans, Fintype, Fintype.card_fin, card_fin, rank_le_card_height
-/
theorem rank_le_height [CommSemiring R] [StrongRankCondition R] {m n : Nat}
    (A : Matrix (Fin m) (Fin n) R) : A.rank <= m :=
  A.rank_le_card_height.trans (Fintype.card_fin m).le

/--
theorem `rank_eq_finrank_span_cols` / 定理 `rank_eq_finrank_span_cols`

English:
theorem rank_eq_finrank_span_cols
  given: [CommSemiring R] (A : Matrix m n R)
  proof: by rw [rank, Matrix.range_mulVecLin]

@[simp]

中文:
定理 rank_eq_finrank_span_cols
  条件: [交换半环 R] (A : 矩阵 m n R)
  证明: by rw [rank, Matrix.range_mulVecLin]

@[simp]

Depends on / 依赖: Matrix, Matrix.range_mulVecLin, h.symm, range_mulVecLin
-/
theorem rank_eq_finrank_span_cols [CommSemiring R] (A : Matrix m n R) :
    A.rank = finrank R (Submodule.span R (Set.range A.col)) := by rw [rank, Matrix.range_mulVecLin]

@[simp]
/--
theorem `cRank_toNat_eq_rank` / 定理 `cRank_toNat_eq_rank`

English:
theorem cRank_toNat_eq_rank
  given: [CommSemiring R] (A : Matrix m n R)
  statement: A.cRank.toNat = A.rank
  proof: by
  rw [cRank_toNat_eq_finrank]; rw [← rank_eq_finrank_span_cols]

@[simp]

中文:
定理 cRank_to自然数_eq_rank
  条件: [交换半环 R] (A : 矩阵 m n R)
  结论: A.cRank.to自然数 = A.rank
  证明: by
  rw [cRank_toNat_eq_finrank]; rw [← rank_eq_finrank_span_cols]

@[simp]

Depends on / 依赖: cRank_toNat_eq_finrank, rank_eq_finrank_span_cols
-/
theorem cRank_toNat_eq_rank [CommSemiring R] (A : Matrix m n R) : A.cRank.toNat = A.rank := by
  rw [cRank_toNat_eq_finrank]; rw [← rank_eq_finrank_span_cols]

@[simp]
/--
theorem `eRank_toNat_eq_rank` / 定理 `eRank_toNat_eq_rank`

English:
theorem eRank_toNat_eq_rank
  given: [CommSemiring R] (A : Matrix m n R)
  statement: A.eRank.toNat = A.rank
  proof: by
  rw [eRank_toNat_eq_finrank]; rw [← rank_eq_finrank_span_cols]

中文:
定理 eRank_to自然数_eq_rank
  条件: [交换半环 R] (A : 矩阵 m n R)
  结论: A.eRank.to自然数 = A.rank
  证明: by
  rw [eRank_toNat_eq_finrank]; rw [← rank_eq_finrank_span_cols]

Depends on / 依赖: eRank_toNat_eq_finrank, rank_eq_finrank_span_cols
-/
theorem eRank_toNat_eq_rank [CommSemiring R] (A : Matrix m n R) : A.eRank.toNat = A.rank := by
  rw [eRank_toNat_eq_finrank]; rw [← rank_eq_finrank_span_cols]

section Field

variable [Field R]

/--
theorem `rank_diagonal` / 定理 `rank_diagonal`

English:
theorem rank_diagonal
  given: [Fintype m] [DecidableEq m] [DecidableEq R] (w : m -> R)
  proof: by
  rw [Matrix.rank]; rw [← Matrix.toLin'_apply']; rw [Module.finrank]; rw [← LinearMap.rank]; rw [LinearMap.rank_diagonal]; rw [Cardinal.toNat_natCast]

中文:
定理 rank_diagonal
  条件: [有限类型 m] [DecidableEq m] [DecidableEq R] (w : m -> R)
  证明: by
  rw [Matrix.rank]; rw [← Matrix.toLin'_apply']; rw [Module.finrank]; rw [← LinearMap.rank]; rw [LinearMap.rank_diagonal]; rw [Cardinal.toNat_natCast]

Depends on / 依赖: Cardinal, Cardinal.toNat_natCast, LinearMap, LinearMap.rank, LinearMap.rank_diagonal, Matrix, Matrix.rank, Matrix.toLin, Module, Module.finrank, _apply, finrank, rank_diagonal, toNat_natCast
-/
theorem rank_diagonal [Fintype m] [DecidableEq m] [DecidableEq R] (w : m -> R) :
    (diagonal w).rank = Fintype.card {i // (w i) != 0} := by
  rw [Matrix.rank]; rw [← Matrix.toLin'_apply']; rw [Module.finrank]; rw [← LinearMap.rank]; rw [LinearMap.rank_diagonal]; rw [Cardinal.toNat_natCast]

open TransvectionStruct in
/--
theorem `exists_rank_normal_form` / 定理 `exists_rank_normal_form`

English:
theorem exists_rank_normal_form
  given: [Fintype m] [DecidableEq m] (M : Matrix m m R)
  proof: by
  classical
  obtain ⟨L, L', D, hM0⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  set E := fun i => if D i = 0 then 1 else (D i)⁻¹ with E_def
  set s : Finset m := .filter (fun i => D i != 0) .univ with s_def
  set V := diagonal E * (L.reverse.map (toMatrix ∘ .inv)).pro

中文:
定理 存在_rank_normal_form
  条件: [有限类型 m] [DecidableEq m] (M : 矩阵 m m R)
  证明: by
  classical
  obtain ⟨L, L', D, hM0⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  set E := fun i => if D i = 0 then 1 else (D i)⁻¹ with E_def
  set s : Finset m := .filter (fun i => D i != 0) .univ with s_def
  set V := diagonal E * (L.reverse.map (toMatrix ∘ .inv)).pro

Depends on / 依赖: E_def, Finset, IsUnit, L.reverse.map, Matrix, Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec, U.det, U_def, V.det, V_def, classical, det_m, diagonal, exists_list_transvec_mul_diagonal_mul_list_transvec, filter, isUnit_iff_isUnit_det, isUnit_prod_comp_inverse, reverse, reverse.map, s_def
-/
theorem exists_rank_normal_form [Fintype m] [DecidableEq m] (M : Matrix m m R) :
    exists (V U : Matrix m m R) (e : m ≃ Fin M.rank oplus Fin (Fintype.card m - M.rank)),
      IsUnit V ∧ IsUnit U ∧
      V * M * U = (fromBlocks 1 0 0 0).submatrix e e := by
  classical
  obtain ⟨L, L', D, hM0⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  set E := fun i => if D i = 0 then 1 else (D i)⁻¹ with E_def
  set s : Finset m := .filter (fun i => D i != 0) .univ with s_def
  set V := diagonal E * (L.reverse.map (toMatrix ∘ .inv)).prod with V_def
  set U := (L'.reverse.map (toMatrix ∘ .inv)).prod with U_def
have hUdet : IsUnit U.det := (isUnit_iff_isUnit_det _).1 isUnit_prod_comp_inverse _
  have hVdet : IsUnit V.det := by
    rw [V_def]; rw [det_mul]; rw [det_diagonal]
.mul exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 (by grind))
      (isUnit_iff_isUnit_det _).1 (isUnit_prod_comp_inverse _)
  have hM : V * M * U = diagonal (fun i => if i in s then 1 else 0) := by
    rw [V_def]; rw [U_def]; rw [hM0]; rw [mul_assoc]; rw [mul_assoc _ (L'.map _).prod]; rw [prod_mul_reverse_inv_prod]; rw [mul_one]; rw [← mul_assoc]; rw [mul_assoc _ (L.reverse.map _).prod]; rw [reverse_inv_prod_mul_prod]; rw [mul_one]
    ext
    simp only [E_def, mul_diagonal, diagonal_apply, ite_mul, one_mul, zero_mul, s_def,
      Finset.mem_filter, Finset.mem_univ, true_and, ite_not]
    split_ifs with h1 h2 <;> first | rw [← h1, h2] | rw [← h1, inv_mul_cancel₀ h2] | rfl
  have hs : s.card = M.rank := by
    simp [← rank_mul_eq_right_of_isUnit_det V M hVdet, ← rank_mul_eq_left_of_isUnit_det U (V * M)
      hUdet, hM, rank_diagonal]
  set e : m ≃ Fin M.rank oplus Fin (Fintype.card m - M.rank) :=
(Equiv.sumCompl (· in s)).symm.trans (Finset.equivFinOfCardEq hs).sumCongr
Fintype.equivFinOfCardEq by rw [Fintype.card_subtype_compl, Fintype.card_coe, hs] with he
  refine ⟨V, U, e, (isUnit_iff_isUnit_det _).2 hVdet, isUnit_prod_comp_inverse _, ?_⟩
  rw [hM]; rw [← diagonal_one]; rw [← diagonal_zero]; rw [fromBlocks_diagonal]; rw [submatrix_diagonal_equiv]
  refine congrArg _ (funext fun i => ?_)
  split_ifs with hi <;> simp [he, hi]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `cRank_diagonal` / 定理 `cRank_diagonal`

English:
theorem cRank_diagonal
  given: [DecidableEq m] (w : m -> R)
  proof: by
  classical
  set w' : {i // (w i) != 0} -> _ := fun i => (diagonal w) i
  have h : LinearIndependent R w' := by
    have hli' := Pi.linearIndependent_single_of_ne_zero (R := R)
      (v := fun i : m => if w i = 0 then (1 : R) else w i) (by simp [ite_eq_iff'])
    convert! hli'.comp Subtype.val S

中文:
定理 cRank_diagonal
  条件: [DecidableEq m] (w : m -> R)
  证明: by
  classical
  set w' : {i // (w i) != 0} -> _ := fun i => (diagonal w) i
  have h : LinearIndependent R w' := by
    have hli' := Pi.linearIndependent_single_of_ne_zero (R := R)
      (v := fun i : m => if w i = 0 then (1 : R) else w i) (by simp [ite_eq_iff'])
    convert! hli'.comp Subtype.val S

Depends on / 依赖: LinearIndependent, Pi.linearIndependent_single_of_ne_zero, Pi.single_apply, Subtype, Subtype.val, Subtype.val_injective, classical, convert, diagonal, eq_comm, insert, ite_eq_iff, linearIndependent_single_of_ne_zero, single_apply, val_injective
-/
theorem cRank_diagonal [DecidableEq m] (w : m -> R) :
    (diagonal w).cRank = lift.{uR} #{i // (w i) != 0} := by
  classical
  set w' : {i // (w i) != 0} -> _ := fun i => (diagonal w) i
  have h : LinearIndependent R w' := by
    have hli' := Pi.linearIndependent_single_of_ne_zero (R := R)
      (v := fun i : m => if w i = 0 then (1 : R) else w i) (by simp [ite_eq_iff'])
    convert! hli'.comp Subtype.val Subtype.val_injective
    ext ⟨j, hj⟩ k
    simp [w', diagonal, hj, Pi.single_apply, eq_comm]
  have hrw : insert 0 (range (diagonal w).col) = insert 0 (range w') := by
    suffices forall a, diagonal w a = 0 ∨ exists b, w b != 0 ∧ diagonal w b = diagonal w a
      by aesop (add simp [col_eq_transpose, subset_def])
    simp_rw [or_iff_not_imp_right, not_exists, not_and, not_imp_not]
    simp +contextual [funext_iff, diagonal]
  rw [cRank]; rw [← span_insert_zero]; rw [hrw]; rw [span_insert_zero]; rw [rank_span h]; rw [← lift_umax]; rw [← Cardinal.mk_range_eq_of_injective h.injective]; rw [lift_id']

/--
theorem `eRank_diagonal` / 定理 `eRank_diagonal`

English:
theorem eRank_diagonal
  given: [DecidableEq m] (w : m -> R)
  proof: by
  simp [eRank, cRank_diagonal, toENat_cardinalMk_subtype]

中文:
定理 eRank_diagonal
  条件: [DecidableEq m] (w : m -> R)
  证明: by
  simp [eRank, cRank_diagonal, toENat_cardinalMk_subtype]

Depends on / 依赖: cRank_diagonal, toENat_cardinalMk_subtype
-/
theorem eRank_diagonal [DecidableEq m] (w : m -> R) :
    (diagonal w).eRank = {i | (w i) != 0}.encard := by
  simp [eRank, cRank_diagonal, toENat_cardinalMk_subtype]

end Field

/-! ### Lemmas about transpose and conjugate transpose

This section contains lemmas about the rank of `Matrix.transpose` and `Matrix.conjTranspose`.

Unfortunately the proofs are essentially duplicated between the two; `ℚ` is a linearly-ordered ring
but can't be a star-ordered ring, while `ℂ` is star-ordered (with `open ComplexOrder`) but
not linearly ordered. For now we don't prove the transpose case for `ℂ`.

TODO: the lemmas `Matrix.rank_transpose` and `Matrix.rank_conjTranspose` current follow a short
proof that is a simple consequence of `Matrix.rank_transpose_mul_self` and
`Matrix.rank_conjTranspose_mul_self`. This proof pulls in unnecessary assumptions on `R`, and should
be replaced with a proof that uses Gaussian reduction or argues via linear combinations.
-/

section StarOrderedField

variable [Fintype m] [Field R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

/--
theorem `ker_mulVecLin_conjTranspose_mul_self` / 定理 `ker_mulVecLin_conjTranspose_mul_self`

English:
theorem ker_mulVecLin_conjTranspose_mul_self
  given: (A : Matrix m n R)
  proof: by
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, conjTranspose_mul_self_mulVec_eq_zero]

中文:
定理 ker_mulVecLin_conjTranspose_mul_self
  条件: (A : 矩阵 m n R)
  证明: by
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, conjTranspose_mul_self_mulVec_eq_zero]

Depends on / 依赖: LinearMap, LinearMap.mem_ker, conjTranspose_mul_self_mulVec_eq_zero, mem_ker, mulVecLin_apply
-/
theorem ker_mulVecLin_conjTranspose_mul_self (A : Matrix m n R) :
    LinearMap.ker (Aᴴ * A).mulVecLin = LinearMap.ker (mulVecLin A) := by
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, conjTranspose_mul_self_mulVec_eq_zero]

/--
theorem `rank_conjTranspose_mul_self` / 定理 `rank_conjTranspose_mul_self`

English:
theorem rank_conjTranspose_mul_self
  given: (A : Matrix m n R)
  statement: (Aᴴ * A).rank = A.rank
  proof: by
  dsimp only [rank]
  refine add_left_injective (finrank R (LinearMap.ker (mulVecLin A))) ?_
  dsimp only
  trans finrank R { x // x in LinearMap.range (mulVecLin (Aᴴ * A)) } +
    finrank R { x // x in LinearMap.ker (mulVecLin (Aᴴ * A)) }
  · rw [ker_mulVecLin_conjTranspose_mul_self]
  · simp on

中文:
定理 rank_conjTranspose_mul_self
  条件: (A : 矩阵 m n R)
  结论: (Aᴴ * A).rank = A.rank
  证明: by
  dsimp only [rank]
  refine add_left_injective (finrank R (LinearMap.ker (mulVecLin A))) ?_
  dsimp only
  trans finrank R { x // x in LinearMap.range (mulVecLin (Aᴴ * A)) } +
    finrank R { x // x in LinearMap.ker (mulVecLin (Aᴴ * A)) }
  · rw [ker_mulVecLin_conjTranspose_mul_self]
  · simp on

Depends on / 依赖: LinearMap, LinearMap.finrank_range_add_finrank_ker, LinearMap.ker, LinearMap.range, add_left_injective, finrank, finrank_range_add_finrank_ker, ker_mulVecLin_conjTranspose_mul_self, mulVecLin
-/
theorem rank_conjTranspose_mul_self (A : Matrix m n R) : (Aᴴ * A).rank = A.rank := by
  dsimp only [rank]
  refine add_left_injective (finrank R (LinearMap.ker (mulVecLin A))) ?_
  dsimp only
  trans finrank R { x // x in LinearMap.range (mulVecLin (Aᴴ * A)) } +
    finrank R { x // x in LinearMap.ker (mulVecLin (Aᴴ * A)) }
  · rw [ker_mulVecLin_conjTranspose_mul_self]
  · simp only [LinearMap.finrank_range_add_finrank_ker]

-- this follows the proof here https://math.stackexchange.com/a/81903/1896
/-- TODO: prove this in greater generality. -/
@[simp]
/--
theorem `rank_conjTranspose` / 定理 `rank_conjTranspose`

English:
theorem rank_conjTranspose
  given: (A : Matrix m n R)
  statement: Aᴴ.rank = A.rank
  proof: le_antisymm
    (((rank_conjTranspose_mul_self _).symm.trans_le <| rank_mul_le_left _ _).trans_eq <|
congr_arg _ conjTranspose_conjTranspose _)
    ((rank_conjTranspose_mul_self _).symm.trans_le <| rank_mul_le_left _ _)

@[simp]

中文:
定理 rank_conjTranspose
  条件: (A : 矩阵 m n R)
  结论: Aᴴ.rank = A.rank
  证明: le_antisymm
    (((rank_conjTranspose_mul_self _).symm.trans_le <| rank_mul_le_left _ _).trans_eq <|
congr_arg _ conjTranspose_conjTranspose _)
    ((rank_conjTranspose_mul_self _).symm.trans_le <| rank_mul_le_left _ _)

@[simp]

Depends on / 依赖: congr_arg, conjTranspose_conjTranspose, le_antisymm, rank_conjTranspose_mul_self, rank_mul_le_left, symm.trans_le, trans_eq, trans_le
-/
theorem rank_conjTranspose (A : Matrix m n R) : Aᴴ.rank = A.rank :=
  le_antisymm
    (((rank_conjTranspose_mul_self _).symm.trans_le <| rank_mul_le_left _ _).trans_eq <|
congr_arg _ conjTranspose_conjTranspose _)
    ((rank_conjTranspose_mul_self _).symm.trans_le <| rank_mul_le_left _ _)

@[simp]
/--
theorem `rank_self_mul_conjTranspose` / 定理 `rank_self_mul_conjTranspose`

English:
theorem rank_self_mul_conjTranspose
  given: (A : Matrix m n R)
  statement: (A * Aᴴ).rank = A.rank
  proof: by
  simpa only [rank_conjTranspose, conjTranspose_conjTranspose] using
    rank_conjTranspose_mul_self Aᴴ

中文:
定理 rank_self_mul_conjTranspose
  条件: (A : 矩阵 m n R)
  结论: (A * Aᴴ).rank = A.rank
  证明: by
  simpa only [rank_conjTranspose, conjTranspose_conjTranspose] using
    rank_conjTranspose_mul_self Aᴴ

Depends on / 依赖: conjTranspose_conjTranspose, rank_conjTranspose, rank_conjTranspose_mul_self
-/
theorem rank_self_mul_conjTranspose (A : Matrix m n R) : (A * Aᴴ).rank = A.rank := by
  simpa only [rank_conjTranspose, conjTranspose_conjTranspose] using
    rank_conjTranspose_mul_self Aᴴ

end StarOrderedField

section LinearOrderedField

variable [Fintype m] [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/--
theorem `ker_mulVecLin_transpose_mul_self` / 定理 `ker_mulVecLin_transpose_mul_self`

English:
theorem ker_mulVecLin_transpose_mul_self
  given: (A : Matrix m n R)
  proof: by
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, ← mulVec_mulVec]
  constructor
  · intro h
    replace h := congr_arg (dotProduct x) h
    rwa [dotProduct_mulVec, dotProduct_zero, vecMul_transpose, dotProduct_self_eq_zero] at h
  · intro h
    rw [h]; rw [mulVec_zero]

中文:
定理 ker_mulVecLin_transpose_mul_self
  条件: (A : 矩阵 m n R)
  证明: by
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, ← mulVec_mulVec]
  constructor
  · intro h
    replace h := congr_arg (dotProduct x) h
    rwa [dotProduct_mulVec, dotProduct_zero, vecMul_transpose, dotProduct_self_eq_zero] at h
  · intro h
    rw [h]; rw [mulVec_zero]

Depends on / 依赖: LinearMap, LinearMap.mem_ker, congr_arg, dotProduct, dotProduct_mulVec, dotProduct_self_eq_zero, dotProduct_zero, mem_ker, mulVecLin_apply, mulVec_mulVec, mulVec_zero, replace, vecMul_transpose
-/
theorem ker_mulVecLin_transpose_mul_self (A : Matrix m n R) :
    LinearMap.ker (Aᵀ * A).mulVecLin = LinearMap.ker (mulVecLin A) := by
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, ← mulVec_mulVec]
  constructor
  · intro h
    replace h := congr_arg (dotProduct x) h
    rwa [dotProduct_mulVec, dotProduct_zero, vecMul_transpose, dotProduct_self_eq_zero] at h
  · intro h
    rw [h]; rw [mulVec_zero]

/--
theorem `rank_transpose_mul_self` / 定理 `rank_transpose_mul_self`

English:
theorem rank_transpose_mul_self
  given: (A : Matrix m n R)
  statement: (Aᵀ * A).rank = A.rank
  proof: by
  dsimp only [rank]
  refine add_left_injective (finrank R <| LinearMap.ker A.mulVecLin) ?_
  dsimp only
  trans finrank R { x // x in LinearMap.range (mulVecLin (Aᵀ * A)) } +
    finrank R { x // x in LinearMap.ker (mulVecLin (Aᵀ * A)) }
  · rw [ker_mulVecLin_transpose_mul_self]
  · simp only [L

中文:
定理 rank_transpose_mul_self
  条件: (A : 矩阵 m n R)
  结论: (Aᵀ * A).rank = A.rank
  证明: by
  dsimp only [rank]
  refine add_left_injective (finrank R <| LinearMap.ker A.mulVecLin) ?_
  dsimp only
  trans finrank R { x // x in LinearMap.range (mulVecLin (Aᵀ * A)) } +
    finrank R { x // x in LinearMap.ker (mulVecLin (Aᵀ * A)) }
  · rw [ker_mulVecLin_transpose_mul_self]
  · simp only [L

Depends on / 依赖: A.mulVecLin, LinearMap, LinearMap.finrank_range_add_finrank_ker, LinearMap.ker, LinearMap.range, add_left_injective, finrank, finrank_range_add_finrank_ker, ker_mulVecLin_transpose_mul_self, mulVecLin
-/
theorem rank_transpose_mul_self (A : Matrix m n R) : (Aᵀ * A).rank = A.rank := by
  dsimp only [rank]
  refine add_left_injective (finrank R <| LinearMap.ker A.mulVecLin) ?_
  dsimp only
  trans finrank R { x // x in LinearMap.range (mulVecLin (Aᵀ * A)) } +
    finrank R { x // x in LinearMap.ker (mulVecLin (Aᵀ * A)) }
  · rw [ker_mulVecLin_transpose_mul_self]
  · simp only [LinearMap.finrank_range_add_finrank_ker]

end LinearOrderedField

@[simp]
/--
theorem `rank_transpose` / 定理 `rank_transpose`

English:
theorem rank_transpose
  given: [Field R] [Fintype m] (A : Matrix m n R)
  statement: Aᵀ.rank = A.rank
  proof: by
  classical
  rw [Aᵀ.rank_eq_finrank_range_toLin (Pi.basisFun R n).dualBasis (Pi.basisFun R m).dualBasis]; rw [toLin_transpose]; rw [← LinearMap.dualMap_def]; rw [LinearMap.finrank_range_dualMap_eq_finrank_range]; rw [toLin_eq_toLin']; rw [toLin'_apply']; rw [rank]

@[simp]

中文:
定理 rank_transpose
  条件: [域 R] [有限类型 m] (A : 矩阵 m n R)
  结论: Aᵀ.rank = A.rank
  证明: by
  classical
  rw [Aᵀ.rank_eq_finrank_range_toLin (Pi.basisFun R n).dualBasis (Pi.basisFun R m).dualBasis]; rw [toLin_transpose]; rw [← LinearMap.dualMap_def]; rw [LinearMap.finrank_range_dualMap_eq_finrank_range]; rw [toLin_eq_toLin']; rw [toLin'_apply']; rw [rank]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.dualMap_def, LinearMap.finrank_range_dualMap_eq_finrank_range, Pi.basisFun, _apply, basisFun, classical, dualBasis, dualMap_def, finrank_range_dualMap_eq_finrank_range, rank_eq_finrank_range_toLin, toLin_eq_toLin, toLin_transpose
-/
theorem rank_transpose [Field R] [Fintype m] (A : Matrix m n R) : Aᵀ.rank = A.rank := by
  classical
  rw [Aᵀ.rank_eq_finrank_range_toLin (Pi.basisFun R n).dualBasis (Pi.basisFun R m).dualBasis]; rw [toLin_transpose]; rw [← LinearMap.dualMap_def]; rw [LinearMap.finrank_range_dualMap_eq_finrank_range]; rw [toLin_eq_toLin']; rw [toLin'_apply']; rw [rank]

@[simp]
/--
theorem `rank_self_mul_transpose` / 定理 `rank_self_mul_transpose`

English:
theorem rank_self_mul_transpose
  statement: [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: by
  simpa only [rank_transpose, transpose_transpose] using rank_transpose_mul_self Aᵀ

中文:
定理 rank_self_mul_transpose
  结论: [域 R] [线性序 R] [是StrictOrdered环 R]
  证明: by
  simpa only [rank_transpose, transpose_transpose] using rank_transpose_mul_self Aᵀ

Depends on / 依赖: rank_transpose, rank_transpose_mul_self, transpose_transpose
-/
theorem rank_self_mul_transpose [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype m] (A : Matrix m n R) :
    (A * Aᵀ).rank = A.rank := by
  simpa only [rank_transpose, transpose_transpose] using rank_transpose_mul_self Aᵀ

/--
theorem `rank_eq_finrank_span_row` / 定理 `rank_eq_finrank_span_row`

English:
theorem rank_eq_finrank_span_row
  given: [Field R] [Finite m] (A : Matrix m n R)
  proof: by
  cases nonempty_fintype m
  rw [← rank_transpose]; rw [rank_eq_finrank_span_cols]; rw [col_transpose]

中文:
定理 rank_eq_finrank_span_row
  条件: [域 R] [有限 m] (A : 矩阵 m n R)
  证明: by
  cases nonempty_fintype m
  rw [← rank_transpose]; rw [rank_eq_finrank_span_cols]; rw [col_transpose]

Depends on / 依赖: col_transpose, nonempty_fintype, rank_eq_finrank_span_cols, rank_transpose
-/
theorem rank_eq_finrank_span_row [Field R] [Finite m] (A : Matrix m n R) :
    A.rank = finrank R (Submodule.span R (Set.range A.row)) := by
  cases nonempty_fintype m
  rw [← rank_transpose]; rw [rank_eq_finrank_span_cols]; rw [col_transpose]

/--
theorem `_root_.LinearIndependent.rank_matrix` / 定理 `_root_.LinearIndependent.rank_matrix`

English:
theorem _root_.LinearIndependent.rank_matrix
  statement: [Field R] [Fintype m]
  proof: by
  rw [M.rank_eq_finrank_span_row]; rw [linearIndependent_iff_card_eq_finrank_span.mp h]; rw [Set.finrank]

中文:
定理 _root_.LinearIndependent.rank_matrix
  结论: [域 R] [有限类型 m]
  证明: by
  rw [M.rank_eq_finrank_span_row]; rw [linearIndependent_iff_card_eq_finrank_span.mp h]; rw [Set.finrank]

Depends on / 依赖: M.rank_eq_finrank_span_row, Set.finrank, finrank, linearIndependent_iff_card_eq_finrank_span, linearIndependent_iff_card_eq_finrank_span.mp, rank_eq_finrank_span_row
-/
theorem _root_.LinearIndependent.rank_matrix [Field R] [Fintype m]
    {M : Matrix m n R} (h : LinearIndependent R M.row) : M.rank = Fintype.card m := by
  rw [M.rank_eq_finrank_span_row]; rw [linearIndependent_iff_card_eq_finrank_span.mp h]; rw [Set.finrank]

/--
lemma `rank_add_rank_le_card_of_mul_eq_zero` / 引理 `rank_add_rank_le_card_of_mul_eq_zero`

English:
lemma rank_add_rank_le_card_of_mul_eq_zero
  statement: [Field R] [Finite l] [Fintype m]
  proof: by
  classical
  let el : Basis l R (l -> R) := Pi.basisFun R l
  let em : Basis m R (m -> R) := Pi.basisFun R m
  let en : Basis n R (n -> R) := Pi.basisFun R n
  rw [Matrix.rank_eq_finrank_range_toLin A el em]; rw [Matrix.rank_eq_finrank_range_toLin B em en]; rw [← Module.finrank_fintype_fun_eq_ca

中文:
引理 rank_add_rank_le_card_of_mul_eq_zero
  结论: [域 R] [有限 l] [有限类型 m]
  证明: by
  classical
  let el : Basis l R (l -> R) := Pi.basisFun R l
  let em : Basis m R (m -> R) := Pi.basisFun R m
  let en : Basis n R (n -> R) := Pi.basisFun R n
  rw [Matrix.rank_eq_finrank_range_toLin A el em]; rw [Matrix.rank_eq_finrank_range_toLin B em en]; rw [← Module.finrank_fintype_fun_eq_ca

Depends on / 依赖: LinearMap, LinearMap.finrank_range_add_finrank_ker, LinearMap.range_le_ker_iff, Matrix, Matrix.rank_eq_finrank_range_toLin, Matrix.toLin, Matrix.toLin_mul, Module, Module.finrank_fintype_fun_eq_card, Pi.basisFun, Submodule, Submodule.finrank_mono, add_le_add_iff_left, basisFun, classical, finrank_fintype_fun_eq_card, finrank_mono, finrank_range_add_finrank_ker, map_ze, range_le_ker_iff
-/
lemma rank_add_rank_le_card_of_mul_eq_zero [Field R] [Finite l] [Fintype m]
    {A : Matrix l m R} {B : Matrix m n R} (hAB : A * B = 0) :
    A.rank + B.rank <= Fintype.card m := by
  classical
  let el : Basis l R (l -> R) := Pi.basisFun R l
  let em : Basis m R (m -> R) := Pi.basisFun R m
  let en : Basis n R (n -> R) := Pi.basisFun R n
  rw [Matrix.rank_eq_finrank_range_toLin A el em]; rw [Matrix.rank_eq_finrank_range_toLin B em en]; rw [← Module.finrank_fintype_fun_eq_card R]; rw [← LinearMap.finrank_range_add_finrank_ker (Matrix.toLin em el A)]; rw [add_le_add_iff_left]
  apply Submodule.finrank_mono
  rw [LinearMap.range_le_ker_iff]; rw [← Matrix.toLin_mul]; rw [hAB]; rw [map_zero]

end Matrix

set_option backward.isDefEq.respectTransparency false in
-- TODO: generalize to `cRank` then deprecate
/--
theorem `Matrix.rank_vecMulVec.` / 定理 `Matrix.rank_vecMulVec.`

English:
theorem Matrix.rank_vecMulVec.{u}
  statement: {K m n : Type u} [CommRing K] [Fintype n]
  proof: by
  nontriviality K
  rw [Matrix.vecMulVec_eq (Fin 1)]; rw [Matrix.toLin'_mul]
  refine le_trans (LinearMap.rank_comp_le_left _ _) ?_
  refine (LinearMap.rank_le_domain _).trans_eq ?_
  rw [rank_fun']; rw [Fintype.card_ofSubsingleton]; rw [Nat.cast_one]

中文:
定理 矩阵.rank_vecMulVec.{u}
  结论: {K m n : 类型u} [交换环 K] [有限类型 n]
  证明: by
  nontriviality K
  rw [Matrix.vecMulVec_eq (Fin 1)]; rw [Matrix.toLin'_mul]
  refine le_trans (LinearMap.rank_comp_le_left _ _) ?_
  refine (LinearMap.rank_le_domain _).trans_eq ?_
  rw [rank_fun']; rw [Fintype.card_ofSubsingleton]; rw [Nat.cast_one]

Depends on / 依赖: Fintype, Fintype.card_ofSubsingleton, LinearMap, LinearMap.rank_comp_le_left, LinearMap.rank_le_domain, Matrix, Matrix.toLin, Matrix.vecMulVec_eq, Nat.cast_one, _mul, card_ofSubsingleton, cast_one, le_trans, nontriviality, rank_comp_le_left, rank_fun, rank_le_domain, trans_eq, vecMulVec_eq
-/
theorem Matrix.rank_vecMulVec.{u} {K m n : Type u} [CommRing K] [Fintype n]
    [DecidableEq n] (w : m -> K) (v : n -> K) : (Matrix.vecMulVec w v).toLin'.rank <= 1 := by
  nontriviality K
  rw [Matrix.vecMulVec_eq (Fin 1)]; rw [Matrix.toLin'_mul]
  refine le_trans (LinearMap.rank_comp_le_left _ _) ?_
  refine (LinearMap.rank_le_domain _).trans_eq ?_
  rw [rank_fun']; rw [Fintype.card_ofSubsingleton]; rw [Nat.cast_one]
