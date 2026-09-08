/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Lie.EngelSubalgebra
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.LinearMap.Polynomial
public import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# Rank of a Lie algebra and regular elements

Let `L` be a Lie algebra over a nontrivial commutative ring `R`,
and assume that `L` is finite free as `R`-module.
Then the coefficients of the characteristic polynomial of `ad R L x` are polynomial in `x`.
The *rank* of `L` is the smallest `n` for which the `n`-th coefficient is not the zero polynomial.

Continuing to write `n` for the rank of `L`, an element `x` of `L` is *regular*
if the `n`-th coefficient of the characteristic polynomial of `ad R L x` is non-zero.

## Main declarations

* `LieAlgebra.rank R L` is the rank of a Lie algebra `L` over a commutative ring `R`.
* `LieAlgebra.IsRegular R x` is the predicate that an element `x` of a Lie algebra `L` is regular.

## References

* [barnes1967]: "On Cartan subalgebras of Lie algebras" by D.W. Barnes.

-/

@[expose] public section

open Module

variable {R A L M ι ιₘ : Type*}
variable [CommRing R]
variable [CommRing A] [Algebra R A]
variable [LieRing L] [LieAlgebra R L] [Module.Finite R L] [Module.Free R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [Module.Finite R M] [Module.Free R M]
variable [Fintype ι]
variable [Fintype ιₘ]
variable (b : Basis ι R L) (bₘ : Basis ιₘ R M) (x : L)

namespace LieModule

open LieAlgebra LinearMap Module.Free
attribute [local instance 100] LieRing.ofAssociativeRing

variable (R L M)

local notation "φ" => LieHom.toLinearMap (LieModule.toEnd R L M)

/--
Let `M` be a representation of a Lie algebra `L` over a nontrivial commutative ring `R`,
and assume that `L` and `M` are finite free as `R`-module.
Then the coefficients of the characteristic polynomial of `⁅x, ·⁆` are polynomial in `x`.
The *rank* of `M` is the smallest `n` for which the `n`-th coefficient is not the zero polynomial.
-/
noncomputable
/-
**LieModule.rank** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：rank : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def rank : ℕ := nilRank φ
/-
**LieModule.polyCharpoly_coeff_rank_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `LieModule
`。
形式化陈述：polyCharpoly_coeff_rank_ne_zero [Nontrivial R] [DecidableEq ι] : (polyChar
poly φ b).coeff (rank R L M) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.polyCharpoly_coeff_nilRank_ne_zero`：polyCharpoly_coeff_nilRank
_ne_zero : (polyCharpoly φ b).coeff (nilRank φ) != 0
-/
lemma polyCharpoly_coeff_rank_ne_zero [Nontrivial R] [DecidableEq ι] :
    (polyCharpoly φ b).coeff (rank R L M) ≠ 0 :=
  polyCharpoly_coeff_nilRank_ne_zero _ _
/-
**LieModule.rank_eq_natTrailingDegree** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：rank_eq_natTrailingDegree [Nontrivial R] [DecidableEq ι] : rank R L M = (p
olyCharpoly φ b).natTrailingDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.nilRank_eq_polyCharpoly_natTrailingDegree`：nilRank_eq_polyChar
poly_natTrailingDegree (b : Basis ι R L) : nilRank φ = (polyCharpoly φ b).natTra
ilingDegree
-/
lemma rank_eq_natTrailingDegree [Nontrivial R] [DecidableEq ι] :
    rank R L M = (polyCharpoly φ b).natTrailingDegree := by
  apply nilRank_eq_polyCharpoly_natTrailingDegree

open Module

include bₘ in
/-
**LieModule.rank_le_card** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：rank_le_card [Nontrivial R] : rank R L M <= Fintype.card ιₘ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.nilRank_le_card`：nilRank_le_card {ι : Type*} [Fintype ι] (b : 
Basis ι R M) : nilRank φ <= Fintype.card ι
-/
lemma rank_le_card [Nontrivial R] : rank R L M ≤ Fintype.card ιₘ :=
  nilRank_le_card _ bₘ

open Module
/-
**LieModule.rank_le_finrank** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：rank_le_finrank [Nontrivial R] : rank R L M <= finrank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.nilRank_le_finrank`：nilRank_le_finrank : nilRank φ <= finrank 
R M
-/
lemma rank_le_finrank [Nontrivial R] : rank R L M ≤ finrank R M :=
  nilRank_le_finrank _

variable {L}
/-
**LieModule.rank_le_natTrailingDegree_charpoly_ad** 是 Mathlib 中的一个引理，位于命名空间 `Lie
Module`。
形式化陈述：rank_le_natTrailingDegree_charpoly_ad [Nontrivial R] : rank R L M <= (toEn
d R L M x).charpoly.natTrailingDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.nilRank_le_natTrailingDegree_charpoly`：nilRank_le_natTrailingD
egree_charpoly (x : L) : nilRank φ <= (φ x).charpoly.natTrailingDegree
-/
lemma rank_le_natTrailingDegree_charpoly_ad [Nontrivial R] :
    rank R L M ≤ (toEnd R L M x).charpoly.natTrailingDegree :=
  nilRank_le_natTrailingDegree_charpoly _ _

/-- Let `x` be an element of a Lie algebra `L` over `R`, and write `n` for `rank R L`.
Then `x` is *regular*
if the `n`-th coefficient of the characteristic polynomial of `ad R L x` is non-zero. -/
/-
**LieModule.IsRegular** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：IsRegular (x : L) : Prop
参数：x : L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `x` be an element of a Lie algebra `L` over `R`, and write `n` for `rank R L
`.
Then `x` is *regular*
if the `n`-th coefficient of the characteristic polynomial of `ad R L x` is non-
zero.
-/
def IsRegular (x : L) : Prop := LinearMap.IsNilRegular φ x
/-
**LieModule.isRegular_def** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：isRegular_def : IsRegular R M x ↔ (toEnd R L M x).charpoly.coeff (rank R L
 M) != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRegular_def :
    IsRegular R M x ↔ (toEnd R L M x).charpoly.coeff (rank R L M) ≠ 0 := Iff.rfl
/-
**LieModule.isRegular_iff_coeff_polyCharpoly_rank_ne_zero** 是 Mathlib 中的一个引理，位于命
名空间 `LieModule`。
形式化陈述：isRegular_iff_coeff_polyCharpoly_rank_ne_zero [DecidableEq ι] : IsRegular 
R M x ↔ MvPolynomial.eval (b.repr x) ((polyCharpoly φ b).coeff (rank R L M)) != 
0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero`：isNilRegu
lar_iff_coeff_polyCharpoly_nilRank_ne_zero : IsNilRegular φ x ↔ MvPolynomial.eva
l (b.repr x) ((polyCharpoly φ b).coeff (nilRank φ))…
-/
lemma isRegular_iff_coeff_polyCharpoly_rank_ne_zero [DecidableEq ι] :
    IsRegular R M x ↔
    MvPolynomial.eval (b.repr x)
      ((polyCharpoly φ b).coeff (rank R L M)) ≠ 0 :=
  LinearMap.isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero _ _ _
/-
**LieModule.isRegular_iff_natTrailingDegree_charpoly_eq_rank** 是 Mathlib 中的一个引理，
位于命名空间 `LieModule`。
形式化陈述：isRegular_iff_natTrailingDegree_charpoly_eq_rank [Nontrivial R] : IsRegula
r R M x ↔ (toEnd R L M x).charpoly.natTrailingDegree = rank R L M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank`：isNilR
egular_iff_natTrailingDegree_charpoly_eq_nilRank [Nontrivial R] : IsNilRegular φ
 x ↔ (φ x).charpoly.natTrailingDegree = nilRank φ
-/
lemma isRegular_iff_natTrailingDegree_charpoly_eq_rank [Nontrivial R] :
    IsRegular R M x ↔ (toEnd R L M x).charpoly.natTrailingDegree = rank R L M :=
  LinearMap.isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank _ _
section IsDomain

variable (L)
variable [IsDomain R]

open Cardinal Module MvPolynomial in
/-
**LieModule.exists_isRegular_of_finrank_le_card** 是 Mathlib 中的一个引理，位于命名空间 `LieMo
dule`。
形式化陈述：exists_isRegular_of_finrank_le_card (h : finrank R M <= #R) : exists x : L
, IsRegular R M x
参数：h : finrank R M <= #R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.exists_isNilRegular_of_finrank_le_card`：exists_isNilRegular_of
_finrank_le_card (h : finrank R M <= #R) : exists x : L, IsNilRegular φ x
-/
lemma exists_isRegular_of_finrank_le_card (h : finrank R M ≤ #R) :
    ∃ x : L, IsRegular R M x :=
  LinearMap.exists_isNilRegular_of_finrank_le_card _ h
/-
**LieModule.exists_isRegular** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：exists_isRegular [Infinite R] : exists x : L, IsRegular R M x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.exists_isNilRegular`：exists_isNilRegular [Infinite R] : exists
 x : L, IsNilRegular φ x
-/
lemma exists_isRegular [Infinite R] : ∃ x : L, IsRegular R M x :=
  LinearMap.exists_isNilRegular _

end IsDomain

end LieModule

namespace LieAlgebra

open LieAlgebra LinearMap Module.Free
attribute [local instance 100] LieRing.ofAssociativeRing

variable (R L)

/--
Let `L` be a Lie algebra over a nontrivial commutative ring `R`,
and assume that `L` is finite free as `R`-module.
Then the coefficients of the characteristic polynomial of `ad R L x` are polynomial in `x`.
The *rank* of `L` is the smallest `n` for which the `n`-th coefficient is not the zero polynomial.
-/
noncomputable
/-
**LieAlgebra.rank** 是 Mathlib 中的一个缩写定义，位于命名空间 `LieAlgebra`。
形式化陈述：rank : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev rank : ℕ := LieModule.rank R L L
/-
**LieAlgebra.polyCharpoly_coeff_rank_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgeb
ra`。
形式化陈述：polyCharpoly_coeff_rank_ne_zero [Nontrivial R] [DecidableEq ι] : (polyChar
poly (ad R L).toLinearMap b).coeff (rank R L) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.polyCharpoly_coeff_nilRank_ne_zero`：polyCharpoly_coeff_nilRank
_ne_zero : (polyCharpoly φ b).coeff (nilRank φ) != 0
-/
lemma polyCharpoly_coeff_rank_ne_zero [Nontrivial R] [DecidableEq ι] :
    (polyCharpoly (ad R L).toLinearMap b).coeff (rank R L) ≠ 0 :=
  polyCharpoly_coeff_nilRank_ne_zero _ _
/-
**LieAlgebra.rank_eq_natTrailingDegree** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：rank_eq_natTrailingDegree [Nontrivial R] [DecidableEq ι] : rank R L = (pol
yCharpoly (ad R L).toLinearMap b).natTrailingDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.nilRank_eq_polyCharpoly_natTrailingDegree`：nilRank_eq_polyChar
poly_natTrailingDegree (b : Basis ι R L) : nilRank φ = (polyCharpoly φ b).natTra
ilingDegree
-/
lemma rank_eq_natTrailingDegree [Nontrivial R] [DecidableEq ι] :
    rank R L = (polyCharpoly (ad R L).toLinearMap b).natTrailingDegree := by
  apply nilRank_eq_polyCharpoly_natTrailingDegree

open Module

include b in
/-
**LieAlgebra.rank_le_card** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：rank_le_card [Nontrivial R] : rank R L <= Fintype.card ι
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.nilRank_le_card`：nilRank_le_card {ι : Type*} [Fintype ι] (b : 
Basis ι R M) : nilRank φ <= Fintype.card ι
-/
lemma rank_le_card [Nontrivial R] : rank R L ≤ Fintype.card ι :=
  nilRank_le_card _ b
/-
**LieAlgebra.rank_le_finrank** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：rank_le_finrank [Nontrivial R] : rank R L <= finrank R L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.nilRank_le_finrank`：nilRank_le_finrank : nilRank φ <= finrank 
R M
-/
lemma rank_le_finrank [Nontrivial R] : rank R L ≤ finrank R L :=
  nilRank_le_finrank _

variable {L}
/-
**LieAlgebra.rank_le_natTrailingDegree_charpoly_ad** 是 Mathlib 中的一个引理，位于命名空间 `Li
eAlgebra`。
形式化陈述：rank_le_natTrailingDegree_charpoly_ad [Nontrivial R] : rank R L <= (ad R L
 x).charpoly.natTrailingDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.nilRank_le_natTrailingDegree_charpoly`：nilRank_le_natTrailingD
egree_charpoly (x : L) : nilRank φ <= (φ x).charpoly.natTrailingDegree
-/
lemma rank_le_natTrailingDegree_charpoly_ad [Nontrivial R] :
    rank R L ≤ (ad R L x).charpoly.natTrailingDegree :=
  nilRank_le_natTrailingDegree_charpoly _ _

/-- Let `x` be an element of a Lie algebra `L` over `R`, and write `n` for `rank R L`.
Then `x` is *regular*
if the `n`-th coefficient of the characteristic polynomial of `ad R L x` is non-zero. -/
/-
**LieAlgebra.IsRegular** 是 Mathlib 中的一个缩写定义，位于命名空间 `LieAlgebra`。
形式化陈述：IsRegular (x : L) : Prop
参数：x : L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `x` be an element of a Lie algebra `L` over `R`, and write `n` for `rank R L
`.
Then `x` is *regular*
if the `n`-th coefficient of the characteristic polynomial of `ad R L x` is non-
zero.
-/
abbrev IsRegular (x : L) : Prop := LieModule.IsRegular R L x
/-
**LieAlgebra.isRegular_def** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：isRegular_def : IsRegular R x ↔ (Polynomial.coeff (ad R L x).charpoly (ran
k R L) != 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRegular_def :
    IsRegular R x ↔ (Polynomial.coeff (ad R L x).charpoly (rank R L) ≠ 0) := Iff.rfl
/-
**LieAlgebra.isRegular_iff_coeff_polyCharpoly_rank_ne_zero** 是 Mathlib 中的一个引理，位于
命名空间 `LieAlgebra`。
形式化陈述：isRegular_iff_coeff_polyCharpoly_rank_ne_zero [DecidableEq ι] : IsRegular 
R x ↔ MvPolynomial.eval (b.repr x) ((polyCharpoly (ad R L).toLinearMap b).coeff 
(rank R L)) != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero`：isNilRegu
lar_iff_coeff_polyCharpoly_nilRank_ne_zero : IsNilRegular φ x ↔ MvPolynomial.eva
l (b.repr x) ((polyCharpoly φ b).coeff (nilRank φ))…
-/
lemma isRegular_iff_coeff_polyCharpoly_rank_ne_zero [DecidableEq ι] :
    IsRegular R x ↔
    MvPolynomial.eval (b.repr x)
      ((polyCharpoly (ad R L).toLinearMap b).coeff (rank R L)) ≠ 0 :=
  LinearMap.isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero _ _ _
/-
**LieAlgebra.isRegular_iff_natTrailingDegree_charpoly_eq_rank** 是 Mathlib 中的一个引理
，位于命名空间 `LieAlgebra`。
形式化陈述：isRegular_iff_natTrailingDegree_charpoly_eq_rank [Nontrivial R] : IsRegula
r R x ↔ (ad R L x).charpoly.natTrailingDegree = rank R L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank`：isNilR
egular_iff_natTrailingDegree_charpoly_eq_nilRank [Nontrivial R] : IsNilRegular φ
 x ↔ (φ x).charpoly.natTrailingDegree = nilRank φ
-/
lemma isRegular_iff_natTrailingDegree_charpoly_eq_rank [Nontrivial R] :
    IsRegular R x ↔ (ad R L x).charpoly.natTrailingDegree = rank R L :=
  LinearMap.isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank _ _
section IsDomain

variable (L)
variable [IsDomain R]

open Cardinal Module MvPolynomial in
/-
**LieAlgebra.exists_isRegular_of_finrank_le_card** 是 Mathlib 中的一个引理，位于命名空间 `LieA
lgebra`。
形式化陈述：exists_isRegular_of_finrank_le_card (h : finrank R L <= #R) : exists x : L
, IsRegular R x
参数：h : finrank R L <= #R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.exists_isNilRegular_of_finrank_le_card`：exists_isNilRegular_of
_finrank_le_card (h : finrank R M <= #R) : exists x : L, IsNilRegular φ x
-/
lemma exists_isRegular_of_finrank_le_card (h : finrank R L ≤ #R) :
    ∃ x : L, IsRegular R x :=
  LinearMap.exists_isNilRegular_of_finrank_le_card _ h
/-
**LieAlgebra.exists_isRegular** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：exists_isRegular [Infinite R] : exists x : L, IsRegular R x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.exists_isNilRegular`：exists_isNilRegular [Infinite R] : exists
 x : L, IsNilRegular φ x
-/
lemma exists_isRegular [Infinite R] : ∃ x : L, IsRegular R x :=
  LinearMap.exists_isNilRegular _

end IsDomain

end LieAlgebra

namespace LieAlgebra

variable (K : Type*) {L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]

open Module LieSubalgebra

/-
**LieAlgebra.finrank_engel** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：finrank_engel (x : L) : finrank K (engel K x) = (ad K L x).charpoly.natTra
ilingDegree
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.finrank_maxGenEigenspace_zero_eq`：finrank_maxGenEigenspace_zer
o_eq (φ : Module.End K M) : finrank K (φ.maxGenEigenspace 0) = natTrailingDegree
 (φ.charpoly)
-/
lemma finrank_engel (x : L) :
    finrank K (engel K x) = (ad K L x).charpoly.natTrailingDegree :=
  (ad K L x).finrank_maxGenEigenspace_zero_eq
/-
**LieAlgebra.rank_le_finrank_engel** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：rank_le_finrank_engel (x : L) : rank K L <= finrank K (engel K x)
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用引理 `LieAlgebra.rank_le_natTrailingDegree_charpoly_ad`：rank_le_natTrailingDeg
ree_charpoly_ad [Nontrivial R] : rank R L <= (ad R L x).charpoly.natTrailingDegr
ee
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `LieAlgebra.finrank_engel`：finrank_engel (x : L) : finrank K (engel K x) 
= (ad K L x).charpoly.natTrailingDegree
-/
lemma rank_le_finrank_engel (x : L) :
    rank K L ≤ finrank K (engel K x) :=
  (rank_le_natTrailingDegree_charpoly_ad K x).trans
    (finrank_engel K x).ge
/-
**LieAlgebra.isRegular_iff_finrank_engel_eq_rank** 是 Mathlib 中的一个引理，位于命名空间 `LieA
lgebra`。
形式化陈述：isRegular_iff_finrank_engel_eq_rank (x : L) : IsRegular K x ↔ finrank K (e
ngel K x) = rank K L
参数：x : L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.isRegular_iff_natTrailingDegree_charpoly_eq_rank`：isRegular_i
ff_natTrailingDegree_charpoly_eq_rank [Nontrivial R] : IsRegular R x ↔ (ad R L x
).charpoly.natTrailingDegree = rank R L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `LieAlgebra.finrank_engel`：finrank_engel (x : L) : finrank K (engel K x) 
= (ad K L x).charpoly.natTrailingDegree
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRegular_iff_finrank_engel_eq_rank (x : L) :
    IsRegular K x ↔ finrank K (engel K x) = rank K L := by
  rw [isRegular_iff_natTrailingDegree_charpoly_eq_rank, finrank_engel]

end LieAlgebra

