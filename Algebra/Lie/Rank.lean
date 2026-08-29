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
/--
Definition of `rank` / `rank` 的定义

English:
definition rank
  signature: : Nat
  body: nilRank φ

中文:
定义 rank
  签名: : 自然数
  定义体: nilRank φ

Depends on / 依赖: nilRank
-/
def rank : Nat := nilRank φ

/--
lemma `polyCharpoly_coeff_rank_ne_zero` / 引理 `polyCharpoly_coeff_rank_ne_zero`

English:
lemma polyCharpoly_coeff_rank_ne_zero
  given: [Nontrivial R] [DecidableEq ι]
  proof: polyCharpoly_coeff_nilRank_ne_zero _ _

中文:
引理 polyCharpoly_coeff_rank_ne_zero
  条件: [非平凡 R] [DecidableEq ι]
  证明: polyCharpoly_coeff_nilRank_ne_zero _ _

Depends on / 依赖: polyCharpoly_coeff_nilRank_ne_zero
-/
lemma polyCharpoly_coeff_rank_ne_zero [Nontrivial R] [DecidableEq ι] :
    (polyCharpoly φ b).coeff (rank R L M) != 0 :=
  polyCharpoly_coeff_nilRank_ne_zero _ _

/--
lemma `rank_eq_natTrailingDegree` / 引理 `rank_eq_natTrailingDegree`

English:
lemma rank_eq_natTrailingDegree
  given: [Nontrivial R] [DecidableEq ι]
  proof: by
  apply nilRank_eq_polyCharpoly_natTrailingDegree

中文:
引理 rank_eq_natTrailingDegree
  条件: [非平凡 R] [DecidableEq ι]
  证明: by
  apply nilRank_eq_polyCharpoly_natTrailingDegree

Depends on / 依赖: nilRank_eq_polyCharpoly_natTrailingDegree
-/
lemma rank_eq_natTrailingDegree [Nontrivial R] [DecidableEq ι] :
    rank R L M = (polyCharpoly φ b).natTrailingDegree := by
  apply nilRank_eq_polyCharpoly_natTrailingDegree

open Module

include bₘ in
/--
lemma `rank_le_card` / 引理 `rank_le_card`

English:
lemma rank_le_card
  given: [Nontrivial R]
  statement: rank R L M <= Fintype.card ιₘ
  proof: nilRank_le_card _ bₘ

中文:
引理 rank_le_card
  条件: [非平凡 R]
  结论: rank R L M <= 有限类型.card ιₘ
  证明: nilRank_le_card _ bₘ

Depends on / 依赖: nilRank_le_card
-/
lemma rank_le_card [Nontrivial R] : rank R L M <= Fintype.card ιₘ :=
  nilRank_le_card _ bₘ

open Module
/--
lemma `rank_le_finrank` / 引理 `rank_le_finrank`

English:
lemma rank_le_finrank
  given: [Nontrivial R]
  statement: rank R L M <= finrank R M
  proof: nilRank_le_finrank _

中文:
引理 rank_le_finrank
  条件: [非平凡 R]
  结论: rank R L M <= finrank R M
  证明: nilRank_le_finrank _

Depends on / 依赖: nilRank_le_finrank
-/
lemma rank_le_finrank [Nontrivial R] : rank R L M <= finrank R M :=
  nilRank_le_finrank _

variable {L}

/--
lemma `rank_le_natTrailingDegree_charpoly_ad` / 引理 `rank_le_natTrailingDegree_charpoly_ad`

English:
lemma rank_le_natTrailingDegree_charpoly_ad
  given: [Nontrivial R]
  proof: nilRank_le_natTrailingDegree_charpoly _ _

中文:
引理 rank_le_natTrailingDegree_charpoly_ad
  条件: [非平凡 R]
  证明: nilRank_le_natTrailingDegree_charpoly _ _

Depends on / 依赖: nilRank_le_natTrailingDegree_charpoly
-/
lemma rank_le_natTrailingDegree_charpoly_ad [Nontrivial R] :
    rank R L M <= (toEnd R L M x).charpoly.natTrailingDegree :=
  nilRank_le_natTrailingDegree_charpoly _ _

/--
Definition of `IsRegular` / `IsRegular` 的定义

English:
definition IsRegular
  signature: (x : L)
  body: LinearMap.IsNilRegular φ x

中文:
定义 是正则
  签名: (x : L)
  定义体: LinearMap.IsNilRegular φ x

Depends on / 依赖: IsNilRegular, LinearMap, LinearMap.IsNilRegular
-/
def IsRegular (x : L) : Prop := LinearMap.IsNilRegular φ x

/--
lemma `isRegular_def` / 引理 `isRegular_def`

English:
lemma isRegular_def
  proof: Iff.rfl

中文:
引理 isRegular_def
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isRegular_def :
    IsRegular R M x ↔ (toEnd R L M x).charpoly.coeff (rank R L M) != 0 := Iff.rfl

/--
lemma `isRegular_iff_coeff_polyCharpoly_rank_ne_zero` / 引理 `isRegular_iff_coeff_polyCharpoly_rank_ne_zero`

English:
lemma isRegular_iff_coeff_polyCharpoly_rank_ne_zero
  given: [DecidableEq ι]
  proof: LinearMap.isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero _ _ _

中文:
引理 isRegular_iff_coeff_polyCharpoly_rank_ne_zero
  条件: [DecidableEq ι]
  证明: LinearMap.isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero _ _ _

Depends on / 依赖: LinearMap, LinearMap.isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero, isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero
-/
lemma isRegular_iff_coeff_polyCharpoly_rank_ne_zero [DecidableEq ι] :
    IsRegular R M x ↔
    MvPolynomial.eval (b.repr x)
      ((polyCharpoly φ b).coeff (rank R L M)) != 0 :=
  LinearMap.isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero _ _ _

/--
lemma `isRegular_iff_natTrailingDegree_charpoly_eq_rank` / 引理 `isRegular_iff_natTrailingDegree_charpoly_eq_rank`

English:
lemma isRegular_iff_natTrailingDegree_charpoly_eq_rank
  given: [Nontrivial R]
  proof: LinearMap.isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank _ _

中文:
引理 isRegular_iff_natTrailingDegree_charpoly_eq_rank
  条件: [非平凡 R]
  证明: LinearMap.isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank _ _

Depends on / 依赖: LinearMap, LinearMap.isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank, e.symm, isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank
-/
lemma isRegular_iff_natTrailingDegree_charpoly_eq_rank [Nontrivial R] :
    IsRegular R M x ↔ (toEnd R L M x).charpoly.natTrailingDegree = rank R L M :=
  LinearMap.isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank _ _
section IsDomain

variable (L)
variable [IsDomain R]

open Cardinal Module MvPolynomial in
/--
lemma `exists_isRegular_of_finrank_le_card` / 引理 `exists_isRegular_of_finrank_le_card`

English:
lemma exists_isRegular_of_finrank_le_card
  given: (h : finrank R M <= #R)
  proof: LinearMap.exists_isNilRegular_of_finrank_le_card _ h

中文:
引理 存在_isRegular_of_finrank_le_card
  条件: (h : finrank R M <= #R)
  证明: LinearMap.exists_isNilRegular_of_finrank_le_card _ h

Depends on / 依赖: LinearMap, LinearMap.exists_isNilRegular_of_finrank_le_card, exists_isNilRegular_of_finrank_le_card
-/
lemma exists_isRegular_of_finrank_le_card (h : finrank R M <= #R) :
    exists x : L, IsRegular R M x :=
  LinearMap.exists_isNilRegular_of_finrank_le_card _ h

/--
lemma `exists_isRegular` / 引理 `exists_isRegular`

English:
lemma exists_isRegular
  given: [Infinite R]
  statement: exists x : L, IsRegular R M x
  proof: LinearMap.exists_isNilRegular _

中文:
引理 存在_isRegular
  条件: [无限 R]
  结论: 存在 x : L, 是正则 R M x
  证明: LinearMap.exists_isNilRegular _

Depends on / 依赖: LinearMap, LinearMap.exists_isNilRegular, exists_isNilRegular
-/
lemma exists_isRegular [Infinite R] : exists x : L, IsRegular R M x :=
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
/--
Definition of `rank` / `rank` 的定义

English:
abbreviation rank
  signature: : Nat
  body: LieModule.rank R L L

中文:
缩写 rank
  签名: : 自然数
  定义体: LieModule.rank R L L

Depends on / 依赖: LieModule, LieModule.rank
-/
abbrev rank : Nat := LieModule.rank R L L

/--
lemma `polyCharpoly_coeff_rank_ne_zero` / 引理 `polyCharpoly_coeff_rank_ne_zero`

English:
lemma polyCharpoly_coeff_rank_ne_zero
  given: [Nontrivial R] [DecidableEq ι]
  proof: polyCharpoly_coeff_nilRank_ne_zero _ _

中文:
引理 polyCharpoly_coeff_rank_ne_zero
  条件: [非平凡 R] [DecidableEq ι]
  证明: polyCharpoly_coeff_nilRank_ne_zero _ _

Depends on / 依赖: polyCharpoly_coeff_nilRank_ne_zero
-/
lemma polyCharpoly_coeff_rank_ne_zero [Nontrivial R] [DecidableEq ι] :
    (polyCharpoly (ad R L).toLinearMap b).coeff (rank R L) != 0 :=
  polyCharpoly_coeff_nilRank_ne_zero _ _

/--
lemma `rank_eq_natTrailingDegree` / 引理 `rank_eq_natTrailingDegree`

English:
lemma rank_eq_natTrailingDegree
  given: [Nontrivial R] [DecidableEq ι]
  proof: by
  apply nilRank_eq_polyCharpoly_natTrailingDegree

中文:
引理 rank_eq_natTrailingDegree
  条件: [非平凡 R] [DecidableEq ι]
  证明: by
  apply nilRank_eq_polyCharpoly_natTrailingDegree

Depends on / 依赖: nilRank_eq_polyCharpoly_natTrailingDegree
-/
lemma rank_eq_natTrailingDegree [Nontrivial R] [DecidableEq ι] :
    rank R L = (polyCharpoly (ad R L).toLinearMap b).natTrailingDegree := by
  apply nilRank_eq_polyCharpoly_natTrailingDegree

open Module

include b in
/--
lemma `rank_le_card` / 引理 `rank_le_card`

English:
lemma rank_le_card
  given: [Nontrivial R]
  statement: rank R L <= Fintype.card ι
  proof: nilRank_le_card _ b

中文:
引理 rank_le_card
  条件: [非平凡 R]
  结论: rank R L <= 有限类型.card ι
  证明: nilRank_le_card _ b

Depends on / 依赖: nilRank_le_card
-/
lemma rank_le_card [Nontrivial R] : rank R L <= Fintype.card ι :=
  nilRank_le_card _ b

/--
lemma `rank_le_finrank` / 引理 `rank_le_finrank`

English:
lemma rank_le_finrank
  given: [Nontrivial R]
  statement: rank R L <= finrank R L
  proof: nilRank_le_finrank _

中文:
引理 rank_le_finrank
  条件: [非平凡 R]
  结论: rank R L <= finrank R L
  证明: nilRank_le_finrank _

Depends on / 依赖: nilRank_le_finrank
-/
lemma rank_le_finrank [Nontrivial R] : rank R L <= finrank R L :=
  nilRank_le_finrank _

variable {L}

/--
lemma `rank_le_natTrailingDegree_charpoly_ad` / 引理 `rank_le_natTrailingDegree_charpoly_ad`

English:
lemma rank_le_natTrailingDegree_charpoly_ad
  given: [Nontrivial R]
  proof: nilRank_le_natTrailingDegree_charpoly _ _

中文:
引理 rank_le_natTrailingDegree_charpoly_ad
  条件: [非平凡 R]
  证明: nilRank_le_natTrailingDegree_charpoly _ _

Depends on / 依赖: nilRank_le_natTrailingDegree_charpoly
-/
lemma rank_le_natTrailingDegree_charpoly_ad [Nontrivial R] :
    rank R L <= (ad R L x).charpoly.natTrailingDegree :=
  nilRank_le_natTrailingDegree_charpoly _ _

/--
Definition of `IsRegular` / `IsRegular` 的定义

English:
abbreviation IsRegular
  signature: (x : L)
  body: LieModule.IsRegular R L x

中文:
缩写 是正则
  签名: (x : L)
  定义体: LieModule.IsRegular R L x

Depends on / 依赖: IsRegular, LieModule, LieModule.IsRegular
-/
abbrev IsRegular (x : L) : Prop := LieModule.IsRegular R L x

/--
lemma `isRegular_def` / 引理 `isRegular_def`

English:
lemma isRegular_def
  proof: Iff.rfl

中文:
引理 isRegular_def
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isRegular_def :
    IsRegular R x ↔ (Polynomial.coeff (ad R L x).charpoly (rank R L) != 0) := Iff.rfl

/--
lemma `isRegular_iff_coeff_polyCharpoly_rank_ne_zero` / 引理 `isRegular_iff_coeff_polyCharpoly_rank_ne_zero`

English:
lemma isRegular_iff_coeff_polyCharpoly_rank_ne_zero
  given: [DecidableEq ι]
  proof: LinearMap.isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero _ _ _

中文:
引理 isRegular_iff_coeff_polyCharpoly_rank_ne_zero
  条件: [DecidableEq ι]
  证明: LinearMap.isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero _ _ _

Depends on / 依赖: LinearMap, LinearMap.isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero, isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero
-/
lemma isRegular_iff_coeff_polyCharpoly_rank_ne_zero [DecidableEq ι] :
    IsRegular R x ↔
    MvPolynomial.eval (b.repr x)
      ((polyCharpoly (ad R L).toLinearMap b).coeff (rank R L)) != 0 :=
  LinearMap.isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero _ _ _

/--
lemma `isRegular_iff_natTrailingDegree_charpoly_eq_rank` / 引理 `isRegular_iff_natTrailingDegree_charpoly_eq_rank`

English:
lemma isRegular_iff_natTrailingDegree_charpoly_eq_rank
  given: [Nontrivial R]
  proof: LinearMap.isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank _ _

中文:
引理 isRegular_iff_natTrailingDegree_charpoly_eq_rank
  条件: [非平凡 R]
  证明: LinearMap.isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank _ _

Depends on / 依赖: LinearMap, LinearMap.isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank, isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank
-/
lemma isRegular_iff_natTrailingDegree_charpoly_eq_rank [Nontrivial R] :
    IsRegular R x ↔ (ad R L x).charpoly.natTrailingDegree = rank R L :=
  LinearMap.isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank _ _
section IsDomain

variable (L)
variable [IsDomain R]

open Cardinal Module MvPolynomial in
/--
lemma `exists_isRegular_of_finrank_le_card` / 引理 `exists_isRegular_of_finrank_le_card`

English:
lemma exists_isRegular_of_finrank_le_card
  given: (h : finrank R L <= #R)
  proof: LinearMap.exists_isNilRegular_of_finrank_le_card _ h

中文:
引理 存在_isRegular_of_finrank_le_card
  条件: (h : finrank R L <= #R)
  证明: LinearMap.exists_isNilRegular_of_finrank_le_card _ h

Depends on / 依赖: LinearMap, LinearMap.exists_isNilRegular_of_finrank_le_card, exists_isNilRegular_of_finrank_le_card
-/
lemma exists_isRegular_of_finrank_le_card (h : finrank R L <= #R) :
    exists x : L, IsRegular R x :=
  LinearMap.exists_isNilRegular_of_finrank_le_card _ h

/--
lemma `exists_isRegular` / 引理 `exists_isRegular`

English:
lemma exists_isRegular
  given: [Infinite R]
  statement: exists x : L, IsRegular R x
  proof: LinearMap.exists_isNilRegular _

中文:
引理 存在_isRegular
  条件: [无限 R]
  结论: 存在 x : L, 是正则 R x
  证明: LinearMap.exists_isNilRegular _

Depends on / 依赖: LinearMap, LinearMap.exists_isNilRegular, exists_isNilRegular
-/
lemma exists_isRegular [Infinite R] : exists x : L, IsRegular R x :=
  LinearMap.exists_isNilRegular _

end IsDomain

end LieAlgebra

namespace LieAlgebra

variable (K : Type*) {L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]

open Module LieSubalgebra

/--
lemma `finrank_engel` / 引理 `finrank_engel`

English:
lemma finrank_engel
  given: (x : L)
  proof: (ad K L x).finrank_maxGenEigenspace_zero_eq

中文:
引理 finrank_engel
  条件: (x : L)
  证明: (ad K L x).finrank_maxGenEigenspace_zero_eq

Depends on / 依赖: finrank_maxGenEigenspace_zero_eq
-/
lemma finrank_engel (x : L) :
    finrank K (engel K x) = (ad K L x).charpoly.natTrailingDegree :=
  (ad K L x).finrank_maxGenEigenspace_zero_eq

/--
lemma `rank_le_finrank_engel` / 引理 `rank_le_finrank_engel`

English:
lemma rank_le_finrank_engel
  given: (x : L)
  proof: (rank_le_natTrailingDegree_charpoly_ad K x).trans
    (finrank_engel K x).ge

中文:
引理 rank_le_finrank_engel
  条件: (x : L)
  证明: (rank_le_natTrailingDegree_charpoly_ad K x).trans
    (finrank_engel K x).ge

Depends on / 依赖: finrank_engel, rank_le_natTrailingDegree_charpoly_ad
-/
lemma rank_le_finrank_engel (x : L) :
    rank K L <= finrank K (engel K x) :=
  (rank_le_natTrailingDegree_charpoly_ad K x).trans
    (finrank_engel K x).ge

/--
lemma `isRegular_iff_finrank_engel_eq_rank` / 引理 `isRegular_iff_finrank_engel_eq_rank`

English:
lemma isRegular_iff_finrank_engel_eq_rank
  given: (x : L)
  proof: by
  rw [isRegular_iff_natTrailingDegree_charpoly_eq_rank]; rw [finrank_engel]

中文:
引理 isRegular_iff_finrank_engel_eq_rank
  条件: (x : L)
  证明: by
  rw [isRegular_iff_natTrailingDegree_charpoly_eq_rank]; rw [finrank_engel]

Depends on / 依赖: finrank_engel, isRegular_iff_natTrailingDegree_charpoly_eq_rank
-/
lemma isRegular_iff_finrank_engel_eq_rank (x : L) :
    IsRegular K x ↔ finrank K (engel K x) = rank K L := by
  rw [isRegular_iff_natTrailingDegree_charpoly_eq_rank]; rw [finrank_engel]

end LieAlgebra
