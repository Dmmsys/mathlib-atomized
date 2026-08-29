/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang, Fangming Li
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.Order.Antidiag.Prod

/-!
# Internally graded rings and algebras

This module provides `DirectSum.GSemiring` and `DirectSum.GCommSemiring` instances for a collection
of subobjects `A` when a `SetLike.GradedMonoid` instance is available:

* `SetLike.gnonUnitalNonAssocSemiring`
* `SetLike.gsemiring`
* `SetLike.gcommSemiring`

With these instances in place, it provides the bundled canonical maps out of a direct sum of
subobjects into their carrier type:

* `DirectSum.coeRingHom` (a `RingHom` version of `DirectSum.coeAddMonoidHom`)
* `DirectSum.coeAlgHom` (an `AlgHom` version of `DirectSum.coeLinearMap`)

Strictly the definitions in this file are not sufficient to fully define an "internal" direct sum;
to represent this case, `(h : DirectSum.IsInternal A) [SetLike.GradedMonoid A]` is
needed. In the future there will likely be a data-carrying, constructive, typeclass version of
`DirectSum.IsInternal` for providing an explicit decomposition function.

When `iSupIndep (Set.range A)` (a weaker condition than
`DirectSum.IsInternal A`), these provide a grading of `⨆ i, A i`, and the
mapping `⨁ i, A i →+ ⨆ i, A i` can be obtained as
`DirectSum.toAddMonoid (fun i ↦ AddSubmonoid.inclusion <| le_iSup A i)`.

This file also provides some extra structure on `A 0`, namely:
* `SetLike.GradeZero.subsemiring`, which leads to
  * `SetLike.GradeZero.instSemiring`
  * `SetLike.GradeZero.instCommSemiring`
* `SetLike.GradeZero.subring`, which leads to
  * `SetLike.GradeZero.instRing`
  * `SetLike.GradeZero.instCommRing`
* `SetLike.GradeZero.subalgebra`, which leads to
  * `SetLike.GradeZero.instAlgebra`

## Tags

internally graded ring
-/

@[expose] public section


open DirectSum

variable {ι : Type*} {σ S R : Type*}

/--
theorem `SetLike.algebraMap_mem_graded` / 定理 `SetLike.algebraMap_mem_graded`

English:
theorem SetLike.algebraMap_mem_graded
  statement: [Zero ι] [CommSemiring S] [Semiring R] [Algebra S R]
  proof: by
  rw [Algebra.algebraMap_eq_smul_one]
exact (A 0).smul_mem s SetLike.one_mem_graded _

中文:
定理 集合状.algebraMap_mem_graded
  结论: [零 ι] [交换半环 S] [半环 R] [代数 S R]
  证明: by
  rw [Algebra.algebraMap_eq_smul_one]
exact (A 0).smul_mem s SetLike.one_mem_graded _

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, SetLike, SetLike.one_mem_graded, algebraMap_eq_smul_one, one_mem_graded, smul_mem
-/
theorem SetLike.algebraMap_mem_graded [Zero ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι -> Submodule S R) [SetLike.GradedOne A] (s : S) : algebraMap S R s in A 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
exact (A 0).smul_mem s SetLike.one_mem_graded _

/--
theorem `SetLike.natCast_mem_graded` / 定理 `SetLike.natCast_mem_graded`

English:
theorem SetLike.natCast_mem_graded
  statement: [Zero ι] [AddMonoidWithOne R] [SetLike σ R]
  proof: by
  induction n with
  | zero =>
    rw [Nat.cast_zero]
    exact zero_mem (A 0)
  | succ _ n_ih =>
    rw [Nat.cast_succ]
    exact add_mem n_ih (SetLike.one_mem_graded _)

中文:
定理 集合状.natCast_mem_graded
  结论: [零 ι] [加法带幺幺半群 R] [集合状 σ R]
  证明: by
  induction n with
  | zero =>
    rw [Nat.cast_zero]
    exact zero_mem (A 0)
  | succ _ n_ih =>
    rw [Nat.cast_succ]
    exact add_mem n_ih (SetLike.one_mem_graded _)

Depends on / 依赖: Nat.cast_succ, Nat.cast_zero, SetLike, SetLike.one_mem_graded, add_mem, cast_succ, cast_zero, n_ih, one_mem_graded, zero_mem
-/
theorem SetLike.natCast_mem_graded [Zero ι] [AddMonoidWithOne R] [SetLike σ R]
    [AddSubmonoidClass σ R] (A : ι -> σ) [SetLike.GradedOne A] (n : Nat) : (n : R) in A 0 := by
  induction n with
  | zero =>
    rw [Nat.cast_zero]
    exact zero_mem (A 0)
  | succ _ n_ih =>
    rw [Nat.cast_succ]
    exact add_mem n_ih (SetLike.one_mem_graded _)

/--
theorem `SetLike.intCast_mem_graded` / 定理 `SetLike.intCast_mem_graded`

English:
theorem SetLike.intCast_mem_graded
  statement: [Zero ι] [AddGroupWithOne R] [SetLike σ R]
  proof: by
  cases z
  · rw [Int.ofNat_eq_natCast, Int.cast_natCast]
    exact SetLike.natCast_mem_graded _ _
  · rw [Int.cast_negSucc]
    exact neg_mem (SetLike.natCast_mem_graded _ _)

中文:
定理 集合状.intCast_mem_graded
  结论: [零 ι] [加法带幺群 R] [集合状 σ R]
  证明: by
  cases z
  · rw [Int.ofNat_eq_natCast, Int.cast_natCast]
    exact SetLike.natCast_mem_graded _ _
  · rw [Int.cast_negSucc]
    exact neg_mem (SetLike.natCast_mem_graded _ _)

Depends on / 依赖: Int.cast_natCast, Int.cast_negSucc, Int.ofNat_eq_natCast, SetLike, SetLike.natCast_mem_graded, cast_natCast, cast_negSucc, natCast_mem_graded, neg_mem, ofNat_eq_natCast
-/
theorem SetLike.intCast_mem_graded [Zero ι] [AddGroupWithOne R] [SetLike σ R]
    [AddSubgroupClass σ R] (A : ι -> σ) [SetLike.GradedOne A] (z : Int) : (z : R) in A 0 := by
  cases z
  · rw [Int.ofNat_eq_natCast, Int.cast_natCast]
    exact SetLike.natCast_mem_graded _ _
  · rw [Int.cast_negSucc]
    exact neg_mem (SetLike.natCast_mem_graded _ _)

section DirectSum

variable [DecidableEq ι]

/-! #### From `AddSubmonoid`s and `AddSubgroup`s -/


namespace SetLike

/--
Instance `gnonUnitalNonAssocSemiring` / 实例 `gnonUnitalNonAssocSemiring`

English:
instance gnonUnitalNonAssocSemiring
  signature: [Add ι] [NonUnitalNonAssocSemiring R] [SetLike σ R]
  body: Subtype.ext (mul_zero _)
  zero_mul _ := Subtype.ext (zero_mul _)
  mul_add _ _ _ := Subtype.ext (mul_add _ _ _)
  add_mul _ _ _ := Subtype.ext (add_mul _ _ _)

中文:
实例 gnonUnitalNonAssocSemiring
  签名: [加法 ι] [非幺非结合半环 R] [集合状 σ R]
  定义体: Subtype.ext (mul_zero _)
  zero_mul _ := Subtype.ext (zero_mul _)
  mul_add _ _ _ := Subtype.ext (mul_add _ _ _)
  add_mul _ _ _ := Subtype.ext (add_mul _ _ _)

Depends on / 依赖: Subtype, Subtype.ext, mul_zero
-/
instance gnonUnitalNonAssocSemiring [Add ι] [NonUnitalNonAssocSemiring R] [SetLike σ R]
    [AddSubmonoidClass σ R] (A : ι -> σ) [SetLike.GradedMul A] :
    DirectSum.GNonUnitalNonAssocSemiring fun i => A i where
  mul_zero _ := Subtype.ext (mul_zero _)
  zero_mul _ := Subtype.ext (zero_mul _)
  mul_add _ _ _ := Subtype.ext (mul_add _ _ _)
  add_mul _ _ _ := Subtype.ext (add_mul _ _ _)

/--
Instance `gsemiring` / 实例 `gsemiring`

English:
instance gsemiring
  signature: [AddMonoid ι] [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι -> σ)
  body: ⟨n, SetLike.natCast_mem_graded _ _⟩
  natCast_zero := Subtype.ext Nat.cast_zero
  natCast_succ n := Subtype.ext (Nat.cast_succ n)

中文:
实例 gsemiring
  签名: [加法幺半群 ι] [半环 R] [集合状 σ R] [加法子幺半群类 σ R] (A : ι -> σ)
  定义体: ⟨n, SetLike.natCast_mem_graded _ _⟩
  natCast_zero := Subtype.ext Nat.cast_zero
  natCast_succ n := Subtype.ext (Nat.cast_succ n)

Depends on / 依赖: SetLike, SetLike.natCast_mem_graded, natCast_mem_graded
-/
instance gsemiring [AddMonoid ι] [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι -> σ)
    [SetLike.GradedMonoid A] : DirectSum.GSemiring fun i => A i where
  natCast n := ⟨n, SetLike.natCast_mem_graded _ _⟩
  natCast_zero := Subtype.ext Nat.cast_zero
  natCast_succ n := Subtype.ext (Nat.cast_succ n)

/--
Instance `gcommSemiring` / 实例 `gcommSemiring`

English:
instance gcommSemiring
  signature: [AddCommMonoid ι] [CommSemiring R] [SetLike σ R] [AddSubmonoidClass σ R]

中文:
实例 gcommSemiring
  签名: [加法交换幺半群 ι] [交换半环 R] [集合状 σ R] [加法子幺半群类 σ R]
-/
instance gcommSemiring [AddCommMonoid ι] [CommSemiring R] [SetLike σ R] [AddSubmonoidClass σ R]
    (A : ι -> σ) [SetLike.GradedMonoid A] : DirectSum.GCommSemiring fun i => A i where

/--
Instance `gring` / 实例 `gring`

English:
instance gring
  signature: [AddMonoid ι] [Ring R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι -> σ)
  body: ⟨z, SetLike.intCast_mem_graded _ _⟩
intCast_ofNat n := Subtype.ext Int.cast_natCast n
intCast_negSucc_ofNat n := Subtype.ext Int.cast_negSucc n

中文:
实例 gring
  签名: [加法幺半群 ι] [环 R] [集合状 σ R] [加法子群类 σ R] (A : ι -> σ)
  定义体: ⟨z, SetLike.intCast_mem_graded _ _⟩
intCast_ofNat n := Subtype.ext Int.cast_natCast n
intCast_negSucc_ofNat n := Subtype.ext Int.cast_negSucc n

Depends on / 依赖: SetLike, SetLike.intCast_mem_graded, intCast_mem_graded
-/
instance gring [AddMonoid ι] [Ring R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι -> σ)
    [SetLike.GradedMonoid A] : DirectSum.GRing fun i => A i where
  intCast z := ⟨z, SetLike.intCast_mem_graded _ _⟩
intCast_ofNat n := Subtype.ext Int.cast_natCast n
intCast_negSucc_ofNat n := Subtype.ext Int.cast_negSucc n

/--
Instance `gcommRing` / 实例 `gcommRing`

English:
instance gcommRing
  signature: [AddCommMonoid ι] [CommRing R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι -> σ)

中文:
实例 gcommRing
  签名: [加法交换幺半群 ι] [交换环 R] [集合状 σ R] [加法子群类 σ R] (A : ι -> σ)
-/
instance gcommRing [AddCommMonoid ι] [CommRing R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι -> σ)
    [SetLike.GradedMonoid A] : DirectSum.GCommRing fun i => A i where

end SetLike

namespace DirectSum

section coe

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι -> σ)

/--
Definition of `coeRingHom` / `coeRingHom` 的定义

English:
definition coeRingHom
  signature: [AddMonoid ι] [SetLike.GradedMonoid A]
  body: DirectSum.toSemiring (fun i => AddSubmonoidClass.subtype (A i)) rfl fun _ _ => rfl

中文:
定义 coeRingHom
  签名: [加法幺半群 ι] [集合状.分次幺半群 A]
  定义体: DirectSum.toSemiring (fun i => AddSubmonoidClass.subtype (A i)) rfl fun _ _ => rfl

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.subtype, DirectSum, DirectSum.toSemiring, subtype, toSemiring
-/
def coeRingHom [AddMonoid ι] [SetLike.GradedMonoid A] : (⨁ i, A i) ->+* R :=
  DirectSum.toSemiring (fun i => AddSubmonoidClass.subtype (A i)) rfl fun _ _ => rfl

/-- The canonical ring isomorphism between `⨁ i, A i` and `R` -/
@[simp]
/--
theorem `coeRingHom_of` / 定理 `coeRingHom_of`

English:
theorem coeRingHom_of
  given: [AddMonoid ι] [SetLike.GradedMonoid A] (i : ι) (x : A i)
  proof: DirectSum.toSemiring_of _ _ _ _ _

中文:
定理 coeRingHom_of
  条件: [加法幺半群 ι] [集合状.分次幺半群 A] (i : ι) (x : A i)
  证明: DirectSum.toSemiring_of _ _ _ _ _

Depends on / 依赖: DirectSum, DirectSum.toSemiring_of, toSemiring_of
-/
theorem coeRingHom_of [AddMonoid ι] [SetLike.GradedMonoid A] (i : ι) (x : A i) :
    (coeRingHom A : _ ->+* R) (of (fun i => A i) i x) = x :=
  DirectSum.toSemiring_of _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coe_mul_apply` / 定理 `coe_mul_apply`

English:
theorem coe_mul_apply
  statement: [AddMonoid ι] [SetLike.GradedMonoid A]
  proof: by
  rw [mul_eq_sum_support_ghas_mul]; rw [DFinsupp.finsetSum_apply]; rw [AddSubmonoidClass.coe_finsetSum]
  simp_rw [coe_of_apply, apply_ite, ZeroMemClass.coe_zero, ← Finset.sum_filter, SetLike.coe_gMul]

中文:
定理 coe_mul_apply
  结论: [加法幺半群 ι] [集合状.分次幺半群 A]
  证明: by
  rw [mul_eq_sum_support_ghas_mul]; rw [DFinsupp.finsetSum_apply]; rw [AddSubmonoidClass.coe_finsetSum]
  simp_rw [coe_of_apply, apply_ite, ZeroMemClass.coe_zero, ← Finset.sum_filter, SetLike.coe_gMul]

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.coe_finsetSum, DFinsupp, DFinsupp.finsetSum_apply, Finset, Finset.sum_filter, SetLike, SetLike.coe_gMul, ZeroMemClass, ZeroMemClass.coe_zero, apply_ite, coe_finsetSum, coe_gMul, coe_of_apply, coe_zero, finsetSum_apply, mul_eq_sum_support_ghas_mul, simp_rw, sum_filter
-/
theorem coe_mul_apply [AddMonoid ι] [SetLike.GradedMonoid A]
    [forall (i : ι) (x : A i), Decidable (x != 0)] (r r' : ⨁ i, A i) (n : ι) :
    ((r * r') n : R) =
      ∑ ij in r.support ×ˢ r'.support with ij.1 + ij.2 = n, (r ij.1 * r' ij.2 : R) := by
  rw [mul_eq_sum_support_ghas_mul]; rw [DFinsupp.finsetSum_apply]; rw [AddSubmonoidClass.coe_finsetSum]
  simp_rw [coe_of_apply, apply_ite, ZeroMemClass.coe_zero, ← Finset.sum_filter, SetLike.coe_gMul]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coe_mul_apply_eq_dfinsuppSum` / 定理 `coe_mul_apply_eq_dfinsuppSum`

English:
theorem coe_mul_apply_eq_dfinsuppSum
  statement: [AddMonoid ι] [SetLike.GradedMonoid A]
  proof: by
  rw [mul_eq_dfinsuppSum]
  iterate 2 rw [DFinsupp.sum_apply, DFinsupp.sum, AddSubmonoidClass.coe_finsetSum]; congr; ext
  dsimp only
  split_ifs with h
  · subst h
    rw [of_eq_same]
    rfl
  · rw [of_eq_of_ne _ _ _ (Ne.symm h)]
    rfl

中文:
定理 coe_mul_apply_eq_dfinsuppSum
  结论: [加法幺半群 ι] [集合状.分次幺半群 A]
  证明: by
  rw [mul_eq_dfinsuppSum]
  iterate 2 rw [DFinsupp.sum_apply, DFinsupp.sum, AddSubmonoidClass.coe_finsetSum]; congr; ext
  dsimp only
  split_ifs with h
  · subst h
    rw [of_eq_same]
    rfl
  · rw [of_eq_of_ne _ _ _ (Ne.symm h)]
    rfl

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.coe_finsetSum, DFinsupp, DFinsupp.sum, DFinsupp.sum_apply, Ne.symm, coe_finsetSum, iterate, mul_eq_dfinsuppSum, of_eq_of_ne, of_eq_same, split_ifs, sum_apply
-/
theorem coe_mul_apply_eq_dfinsuppSum [AddMonoid ι] [SetLike.GradedMonoid A]
    [forall (i : ι) (x : A i), Decidable (x != 0)] (r r' : ⨁ i, A i) (n : ι) :
    ((r * r') n : R) = r.sum fun i ri => r'.sum fun j rj => if i + j = n then (ri * rj : R)
      else 0 := by
  rw [mul_eq_dfinsuppSum]
  iterate 2 rw [DFinsupp.sum_apply, DFinsupp.sum, AddSubmonoidClass.coe_finsetSum]; congr; ext
  dsimp only
  split_ifs with h
  · subst h
    rw [of_eq_same]
    rfl
  · rw [of_eq_of_ne _ _ _ (Ne.symm h)]
    rfl

set_option backward.isDefEq.respectTransparency false in
open Finset in
/--
theorem `coe_mul_apply_eq_sum_antidiagonal` / 定理 `coe_mul_apply_eq_sum_antidiagonal`

English:
theorem coe_mul_apply_eq_sum_antidiagonal
  statement: [AddMonoid ι] [HasAntidiagonal ι]
  proof: by
  classical
  rw [coe_mul_apply]
  apply Finset.sum_subset (fun _ => by simp)
  aesop (erase simp not_and) (add simp not_and_or)

中文:
定理 coe_mul_apply_eq_sum_antidiagonal
  结论: [加法幺半群 ι] [有Antidiagonal ι]
  证明: by
  classical
  rw [coe_mul_apply]
  apply Finset.sum_subset (fun _ => by simp)
  aesop (erase simp not_and) (add simp not_and_or)

Depends on / 依赖: Finset, Finset.sum_subset, classical, coe_mul_apply, not_and, not_and_or, sum_subset
-/
theorem coe_mul_apply_eq_sum_antidiagonal [AddMonoid ι] [HasAntidiagonal ι]
    [SetLike.GradedMonoid A] (r r' : ⨁ i, A i) (n : ι) :
    (r * r') n = ∑ ij in antidiagonal n, (r ij.1 : R) * r' ij.2 := by
  classical
  rw [coe_mul_apply]
  apply Finset.sum_subset (fun _ => by simp)
  aesop (erase simp not_and) (add simp not_and_or)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coe_of_mul_apply_aux` / 定理 `coe_of_mul_apply_aux`

English:
theorem coe_of_mul_apply_aux
  statement: [AddMonoid ι] [SetLike.GradedMonoid A] {i : ι} (r : A i)
  proof: by
  classical
    rw [coe_mul_apply_eq_dfinsuppSum]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, zero_mul, ite_self]
      exact DFinsupp.sum_zero
    simp_rw [DFinsupp.sum, H, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    rw [DFinsupp.notMem_support_iff.mp h]; rw [ZeroMemClass.coe_zero]; rw [mul_zero]

中文:
定理 coe_of_mul_apply_aux
  结论: [加法幺半群 ι] [集合状.分次幺半群 A] {i : ι} (r : A i)
  证明: by
  classical
    rw [coe_mul_apply_eq_dfinsuppSum]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, zero_mul, ite_self]
      exact DFinsupp.sum_zero
    simp_rw [DFinsupp.sum, H, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    rw [DFinsupp.notMem_support_iff.mp h]; rw [ZeroMemClass.coe_zero]; rw [mul_zero]

Depends on / 依赖: DFinsupp, DFinsupp.notMem_support_iff.mp, DFinsupp.sum, DFinsupp.sum_single_index, DFinsupp.sum_zero, Finset, Finset.sum_ite_eq, ZeroMemClass, ZeroMemClass.coe_zero, classical, coe_mul_apply_eq_dfinsuppSum, coe_zero, ite_self, mul_zero, notMem_support_iff, simp_rw, split_ifs, sum_ite_eq, sum_single_index, sum_zero
-/
theorem coe_of_mul_apply_aux [AddMonoid ι] [SetLike.GradedMonoid A] {i : ι} (r : A i)
    (r' : ⨁ i, A i) {j n : ι} (H : forall x : ι, i + x = n ↔ x = j) :
    ((of (fun i => A i) i r * r') n : R) = r * r' j := by
  classical
    rw [coe_mul_apply_eq_dfinsuppSum]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, zero_mul, ite_self]
      exact DFinsupp.sum_zero
    simp_rw [DFinsupp.sum, H, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    rw [DFinsupp.notMem_support_iff.mp h]; rw [ZeroMemClass.coe_zero]; rw [mul_zero]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coe_mul_of_apply_aux` / 定理 `coe_mul_of_apply_aux`

English:
theorem coe_mul_of_apply_aux
  statement: [AddMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i) {i : ι}
  proof: by
  classical
    rw [coe_mul_apply_eq_dfinsuppSum]; rw [DFinsupp.sum_comm]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, mul_zero, ite_self]
      exact DFinsupp.sum_zero
    simp_rw [DFinsupp.sum, H, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    rw [DFinsupp.notMem_support_iff.mp h]; rw [ZeroMemClass.coe_zero]; rw [zero_mul]

中文:
定理 coe_mul_of_apply_aux
  结论: [加法幺半群 ι] [集合状.分次幺半群 A] (r : ⨁ i, A i) {i : ι}
  证明: by
  classical
    rw [coe_mul_apply_eq_dfinsuppSum]; rw [DFinsupp.sum_comm]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, mul_zero, ite_self]
      exact DFinsupp.sum_zero
    simp_rw [DFinsupp.sum, H, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    rw [DFinsupp.notMem_support_iff.mp h]; rw [ZeroMemClass.coe_zero]; rw [zero_mul]

Depends on / 依赖: DFinsupp, DFinsupp.notMem_support_iff.mp, DFinsupp.sum, DFinsupp.sum_comm, DFinsupp.sum_single_index, DFinsupp.sum_zero, Finset, Finset.sum_ite_eq, ZeroMemClass, ZeroMemClass.coe_zero, classical, coe_mul_apply_eq_dfinsuppSum, coe_zero, ite_self, mul_zero, notMem_support_iff, simp_rw, split_ifs, sum_comm, sum_ite_eq
-/
theorem coe_mul_of_apply_aux [AddMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i) {i : ι}
    (r' : A i) {j n : ι} (H : forall x : ι, x + i = n ↔ x = j) :
    ((r * of (fun i => A i) i r') n : R) = r j * r' := by
  classical
    rw [coe_mul_apply_eq_dfinsuppSum]; rw [DFinsupp.sum_comm]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, mul_zero, ite_self]
      exact DFinsupp.sum_zero
    simp_rw [DFinsupp.sum, H, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    rw [DFinsupp.notMem_support_iff.mp h]; rw [ZeroMemClass.coe_zero]; rw [zero_mul]

/--
theorem `coe_of_mul_apply_add` / 定理 `coe_of_mul_apply_add`

English:
theorem coe_of_mul_apply_add
  statement: [AddLeftCancelMonoid ι] [SetLike.GradedMonoid A] {i : ι} (r : A i)
  proof: coe_of_mul_apply_aux _ _ _ fun _x => ⟨fun h => add_left_cancel h, fun h => h ▸ rfl⟩

中文:
定理 coe_of_mul_apply_add
  结论: [加法左消去幺半群 ι] [集合状.分次幺半群 A] {i : ι} (r : A i)
  证明: coe_of_mul_apply_aux _ _ _ fun _x => ⟨fun h => add_left_cancel h, fun h => h ▸ rfl⟩

Depends on / 依赖: add_left_cancel, coe_of_mul_apply_aux
-/
theorem coe_of_mul_apply_add [AddLeftCancelMonoid ι] [SetLike.GradedMonoid A] {i : ι} (r : A i)
    (r' : ⨁ i, A i) (j : ι) : ((of (fun i => A i) i r * r') (i + j) : R) = r * r' j :=
  coe_of_mul_apply_aux _ _ _ fun _x => ⟨fun h => add_left_cancel h, fun h => h ▸ rfl⟩

/--
theorem `coe_mul_of_apply_add` / 定理 `coe_mul_of_apply_add`

English:
theorem coe_mul_of_apply_add
  statement: [AddRightCancelMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i)
  proof: coe_mul_of_apply_aux _ _ _ fun _x => ⟨fun h => add_right_cancel h, fun h => h ▸ rfl⟩

中文:
定理 coe_mul_of_apply_add
  结论: [加法右消去幺半群 ι] [集合状.分次幺半群 A] (r : ⨁ i, A i)
  证明: coe_mul_of_apply_aux _ _ _ fun _x => ⟨fun h => add_right_cancel h, fun h => h ▸ rfl⟩

Depends on / 依赖: add_right_cancel, coe_mul_of_apply_aux
-/
theorem coe_mul_of_apply_add [AddRightCancelMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i)
    {i : ι} (r' : A i) (j : ι) : ((r * of (fun i => A i) i r') (j + i) : R) = r j * r' :=
  coe_mul_of_apply_aux _ _ _ fun _x => ⟨fun h => add_right_cancel h, fun h => h ▸ rfl⟩

/--
theorem `coe_of_mul_apply_of_mem_zero` / 定理 `coe_of_mul_apply_of_mem_zero`

English:
theorem coe_of_mul_apply_of_mem_zero
  statement: [AddMonoid ι] [SetLike.GradedMonoid A] (r : A 0)
  proof: coe_of_mul_apply_aux _ _ _ fun _x => by rw [zero_add]

中文:
定理 coe_of_mul_apply_of_mem_zero
  结论: [加法幺半群 ι] [集合状.分次幺半群 A] (r : A 0)
  证明: coe_of_mul_apply_aux _ _ _ fun _x => by rw [zero_add]

Depends on / 依赖: coe_of_mul_apply_aux, zero_add
-/
theorem coe_of_mul_apply_of_mem_zero [AddMonoid ι] [SetLike.GradedMonoid A] (r : A 0)
    (r' : ⨁ i, A i) (j : ι) : ((of (fun i => A i) 0 r * r') j : R) = r * r' j :=
  coe_of_mul_apply_aux _ _ _ fun _x => by rw [zero_add]

/--
theorem `coe_mul_of_apply_of_mem_zero` / 定理 `coe_mul_of_apply_of_mem_zero`

English:
theorem coe_mul_of_apply_of_mem_zero
  statement: [AddMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i)
  proof: coe_mul_of_apply_aux _ _ _ fun _x => by rw [add_zero]

中文:
定理 coe_mul_of_apply_of_mem_zero
  结论: [加法幺半群 ι] [集合状.分次幺半群 A] (r : ⨁ i, A i)
  证明: coe_mul_of_apply_aux _ _ _ fun _x => by rw [add_zero]

Depends on / 依赖: Seq.TerminatedAt, Seq.head, Stream, TerminatedAt, _tail, add_zero, coe_mul_of_apply_aux, generalizing, gp_head, s.get, s.head, s.tail.TerminatedAt, s_head_eq, terminatedAt_n
-/
theorem coe_mul_of_apply_of_mem_zero [AddMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i)
    (r' : A 0) (j : ι) : ((r * of (fun i => A i) 0 r') j : R) = r j * r' :=
  coe_mul_of_apply_aux _ _ _ fun _x => by rw [add_zero]

end coe

section CanonicallyOrderedAddCommMonoid

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι -> σ)
variable [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι] [SetLike.GradedMonoid A]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `coe_of_mul_apply_of_not_le` / 定理 `coe_of_mul_apply_of_not_le`

English:
theorem coe_of_mul_apply_of_not_le
  given: {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) (h : ¬i <= n)
  proof: by
  classical
    rw [coe_mul_apply_eq_dfinsuppSum]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, zero_mul, ite_self]
      exact DFinsupp.sum_zero
    · rw [DFinsupp.sum, Finset.sum_ite_of_false, Finset.sum_const_zero]
      exact fun x _ H => h ((self_le_add_right i x).trans_eq H)

中文:
定理 coe_of_mul_apply_of_not_le
  条件: {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) (h : ¬i <= n)
  证明: by
  classical
    rw [coe_mul_apply_eq_dfinsuppSum]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, zero_mul, ite_self]
      exact DFinsupp.sum_zero
    · rw [DFinsupp.sum, Finset.sum_ite_of_false, Finset.sum_const_zero]
      exact fun x _ H => h ((self_le_add_right i x).trans_eq H)

Depends on / 依赖: Aux_stable_step_of_terminated, DFinsupp, DFinsupp.sum, DFinsupp.sum_single_index, DFinsupp.sum_zero, Finset, Finset.sum_const_zero, Finset.sum_ite_of_false, ZeroMemClass, ZeroMemClass.coe_zero, classical, coe_mul_apply_eq_dfinsuppSum, coe_zero, ite_self, n_le_m, s.terminated_stable, self_le_add_right, simp_rw, sum_const_zero, sum_ite_of_false
-/
theorem coe_of_mul_apply_of_not_le {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) (h : ¬i <= n) :
    ((of (fun i => A i) i r * r') n : R) = 0 := by
  classical
    rw [coe_mul_apply_eq_dfinsuppSum]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, zero_mul, ite_self]
      exact DFinsupp.sum_zero
    · rw [DFinsupp.sum, Finset.sum_ite_of_false, Finset.sum_const_zero]
      exact fun x _ H => h ((self_le_add_right i x).trans_eq H)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `coe_mul_of_apply_of_not_le` / 定理 `coe_mul_of_apply_of_not_le`

English:
theorem coe_mul_of_apply_of_not_le
  given: (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) (h : ¬i <= n)
  proof: by
  classical
    rw [coe_mul_apply_eq_dfinsuppSum]; rw [DFinsupp.sum_comm]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, mul_zero, ite_self]
      exact DFinsupp.sum_zero
    · rw [DFinsupp.sum, Finset.sum_ite_of_false, Finset.sum_const_zero]
      exact fun x _ H => h ((self_le_add_left i x).trans_eq H)

中文:
定理 coe_mul_of_apply_of_not_le
  条件: (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) (h : ¬i <= n)
  证明: by
  classical
    rw [coe_mul_apply_eq_dfinsuppSum]; rw [DFinsupp.sum_comm]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, mul_zero, ite_self]
      exact DFinsupp.sum_zero
    · rw [DFinsupp.sum, Finset.sum_ite_of_false, Finset.sum_const_zero]
      exact fun x _ H => h ((self_le_add_left i x).trans_eq H)

Depends on / 依赖: DFinsupp, DFinsupp.sum, DFinsupp.sum_comm, DFinsupp.sum_single_index, DFinsupp.sum_zero, Finset, Finset.sum_const_zero, Finset.sum_ite_of_false, ZeroMemClass, ZeroMemClass.coe_zero, classical, coe_mul_apply_eq_dfinsuppSum, coe_zero, ite_self, mul_zero, self_le_add_left, simp_rw, sum_comm, sum_const_zero, sum_ite_of_false
-/
theorem coe_mul_of_apply_of_not_le (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) (h : ¬i <= n) :
    ((r * of (fun i => A i) i r') n : R) = 0 := by
  classical
    rw [coe_mul_apply_eq_dfinsuppSum]; rw [DFinsupp.sum_comm]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, mul_zero, ite_self]
      exact DFinsupp.sum_zero
    · rw [DFinsupp.sum, Finset.sum_ite_of_false, Finset.sum_const_zero]
      exact fun x _ H => h ((self_le_add_left i x).trans_eq H)

variable [Sub ι] [OrderedSub ι] [AddLeftReflectLE ι]


/--
theorem `coe_mul_of_apply_of_le` / 定理 `coe_mul_of_apply_of_le`

English:
theorem coe_mul_of_apply_of_le
  given: (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) (h : i <= n)
  proof: coe_mul_of_apply_aux _ _ _ fun _x => (eq_tsub_iff_add_eq_of_le h).symm

中文:
定理 coe_mul_of_apply_of_le
  条件: (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) (h : i <= n)
  证明: coe_mul_of_apply_aux _ _ _ fun _x => (eq_tsub_iff_add_eq_of_le h).symm

Depends on / 依赖: coe_mul_of_apply_aux, eq_tsub_iff_add_eq_of_le
-/
theorem coe_mul_of_apply_of_le (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) (h : i <= n) :
    ((r * of (fun i => A i) i r') n : R) = r (n - i) * r' :=
  coe_mul_of_apply_aux _ _ _ fun _x => (eq_tsub_iff_add_eq_of_le h).symm

/--
theorem `coe_of_mul_apply_of_le` / 定理 `coe_of_mul_apply_of_le`

English:
theorem coe_of_mul_apply_of_le
  given: {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) (h : i <= n)
  proof: coe_of_mul_apply_aux _ _ _ fun x => by rw [eq_tsub_iff_add_eq_of_le h, add_comm]

中文:
定理 coe_of_mul_apply_of_le
  条件: {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) (h : i <= n)
  证明: coe_of_mul_apply_aux _ _ _ fun x => by rw [eq_tsub_iff_add_eq_of_le h, add_comm]

Depends on / 依赖: add_comm, coe_of_mul_apply_aux, eq_tsub_iff_add_eq_of_le
-/
theorem coe_of_mul_apply_of_le {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) (h : i <= n) :
    ((of (fun i => A i) i r * r') n : R) = r * r' (n - i) :=
  coe_of_mul_apply_aux _ _ _ fun x => by rw [eq_tsub_iff_add_eq_of_le h, add_comm]

/--
theorem `coe_mul_of_apply` / 定理 `coe_mul_of_apply`

English:
theorem coe_mul_of_apply
  given: (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) [Decidable (i <= n)]
  proof: by
  split_ifs with h
  exacts [coe_mul_of_apply_of_le _ _ _ n h, coe_mul_of_apply_of_not_le _ _ _ n h]

中文:
定理 coe_mul_of_apply
  条件: (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) [可判定 (i <= n)]
  证明: by
  split_ifs with h
  exacts [coe_mul_of_apply_of_le _ _ _ n h, coe_mul_of_apply_of_not_le _ _ _ n h]

Depends on / 依赖: coe_mul_of_apply_of_le, coe_mul_of_apply_of_not_le, exacts, split_ifs
-/
theorem coe_mul_of_apply (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) [Decidable (i <= n)] :
    ((r * of (fun i => A i) i r') n : R) = if i <= n then (r (n - i) : R) * r' else 0 := by
  split_ifs with h
  exacts [coe_mul_of_apply_of_le _ _ _ n h, coe_mul_of_apply_of_not_le _ _ _ n h]

/--
theorem `coe_of_mul_apply` / 定理 `coe_of_mul_apply`

English:
theorem coe_of_mul_apply
  given: {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) [Decidable (i <= n)]
  proof: by
  split_ifs with h
  exacts [coe_of_mul_apply_of_le _ _ _ n h, coe_of_mul_apply_of_not_le _ _ _ n h]

中文:
定理 coe_of_mul_apply
  条件: {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) [可判定 (i <= n)]
  证明: by
  split_ifs with h
  exacts [coe_of_mul_apply_of_le _ _ _ n h, coe_of_mul_apply_of_not_le _ _ _ n h]

Depends on / 依赖: Aux_stable_of_terminated, coe_of_mul_apply_of_le, coe_of_mul_apply_of_not_le, exacts, n_le_m, split_ifs, terminatedAt_n
-/
theorem coe_of_mul_apply {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) [Decidable (i <= n)] :
    ((of (fun i => A i) i r * r') n : R) = if i <= n then (r * r' (n - i) : R) else 0 := by
  split_ifs with h
  exacts [coe_of_mul_apply_of_le _ _ _ n h, coe_of_mul_apply_of_not_le _ _ _ n h]

end CanonicallyOrderedAddCommMonoid

end DirectSum

/-! #### From `Submodule`s -/

namespace Submodule

/--
Instance `galgebra` / 实例 `galgebra`

English:
instance galgebra
  signature: [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R] (A : ι -> Submodule S R)
  body: ((Algebra.linearMap S R).codRestrict (A 0) <| SetLike.algebraMap_mem_graded A).toAddMonoidHom
map_one := Subtype.ext (algebraMap S R).map_one
map_mul _x _y := Sigma.subtype_ext (add_zero 0).symm (algebraMap S R).map_mul _ _
  commutes := fun _r ⟨i, _xi⟩ =>
Sigma.subtype_ext ((zero_add i).trans (add_zero i).symm) Algebra.commutes _ _
smul_def := fun _r ⟨i, _xi⟩ => Sigma.subtype_ext (zero_add i).symm Algebra.smul_def _ _

@[simp]

中文:
实例 galgebra
  签名: [加法幺半群 ι] [交换半环 S] [半环 R] [代数 S R] (A : ι -> 子模 S R)
  定义体: ((Algebra.linearMap S R).codRestrict (A 0) <| SetLike.algebraMap_mem_graded A).toAddMonoidHom
map_one := Subtype.ext (algebraMap S R).map_one
map_mul _x _y := Sigma.subtype_ext (add_zero 0).symm (algebraMap S R).map_mul _ _
  commutes := fun _r ⟨i, _xi⟩ =>
Sigma.subtype_ext ((zero_add i).trans (add_zero i).symm) Algebra.commutes _ _
smul_def := fun _r ⟨i, _xi⟩ => Sigma.subtype_ext (zero_add i).symm Algebra.smul_def _ _

@[simp]

Depends on / 依赖: Algebra, Algebra.commutes, Algebra.linearMap, Algebra.smul_def, SetLike, SetLike.algebraMap_mem_graded, Sigma.subtype_ext, Subtype, Subtype.ext, add_zero, algebraMap, algebraMap_mem_graded, codRestrict, commutes, linearMap, map_mul, map_one, smul_def, subtype_ext, toAddMonoidHom
-/
instance galgebra [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R] (A : ι -> Submodule S R)
    [SetLike.GradedMonoid A] : DirectSum.GAlgebra S fun i => A i where
  toFun :=
    ((Algebra.linearMap S R).codRestrict (A 0) <| SetLike.algebraMap_mem_graded A).toAddMonoidHom
map_one := Subtype.ext (algebraMap S R).map_one
map_mul _x _y := Sigma.subtype_ext (add_zero 0).symm (algebraMap S R).map_mul _ _
  commutes := fun _r ⟨i, _xi⟩ =>
Sigma.subtype_ext ((zero_add i).trans (add_zero i).symm) Algebra.commutes _ _
smul_def := fun _r ⟨i, _xi⟩ => Sigma.subtype_ext (zero_add i).symm Algebra.smul_def _ _

@[simp]
/--
theorem `setLike.coe_galgebra_toFun` / 定理 `setLike.coe_galgebra_toFun`

English:
theorem setLike.coe_galgebra_toFun
  statement: {ι} [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
  proof: rfl

中文:
定理 setLike.coe_galgebra_toFun
  结论: {ι} [加法幺半群 ι] [交换半环 S] [半环 R] [代数 S R]
  证明: rfl

Depends on / 依赖: algebraMap
-/
theorem setLike.coe_galgebra_toFun {ι} [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι -> Submodule S R) [SetLike.GradedMonoid A] (s : S) :
    (DirectSum.GAlgebra.toFun (A := fun i => A i) s) = (algebraMap S R s : R) :=
  rfl

/--
Instance `nat_power_gradedMonoid` / 实例 `nat_power_gradedMonoid`

English:
instance nat_power_gradedMonoid
  signature: [CommSemiring S] [Semiring R] [Algebra S R] (p : Submodule S R)
  body: by
    rw [← one_le]; rw [pow_zero]
  mul_mem i j p q hp hq := by
    rw [pow_add]
    exact Submodule.mul_mem_mul hp hq

中文:
实例 nat_power_gradedMonoid
  签名: [交换半环 S] [半环 R] [代数 S R] (p : 子模 S R)
  定义体: by
    rw [← one_le]; rw [pow_zero]
  mul_mem i j p q hp hq := by
    rw [pow_add]
    exact Submodule.mul_mem_mul hp hq

Depends on / 依赖: Submodule, Submodule.mul_mem_mul, mul_mem, mul_mem_mul, one_le, pow_add, pow_zero
-/
instance nat_power_gradedMonoid [CommSemiring S] [Semiring R] [Algebra S R] (p : Submodule S R) :
    SetLike.GradedMonoid fun i : Nat => p ^ i where
  one_mem := by
    rw [← one_le]; rw [pow_zero]
  mul_mem i j p q hp hq := by
    rw [pow_add]
    exact Submodule.mul_mem_mul hp hq

end Submodule

/--
Definition of `DirectSum.coeAlgHom` / `DirectSum.coeAlgHom` 的定义

English:
definition DirectSum.coeAlgHom
  signature: [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
  body: DirectSum.toAlgebra S _ (fun i => (A i).subtype) rfl (fun _ _ => rfl)

中文:
定义 直和.coeAlgHom
  签名: [加法幺半群 ι] [交换半环 S] [半环 R] [代数 S R]
  定义体: DirectSum.toAlgebra S _ (fun i => (A i).subtype) rfl (fun _ _ => rfl)

Depends on / 依赖: DirectSum, DirectSum.toAlgebra, subtype, toAlgebra
-/
def DirectSum.coeAlgHom [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι -> Submodule S R) [SetLike.GradedMonoid A] : (⨁ i, A i) ->ₐ[S] R :=
  DirectSum.toAlgebra S _ (fun i => (A i).subtype) rfl (fun _ _ => rfl)

/--
theorem `Submodule.iSup_eq_toSubmodule_range` / 定理 `Submodule.iSup_eq_toSubmodule_range`

English:
theorem Submodule.iSup_eq_toSubmodule_range
  statement: [AddMonoid ι] [CommSemiring S] [Semiring R]
  proof: (Submodule.iSup_eq_range_dfinsupp_lsum A).trans SetLike.coe_injective rfl

@[simp]

中文:
定理 子模.iSup_eq_toSubmodule_range
  结论: [加法幺半群 ι] [交换半环 S] [半环 R]
  证明: (Submodule.iSup_eq_range_dfinsupp_lsum A).trans SetLike.coe_injective rfl

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, Submodule, Submodule.iSup_eq_range_dfinsupp_lsum, coe_injective, iSup_eq_range_dfinsupp_lsum
-/
theorem Submodule.iSup_eq_toSubmodule_range [AddMonoid ι] [CommSemiring S] [Semiring R]
    [Algebra S R] (A : ι -> Submodule S R) [SetLike.GradedMonoid A] :
    ⨆ i, A i = Subalgebra.toSubmodule (DirectSum.coeAlgHom A).range :=
(Submodule.iSup_eq_range_dfinsupp_lsum A).trans SetLike.coe_injective rfl

@[simp]
/--
theorem `DirectSum.coeAlgHom_of` / 定理 `DirectSum.coeAlgHom_of`

English:
theorem DirectSum.coeAlgHom_of
  statement: [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
  proof: DirectSum.toSemiring_of _ rfl (fun _ _ => rfl) _ _

中文:
定理 直和.coeAlgHom_of
  结论: [加法幺半群 ι] [交换半环 S] [半环 R] [代数 S R]
  证明: DirectSum.toSemiring_of _ rfl (fun _ _ => rfl) _ _

Depends on / 依赖: DirectSum, DirectSum.toSemiring_of, toSemiring_of
-/
theorem DirectSum.coeAlgHom_of [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι -> Submodule S R) [SetLike.GradedMonoid A] (i : ι) (x : A i) :
    DirectSum.coeAlgHom A (DirectSum.of (fun i => A i) i x) = x :=
  DirectSum.toSemiring_of _ rfl (fun _ _ => rfl) _ _

end DirectSum

/-! ### Facts about grade zero -/

namespace SetLike.GradeZero

section Semiring
variable [Semiring R] [AddMonoid ι] [SetLike σ R] [AddSubmonoidClass σ R]
variable (A : ι -> σ) [SetLike.GradedMonoid A]

/--
Definition of `subsemiring` / `subsemiring` 的定义

English:
definition subsemiring
  signature: : Subsemiring R where
  body: submonoid A
  add_mem' := add_mem
  zero_mem' := zero_mem (A 0)

中文:
定义 subsemiring
  签名: : 子半环 R where
  定义体: submonoid A
  add_mem' := add_mem
  zero_mem' := zero_mem (A 0)

Depends on / 依赖: submonoid
-/
def subsemiring : Subsemiring R where
  __ := submonoid A
  add_mem' := add_mem
  zero_mem' := zero_mem (A 0)

-- TODO: it might be expensive to unify `A` in this instance in practice
/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: : Semiring (A 0)
  body: inferInstanceAs Semiring (subsemiring A)

中文:
实例 instSemiring
  签名: : 半环 (A 0)
  定义体: inferInstanceAs Semiring (subsemiring A)

Depends on / 依赖: Semiring, subsemiring
-/
instance instSemiring : Semiring (A 0) := inferInstanceAs Semiring (subsemiring A)

/--
theorem `coe_natCast` / 定理 `coe_natCast`

English:
theorem coe_natCast
  given: (n : Nat)
  statement: (n : A 0) = (n : R)
  proof: rfl

中文:
定理 coe_natCast
  条件: (n : 自然数)
  结论: (n : A 0) = (n : R)
  证明: rfl
-/
@[simp, norm_cast] theorem coe_natCast (n : Nat) : (n : A 0) = (n : R) := rfl

/--
theorem `coe_ofNat` / 定理 `coe_ofNat`

English:
theorem coe_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: rfl

中文:
定理 coe_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: rfl
-/
@[simp, norm_cast] theorem coe_ofNat (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : A 0) = (ofNat(n) : R) := rfl

end Semiring

section CommSemiring
variable [CommSemiring R] [AddMonoid ι] [SetLike σ R] [AddSubmonoidClass σ R]
variable (A : ι -> σ) [SetLike.GradedMonoid A]

-- TODO: it might be expensive to unify `A` in this instance in practice
/--
Instance `instCommSemiring` / 实例 `instCommSemiring`

English:
instance instCommSemiring
  signature: : CommSemiring (A 0)
  body: inferInstanceAs CommSemiring (subsemiring A)

中文:
实例 instCommSemiring
  签名: : 交换半环 (A 0)
  定义体: inferInstanceAs CommSemiring (subsemiring A)

Depends on / 依赖: CommSemiring, subsemiring
-/
instance instCommSemiring : CommSemiring (A 0) := inferInstanceAs CommSemiring (subsemiring A)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra (A 0) R
  body: inferInstanceAs Algebra (SetLike.GradeZero.subsemiring A) R

中文:
实例 :
  签名: 代数 (A 0) R
  定义体: inferInstanceAs Algebra (SetLike.GradeZero.subsemiring A) R

Depends on / 依赖: Algebra, GradeZero, SetLike, SetLike.GradeZero.subsemiring, subsemiring
-/
instance : Algebra (A 0) R :=
inferInstanceAs Algebra (SetLike.GradeZero.subsemiring A) R

/--
lemma `algebraMap_apply` / 引理 `algebraMap_apply`

English:
lemma algebraMap_apply
  given: (x : A 0)
  statement: algebraMap (A 0) R x = x
  proof: rfl

中文:
引理 algebraMap_apply
  条件: (x : A 0)
  结论: algebraMap (A 0) R x = x
  证明: rfl
-/
@[simp] lemma algebraMap_apply (x : A 0) : algebraMap (A 0) R x = x := rfl

end CommSemiring

section Ring
variable [Ring R] [AddMonoid ι] [SetLike σ R] [AddSubgroupClass σ R]
variable (A : ι -> σ) [SetLike.GradedMonoid A]

/--
Definition of `subring` / `subring` 的定义

English:
definition subring
  signature: : Subring R where
  body: subsemiring A
  neg_mem' := neg_mem

中文:
定义 subring
  签名: : 子环 R where
  定义体: subsemiring A
  neg_mem' := neg_mem

Depends on / 依赖: subsemiring
-/
def subring : Subring R where
  __ := subsemiring A
  neg_mem' := neg_mem

-- TODO: it might be expensive to unify `A` in this instance in practice
/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: : Ring (A 0)
  body: inferInstanceAs Ring (subring A)

中文:
实例 instRing
  签名: : 环 (A 0)
  定义体: inferInstanceAs Ring (subring A)

Depends on / 依赖: subring
-/
instance instRing : Ring (A 0) := inferInstanceAs Ring (subring A)

/--
theorem `coe_intCast` / 定理 `coe_intCast`

English:
theorem coe_intCast
  given: (z : Int)
  statement: (z : A 0) = (z : R)
  proof: rfl

中文:
定理 coe_intCast
  条件: (z : 整数)
  结论: (z : A 0) = (z : R)
  证明: rfl
-/
theorem coe_intCast (z : Int) : (z : A 0) = (z : R) := rfl

end Ring

section CommRing
variable [CommRing R] [AddCommMonoid ι] [SetLike σ R] [AddSubgroupClass σ R]
variable (A : ι -> σ) [SetLike.GradedMonoid A]

-- TODO: it might be expensive to unify `A` in this instance in practice
/--
Instance `instCommRing` / 实例 `instCommRing`

English:
instance instCommRing
  signature: : CommRing (A 0)
  body: inferInstanceAs CommRing (subring A)

中文:
实例 instCommRing
  签名: : 交换环 (A 0)
  定义体: inferInstanceAs CommRing (subring A)

Depends on / 依赖: CommRing, subring
-/
instance instCommRing : CommRing (A 0) := inferInstanceAs CommRing (subring A)

end CommRing

section Algebra
variable [CommSemiring S] [Semiring R] [Algebra S R] [AddMonoid ι]
variable (A : ι -> Submodule S R) [SetLike.GradedMonoid A]

/--
Definition of `subalgebra` / `subalgebra` 的定义

English:
definition subalgebra
  signature: : Subalgebra S R where
  body: subsemiring A
  algebraMap_mem' := algebraMap_mem_graded A

中文:
定义 subalgebra
  签名: : 子代数 S R where
  定义体: subsemiring A
  algebraMap_mem' := algebraMap_mem_graded A

Depends on / 依赖: subsemiring
-/
def subalgebra : Subalgebra S R where
  __ := subsemiring A
  algebraMap_mem' := algebraMap_mem_graded A

-- TODO: it might be expensive to unify `A` in this instance in practice
/--
Instance `instAlgebra` / 实例 `instAlgebra`

English:
instance instAlgebra
  signature: : Algebra S (A 0)
  body: inferInstanceAs Algebra S (subalgebra A)

中文:
实例 instAlgebra
  签名: : 代数 S (A 0)
  定义体: inferInstanceAs Algebra S (subalgebra A)

Depends on / 依赖: Algebra, subalgebra
-/
instance instAlgebra : Algebra S (A 0) := inferInstanceAs Algebra S (subalgebra A)

/--
theorem `coe_algebraMap` / 定理 `coe_algebraMap`

English:
theorem coe_algebraMap
  given: (s : S)
  proof: rfl

中文:
定理 coe_algebraMap
  条件: (s : S)
  证明: rfl
-/
@[simp, norm_cast] theorem coe_algebraMap (s : S) :
    ↑(algebraMap _ (A 0) s) = algebraMap _ R s := rfl

end Algebra

end SetLike.GradeZero

section HomogeneousElement

/--
theorem `SetLike.homogeneous_zero_submodule` / 定理 `SetLike.homogeneous_zero_submodule`

English:
theorem SetLike.homogeneous_zero_submodule
  statement: [Zero ι] [Semiring S] [AddCommMonoid R] [Module S R]
  proof: ⟨0, Submodule.zero_mem _⟩

中文:
定理 集合状.homogeneous_zero_submodule
  结论: [零 ι] [半环 S] [加法交换幺半群 R] [模 S R]
  证明: ⟨0, Submodule.zero_mem _⟩

Depends on / 依赖: Submodule, Submodule.zero_mem, zero_mem
-/
theorem SetLike.homogeneous_zero_submodule [Zero ι] [Semiring S] [AddCommMonoid R] [Module S R]
    (A : ι -> Submodule S R) : SetLike.IsHomogeneousElem A (0 : R) :=
  ⟨0, Submodule.zero_mem _⟩

/--
theorem `SetLike.Homogeneous.smul` / 定理 `SetLike.Homogeneous.smul`

English:
theorem SetLike.Homogeneous.smul
  statement: [CommSemiring S] [Semiring R] [Algebra S R] {A : ι -> Submodule S R}
  proof: let ⟨i, hi⟩ := hr
  ⟨i, Submodule.smul_mem _ _ hi⟩

中文:
定理 集合状.齐次.smul
  结论: [交换半环 S] [半环 R] [代数 S R] {A : ι -> 子模 S R}
  证明: let ⟨i, hi⟩ := hr
  ⟨i, Submodule.smul_mem _ _ hi⟩

Depends on / 依赖: Submodule, Submodule.smul_mem, smul_mem
-/
theorem SetLike.Homogeneous.smul [CommSemiring S] [Semiring R] [Algebra S R] {A : ι -> Submodule S R}
    {s : S} {r : R} (hr : SetLike.IsHomogeneousElem A r) : SetLike.IsHomogeneousElem A (s • r) :=
  let ⟨i, hi⟩ := hr
  ⟨i, Submodule.smul_mem _ _ hi⟩

end HomogeneousElement

/-! ### Gradings by canonically linearly ordered additive monoids -/

section LinearOrderedAddCommMonoid

variable [AddCommMonoid ι] [LinearOrder ι] [IsOrderedAddMonoid ι] [DecidableEq ι]

section Semiring

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R]
variable {A : ι -> σ} [SetLike.GradedMonoid A]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mul_apply_eq_zero` / 定理 `mul_apply_eq_zero`

English:
theorem mul_apply_eq_zero
  statement: {r r' : ⨁ i, A i} {m n : ι}
  proof: by
  classical
  rw [Subtype.ext_iff]; rw [ZeroMemClass.coe_zero]; rw [coe_mul_apply]
  apply Finset.sum_eq_zero fun x hx => ?_
  obtain (hx | hx) : x.1 < m ∨ x.2 < n := by
    by_contra! ⟨hm, hn⟩
    obtain rfl : x.1 + x.2 = k := by simp_all
apply lt_irrefl (m + n) lt_of_le_of_lt (by gcongr) hk
  all_goals simp [hr, hr', hx]

中文:
定理 mul_apply_eq_zero
  结论: {r r' : ⨁ i, A i} {m n : ι}
  证明: by
  classical
  rw [Subtype.ext_iff]; rw [ZeroMemClass.coe_zero]; rw [coe_mul_apply]
  apply Finset.sum_eq_zero fun x hx => ?_
  obtain (hx | hx) : x.1 < m ∨ x.2 < n := by
    by_contra! ⟨hm, hn⟩
    obtain rfl : x.1 + x.2 = k := by simp_all
apply lt_irrefl (m + n) lt_of_le_of_lt (by gcongr) hk
  all_goals simp [hr, hr', hx]

Depends on / 依赖: Finset, Finset.sum_eq_zero, Subtype, Subtype.ext_iff, ZeroMemClass, ZeroMemClass.coe_zero, all_goals, classical, coe_mul_apply, coe_zero, ext_iff, lt_irrefl, lt_of_le_of_lt, sum_eq_zero
-/
theorem mul_apply_eq_zero {r r' : ⨁ i, A i} {m n : ι}
    (hr : forall i < m, r i = 0) (hr' : forall i < n, r' i = 0) ⦃k : ι⦄ (hk : k < m + n) :
    (r * r') k = 0 := by
  classical
  rw [Subtype.ext_iff]; rw [ZeroMemClass.coe_zero]; rw [coe_mul_apply]
  apply Finset.sum_eq_zero fun x hx => ?_
  obtain (hx | hx) : x.1 < m ∨ x.2 < n := by
    by_contra! ⟨hm, hn⟩
    obtain rfl : x.1 + x.2 = k := by simp_all
apply lt_irrefl (m + n) lt_of_le_of_lt (by gcongr) hk
  all_goals simp [hr, hr', hx]

variable [CanonicallyOrderedAdd ι]

/--
theorem `listProd_apply_eq_zero'` / 定理 `listProd_apply_eq_zero'`

English:
theorem listProd_apply_eq_zero'
  statement: {l : List ((⨁ i, A i) × ι)}
  proof: by
  induction l generalizing n with
  | nil => simp at hn
  | cons head tail ih =>
    simp only [List.mem_cons, forall_eq_or_imp, List.map_cons, List.sum_cons,
      List.prod_cons] at hl hn ⊢
    exact mul_apply_eq_zero hl.1 (ih hl.2) hn

中文:
定理 listProd_apply_eq_zero'
  结论: {l : 列表 ((⨁ i, A i) × ι)}
  证明: by
  induction l generalizing n with
  | nil => simp at hn
  | cons head tail ih =>
    simp only [List.mem_cons, forall_eq_or_imp, List.map_cons, List.sum_cons,
      List.prod_cons] at hl hn ⊢
    exact mul_apply_eq_zero hl.1 (ih hl.2) hn

Depends on / 依赖: List.map_cons, List.mem_cons, List.prod_cons, List.sum_cons, forall_eq_or_imp, generalizing, map_cons, mem_cons, mul_apply_eq_zero, prod_cons, sum_cons
-/
theorem listProd_apply_eq_zero' {l : List ((⨁ i, A i) × ι)}
    (hl : forall xn in l, forall k < xn.2, xn.1 k = 0) ⦃n : ι⦄ (hn : n < (l.map Prod.snd).sum) :
    (l.map Prod.fst).prod n = 0 := by
  induction l generalizing n with
  | nil => simp at hn
  | cons head tail ih =>
    simp only [List.mem_cons, forall_eq_or_imp, List.map_cons, List.sum_cons,
      List.prod_cons] at hl hn ⊢
    exact mul_apply_eq_zero hl.1 (ih hl.2) hn

/--
theorem `listProd_apply_eq_zero` / 定理 `listProd_apply_eq_zero`

English:
theorem listProd_apply_eq_zero
  statement: {l : List (⨁ i, A i)} {m : ι}
  proof: by
  -- a proof which uses `DirectSum.listProd_apply_eq_zero'` is actually more work
  induction l generalizing n with
  | nil => simp at hn
  | cons head tail ih =>
    simp only [List.mem_cons, forall_eq_or_imp, List.length_cons, List.prod_cons] at hl hn ⊢
    refine mul_apply_eq_zero hl.1 (ih hl.2) ?_
    simpa [add_smul, add_comm m] using hn

中文:
定理 listProd_apply_eq_zero
  结论: {l : 列表 (⨁ i, A i)} {m : ι}
  证明: by
  -- a proof which uses `DirectSum.listProd_apply_eq_zero'` is actually more work
  induction l generalizing n with
  | nil => simp at hn
  | cons head tail ih =>
    simp only [List.mem_cons, forall_eq_or_imp, List.length_cons, List.prod_cons] at hl hn ⊢
    refine mul_apply_eq_zero hl.1 (ih hl.2) ?_
    simpa [add_smul, add_comm m] using hn
-/
theorem listProd_apply_eq_zero {l : List (⨁ i, A i)} {m : ι}
    (hl : forall x in l, forall k < m, x k = 0) ⦃n : ι⦄ (hn : n < l.length • m) :
    l.prod n = 0 := by
  -- a proof which uses `DirectSum.listProd_apply_eq_zero'` is actually more work
  induction l generalizing n with
  | nil => simp at hn
  | cons head tail ih =>
    simp only [List.mem_cons, forall_eq_or_imp, List.length_cons, List.prod_cons] at hl hn ⊢
    refine mul_apply_eq_zero hl.1 (ih hl.2) ?_
    simpa [add_smul, add_comm m] using hn

end Semiring

variable [CanonicallyOrderedAdd ι]

section CommSemiring

variable [CommSemiring R] [SetLike σ R] [AddSubmonoidClass σ R]
variable {A : ι -> σ} [SetLike.GradedMonoid A]

/--
theorem `multisetProd_apply_eq_zero'` / 定理 `multisetProd_apply_eq_zero'`

English:
theorem multisetProd_apply_eq_zero'
  statement: {s : Multiset ((⨁ i, A i) × ι)}
  proof: by
  have := listProd_apply_eq_zero' (l := s.toList) (by simpa using hs)
    (by simpa [← Multiset.sum_coe, ← Multiset.map_coe])
  simpa [← Multiset.prod_coe, ← Multiset.map_coe]

中文:
定理 multisetProd_apply_eq_zero'
  结论: {s : Multiset ((⨁ i, A i) × ι)}
  证明: by
  have := listProd_apply_eq_zero' (l := s.toList) (by simpa using hs)
    (by simpa [← Multiset.sum_coe, ← Multiset.map_coe])
  simpa [← Multiset.prod_coe, ← Multiset.map_coe]

Depends on / 依赖: Multiset, Multiset.map_coe, Multiset.prod_coe, Multiset.sum_coe, listProd_apply_eq_zero, map_coe, prod_coe, s.toList, sum_coe, toList
-/
theorem multisetProd_apply_eq_zero' {s : Multiset ((⨁ i, A i) × ι)}
    (hs : forall xn in s, forall k < xn.2, xn.1 k = 0) ⦃n : ι⦄ (hn : n < (s.map Prod.snd).sum) :
    (s.map Prod.fst).prod n = 0 := by
  have := listProd_apply_eq_zero' (l := s.toList) (by simpa using hs)
    (by simpa [← Multiset.sum_coe, ← Multiset.map_coe])
  simpa [← Multiset.prod_coe, ← Multiset.map_coe]

/--
theorem `multisetProd_apply_eq_zero` / 定理 `multisetProd_apply_eq_zero`

English:
theorem multisetProd_apply_eq_zero
  statement: {s : Multiset (⨁ i, A i)} {m : ι}
  proof: by
  have := listProd_apply_eq_zero (l := s.toList) (by simpa using hs)
    (by simpa [← Multiset.sum_coe, ← Multiset.map_coe])
  simpa [← Multiset.prod_coe, ← Multiset.map_coe]

中文:
定理 multisetProd_apply_eq_zero
  结论: {s : Multiset (⨁ i, A i)} {m : ι}
  证明: by
  have := listProd_apply_eq_zero (l := s.toList) (by simpa using hs)
    (by simpa [← Multiset.sum_coe, ← Multiset.map_coe])
  simpa [← Multiset.prod_coe, ← Multiset.map_coe]

Depends on / 依赖: Multiset, Multiset.map_coe, Multiset.prod_coe, Multiset.sum_coe, listProd_apply_eq_zero, map_coe, prod_coe, s.toList, sum_coe, toList
-/
theorem multisetProd_apply_eq_zero {s : Multiset (⨁ i, A i)} {m : ι}
    (hs : forall x in s, forall k < m, x k = 0) ⦃n : ι⦄ (hn : n < s.card • m) :
    s.prod n = 0 := by
  have := listProd_apply_eq_zero (l := s.toList) (by simpa using hs)
    (by simpa [← Multiset.sum_coe, ← Multiset.map_coe])
  simpa [← Multiset.prod_coe, ← Multiset.map_coe]

/--
theorem `finsetProd_apply_eq_zero'` / 定理 `finsetProd_apply_eq_zero'`

English:
theorem finsetProd_apply_eq_zero'
  statement: {s : Finset ((⨁ i, A i) × ι)}
  proof: by
  simpa using listProd_apply_eq_zero' (l := s.toList) (by simpa using hs) (by simpa)

中文:
定理 finsetProd_apply_eq_zero'
  结论: {s : 有限集 ((⨁ i, A i) × ι)}
  证明: by
  simpa using listProd_apply_eq_zero' (l := s.toList) (by simpa using hs) (by simpa)

Depends on / 依赖: listProd_apply_eq_zero, s.toList, toList
-/
theorem finsetProd_apply_eq_zero' {s : Finset ((⨁ i, A i) × ι)}
    (hs : forall xn in s, forall k < xn.2, xn.1 k = 0) ⦃n : ι⦄ (hn : n < ∑ xn in s, xn.2) :
    (∏ xn in s, xn.1) n = 0 := by
  simpa using listProd_apply_eq_zero' (l := s.toList) (by simpa using hs) (by simpa)

/--
theorem `finsetProd_apply_eq_zero` / 定理 `finsetProd_apply_eq_zero`

English:
theorem finsetProd_apply_eq_zero
  statement: {s : Finset (⨁ i, A i)} {m : ι}
  proof: by
  simpa using listProd_apply_eq_zero (l := s.toList) (by simpa using hs) (by simpa)

中文:
定理 finsetProd_apply_eq_zero
  结论: {s : 有限集 (⨁ i, A i)} {m : ι}
  证明: by
  simpa using listProd_apply_eq_zero (l := s.toList) (by simpa using hs) (by simpa)

Depends on / 依赖: listProd_apply_eq_zero, s.toList, toList
-/
theorem finsetProd_apply_eq_zero {s : Finset (⨁ i, A i)} {m : ι}
    (hs : forall x in s, forall k < m, x k = 0) ⦃n : ι⦄ (hn : n < s.card • m) :
    (∏ x in s, x) n = 0 := by
  simpa using listProd_apply_eq_zero (l := s.toList) (by simpa using hs) (by simpa)

end CommSemiring

end LinearOrderedAddCommMonoid
