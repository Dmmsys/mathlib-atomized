/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Adjoin.Tower
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Orzech

/-!
# Finiteness conditions in commutative algebra

In this file we define a notion of finiteness that is common in commutative algebra.

## Main declarations

- `Algebra.FiniteType`, `RingHom.FiniteType`, `AlgHom.FiniteType`
  all of these express that some object is finitely generated *as an algebra* over some base ring.

-/

@[expose] public section

open Function (Surjective)

open Polynomial

section ModuleAndAlgebra

universe uR uS uA uB uM uN
variable (R : Type uR) (S : Type uS) (A : Type uA) (B : Type uB) (M : Type uM) (N : Type uN)

/--
Definition of `Algebra.FiniteType` / `Algebra.FiniteType` 的定义

English:
class Algebra.FiniteType
  parameters: [CommSemiring R] [Semiring A] [Algebra R A]
  axioms and operations (1):
    - out : (⊤ : Subalgebra R A).FG

中文:
类 代数.有限型
  参数: [交换半环 R] [半环 A] [代数 R A]
  公理与运算 (1 个):
    - out : (⊤ : 子代数 R A).FG
-/
class Algebra.FiniteType [CommSemiring R] [Semiring A] [Algebra R A] : Prop where
  out : (⊤ : Subalgebra R A).FG

namespace Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

namespace Finite

open Submodule Set

variable {R S M N}

section Algebra

-- see Note [lower instance priority]
instance (priority := 100) finiteType {R : Type*} (A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] [hRA : Module.Finite R A] : Algebra.FiniteType R A :=
  ⟨Subalgebra.fg_of_submodule_fg hRA.1⟩

end Algebra

end Finite

end Module

namespace Algebra

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra R A] [Algebra R B]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

namespace FiniteType

/--
theorem `of_restrictScalars_finiteType` / 定理 `of_restrictScalars_finiteType`

English:
theorem of_restrictScalars_finiteType
  given: [Algebra S A] [IsScalarTower R S A] [hA : FiniteType R A]
  proof: by
  obtain ⟨s, hS⟩ := hA.out
  refine ⟨⟨s, eq_top_iff.2 fun b => ?_⟩⟩
  have le : adjoin R (s : Set A) <= Subalgebra.restrictScalars R (adjoin S s) := by
    apply (Algebra.adjoin_le _ : adjoin R (s : Set A) <= Subalgebra.restrictScalars R (adjoin S ↑s))
    simp only [Subalgebra.coe_restrictScalars]
    exact Algebra.subset_adjoin
  exact le (eq_top_iff.1 hS b)

中文:
定理 of_restrictScalars_finiteType
  条件: [代数 S A] [标量塔 R S A] [hA : 有限型 R A]
  证明: by
  obtain ⟨s, hS⟩ := hA.out
  refine ⟨⟨s, eq_top_iff.2 fun b => ?_⟩⟩
  have le : adjoin R (s : Set A) <= Subalgebra.restrictScalars R (adjoin S s) := by
    apply (Algebra.adjoin_le _ : adjoin R (s : Set A) <= Subalgebra.restrictScalars R (adjoin S ↑s))
    simp only [Subalgebra.coe_restrictScalars]
    exact Algebra.subset_adjoin
  exact le (eq_top_iff.1 hS b)

Depends on / 依赖: Algebra, Algebra.adjoin_le, Algebra.subset_adjoin, Subalgebra, Subalgebra.coe_restrictScalars, Subalgebra.restrictScalars, adjoin, adjoin_le, coe_restrictScalars, eq_top_iff, hA.out, restrictScalars, subset_adjoin
-/
theorem of_restrictScalars_finiteType [Algebra S A] [IsScalarTower R S A] [hA : FiniteType R A] :
    FiniteType S A := by
  obtain ⟨s, hS⟩ := hA.out
  refine ⟨⟨s, eq_top_iff.2 fun b => ?_⟩⟩
  have le : adjoin R (s : Set A) <= Subalgebra.restrictScalars R (adjoin S s) := by
    apply (Algebra.adjoin_le _ : adjoin R (s : Set A) <= Subalgebra.restrictScalars R (adjoin S ↑s))
    simp only [Subalgebra.coe_restrictScalars]
    exact Algebra.subset_adjoin
  exact le (eq_top_iff.1 hS b)

variable {R S A B}

/--
theorem `of_surjective` / 定理 `of_surjective`

English:
theorem of_surjective
  given: [FiniteType R A] (f : A ->ₐ[R] B) (hf : Surjective f)
  statement: FiniteType R B
  proof: ⟨by
    convert ‹FiniteType R A›.1.map f
    simpa only [map_top f, @eq_comm _ ⊤, eq_top_iff, AlgHom.mem_range] using! hf⟩

中文:
定理 of_surjective
  条件: [有限型 R A] (f : A ->ₐ[R] B) (hf : 满射 f)
  结论: 有限型 R B
  证明: ⟨by
    convert ‹FiniteType R A›.1.map f
    simpa only [map_top f, @eq_comm _ ⊤, eq_top_iff, AlgHom.mem_range] using! hf⟩

Depends on / 依赖: AlgHom, AlgHom.mem_range, FiniteType, convert, eq_comm, eq_top_iff, map_top, mem_range
-/
theorem of_surjective [FiniteType R A] (f : A ->ₐ[R] B) (hf : Surjective f) : FiniteType R B :=
  ⟨by
    convert ‹FiniteType R A›.1.map f
    simpa only [map_top f, @eq_comm _ ⊤, eq_top_iff, AlgHom.mem_range] using! hf⟩

/--
theorem `equiv` / 定理 `equiv`

English:
theorem equiv
  given: (hRA : FiniteType R A) (e : A ≃ₐ[R] B)
  statement: FiniteType R B
  proof: hRA.of_surjective e e.surjective

中文:
定理 equiv
  条件: (hRA : 有限型 R A) (e : A ≃ₐ[R] B)
  结论: 有限型 R B
  证明: hRA.of_surjective e e.surjective

Depends on / 依赖: e.surjective, hRA.of_surjective, of_surjective, surjective
-/
theorem equiv (hRA : FiniteType R A) (e : A ≃ₐ[R] B) : FiniteType R B :=
  hRA.of_surjective e e.surjective

/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: [Algebra S A] [IsScalarTower R S A] (hRS : FiniteType R S) (hSA : FiniteType S A)
  proof: ⟨fg_trans' hRS.1 hSA.1⟩

中文:
定理 trans
  条件: [代数 S A] [标量塔 R S A] (hRS : 有限型 R S) (hSA : 有限型 S A)
  证明: ⟨fg_trans' hRS.1 hSA.1⟩

Depends on / 依赖: fg_trans
-/
theorem trans [Algebra S A] [IsScalarTower R S A] (hRS : FiniteType R S) (hSA : FiniteType S A) :
    FiniteType R A :=
  ⟨fg_trans' hRS.1 hSA.1⟩

/--
Instance `quotient` / 实例 `quotient`

English:
instance quotient
  signature: (R : Type*) {S : Type*} [CommSemiring R] [CommRing S] [Algebra R S] (I : Ideal S)
  body: Algebra.FiniteType.trans h inferInstance

中文:
实例 quotient
  签名: (R : 类型) {S : 类型} [交换半环 R] [交换环 S] [代数 R S] (I : 理想 S)
  定义体: Algebra.FiniteType.trans h inferInstance

Depends on / 依赖: Algebra, Algebra.FiniteType.trans, FiniteType
-/
instance quotient (R : Type*) {S : Type*} [CommSemiring R] [CommRing S] [Algebra R S] (I : Ideal S)
    [h : Algebra.FiniteType R S] : Algebra.FiniteType R (S ⧸ I) :=
  Algebra.FiniteType.trans h inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FiniteType
  signature: R S] : FiniteType R S[X]
  body: by
  refine .trans ‹_› ⟨{Polynomial.X}, ?_⟩
  rw [Finset.coe_singleton]
  exact Polynomial.adjoin_X

中文:
实例 [有限型
  签名: R S] : 有限型 R S[X]
  定义体: by
  refine .trans ‹_› ⟨{Polynomial.X}, ?_⟩
  rw [Finset.coe_singleton]
  exact Polynomial.adjoin_X

Depends on / 依赖: Finset, Finset.coe_singleton, Polynomial, Polynomial.X, Polynomial.adjoin_X, adjoin_X, coe_singleton
-/
instance [FiniteType R S] : FiniteType R S[X] := by
  refine .trans ‹_› ⟨{Polynomial.X}, ?_⟩
  rw [Finset.coe_singleton]
  exact Polynomial.adjoin_X

instance {ι : Type*} [Finite ι] [FiniteType R S] : FiniteType R (MvPolynomial ι S) := by
  classical
  cases nonempty_fintype ι
  refine .trans ‹_› ⟨Finset.univ.image MvPolynomial.X, ?_⟩
  rw [Finset.coe_image]; rw [Finset.coe_univ]; rw [Set.image_univ]
  exact MvPolynomial.adjoin_range_X

instance {ι : Type*} [Finite ι] [FiniteType R S] : FiniteType R (FreeAlgebra S ι) := by
  classical
  cases nonempty_fintype ι
  refine .trans ‹_› ⟨Finset.univ.image (FreeAlgebra.ι _), ?_⟩
  rw [Finset.coe_image]; rw [Finset.coe_univ]; rw [Set.image_univ]
  exact FreeAlgebra.adjoin_range_ι ..

/--
theorem `iff_quotient_freeAlgebra` / 定理 `iff_quotient_freeAlgebra`

English:
theorem iff_quotient_freeAlgebra
  proof: by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, FreeAlgebra.lift _ (↑), ?_⟩
    rw [← Set.range_eq_univ]; rw [← AlgHom.coe_range]; rw [← adjoin_range_eq_range_freeAlgebra_lift]; rw [Subtype.range_coe_subtype]; rw [Finset.setOfPred_mem]; rw [hs]; rw [coe_top]
  · rintro ⟨s, f, hsur⟩
    exact .of_surjective f hsur

中文:
定理 iff_quotient_freeAlgebra
  证明: by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, FreeAlgebra.lift _ (↑), ?_⟩
    rw [← Set.range_eq_univ]; rw [← AlgHom.coe_range]; rw [← adjoin_range_eq_range_freeAlgebra_lift]; rw [Subtype.range_coe_subtype]; rw [Finset.setOfPred_mem]; rw [hs]; rw [coe_top]
  · rintro ⟨s, f, hsur⟩
    exact .of_surjective f hsur

Depends on / 依赖: AlgHom, AlgHom.coe_range, Finset, Finset.setOfPred_mem, FreeAlgebra, FreeAlgebra.lift, Set.range_eq_univ, Subtype, Subtype.range_coe_subtype, adjoin_range_eq_range_freeAlgebra_lift, coe_range, coe_top, of_surjective, range_coe_subtype, range_eq_univ, setOfPred_mem
-/
theorem iff_quotient_freeAlgebra :
    FiniteType R A ↔
      exists (s : Finset A) (f : FreeAlgebra R s ->ₐ[R] A), Surjective f := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, FreeAlgebra.lift _ (↑), ?_⟩
    rw [← Set.range_eq_univ]; rw [← AlgHom.coe_range]; rw [← adjoin_range_eq_range_freeAlgebra_lift]; rw [Subtype.range_coe_subtype]; rw [Finset.setOfPred_mem]; rw [hs]; rw [coe_top]
  · rintro ⟨s, f, hsur⟩
    exact .of_surjective f hsur

/--
theorem `iff_quotient_mvPolynomial` / 定理 `iff_quotient_mvPolynomial`

English:
theorem iff_quotient_mvPolynomial
  proof: by
  constructor
  · rintro ⟨s, hs⟩
    use s, MvPolynomial.aeval (↑)
    intro x
    rw [← Set.mem_range]; rw [← AlgHom.coe_range]; rw [← adjoin_eq_range]; rw [SetLike.mem_coe]; rw [hs]
    apply mem_top
  · rintro ⟨s, f, hsur⟩
    exact .of_surjective f hsur

中文:
定理 iff_quotient_mvPolynomial
  证明: by
  constructor
  · rintro ⟨s, hs⟩
    use s, MvPolynomial.aeval (↑)
    intro x
    rw [← Set.mem_range]; rw [← AlgHom.coe_range]; rw [← adjoin_eq_range]; rw [SetLike.mem_coe]; rw [hs]
    apply mem_top
  · rintro ⟨s, f, hsur⟩
    exact .of_surjective f hsur

Depends on / 依赖: AlgHom, AlgHom.coe_range, MvPolynomial, MvPolynomial.aeval, Set.mem_range, SetLike, SetLike.mem_coe, adjoin_eq_range, coe_range, mem_coe, mem_range, mem_top, of_surjective
-/
theorem iff_quotient_mvPolynomial :
    FiniteType R S ↔
      exists (s : Finset S) (f : MvPolynomial { x // x in s } R ->ₐ[R] S), Surjective f := by
  constructor
  · rintro ⟨s, hs⟩
    use s, MvPolynomial.aeval (↑)
    intro x
    rw [← Set.mem_range]; rw [← AlgHom.coe_range]; rw [← adjoin_eq_range]; rw [SetLike.mem_coe]; rw [hs]
    apply mem_top
  · rintro ⟨s, f, hsur⟩
    exact .of_surjective f hsur

/--
theorem `iff_quotient_freeAlgebra'` / 定理 `iff_quotient_freeAlgebra'`

English:
theorem iff_quotient_freeAlgebra'
  statement: FiniteType R A ↔
  proof: by
  constructor
  · rw [iff_quotient_freeAlgebra]
    rintro ⟨s, f, hsur⟩
    use { x : A // x in s }, inferInstance, f
  · rintro ⟨ι, hfintype, f, hsur⟩
    let : Fintype ι := hfintype
    exact .of_surjective f hsur

中文:
定理 iff_quotient_freeAlgebra'
  结论: 有限型 R A ↔
  证明: by
  constructor
  · rw [iff_quotient_freeAlgebra]
    rintro ⟨s, f, hsur⟩
    use { x : A // x in s }, inferInstance, f
  · rintro ⟨ι, hfintype, f, hsur⟩
    let : Fintype ι := hfintype
    exact .of_surjective f hsur

Depends on / 依赖: Fintype, hfintype, iff_quotient_freeAlgebra, of_surjective
-/
theorem iff_quotient_freeAlgebra' : FiniteType R A ↔
    exists (ι : Type uA) (_ : Fintype ι) (f : FreeAlgebra R ι ->ₐ[R] A), Surjective f := by
  constructor
  · rw [iff_quotient_freeAlgebra]
    rintro ⟨s, f, hsur⟩
    use { x : A // x in s }, inferInstance, f
  · rintro ⟨ι, hfintype, f, hsur⟩
    let : Fintype ι := hfintype
    exact .of_surjective f hsur

/--
theorem `iff_quotient_mvPolynomial'` / 定理 `iff_quotient_mvPolynomial'`

English:
theorem iff_quotient_mvPolynomial'
  statement: FiniteType R S ↔
  proof: by
  constructor
  · rw [iff_quotient_mvPolynomial]
    rintro ⟨s, f, hsur⟩
    use { x : S // x in s }, inferInstance, f
  · rintro ⟨ι, hfintype, f, hsur⟩
    let : Fintype ι := hfintype
    exact .of_surjective f hsur

中文:
定理 iff_quotient_mvPolynomial'
  结论: 有限型 R S ↔
  证明: by
  constructor
  · rw [iff_quotient_mvPolynomial]
    rintro ⟨s, f, hsur⟩
    use { x : S // x in s }, inferInstance, f
  · rintro ⟨ι, hfintype, f, hsur⟩
    let : Fintype ι := hfintype
    exact .of_surjective f hsur

Depends on / 依赖: Fintype, hfintype, iff_quotient_mvPolynomial, of_surjective
-/
theorem iff_quotient_mvPolynomial' : FiniteType R S ↔
    exists (ι : Type uS) (_ : Fintype ι) (f : MvPolynomial ι R ->ₐ[R] S), Surjective f := by
  constructor
  · rw [iff_quotient_mvPolynomial]
    rintro ⟨s, f, hsur⟩
    use { x : S // x in s }, inferInstance, f
  · rintro ⟨ι, hfintype, f, hsur⟩
    let : Fintype ι := hfintype
    exact .of_surjective f hsur

/--
theorem `iff_quotient_mvPolynomial''` / 定理 `iff_quotient_mvPolynomial''`

English:
theorem iff_quotient_mvPolynomial''
  proof: by
  constructor
  · rw [iff_quotient_mvPolynomial']
    rintro ⟨ι, hfintype, f, hsur⟩
    have equiv := MvPolynomial.renameEquiv R (Fintype.equivFin ι)
    exact ⟨Fintype.card ι, AlgHom.comp f equiv.symm.toAlgHom, by simpa using hsur⟩
  · rintro ⟨n, f, hsur⟩
    exact .of_surjective f hsur

中文:
定理 iff_quotient_mvPolynomial''
  证明: by
  constructor
  · rw [iff_quotient_mvPolynomial']
    rintro ⟨ι, hfintype, f, hsur⟩
    have equiv := MvPolynomial.renameEquiv R (Fintype.equivFin ι)
    exact ⟨Fintype.card ι, AlgHom.comp f equiv.symm.toAlgHom, by simpa using hsur⟩
  · rintro ⟨n, f, hsur⟩
    exact .of_surjective f hsur

Depends on / 依赖: AlgHom, AlgHom.comp, Fintype, Fintype.card, Fintype.equivFin, MvPolynomial, MvPolynomial.renameEquiv, equiv.symm.toAlgHom, equivFin, hfintype, iff_quotient_mvPolynomial, of_surjective, renameEquiv, toAlgHom
-/
theorem iff_quotient_mvPolynomial'' :
    FiniteType R S ↔ exists (n : Nat) (f : MvPolynomial (Fin n) R ->ₐ[R] S), Surjective f := by
  constructor
  · rw [iff_quotient_mvPolynomial']
    rintro ⟨ι, hfintype, f, hsur⟩
    have equiv := MvPolynomial.renameEquiv R (Fintype.equivFin ι)
    exact ⟨Fintype.card ι, AlgHom.comp f equiv.symm.toAlgHom, by simpa using hsur⟩
  · rintro ⟨n, f, hsur⟩
    exact .of_surjective f hsur

/--
Instance `prod` / 实例 `prod`

English:
instance prod
  signature: [hA : FiniteType R A] [hB : FiniteType R B]
  body: ⟨by rw [← Subalgebra.prod_top]; exact hA.1.prod hB.1⟩

中文:
实例 乘积
  签名: [hA : 有限型 R A] [hB : 有限型 R B]
  定义体: ⟨by rw [← Subalgebra.prod_top]; exact hA.1.prod hB.1⟩

Depends on / 依赖: Subalgebra, Subalgebra.prod_top, prod_top
-/
instance prod [hA : FiniteType R A] [hB : FiniteType R B] : FiniteType R (A × B) :=
  ⟨by rw [← Subalgebra.prod_top]; exact hA.1.prod hB.1⟩

/--
theorem `isNoetherianRing` / 定理 `isNoetherianRing`

English:
theorem isNoetherianRing
  statement: (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  proof: by
  obtain ⟨s, hs⟩ := h.1
  apply
    isNoetherianRing_of_surjective (MvPolynomial s R) S
      (MvPolynomial.aeval (↑) : MvPolynomial s R ->ₐ[R] S).toRingHom
  rw [← Set.range_eq_univ]; rw [AlgHom.toRingHom_eq_coe]; rw [RingHom.coe_coe]; rw [← AlgHom.coe_range]; rw [← Algebra.adjoin_range_eq_range_aeval]; rw [Subtype.range_coe_subtype]; rw [Finset.setOfPred_mem]; rw [hs]
  rfl

中文:
定理 isNoetherianRing
  结论: (R S : 类型) [交换环 R] [交换环 S] [代数 R S]
  证明: by
  obtain ⟨s, hs⟩ := h.1
  apply
    isNoetherianRing_of_surjective (MvPolynomial s R) S
      (MvPolynomial.aeval (↑) : MvPolynomial s R ->ₐ[R] S).toRingHom
  rw [← Set.range_eq_univ]; rw [AlgHom.toRingHom_eq_coe]; rw [RingHom.coe_coe]; rw [← AlgHom.coe_range]; rw [← Algebra.adjoin_range_eq_range_aeval]; rw [Subtype.range_coe_subtype]; rw [Finset.setOfPred_mem]; rw [hs]
  rfl

Depends on / 依赖: AlgHom, AlgHom.coe_range, AlgHom.toRingHom_eq_coe, Algebra, Algebra.adjoin_range_eq_range_aeval, Finset, Finset.setOfPred_mem, MvPolynomial, MvPolynomial.aeval, RingHom, RingHom.coe_coe, Set.range_eq_univ, Subtype, Subtype.range_coe_subtype, adjoin_range_eq_range_aeval, coe_coe, coe_range, isNoetherianRing_of_surjective, range_coe_subtype, range_eq_univ
-/
theorem isNoetherianRing (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [h : Algebra.FiniteType R S] [IsNoetherianRing R] : IsNoetherianRing S := by
  obtain ⟨s, hs⟩ := h.1
  apply
    isNoetherianRing_of_surjective (MvPolynomial s R) S
      (MvPolynomial.aeval (↑) : MvPolynomial s R ->ₐ[R] S).toRingHom
  rw [← Set.range_eq_univ]; rw [AlgHom.toRingHom_eq_coe]; rw [RingHom.coe_coe]; rw [← AlgHom.coe_range]; rw [← Algebra.adjoin_range_eq_range_aeval]; rw [Subtype.range_coe_subtype]; rw [Finset.setOfPred_mem]; rw [hs]
  rfl

/--
theorem `_root_.Subalgebra.fg_iff_finiteType` / 定理 `_root_.Subalgebra.fg_iff_finiteType`

English:
theorem _root_.Subalgebra.fg_iff_finiteType
  given: (S : Subalgebra R A)
  statement: S.FG ↔ Algebra.FiniteType R S
  proof: S.fg_top.symm.trans ⟨fun h => ⟨h⟩, fun h => h.out⟩

中文:
定理 _root_.子代数.fg_iff_finiteType
  条件: (S : 子代数 R A)
  结论: S.FG ↔ 代数.有限型 R S
  证明: S.fg_top.symm.trans ⟨fun h => ⟨h⟩, fun h => h.out⟩

Depends on / 依赖: S.fg_top.symm.trans, fg_top, h.out
-/
theorem _root_.Subalgebra.fg_iff_finiteType (S : Subalgebra R A) : S.FG ↔ Algebra.FiniteType R S :=
  S.fg_top.symm.trans ⟨fun h => ⟨h⟩, fun h => h.out⟩

/--
lemma `adjoin_of_finite` / 引理 `adjoin_of_finite`

English:
lemma adjoin_of_finite
  given: {A : Type*} [CommSemiring A] [Algebra R A] {t : Set A} (h : Set.Finite t)
  proof: by
  rw [← Subalgebra.fg_iff_finiteType]
  exact ⟨h.toFinset, by simp⟩

中文:
引理 adjoin_of_finite
  条件: {A : 类型} [交换半环 A] [代数 R A] {t : 集合 A} (h : 集合.有限 t)
  证明: by
  rw [← Subalgebra.fg_iff_finiteType]
  exact ⟨h.toFinset, by simp⟩

Depends on / 依赖: Subalgebra, Subalgebra.fg_iff_finiteType, fg_iff_finiteType, h.toFinset, toFinset
-/
lemma adjoin_of_finite {A : Type*} [CommSemiring A] [Algebra R A] {t : Set A} (h : Set.Finite t) :
    FiniteType R (Algebra.adjoin R t) := by
  rw [← Subalgebra.fg_iff_finiteType]
  exact ⟨h.toFinset, by simp⟩

end FiniteType

end Algebra

end ModuleAndAlgebra

namespace RingHom

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- A ring morphism `A →+* B` is of `FiniteType` if `B` is finitely generated as `A`-algebra. -/
@[algebraize]
/--
Definition of `FiniteType` / `FiniteType` 的定义

English:
definition FiniteType
  signature: (f : A ->+* B)
  body: @Algebra.FiniteType A B _ _ f.toAlgebra

中文:
定义 有限型
  签名: (f : A ->+* B)
  定义体: @Algebra.FiniteType A B _ _ f.toAlgebra

Depends on / 依赖: Algebra, Algebra.FiniteType, FiniteType, f.toAlgebra, toAlgebra
-/
def FiniteType (f : A ->+* B) : Prop :=
  @Algebra.FiniteType A B _ _ f.toAlgebra

/--
lemma `finiteType_algebraMap` / 引理 `finiteType_algebraMap`

English:
lemma finiteType_algebraMap
  given: [Algebra A B]
  proof: by
  rw [FiniteType]; rw [toAlgebra_algebraMap]

中文:
引理 finiteType_algebraMap
  条件: [代数 A B]
  证明: by
  rw [FiniteType]; rw [toAlgebra_algebraMap]

Depends on / 依赖: FiniteType, toAlgebra_algebraMap
-/
lemma finiteType_algebraMap [Algebra A B] :
    (algebraMap A B).FiniteType ↔ Algebra.FiniteType A B := by
  rw [FiniteType]; rw [toAlgebra_algebraMap]

namespace Finite

/--
theorem `finiteType` / 定理 `finiteType`

English:
theorem finiteType
  given: {f : A ->+* B} (hf : f.Finite)
  statement: FiniteType f
  proof: @Module.Finite.finiteType _ _ _ _ f.toAlgebra hf

中文:
定理 finiteType
  条件: {f : A ->+* B} (hf : f.有限)
  结论: 有限型 f
  证明: @Module.Finite.finiteType _ _ _ _ f.toAlgebra hf

Depends on / 依赖: Finite, Module, Module.Finite.finiteType, f.toAlgebra, finiteType, toAlgebra
-/
theorem finiteType {f : A ->+* B} (hf : f.Finite) : FiniteType f :=
  @Module.Finite.finiteType _ _ _ _ f.toAlgebra hf

end Finite

namespace FiniteType

-- TODO: should infer_instance be marked as normalising?
set_option linter.flexible false in
variable (A) in
/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: FiniteType (RingHom.id A)
  proof: by simp [FiniteType]; infer_instance

中文:
定理 id
  结论: 有限型 (环态射.id A)
  证明: by simp [FiniteType]; infer_instance

Depends on / 依赖: FiniteType, infer_instance
-/
theorem id : FiniteType (RingHom.id A) := by simp [FiniteType]; infer_instance

/--
theorem `comp_surjective` / 定理 `comp_surjective`

English:
theorem comp_surjective
  given: {f : A ->+* B} {g : B ->+* C} (hf : f.FiniteType) (hg : Surjective g)
  proof: by
  algebraize_only [f, g.comp f]
  exact ‹Algebra.FiniteType _ _›.of_surjective
    { g with
      toFun := g
      commutes' := fun a => rfl }
    hg

中文:
定理 comp_surjective
  条件: {f : A ->+* B} {g : B ->+* C} (hf : f.有限型) (hg : 满射 g)
  证明: by
  algebraize_only [f, g.comp f]
  exact ‹Algebra.FiniteType _ _›.of_surjective
    { g with
      toFun := g
      commutes' := fun a => rfl }
    hg

Depends on / 依赖: Algebra, Algebra.FiniteType, FiniteType, algebraize_only, commutes, g.comp, of_surjective
-/
theorem comp_surjective {f : A ->+* B} {g : B ->+* C} (hf : f.FiniteType) (hg : Surjective g) :
    (g.comp f).FiniteType := by
  algebraize_only [f, g.comp f]
  exact ‹Algebra.FiniteType _ _›.of_surjective
    { g with
      toFun := g
      commutes' := fun a => rfl }
    hg

/--
theorem `of_surjective` / 定理 `of_surjective`

English:
theorem of_surjective
  given: (f : A ->+* B) (hf : Surjective f)
  statement: f.FiniteType
  proof: by
  rw [← f.comp_id]
  exact (id A).comp_surjective hf

中文:
定理 of_surjective
  条件: (f : A ->+* B) (hf : 满射 f)
  结论: f.有限型
  证明: by
  rw [← f.comp_id]
  exact (id A).comp_surjective hf

Depends on / 依赖: comp_id, comp_surjective, f.comp_id
-/
theorem of_surjective (f : A ->+* B) (hf : Surjective f) : f.FiniteType := by
  rw [← f.comp_id]
  exact (id A).comp_surjective hf

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: {g : B ->+* C} {f : A ->+* B} (hg : g.FiniteType) (hf : f.FiniteType)
  proof: by
  algebraize_only [f, g, g.comp f]
  exact Algebra.FiniteType.trans hf hg

中文:
定理 comp
  条件: {g : B ->+* C} {f : A ->+* B} (hg : g.有限型) (hf : f.有限型)
  证明: by
  algebraize_only [f, g, g.comp f]
  exact Algebra.FiniteType.trans hf hg

Depends on / 依赖: Algebra, Algebra.FiniteType.trans, FiniteType, algebraize_only, g.comp
-/
theorem comp {g : B ->+* C} {f : A ->+* B} (hg : g.FiniteType) (hf : f.FiniteType) :
    (g.comp f).FiniteType := by
  algebraize_only [f, g, g.comp f]
  exact Algebra.FiniteType.trans hf hg

/--
theorem `of_finite` / 定理 `of_finite`

English:
theorem of_finite
  given: {f : A ->+* B} (hf : f.Finite)
  statement: f.FiniteType
  proof: @Module.Finite.finiteType _ _ _ _ f.toAlgebra hf

alias _root_.RingHom.Finite.to_finiteType := of_finite

中文:
定理 of_finite
  条件: {f : A ->+* B} (hf : f.有限)
  结论: f.有限型
  证明: @Module.Finite.finiteType _ _ _ _ f.toAlgebra hf

alias _root_.RingHom.Finite.to_finiteType := of_finite

Depends on / 依赖: Finite, Module, Module.Finite.finiteType, f.toAlgebra, finiteType, toAlgebra
-/
theorem of_finite {f : A ->+* B} (hf : f.Finite) : f.FiniteType :=
  @Module.Finite.finiteType _ _ _ _ f.toAlgebra hf

alias _root_.RingHom.Finite.to_finiteType := of_finite

/--
theorem `of_comp_finiteType` / 定理 `of_comp_finiteType`

English:
theorem of_comp_finiteType
  given: {f : A ->+* B} {g : B ->+* C} (h : (g.comp f).FiniteType)
  proof: by
  algebraize [f, g, g.comp f]
  exact Algebra.FiniteType.of_restrictScalars_finiteType A B C

中文:
定理 of_comp_finiteType
  条件: {f : A ->+* B} {g : B ->+* C} (h : (g.comp f).有限型)
  证明: by
  algebraize [f, g, g.comp f]
  exact Algebra.FiniteType.of_restrictScalars_finiteType A B C

Depends on / 依赖: Algebra, Algebra.FiniteType.of_restrictScalars_finiteType, FiniteType, algebraize, g.comp, of_restrictScalars_finiteType
-/
theorem of_comp_finiteType {f : A ->+* B} {g : B ->+* C} (h : (g.comp f).FiniteType) :
    g.FiniteType := by
  algebraize [f, g, g.comp f]
  exact Algebra.FiniteType.of_restrictScalars_finiteType A B C

end FiniteType

end RingHom

namespace AlgHom

variable {R A B C : Type*} [CommRing R]
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

/--
Definition of `FiniteType` / `FiniteType` 的定义

English:
definition FiniteType
  signature: (f : A ->ₐ[R] B)
  body: f.toRingHom.FiniteType

中文:
定义 有限型
  签名: (f : A ->ₐ[R] B)
  定义体: f.toRingHom.FiniteType

Depends on / 依赖: FiniteType, f.toRingHom.FiniteType, toRingHom
-/
def FiniteType (f : A ->ₐ[R] B) : Prop :=
  f.toRingHom.FiniteType

namespace Finite

/--
theorem `finiteType` / 定理 `finiteType`

English:
theorem finiteType
  given: {f : A ->ₐ[R] B} (hf : f.Finite)
  statement: FiniteType f
  proof: RingHom.Finite.finiteType hf

中文:
定理 finiteType
  条件: {f : A ->ₐ[R] B} (hf : f.有限)
  结论: 有限型 f
  证明: RingHom.Finite.finiteType hf

Depends on / 依赖: Finite, RingHom, RingHom.Finite.finiteType, finiteType
-/
theorem finiteType {f : A ->ₐ[R] B} (hf : f.Finite) : FiniteType f :=
  RingHom.Finite.finiteType hf

end Finite

namespace FiniteType

variable (R A)

/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: FiniteType (AlgHom.id R A)
  proof: RingHom.FiniteType.id A

中文:
定理 id
  结论: 有限型 (代数态射.id R A)
  证明: RingHom.FiniteType.id A

Depends on / 依赖: FiniteType, RingHom, RingHom.FiniteType.id
-/
theorem id : FiniteType (AlgHom.id R A) :=
  RingHom.FiniteType.id A

variable {R A}

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: {g : B ->ₐ[R] C} {f : A ->ₐ[R] B} (hg : g.FiniteType) (hf : f.FiniteType)
  proof: RingHom.FiniteType.comp hg hf

中文:
定理 comp
  条件: {g : B ->ₐ[R] C} {f : A ->ₐ[R] B} (hg : g.有限型) (hf : f.有限型)
  证明: RingHom.FiniteType.comp hg hf

Depends on / 依赖: FiniteType, RingHom, RingHom.FiniteType.comp
-/
theorem comp {g : B ->ₐ[R] C} {f : A ->ₐ[R] B} (hg : g.FiniteType) (hf : f.FiniteType) :
    (g.comp f).FiniteType :=
  RingHom.FiniteType.comp hg hf

/--
theorem `comp_surjective` / 定理 `comp_surjective`

English:
theorem comp_surjective
  given: {f : A ->ₐ[R] B} {g : B ->ₐ[R] C} (hf : f.FiniteType) (hg : Surjective g)
  proof: RingHom.FiniteType.comp_surjective hf hg

中文:
定理 comp_surjective
  条件: {f : A ->ₐ[R] B} {g : B ->ₐ[R] C} (hf : f.有限型) (hg : 满射 g)
  证明: RingHom.FiniteType.comp_surjective hf hg

Depends on / 依赖: FiniteType, RingHom, RingHom.FiniteType.comp_surjective, comp_surjective
-/
theorem comp_surjective {f : A ->ₐ[R] B} {g : B ->ₐ[R] C} (hf : f.FiniteType) (hg : Surjective g) :
    (g.comp f).FiniteType :=
  RingHom.FiniteType.comp_surjective hf hg

/--
theorem `of_surjective` / 定理 `of_surjective`

English:
theorem of_surjective
  given: (f : A ->ₐ[R] B) (hf : Surjective f)
  statement: f.FiniteType
  proof: RingHom.FiniteType.of_surjective f.toRingHom hf

中文:
定理 of_surjective
  条件: (f : A ->ₐ[R] B) (hf : 满射 f)
  结论: f.有限型
  证明: RingHom.FiniteType.of_surjective f.toRingHom hf

Depends on / 依赖: FiniteType, RingHom, RingHom.FiniteType.of_surjective, f.toRingHom, of_surjective, toRingHom
-/
theorem of_surjective (f : A ->ₐ[R] B) (hf : Surjective f) : f.FiniteType :=
  RingHom.FiniteType.of_surjective f.toRingHom hf

/--
theorem `of_comp_finiteType` / 定理 `of_comp_finiteType`

English:
theorem of_comp_finiteType
  given: {f : A ->ₐ[R] B} {g : B ->ₐ[R] C} (h : (g.comp f).FiniteType)
  proof: RingHom.FiniteType.of_comp_finiteType h

中文:
定理 of_comp_finiteType
  条件: {f : A ->ₐ[R] B} {g : B ->ₐ[R] C} (h : (g.comp f).有限型)
  证明: RingHom.FiniteType.of_comp_finiteType h

Depends on / 依赖: FiniteType, RingHom, RingHom.FiniteType.of_comp_finiteType, of_comp_finiteType
-/
theorem of_comp_finiteType {f : A ->ₐ[R] B} {g : B ->ₐ[R] C} (h : (g.comp f).FiniteType) :
    g.FiniteType :=
  RingHom.FiniteType.of_comp_finiteType h

end FiniteType

end AlgHom

section MonoidAlgebra

variable {R : Type*} {M : Type*}

namespace AddMonoidAlgebra

open Algebra AddSubmonoid Submodule

section Span

section Semiring

variable [CommSemiring R] [AddMonoid M]

/--
theorem `mem_adjoin_support` / 定理 `mem_adjoin_support`

English:
theorem mem_adjoin_support
  given: (f : R[M])
  statement: f in adjoin R (of' R M '' f.coeff.support)
  proof: (adjoin R (of' R M '' f.coeff.support)).toSubmodule.span_le.2 subset_adjoin
    (mem_span_support_coeff f)

中文:
定理 mem_adjoin_support
  条件: (f : R[M])
  结论: f in adjoin R (of' R M '' f.coeff.support)
  证明: (adjoin R (of' R M '' f.coeff.support)).toSubmodule.span_le.2 subset_adjoin
    (mem_span_support_coeff f)

Depends on / 依赖: adjoin, f.coeff.support, mem_span_support_coeff, span_le, subset_adjoin, support, toSubmodule, toSubmodule.span_le
-/
theorem mem_adjoin_support (f : R[M]) : f in adjoin R (of' R M '' f.coeff.support) :=
  (adjoin R (of' R M '' f.coeff.support)).toSubmodule.span_le.2 subset_adjoin
    (mem_span_support_coeff f)

/--
theorem `support_gen_of_gen` / 定理 `support_gen_of_gen`

English:
theorem support_gen_of_gen
  given: {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤)
  proof: by
  refine le_antisymm le_top ?_
  rw [← hS]; rw [adjoin_le_iff]
  intro f hf
  have hincl : of' R M '' f.coeff.support subseteq ⋃ g in S, of' R M '' g.coeff.support :=
    fun s hs => Set.mem_iUnion₂.2 ⟨f, hf, hs⟩
  exact adjoin_mono hincl (mem_adjoin_support f)

中文:
定理 support_gen_of_gen
  条件: {S : 集合 R[M]} (hS : 代数.adjoin R S = ⊤)
  证明: by
  refine le_antisymm le_top ?_
  rw [← hS]; rw [adjoin_le_iff]
  intro f hf
  have hincl : of' R M '' f.coeff.support subseteq ⋃ g in S, of' R M '' g.coeff.support :=
    fun s hs => Set.mem_iUnion₂.2 ⟨f, hf, hs⟩
  exact adjoin_mono hincl (mem_adjoin_support f)

Depends on / 依赖: Set.mem_iUnion, adjoin_le_iff, adjoin_mono, f.coeff.support, g.coeff.support, le_antisymm, le_top, mem_adjoin_support, subseteq, support
-/
theorem support_gen_of_gen {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (⋃ f in S, of' R M '' (f.coeff.support : Set M)) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hS]; rw [adjoin_le_iff]
  intro f hf
  have hincl : of' R M '' f.coeff.support subseteq ⋃ g in S, of' R M '' g.coeff.support :=
    fun s hs => Set.mem_iUnion₂.2 ⟨f, hf, hs⟩
  exact adjoin_mono hincl (mem_adjoin_support f)

/--
theorem `support_gen_of_gen'` / 定理 `support_gen_of_gen'`

English:
theorem support_gen_of_gen'
  given: {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤)
  proof: by
  suffices of' R M '' ⋃ f in S, (f.coeff.support : Set M) = ⋃ f in S, of' R M '' f.coeff.support by
    rw [this]
    exact support_gen_of_gen hS
  simp only [Set.image_iUnion]

中文:
定理 support_gen_of_gen'
  条件: {S : 集合 R[M]} (hS : 代数.adjoin R S = ⊤)
  证明: by
  suffices of' R M '' ⋃ f in S, (f.coeff.support : Set M) = ⋃ f in S, of' R M '' f.coeff.support by
    rw [this]
    exact support_gen_of_gen hS
  simp only [Set.image_iUnion]

Depends on / 依赖: FriendlyOperation, Seq.FriendlyOperation.coind_comp_friend_left, Set.image_iUnion, coind_comp_friend_left, destruct_eq_destruct_map, f.coeff.support, h_base, h_op, h_step, image_iUnion, motive, support, support_gen_of_gen
-/
theorem support_gen_of_gen' {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (of' R M '' ⋃ f in S, (f.coeff.support : Set M)) = ⊤ := by
  suffices of' R M '' ⋃ f in S, (f.coeff.support : Set M) = ⋃ f in S, of' R M '' f.coeff.support by
    rw [this]
    exact support_gen_of_gen hS
  simp only [Set.image_iUnion]

end Semiring

section Ring

variable [CommRing R] [AddMonoid M]

/--
theorem `exists_finset_adjoin_eq_top` / 定理 `exists_finset_adjoin_eq_top`

English:
theorem exists_finset_adjoin_eq_top
  given: [h : FiniteType R R[M]]
  proof: by
  obtain ⟨S, hS⟩ := h
  let : DecidableEq M := Classical.decEq M
  use Finset.biUnion S fun f => f.coeff.support
  have : S.biUnion (fun f => f.coeff.support) = ⋃ f in S, (f.coeff.support : Set M) := by
    simp only [Finset.set_biUnion_coe, Finset.coe_biUnion]
  rw [this]
  exact support_gen_of_gen' hS

中文:
定理 存在_finset_adjoin_eq_top
  条件: [h : 有限型 R R[M]]
  证明: by
  obtain ⟨S, hS⟩ := h
  let : DecidableEq M := Classical.decEq M
  use Finset.biUnion S fun f => f.coeff.support
  have : S.biUnion (fun f => f.coeff.support) = ⋃ f in S, (f.coeff.support : Set M) := by
    simp only [Finset.set_biUnion_coe, Finset.coe_biUnion]
  rw [this]
  exact support_gen_of_gen' hS

Depends on / 依赖: Classical, Classical.decEq, DecidableEq, Finset, Finset.biUnion, Finset.coe_biUnion, Finset.set_biUnion_coe, FriendlyOperation, S.biUnion, Seq.FriendlyOperation.coind_comp_friend_right, biUnion, coe_biUnion, coind_comp_friend_right, destruct_eq_destruct_map, f.coeff.support, h_base, h_op, h_step, motive, set_biUnion_coe
-/
theorem exists_finset_adjoin_eq_top [h : FiniteType R R[M]] :
    exists G : Finset M, Algebra.adjoin R (of' R M '' G) = ⊤ := by
  obtain ⟨S, hS⟩ := h
  let : DecidableEq M := Classical.decEq M
  use Finset.biUnion S fun f => f.coeff.support
  have : S.biUnion (fun f => f.coeff.support) = ⋃ f in S, (f.coeff.support : Set M) := by
    simp only [Finset.set_biUnion_coe, Finset.coe_biUnion]
  rw [this]
  exact support_gen_of_gen' hS

end Ring

end Span

/--
theorem `mvPolynomial_aeval_of_surjective_of_closure` / 定理 `mvPolynomial_aeval_of_surjective_of_closure`

English:
theorem mvPolynomial_aeval_of_surjective_of_closure
  statement: [AddCommMonoid M] [CommSemiring R] {S : Set M}
  proof: by
  intro f
  induction f using induction_on with
  | of m =>
    have : m in closure S := hS.symm ▸ mem_top _
    refine AddSubmonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨MvPolynomial.X ⟨m, hm⟩, MvPolynomial.aeval_X _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul]; rw [hP₁]; rw [hP₂]; rw [of_apply]; rw [of_apply]; rw [of_apply]; rw [single_mul_single]; rw [one_mul]; rfl⟩
  | add f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩
    rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | smul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩

中文:
定理 mvPolynomial_aeval_of_surjective_of_closure
  结论: [加法交换幺半群 M] [交换半环 R] {S : 集合 M}
  证明: by
  intro f
  induction f using induction_on with
  | of m =>
    have : m in closure S := hS.symm ▸ mem_top _
    refine AddSubmonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨MvPolynomial.X ⟨m, hm⟩, MvPolynomial.aeval_X _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul]; rw [hP₁]; rw [hP₂]; rw [of_apply]; rw [of_apply]; rw [of_apply]; rw [single_mul_single]; rw [one_mul]; rfl⟩
  | add f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩
    rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | smul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩

Depends on / 依赖: AddSubmonoid, AddSubmonoid.closure_induction, MvPolynomial, MvPolynomial.X, MvPolynomial.aeval_X, aeval_X, closure, closure_induction, hS.symm, induction_on, map_mul, map_one, mem_top, of_apply, one_mul, single_mul_single
-/
theorem mvPolynomial_aeval_of_surjective_of_closure [AddCommMonoid M] [CommSemiring R] {S : Set M}
    (hS : closure S = ⊤) :
    Function.Surjective
      (MvPolynomial.aeval fun s : S => of' R M ↑s : MvPolynomial S R -> R[M]) := by
  intro f
  induction f using induction_on with
  | of m =>
    have : m in closure S := hS.symm ▸ mem_top _
    refine AddSubmonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨MvPolynomial.X ⟨m, hm⟩, MvPolynomial.aeval_X _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul]; rw [hP₁]; rw [hP₂]; rw [of_apply]; rw [of_apply]; rw [of_apply]; rw [single_mul_single]; rw [one_mul]; rfl⟩
  | add f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩
    rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | smul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩

variable [AddMonoid M]

/--
theorem `freeAlgebra_lift_of_surjective_of_closure` / 定理 `freeAlgebra_lift_of_surjective_of_closure`

English:
theorem freeAlgebra_lift_of_surjective_of_closure
  statement: [CommSemiring R] {S : Set M}
  proof: by
  intro f
  induction f using induction_on with
  | of m =>
    have : m in closure S := hS.symm ▸ mem_top _
    refine AddSubmonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨FreeAlgebra.ι R ⟨m, hm⟩, FreeAlgebra.lift_ι_apply _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul]; rw [hP₁]; rw [hP₂]; rw [of_apply]; rw [of_apply]; rw [of_apply]; rw [single_mul_single]; rw [one_mul]; rfl⟩
  | add f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩
    rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | smul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩

中文:
定理 freeAlgebra_lift_of_surjective_of_closure
  结论: [交换半环 R] {S : 集合 M}
  证明: by
  intro f
  induction f using induction_on with
  | of m =>
    have : m in closure S := hS.symm ▸ mem_top _
    refine AddSubmonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨FreeAlgebra.ι R ⟨m, hm⟩, FreeAlgebra.lift_ι_apply _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul]; rw [hP₁]; rw [hP₂]; rw [of_apply]; rw [of_apply]; rw [of_apply]; rw [single_mul_single]; rw [one_mul]; rfl⟩
  | add f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩
    rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | smul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩

Depends on / 依赖: AddSubmonoid, AddSubmonoid.closure_induction, FreeAlgebra, FreeAlgebra.lift_, MultiseriesExpansion, basis_tl, closure, closure_induction, hS.symm, induction_on, map_mul, map_one, mem_top, of_apply, one_mul, single_mul_single
-/
theorem freeAlgebra_lift_of_surjective_of_closure [CommSemiring R] {S : Set M}
    (hS : closure S = ⊤) :
    Function.Surjective
      (FreeAlgebra.lift R fun s : S => of' R M ↑s : FreeAlgebra R S -> R[M]) := by
  intro f
  induction f using induction_on with
  | of m =>
    have : m in closure S := hS.symm ▸ mem_top _
    refine AddSubmonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨FreeAlgebra.ι R ⟨m, hm⟩, FreeAlgebra.lift_ι_apply _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul]; rw [hP₁]; rw [hP₂]; rw [of_apply]; rw [of_apply]; rw [of_apply]; rw [single_mul_single]; rw [one_mul]; rfl⟩
  | add f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩
    rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | smul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩

variable (R M)

/--
Instance `finiteType_of_fg` / 实例 `finiteType_of_fg`

English:
instance finiteType_of_fg
  signature: [CommRing R] [h : AddMonoid.FG M]
  body: by
  obtain ⟨S, hS⟩ := h.fg_top
  exact .of_surjective
      (FreeAlgebra.lift R fun s : (S : Set M) => of' R M ↑s)
      (freeAlgebra_lift_of_surjective_of_closure hS)

中文:
实例 finiteType_of_fg
  签名: [交换环 R] [h : 加法幺半群.FG M]
  定义体: by
  obtain ⟨S, hS⟩ := h.fg_top
  exact .of_surjective
      (FreeAlgebra.lift R fun s : (S : Set M) => of' R M ↑s)
      (freeAlgebra_lift_of_surjective_of_closure hS)

Depends on / 依赖: FreeAlgebra, FreeAlgebra.lift, fg_top, freeAlgebra_lift_of_surjective_of_closure, h.fg_top, ms.toSeq, of_surjective
-/
instance finiteType_of_fg [CommRing R] [h : AddMonoid.FG M] :
    FiniteType R R[M] := by
  obtain ⟨S, hS⟩ := h.fg_top
  exact .of_surjective
      (FreeAlgebra.lift R fun s : (S : Set M) => of' R M ↑s)
      (freeAlgebra_lift_of_surjective_of_closure hS)

variable {R M}

/--
theorem `finiteType_iff_fg` / 定理 `finiteType_iff_fg`

English:
theorem finiteType_iff_fg
  given: [CommRing R] [Nontrivial R]
  proof: by
  refine ⟨fun h => ?_, fun h => @AddMonoidAlgebra.finiteType_of_fg _ _ _ _ h⟩
  obtain ⟨S, hS⟩ := @exists_finset_adjoin_eq_top R M _ _ h
  refine AddMonoid.fg_def.2 ⟨S, (eq_top_iff' _).2 fun m => ?_⟩
  have hm : of' R M m in Subalgebra.toSubmodule (adjoin R (of' R M '' ↑S)) := by
    simp only [hS, top_toSubmodule, Submodule.mem_top]
  rw [adjoin_eq_span] at hm
  exact mem_closure_of_mem_span_closure hm

中文:
定理 finiteType_iff_fg
  条件: [交换环 R] [非平凡 R]
  证明: by
  refine ⟨fun h => ?_, fun h => @AddMonoidAlgebra.finiteType_of_fg _ _ _ _ h⟩
  obtain ⟨S, hS⟩ := @exists_finset_adjoin_eq_top R M _ _ h
  refine AddMonoid.fg_def.2 ⟨S, (eq_top_iff' _).2 fun m => ?_⟩
  have hm : of' R M m in Subalgebra.toSubmodule (adjoin R (of' R M '' ↑S)) := by
    simp only [hS, top_toSubmodule, Submodule.mem_top]
  rw [adjoin_eq_span] at hm
  exact mem_closure_of_mem_span_closure hm

Depends on / 依赖: AddMonoid, AddMonoid.fg_def, AddMonoidAlgebra, AddMonoidAlgebra.finiteType_of_fg, Subalgebra, Subalgebra.toSubmodule, Submodule, Submodule.mem_top, adjoin, adjoin_eq_span, eq_top_iff, exists_finset_adjoin_eq_top, fg_def, finiteType_of_fg, mem_closure_of_mem_span_closure, mem_top, toSubmodule, top_toSubmodule
-/
theorem finiteType_iff_fg [CommRing R] [Nontrivial R] :
    FiniteType R R[M] ↔ AddMonoid.FG M := by
  refine ⟨fun h => ?_, fun h => @AddMonoidAlgebra.finiteType_of_fg _ _ _ _ h⟩
  obtain ⟨S, hS⟩ := @exists_finset_adjoin_eq_top R M _ _ h
  refine AddMonoid.fg_def.2 ⟨S, (eq_top_iff' _).2 fun m => ?_⟩
  have hm : of' R M m in Subalgebra.toSubmodule (adjoin R (of' R M '' ↑S)) := by
    simp only [hS, top_toSubmodule, Submodule.mem_top]
  rw [adjoin_eq_span] at hm
  exact mem_closure_of_mem_span_closure hm

/--
theorem `fg_of_finiteType` / 定理 `fg_of_finiteType`

English:
theorem fg_of_finiteType
  given: [CommRing R] [Nontrivial R] [h : FiniteType R R[M]]
  proof: finiteType_iff_fg.1 h

中文:
定理 fg_of_finiteType
  条件: [交换环 R] [非平凡 R] [h : 有限型 R R[M]]
  证明: finiteType_iff_fg.1 h

Depends on / 依赖: finiteType_iff_fg
-/
theorem fg_of_finiteType [CommRing R] [Nontrivial R] [h : FiniteType R R[M]] :
    AddMonoid.FG M :=
  finiteType_iff_fg.1 h

/--
theorem `finiteType_iff_group_fg` / 定理 `finiteType_iff_group_fg`

English:
theorem finiteType_iff_group_fg
  given: {G : Type*} [AddGroup G] [CommRing R] [Nontrivial R]
  proof: by
  simpa [AddGroup.fg_iff_addMonoid_fg] using finiteType_iff_fg

中文:
定理 finiteType_iff_group_fg
  条件: {G : 类型} [加法群 G] [交换环 R] [非平凡 R]
  证明: by
  simpa [AddGroup.fg_iff_addMonoid_fg] using finiteType_iff_fg

Depends on / 依赖: AddGroup, AddGroup.fg_iff_addMonoid_fg, fg_iff_addMonoid_fg, finiteType_iff_fg
-/
theorem finiteType_iff_group_fg {G : Type*} [AddGroup G] [CommRing R] [Nontrivial R] :
    FiniteType R R[G] ↔ AddGroup.FG G := by
  simpa [AddGroup.fg_iff_addMonoid_fg] using finiteType_iff_fg

end AddMonoidAlgebra

namespace MonoidAlgebra

open Algebra Submonoid Submodule

section Span

section Semiring

variable [CommSemiring R] [Monoid M]

/--
theorem `mem_adjoin_support` / 定理 `mem_adjoin_support`

English:
theorem mem_adjoin_support
  given: (f : R[M])
  statement: f in adjoin R (of R M '' f.coeff.support)
  proof: (adjoin R (of R M '' f.coeff.support)).toSubmodule.span_le.2 subset_adjoin
    (mem_span_support_coeff f)

中文:
定理 mem_adjoin_support
  条件: (f : R[M])
  结论: f in adjoin R (of R M '' f.coeff.support)
  证明: (adjoin R (of R M '' f.coeff.support)).toSubmodule.span_le.2 subset_adjoin
    (mem_span_support_coeff f)

Depends on / 依赖: FriendlyOperation, Seq.FriendlyOperation.unfold, adjoin, f.coeff.support, mem_span_support_coeff, span_le, subset_adjoin, support, toSubmodule, toSubmodule.span_le
-/
theorem mem_adjoin_support (f : R[M]) : f in adjoin R (of R M '' f.coeff.support) :=
  (adjoin R (of R M '' f.coeff.support)).toSubmodule.span_le.2 subset_adjoin
    (mem_span_support_coeff f)

/--
theorem `support_gen_of_gen` / 定理 `support_gen_of_gen`

English:
theorem support_gen_of_gen
  given: {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤)
  proof: by
  refine le_antisymm le_top ?_
  rw [← hS]; rw [adjoin_le_iff]
  intro f hf
  have hincl : of R M '' f.coeff.support subseteq ⋃ g in S, of R M '' g.coeff.support :=
    fun s hs => Set.mem_iUnion₂.2 ⟨f, hf, hs⟩
  exact adjoin_mono hincl (mem_adjoin_support f)

中文:
定理 support_gen_of_gen
  条件: {S : 集合 R[M]} (hS : 代数.adjoin R S = ⊤)
  证明: by
  refine le_antisymm le_top ?_
  rw [← hS]; rw [adjoin_le_iff]
  intro f hf
  have hincl : of R M '' f.coeff.support subseteq ⋃ g in S, of R M '' g.coeff.support :=
    fun s hs => Set.mem_iUnion₂.2 ⟨f, hf, hs⟩
  exact adjoin_mono hincl (mem_adjoin_support f)

Depends on / 依赖: FriendlyOperation, FriendlyOperation.unfold, Multiseries, Multiseries.destruct, Seq.FriendlyOperation.destruct_apply_eq_unfold, Seq.FriendlyOperation.unfold, Seq.head, Set.mem_iUnion, adjoin_le_iff, adjoin_mono, destruct, destruct_apply_eq_unfold, f.coeff.support, g.coeff.support, le_antisymm, le_top, mem_adjoin_support, subseteq, support
-/
theorem support_gen_of_gen {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (⋃ f in S, of R M '' (f.coeff.support : Set M)) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hS]; rw [adjoin_le_iff]
  intro f hf
  have hincl : of R M '' f.coeff.support subseteq ⋃ g in S, of R M '' g.coeff.support :=
    fun s hs => Set.mem_iUnion₂.2 ⟨f, hf, hs⟩
  exact adjoin_mono hincl (mem_adjoin_support f)

/--
theorem `support_gen_of_gen'` / 定理 `support_gen_of_gen'`

English:
theorem support_gen_of_gen'
  given: {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤)
  proof: by
  suffices of R M '' ⋃ f in S, f.coeff.support = ⋃ f in S, of R M '' f.coeff.support by
    rw [this]
    exact support_gen_of_gen hS
  simp only [Set.image_iUnion]

中文:
定理 support_gen_of_gen'
  条件: {S : 集合 R[M]} (hS : 代数.adjoin R S = ⊤)
  证明: by
  suffices of R M '' ⋃ f in S, f.coeff.support = ⋃ f in S, of R M '' f.coeff.support by
    rw [this]
    exact support_gen_of_gen hS
  simp only [Set.image_iUnion]

Depends on / 依赖: Set.image_iUnion, f.coeff.support, image_iUnion, support, support_gen_of_gen
-/
theorem support_gen_of_gen' {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (of R M '' ⋃ f in S, (f.coeff.support : Set M)) = ⊤ := by
  suffices of R M '' ⋃ f in S, f.coeff.support = ⋃ f in S, of R M '' f.coeff.support by
    rw [this]
    exact support_gen_of_gen hS
  simp only [Set.image_iUnion]

end Semiring

section Ring

variable [CommRing R] [Monoid M]

/--
theorem `exists_finset_adjoin_eq_top` / 定理 `exists_finset_adjoin_eq_top`

English:
theorem exists_finset_adjoin_eq_top
  given: [h : FiniteType R R[M]]
  proof: by
  obtain ⟨S, hS⟩ := h
  let : DecidableEq M := Classical.decEq M
  use Finset.biUnion S fun f => f.coeff.support
  have : S.biUnion (fun f => f.coeff.support) = ⋃ f in S, (f.coeff.support : Set M) := by
    simp only [Finset.set_biUnion_coe, Finset.coe_biUnion]
  rw [this]
  exact support_gen_of_gen' hS

中文:
定理 存在_finset_adjoin_eq_top
  条件: [h : 有限型 R R[M]]
  证明: by
  obtain ⟨S, hS⟩ := h
  let : DecidableEq M := Classical.decEq M
  use Finset.biUnion S fun f => f.coeff.support
  have : S.biUnion (fun f => f.coeff.support) = ⋃ f in S, (f.coeff.support : Set M) := by
    simp only [Finset.set_biUnion_coe, Finset.coe_biUnion]
  rw [this]
  exact support_gen_of_gen' hS

Depends on / 依赖: Classical, Classical.decEq, DecidableEq, Finset, Finset.biUnion, Finset.coe_biUnion, Finset.set_biUnion_coe, FriendlyOperation, S.biUnion, Seq.FriendlyOperation.id, biUnion, coe_biUnion, f.coeff.support, set_biUnion_coe, support, support_gen_of_gen
-/
theorem exists_finset_adjoin_eq_top [h : FiniteType R R[M]] :
    exists G : Finset M, Algebra.adjoin R (of R M '' G) = ⊤ := by
  obtain ⟨S, hS⟩ := h
  let : DecidableEq M := Classical.decEq M
  use Finset.biUnion S fun f => f.coeff.support
  have : S.biUnion (fun f => f.coeff.support) = ⋃ f in S, (f.coeff.support : Set M) := by
    simp only [Finset.set_biUnion_coe, Finset.coe_biUnion]
  rw [this]
  exact support_gen_of_gen' hS

end Ring

end Span

/--
theorem `mvPolynomial_aeval_of_surjective_of_closure` / 定理 `mvPolynomial_aeval_of_surjective_of_closure`

English:
theorem mvPolynomial_aeval_of_surjective_of_closure
  statement: [CommMonoid M] [CommSemiring R] {S : Set M}
  proof: by
  intro f
  induction f using induction_on with
  | of m =>
    have : m in closure S := hS.symm ▸ mem_top _
    refine Submonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨MvPolynomial.X ⟨m, hm⟩, MvPolynomial.aeval_X _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul]; rw [hP₁]; rw [hP₂]; rw [of_apply]; rw [of_apply]; rw [of_apply]; rw [single_mul_single]; rw [one_mul]⟩
  | add f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩; rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | smul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩

中文:
定理 mvPolynomial_aeval_of_surjective_of_closure
  结论: [交换幺半群 M] [交换半环 R] {S : 集合 M}
  证明: by
  intro f
  induction f using induction_on with
  | of m =>
    have : m in closure S := hS.symm ▸ mem_top _
    refine Submonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨MvPolynomial.X ⟨m, hm⟩, MvPolynomial.aeval_X _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul]; rw [hP₁]; rw [hP₂]; rw [of_apply]; rw [of_apply]; rw [of_apply]; rw [single_mul_single]; rw [one_mul]⟩
  | add f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩; rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | smul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩

Depends on / 依赖: FriendlyOperation, MvPolynomial, MvPolynomial.X, MvPolynomial.aeval_X, Seq.FriendlyOperation.comp, Submonoid, Submonoid.closure_induction, aeval_X, closure, closure_induction, hS.symm, induction_on, map_mul, map_one, mem_top, of_apply, one_mul, single_mul_single
-/
theorem mvPolynomial_aeval_of_surjective_of_closure [CommMonoid M] [CommSemiring R] {S : Set M}
    (hS : closure S = ⊤) :
    Function.Surjective
      (MvPolynomial.aeval fun s : S => of R M ↑s : MvPolynomial S R -> R[M]) := by
  intro f
  induction f using induction_on with
  | of m =>
    have : m in closure S := hS.symm ▸ mem_top _
    refine Submonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨MvPolynomial.X ⟨m, hm⟩, MvPolynomial.aeval_X _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul]; rw [hP₁]; rw [hP₂]; rw [of_apply]; rw [of_apply]; rw [of_apply]; rw [single_mul_single]; rw [one_mul]⟩
  | add f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩; rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | smul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩


variable [Monoid M]

/--
theorem `freeAlgebra_lift_of_surjective_of_closure` / 定理 `freeAlgebra_lift_of_surjective_of_closure`

English:
theorem freeAlgebra_lift_of_surjective_of_closure
  statement: [CommSemiring R] {S : Set M}
  proof: by
  intro f
  induction f using induction_on with
  | of m =>
    have : m in closure S := hS.symm ▸ mem_top _
    refine Submonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨FreeAlgebra.ι R ⟨m, hm⟩, FreeAlgebra.lift_ι_apply _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul]; rw [hP₁]; rw [hP₂]; rw [of_apply]; rw [of_apply]; rw [of_apply]; rw [single_mul_single]; rw [one_mul]⟩
  | add f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩
    rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | smul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩

中文:
定理 freeAlgebra_lift_of_surjective_of_closure
  结论: [交换半环 R] {S : 集合 M}
  证明: by
  intro f
  induction f using induction_on with
  | of m =>
    have : m in closure S := hS.symm ▸ mem_top _
    refine Submonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨FreeAlgebra.ι R ⟨m, hm⟩, FreeAlgebra.lift_ι_apply _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul]; rw [hP₁]; rw [hP₂]; rw [of_apply]; rw [of_apply]; rw [of_apply]; rw [single_mul_single]; rw [one_mul]⟩
  | add f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩
    rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | smul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩

Depends on / 依赖: FreeAlgebra, FreeAlgebra.lift_, FriendlyOperation, Seq.FriendlyOperation.const, Submonoid, Submonoid.closure_induction, closure, closure_induction, hS.symm, induction_on, map_mul, map_one, mem_top, of_apply, one_mul, single_mul_single
-/
theorem freeAlgebra_lift_of_surjective_of_closure [CommSemiring R] {S : Set M}
    (hS : closure S = ⊤) :
    Function.Surjective
      (FreeAlgebra.lift R fun s : S => of R M ↑s : FreeAlgebra R S -> R[M]) := by
  intro f
  induction f using induction_on with
  | of m =>
    have : m in closure S := hS.symm ▸ mem_top _
    refine Submonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨FreeAlgebra.ι R ⟨m, hm⟩, FreeAlgebra.lift_ι_apply _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul]; rw [hP₁]; rw [hP₂]; rw [of_apply]; rw [of_apply]; rw [of_apply]; rw [single_mul_single]; rw [one_mul]⟩
  | add f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩
    rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | smul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩

/--
Instance `finiteType_of_fg` / 实例 `finiteType_of_fg`

English:
instance finiteType_of_fg
  signature: [CommRing R] [Monoid.FG M]
  body: (AddMonoidAlgebra.finiteType_of_fg R (Additive M)).equiv (toAdditiveAlgEquiv R R M).symm

中文:
实例 finiteType_of_fg
  签名: [交换环 R] [幺半群.FG M]
  定义体: (AddMonoidAlgebra.finiteType_of_fg R (Additive M)).equiv (toAdditiveAlgEquiv R R M).symm

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.finiteType_of_fg, Additive, FriendlyOperation, Seq.FriendlyOperation.ite, finiteType_of_fg, toAdditiveAlgEquiv
-/
instance finiteType_of_fg [CommRing R] [Monoid.FG M] : FiniteType R R[M] :=
  (AddMonoidAlgebra.finiteType_of_fg R (Additive M)).equiv (toAdditiveAlgEquiv R R M).symm

/--
theorem `finiteType_iff_fg` / 定理 `finiteType_iff_fg`

English:
theorem finiteType_iff_fg
  given: [CommRing R] [Nontrivial R]
  statement: FiniteType R R[M] ↔ Monoid.FG M where
  proof: Monoid.fg_iff_add_fg.2
AddMonoidAlgebra.finiteType_iff_fg.1 h.equiv toAdditiveAlgEquiv R R M
  mpr _ := inferInstance

中文:
定理 finiteType_iff_fg
  条件: [交换环 R] [非平凡 R]
  结论: 有限型 R R[M] ↔ 幺半群.FG M where
  证明: Monoid.fg_iff_add_fg.2
AddMonoidAlgebra.finiteType_iff_fg.1 h.equiv toAdditiveAlgEquiv R R M
  mpr _ := inferInstance

Depends on / 依赖: Monoid, Monoid.fg_iff_add_fg, basis_hd, fg_iff_add_fg
-/
theorem finiteType_iff_fg [CommRing R] [Nontrivial R] : FiniteType R R[M] ↔ Monoid.FG M where
mp h := Monoid.fg_iff_add_fg.2
AddMonoidAlgebra.finiteType_iff_fg.1 h.equiv toAdditiveAlgEquiv R R M
  mpr _ := inferInstance

/--
theorem `fg_of_finiteType` / 定理 `fg_of_finiteType`

English:
theorem fg_of_finiteType
  given: [CommRing R] [Nontrivial R] [h : FiniteType R R[M]]
  proof: finiteType_iff_fg.1 h

中文:
定理 fg_of_finiteType
  条件: [交换环 R] [非平凡 R] [h : 有限型 R R[M]]
  证明: finiteType_iff_fg.1 h

Depends on / 依赖: FriendlyOperation, Seq.FriendlyOperation.cons_tail, cons_tail, finiteType_iff_fg
-/
theorem fg_of_finiteType [CommRing R] [Nontrivial R] [h : FiniteType R R[M]] :
    Monoid.FG M :=
  finiteType_iff_fg.1 h

/--
theorem `finiteType_iff_group_fg` / 定理 `finiteType_iff_group_fg`

English:
theorem finiteType_iff_group_fg
  given: {G : Type*} [Group G] [CommRing R] [Nontrivial R]
  proof: by
  simpa [Group.fg_iff_monoid_fg] using finiteType_iff_fg

中文:
定理 finiteType_iff_group_fg
  条件: {G : 类型} [群 G] [交换环 R] [非平凡 R]
  证明: by
  simpa [Group.fg_iff_monoid_fg] using finiteType_iff_fg

Depends on / 依赖: FriendlyOperationClass, Group.fg_iff_monoid_fg, Seq.FriendlyOperationClass, Seq.FriendlyOperationClass.comp, fg_iff_monoid_fg, finiteType_iff_fg
-/
theorem finiteType_iff_group_fg {G : Type*} [Group G] [CommRing R] [Nontrivial R] :
    FiniteType R R[G] ↔ Group.FG G := by
  simpa [Group.fg_iff_monoid_fg] using finiteType_iff_fg

end MonoidAlgebra

end MonoidAlgebra

section Orzech

open Submodule Module Module.Finite in
/--
Any commutative ring `R` satisfies the `OrzechProperty`, that is, for any finitely generated
`R`-module `M`, any surjective homomorphism `f : N →ₗ[R] M` from a submodule `N` of `M` to `M`
is injective.

This is a consequence of Noetherian case
(`IsNoetherian.injective_of_surjective_of_injective`), which requires that `M` is a
Noetherian module, but allows `R` to be non-commutative. The reduction of this result to
Noetherian case is adapted from <https://math.stackexchange.com/a/1066110>:
suppose `{ m_j }` is a finite set of generators of `M`, for any `n : N` one can write
`i n = ∑ j, b_j * m_j` for `{ b_j }` in `R`, here `i : N →ₗ[R] M` is the standard inclusion.
We can choose `{ n_j }` which are preimages of `{ m_j }` under `f`, and can choose
`{ c_jl }` in `R` such that `i n_j = ∑ l, c_jl * m_l` for each `j`.
Now let `A` be the subring of `R` generated by `{ b_j }` and `{ c_jl }`, then it is
Noetherian. Let `N'` be the `A`-submodule of `N` generated by `n` and `{ n_j }`,
`M'` be the `A`-submodule of `M` generated by `{ m_j }`,
then it's easy to see that `i` and `f` restrict to `N' →ₗ[A] M'`,
and the restricted version of `f` is surjective, hence by Noetherian case,
it is also injective, in particular, if `f n = 0`, then `n = 0`.

See also Orzech's original paper: *Onto endomorphisms are isomorphisms* [orzech1971].

This implies that nontrivial commutative rings satisfy the strong rank condition:
see `strongRankCondition_of_orzechProperty` in `Mathlib.LinearAlgebra.InvariantBasisNumber`.
A shortcut instance `commRing_strongRankCondition` is also provided.
-/
instance (priority := 100) CommRing.orzechProperty
    (R : Type*) [CommRing R] : OrzechProperty R := by
  refine ⟨fun {M} _ _ _ {N} f hf => ?_⟩
  let := addCommMonoidToAddCommGroup R (M := M)
  let := addCommMonoidToAddCommGroup R (M := N)
  let i := N.subtype
  let hi : Function.Injective i := N.injective_subtype
refine LinearMap.ker_eq_bot.1 LinearMap.ker_eq_bot'.2 fun n hn => ?_
  obtain ⟨k, mj, hmj⟩ := exists_fin (R := R) (M := M)
  rw [← surjective_piEquiv_apply_iff] at hmj
  obtain ⟨b, hb⟩ := hmj (i n)
  choose nj hnj using fun j => hf (mj j)
  choose c hc using fun j => hmj (i (nj j))
  let A := Subring.closure (Set.range b union Set.range c.uncurry)
  let N' := span A ({n} union Set.range nj)
  let M' := span A (Set.range mj)
  have : IsNoetherianRing A := is_noetherian_subring_closure _
    (.union (Set.finite_range _) (Set.finite_range _))
  have : Module.Finite A M' := span_of_finite A (Set.finite_range _)
  refine congr($((LinearMap.ker_eq_bot'.1 <| LinearMap.ker_eq_bot.2 <|
    IsNoetherian.injective_of_surjective_of_injective
      ((i.restrictScalars A).restrict fun x hx => ?_ : N' ->ₗ[A] M')
      ((f.restrictScalars A).restrict fun x hx => ?_ : N' ->ₗ[A] M')
      (fun _ _ h => injective_subtype _ (hi congr(($h).1)))
      fun ⟨x, hx⟩ => ?_) ⟨n, (subset_span (by simp))⟩ (Subtype.val_injective hn)).1)
  · induction hx using span_induction with
    | mem x hx =>
      change i x in M'
      simp only [Set.singleton_union, Set.mem_insert_iff, Set.mem_range] at hx
      rcases hx with hx | ⟨j, rfl⟩
      · rw [hx, ← hb, piEquiv_apply_apply]
        refine Submodule.sum_mem _ fun j _ => ?_
        let b' : A := ⟨b j, Subring.subset_closure (by simp)⟩
        rw [show b j • mj j = b' • mj j from rfl]
        exact smul_mem _ _ (subset_span (by simp))
      · rw [← hc, piEquiv_apply_apply]
        refine Submodule.sum_mem _ fun j' _ => ?_
        let c' : A := ⟨c j j', Subring.subset_closure
          (by simp [show exists a b, c a b = c j j' from ⟨j, j', rfl⟩])⟩
        rw [show c j j' • mj j' = c' • mj j' from rfl]
        exact smul_mem _ _ (subset_span (by simp))
    | zero => simp
    | add x _ y _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact smul_mem _ _ hx
  · induction hx using span_induction with
    | mem x hx =>
      change f x in M'
      simp only [Set.singleton_union, Set.mem_insert_iff, Set.mem_range] at hx
      rcases hx with hx | ⟨j, rfl⟩
      · rw [hx, hn]; exact zero_mem _
      · exact subset_span (by simp [hnj])
    | zero => simp
    | add x _ y _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact smul_mem _ _ hx
  suffices x in LinearMap.range ((f.restrictScalars A).domRestrict N') by
    obtain ⟨a, ha⟩ := this
    exact ⟨a, Subtype.val_injective ha⟩
  induction hx using span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨⟨nj j, subset_span (by simp)⟩, hnj j⟩
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => exact smul_mem _ a hx

end Orzech
