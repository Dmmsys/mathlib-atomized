/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Data.Finite.Sum
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Tower

/-!
# Finiteness conditions in commutative algebra

In this file we define several notions of finiteness that are common in commutative algebra.

## Main declarations

- `Module.Finite`, `RingHom.Finite`, `AlgHom.Finite`
  all of these express that some object is finitely generated *as module* over some base ring.
- `Algebra.FiniteType`, `RingHom.FiniteType`, `AlgHom.FiniteType`
  all of these express that some object is finitely generated *as algebra* over some base ring.
- `Algebra.FinitePresentation`, `RingHom.FinitePresentation`, `AlgHom.FinitePresentation`
  all of these express that some object is finitely presented *as algebra* over some base ring.

-/

@[expose] public section

open Function (Surjective)

open Polynomial

section ModuleAndAlgebra

universe w₁ w₂ w₃

variable (R : Type w₁) (A : Type w₂) (B : Type w₃)

/--
Definition of `Algebra.FinitePresentation` / `Algebra.FinitePresentation` 的定义

English:
class Algebra.FinitePresentation
  parameters: [CommSemiring R] [Semiring A] [Algebra R A]
  axioms and operations (1):
    - out : exists (n : Nat) (f : MvPolynomial (Fin n) R ->ₐ[R] A), Surjective f ∧ (RingHom.ker f.toRingHom).FG

中文:
类 Algebra.FinitePresentation
  参数: [CommSemiring R] [Semiring A] [Algebra R A]
  公理与运算 (1 个):
    - out : 存在 (n : 自然数) (f : MvPolynomial (Fin n) R ->ₐ[R] A), Surjective f ∧ (RingHom.ker f.toRingHom).FG
-/
class Algebra.FinitePresentation [CommSemiring R] [Semiring A] [Algebra R A] : Prop where
  out : exists (n : Nat) (f : MvPolynomial (Fin n) R ->ₐ[R] A), Surjective f ∧ (RingHom.ker f.toRingHom).FG

namespace Algebra

variable [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

namespace FiniteType

variable {R A B}

/--
Instance `of_finitePresentation` / 实例 `of_finitePresentation`

English:
instance of_finitePresentation
  signature: [FinitePresentation R A]
  body: by
  obtain ⟨n, f, hf⟩ := FinitePresentation.out (R := R) (A := A)
  apply FiniteType.iff_quotient_mvPolynomial''.2
  exact ⟨n, f, hf.1⟩

中文:
实例 of_finitePresentation
  签名: [FinitePresentation R A]
  定义体: by
  obtain ⟨n, f, hf⟩ := FinitePresentation.out (R := R) (A := A)
  apply FiniteType.iff_quotient_mvPolynomial''.2
  exact ⟨n, f, hf.1⟩

Depends on / 依赖: FinitePresentation, FinitePresentation.out, FiniteType, FiniteType.iff_quotient_mvPolynomial, iff_quotient_mvPolynomial
-/
instance of_finitePresentation [FinitePresentation R A] : FiniteType R A := by
  obtain ⟨n, f, hf⟩ := FinitePresentation.out (R := R) (A := A)
  apply FiniteType.iff_quotient_mvPolynomial''.2
  exact ⟨n, f, hf.1⟩

end FiniteType

namespace FinitePresentation

variable {R A B}

/--
theorem `of_finiteType` / 定理 `of_finiteType`

English:
theorem of_finiteType
  given: [IsNoetherianRing R]
  statement: FiniteType R A ↔ FinitePresentation R A
  proof: by
  refine ⟨fun h => ?_, fun hfp => Algebra.FiniteType.of_finitePresentation⟩
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  refine ⟨n, f, hf, ?_⟩
  exact (inferInstance : IsNoetherianRing (MvPolynomial (Fin n) R)).noetherian
    (RingHom.ker f.toRingHom)

中文:
定理 of_finiteType
  条件: [IsNoetherianRing R]
  结论: FiniteType R A ↔ FinitePresentation R A
  证明: by
  refine ⟨fun h => ?_, fun hfp => Algebra.FiniteType.of_finitePresentation⟩
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  refine ⟨n, f, hf, ?_⟩
  exact (inferInstance : IsNoetherianRing (MvPolynomial (Fin n) R)).noetherian
    (RingHom.ker f.toRingHom)

Depends on / 依赖: Algebra, Algebra.FiniteType.iff_quotient_mvPolynomial, Algebra.FiniteType.of_finitePresentation, FiniteType, IsNoetherianRing, MvPolynomial, RingHom, RingHom.ker, f.toRingHom, iff_quotient_mvPolynomial, noetherian, of_finitePresentation, toRingHom
-/
theorem of_finiteType [IsNoetherianRing R] : FiniteType R A ↔ FinitePresentation R A := by
  refine ⟨fun h => ?_, fun hfp => Algebra.FiniteType.of_finitePresentation⟩
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  refine ⟨n, f, hf, ?_⟩
  exact (inferInstance : IsNoetherianRing (MvPolynomial (Fin n) R)).noetherian
    (RingHom.ker f.toRingHom)

/--
theorem `equiv` / 定理 `equiv`

English:
theorem equiv
  given: [FinitePresentation R A] (e : A ≃ₐ[R] B)
  statement: FinitePresentation R B
  proof: by
  obtain ⟨n, f, hf⟩ := FinitePresentation.out (R := R) (A := A)
  use n, AlgHom.comp (↑e) f
  constructor
  · rw [AlgHom.coe_comp]
    exact Function.Surjective.comp e.surjective hf.1
  suffices (RingHom.ker (AlgHom.comp (e : A ->ₐ[R] B) f).toRingHom) = RingHom.ker f.toRingHom by
    rw [this]
  

中文:
定理 equiv
  条件: [FinitePresentation R A] (e : A ≃ₐ[R] B)
  结论: FinitePresentation R B
  证明: by
  obtain ⟨n, f, hf⟩ := FinitePresentation.out (R := R) (A := A)
  use n, AlgHom.comp (↑e) f
  constructor
  · rw [AlgHom.coe_comp]
    exact Function.Surjective.comp e.surjective hf.1
  suffices (RingHom.ker (AlgHom.comp (e : A ->ₐ[R] B) f).toRingHom) = RingHom.ker f.toRingHom by
    rw [this]
  

Depends on / 依赖: AlgHom, AlgHom.coe_comp, AlgHom.comp, FinitePresentation, FinitePresentation.out, Function, Function.Surjective.comp, RingHom, RingHom.comp, RingHom.ker, Surjective, coe_comp, e.surjective, e.toAlgHom.toRingHom.comp, e.toRingEquiv, f.toRingHom, surjective, toAlgHom, toRingEquiv, toRingHom
-/
theorem equiv [FinitePresentation R A] (e : A ≃ₐ[R] B) : FinitePresentation R B := by
  obtain ⟨n, f, hf⟩ := FinitePresentation.out (R := R) (A := A)
  use n, AlgHom.comp (↑e) f
  constructor
  · rw [AlgHom.coe_comp]
    exact Function.Surjective.comp e.surjective hf.1
  suffices (RingHom.ker (AlgHom.comp (e : A ->ₐ[R] B) f).toRingHom) = RingHom.ker f.toRingHom by
    rw [this]
    exact hf.2
  have hco : (AlgHom.comp (e : A ->ₐ[R] B) f).toRingHom = RingHom.comp (e.toRingEquiv : A ≃+* B)
    f.toRingHom := by
    have h : (AlgHom.comp (e : A ->ₐ[R] B) f).toRingHom =
      e.toAlgHom.toRingHom.comp f.toRingHom := rfl
    have h1 : ↑e.toRingEquiv = e.toAlgHom.toRingHom := rfl
    rw [h]; rw [h1]
  rw [RingHom.ker_eq_comap_bot]; rw [hco]; rw [← Ideal.comap_comap]; rw [← RingHom.ker_eq_comap_bot]; rw [RingHom.ker_coe_equiv (AlgEquiv.toRingEquiv e)]; rw [RingHom.ker_eq_comap_bot]

variable (R)

/--
lemma `mvPolynomial_aux` / 引理 `mvPolynomial_aux`

English:
lemma mvPolynomial_aux
  given: (ι : Type*) [Finite ι]
  proof: by
    cases nonempty_fintype ι
    let eqv := (MvPolynomial.renameEquiv R <| Fintype.equivFin ι).symm
    exact
      ⟨Fintype.card ι, eqv, eqv.surjective,
        ((RingHom.injective_iff_ker_eq_bot _).1 eqv.injective).symm ▸ Submodule.fg_bot⟩

中文:
引理 mvPolynomial_aux
  条件: (ι : 类型) [Finite ι]
  证明: by
    cases nonempty_fintype ι
    let eqv := (MvPolynomial.renameEquiv R <| Fintype.equivFin ι).symm
    exact
      ⟨Fintype.card ι, eqv, eqv.surjective,
        ((RingHom.injective_iff_ker_eq_bot _).1 eqv.injective).symm ▸ Submodule.fg_bot⟩
-/
private lemma mvPolynomial_aux (ι : Type*) [Finite ι] :
    FinitePresentation R (MvPolynomial ι R) where
  out := by
    cases nonempty_fintype ι
    let eqv := (MvPolynomial.renameEquiv R <| Fintype.equivFin ι).symm
    exact
      ⟨Fintype.card ι, eqv, eqv.surjective,
        ((RingHom.injective_iff_ker_eq_bot _).1 eqv.injective).symm ▸ Submodule.fg_bot⟩

variable {R}

/--
theorem `quotient` / 定理 `quotient`

English:
theorem quotient
  given: {I : Ideal A} (h : I.FG) [FinitePresentation R A]
  proof: by
    obtain ⟨n, f, hf⟩ := FinitePresentation.out (R := R) (A := A)
    refine ⟨n, (Ideal.Quotient.mkₐ R I).comp f, ?_, ?_⟩
    · exact (Ideal.Quotient.mkₐ_surjective R I).comp hf.1
    · refine Ideal.fg_ker_comp _ _ hf.2 ?_ hf.1
      simp [h]

中文:
定理 quotient
  条件: {I : Ideal A} (h : I.FG) [FinitePresentation R A]
  证明: by
    obtain ⟨n, f, hf⟩ := FinitePresentation.out (R := R) (A := A)
    refine ⟨n, (Ideal.Quotient.mkₐ R I).comp f, ?_, ?_⟩
    · exact (Ideal.Quotient.mkₐ_surjective R I).comp hf.1
    · refine Ideal.fg_ker_comp _ _ hf.2 ?_ hf.1
      simp [h]
-/
protected theorem quotient {I : Ideal A} (h : I.FG) [FinitePresentation R A] :
    FinitePresentation R (A ⧸ I) where
  out := by
    obtain ⟨n, f, hf⟩ := FinitePresentation.out (R := R) (A := A)
    refine ⟨n, (Ideal.Quotient.mkₐ R I).comp f, ?_, ?_⟩
    · exact (Ideal.Quotient.mkₐ_surjective R I).comp hf.1
    · refine Ideal.fg_ker_comp _ _ hf.2 ?_ hf.1
      simp [h]

/--
theorem `of_surjective` / 定理 `of_surjective`

English:
theorem of_surjective
  statement: {f : A ->ₐ[R] B} (hf : Function.Surjective f)
  proof: letI : FinitePresentation R (A ⧸ RingHom.ker f) := FinitePresentation.quotient hker
  equiv (Ideal.quotientKerAlgEquivOfSurjective hf)

中文:
定理 of_surjective
  结论: {f : A ->ₐ[R] B} (hf : Function.Surjective f)
  证明: letI : FinitePresentation R (A ⧸ RingHom.ker f) := FinitePresentation.quotient hker
  equiv (Ideal.quotientKerAlgEquivOfSurjective hf)

Depends on / 依赖: FinitePresentation, FinitePresentation.quotient, Ideal.quotientKerAlgEquivOfSurjective, RingHom, RingHom.ker, quotient, quotientKerAlgEquivOfSurjective
-/
theorem of_surjective {f : A ->ₐ[R] B} (hf : Function.Surjective f)
    (hker : (RingHom.ker f.toRingHom).FG)
    [FinitePresentation R A] : FinitePresentation R B :=
  letI : FinitePresentation R (A ⧸ RingHom.ker f) := FinitePresentation.quotient hker
  equiv (Ideal.quotientKerAlgEquivOfSurjective hf)

/--
theorem `iff` / 定理 `iff`

English:
theorem iff
  proof: by
  constructor
  · rintro ⟨n, f, hf⟩
    exact ⟨n, RingHom.ker f.toRingHom, Ideal.quotientKerAlgEquivOfSurjective hf.1, hf.2⟩
  · rintro ⟨n, I, e, hfg⟩
    let := (FinitePresentation.mvPolynomial_aux R _).quotient hfg
    exact equiv e

中文:
定理 iff
  证明: by
  constructor
  · rintro ⟨n, f, hf⟩
    exact ⟨n, RingHom.ker f.toRingHom, Ideal.quotientKerAlgEquivOfSurjective hf.1, hf.2⟩
  · rintro ⟨n, I, e, hfg⟩
    let := (FinitePresentation.mvPolynomial_aux R _).quotient hfg
    exact equiv e

Depends on / 依赖: FinitePresentation, FinitePresentation.mvPolynomial_aux, Ideal.quotientKerAlgEquivOfSurjective, RingHom, RingHom.ker, f.toRingHom, mvPolynomial_aux, quotient, quotientKerAlgEquivOfSurjective, toRingHom
-/
theorem iff :
    FinitePresentation R A ↔
      exists (n : _) (I : Ideal (MvPolynomial (Fin n) R)) (_ : (_ ⧸ I) ≃ₐ[R] A), I.FG := by
  constructor
  · rintro ⟨n, f, hf⟩
    exact ⟨n, RingHom.ker f.toRingHom, Ideal.quotientKerAlgEquivOfSurjective hf.1, hf.2⟩
  · rintro ⟨n, I, e, hfg⟩
    let := (FinitePresentation.mvPolynomial_aux R _).quotient hfg
    exact equiv e

/--
theorem `iff_quotient_mvPolynomial'` / 定理 `iff_quotient_mvPolynomial'`

English:
theorem iff_quotient_mvPolynomial'
  proof: by
  constructor
  · rintro ⟨n, f, hfs, hfk⟩
    set ulift_var := MvPolynomial.renameEquiv R Equiv.ulift
    refine
      ⟨ULift (Fin n), inferInstance, f.comp ulift_var.toAlgHom, hfs.comp ulift_var.surjective,
        Ideal.fg_ker_comp _ _ ?_ hfk ulift_var.surjective⟩
    simpa using! Submodule.fg_

中文:
定理 iff_quotient_mvPolynomial'
  证明: by
  constructor
  · rintro ⟨n, f, hfs, hfk⟩
    set ulift_var := MvPolynomial.renameEquiv R Equiv.ulift
    refine
      ⟨ULift (Fin n), inferInstance, f.comp ulift_var.toAlgHom, hfs.comp ulift_var.surjective,
        Ideal.fg_ker_comp _ _ ?_ hfk ulift_var.surjective⟩
    simpa using! Submodule.fg_

Depends on / 依赖: AlgEquiv, AlgEquiv.symm, Equiv.ulift, Fintype, Fintype.card, Fintype.equivFin, Ideal.fg_ker_comp, MvPolynomial, MvPolynomial.renameEquiv, Submodule, Submodule.fg_bot, equiv.symm, equivFin, f.comp, fg_bot, fg_ker_comp, hfintype, hfs.comp, renameEquiv, surjective
-/
theorem iff_quotient_mvPolynomial' :
    FinitePresentation R A ↔
      exists (ι : Type*) (_ : Fintype ι) (f : MvPolynomial ι R ->ₐ[R] A),
        Surjective f ∧ (RingHom.ker f.toRingHom).FG := by
  constructor
  · rintro ⟨n, f, hfs, hfk⟩
    set ulift_var := MvPolynomial.renameEquiv R Equiv.ulift
    refine
      ⟨ULift (Fin n), inferInstance, f.comp ulift_var.toAlgHom, hfs.comp ulift_var.surjective,
        Ideal.fg_ker_comp _ _ ?_ hfk ulift_var.surjective⟩
    simpa using! Submodule.fg_bot
  · rintro ⟨ι, hfintype, f, hf⟩
    have equiv := MvPolynomial.renameEquiv R (Fintype.equivFin ι)
    use Fintype.card ι, f.comp equiv.symm, hf.1.comp (AlgEquiv.symm equiv).surjective
    refine Ideal.fg_ker_comp (S := MvPolynomial ι R) (A := A) _ f ?_ hf.2 equiv.symm.surjective
    simpa using! Submodule.fg_bot

universe v in
/--
theorem `mvPolynomial_of_finitePresentation` / 定理 `mvPolynomial_of_finitePresentation`

English:
theorem mvPolynomial_of_finitePresentation
  given: [FinitePresentation R A] (ι : Type v) [Finite ι]
  proof: by
  have hfp : FinitePresentation R A := inferInstance
  rw [iff_quotient_mvPolynomial'] at hfp ⊢
  -- Make universe level `v` explicit so it matches that of `ι`
  obtain ⟨(ι' : Type v), _, f, hf_surj, hf_ker⟩ := hfp
  let g := (MvPolynomial.mapAlgHom f).comp (MvPolynomial.sumAlgEquiv R ι ι').toAlg

中文:
定理 mvPolynomial_of_finitePresentation
  条件: [FinitePresentation R A] (ι : 类型v) [Finite ι]
  证明: by
  have hfp : FinitePresentation R A := inferInstance
  rw [iff_quotient_mvPolynomial'] at hfp ⊢
  -- Make universe level `v` explicit so it matches that of `ι`
  obtain ⟨(ι' : Type v), _, f, hf_surj, hf_ker⟩ := hfp
  let g := (MvPolynomial.mapAlgHom f).comp (MvPolynomial.sumAlgEquiv R ι ι').toAlg

Depends on / 依赖: FinitePresentation, iff_quotient_mvPolynomial
-/
theorem mvPolynomial_of_finitePresentation [FinitePresentation R A] (ι : Type v) [Finite ι] :
    FinitePresentation R (MvPolynomial ι A) := by
  have hfp : FinitePresentation R A := inferInstance
  rw [iff_quotient_mvPolynomial'] at hfp ⊢
  -- Make universe level `v` explicit so it matches that of `ι`
  obtain ⟨(ι' : Type v), _, f, hf_surj, hf_ker⟩ := hfp
  let g := (MvPolynomial.mapAlgHom f).comp (MvPolynomial.sumAlgEquiv R ι ι').toAlgHom
  cases nonempty_fintype (ι oplus ι')
  refine
    ⟨ι oplus ι', by infer_instance, g,
      (MvPolynomial.map_surjective f.toRingHom hf_surj).comp (AlgEquiv.surjective _),
      Ideal.fg_ker_comp _ _ ?_ ?_ (AlgEquiv.surjective _)⟩
  · rw [AlgEquiv.toAlgHom_toRingHom, AlgHom.ker_coe_equiv]
    exact Submodule.fg_bot
  · rw [AlgHom.toRingHom_eq_coe, MvPolynomial.mapAlgHom_coe_ringHom, MvPolynomial.ker_map]
    exact hf_ker.map MvPolynomial.C

variable (R A B)

/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  statement: [Algebra A B] [IsScalarTower R A B] [FinitePresentation R A]
  proof: by
  have hfpB : FinitePresentation A B := inferInstance
  obtain ⟨n, I, e, hfg⟩ := iff.1 hfpB
  let : FinitePresentation R (MvPolynomial (Fin n) A ⧸ I) :=
    (mvPolynomial_of_finitePresentation _).quotient hfg
  exact equiv (e.restrictScalars R)

中文:
定理 trans
  结论: [Algebra A B] [IsScalarTower R A B] [FinitePresentation R A]
  证明: by
  have hfpB : FinitePresentation A B := inferInstance
  obtain ⟨n, I, e, hfg⟩ := iff.1 hfpB
  let : FinitePresentation R (MvPolynomial (Fin n) A ⧸ I) :=
    (mvPolynomial_of_finitePresentation _).quotient hfg
  exact equiv (e.restrictScalars R)

Depends on / 依赖: FinitePresentation, MvPolynomial, e.restrictScalars, mvPolynomial_of_finitePresentation, quotient, restrictScalars
-/
theorem trans [Algebra A B] [IsScalarTower R A B] [FinitePresentation R A]
    [FinitePresentation A B] : FinitePresentation R B := by
  have hfpB : FinitePresentation A B := inferInstance
  obtain ⟨n, I, e, hfg⟩ := iff.1 hfpB
  let : FinitePresentation R (MvPolynomial (Fin n) A ⧸ I) :=
    (mvPolynomial_of_finitePresentation _).quotient hfg
  exact equiv (e.restrictScalars R)

/--
Instance `mvPolynomial` / 实例 `mvPolynomial`

English:
instance mvPolynomial
  signature: [FinitePresentation R A] (ι : Type*) [Finite ι]
  body: have := FinitePresentation.mvPolynomial_aux A ι; .trans _ A _

中文:
实例 mvPolynomial
  签名: [FinitePresentation R A] (ι : 类型) [Finite ι]
  定义体: have := FinitePresentation.mvPolynomial_aux A ι; .trans _ A _
-/
protected instance mvPolynomial [FinitePresentation R A] (ι : Type*) [Finite ι] :
    FinitePresentation R (MvPolynomial ι A) :=
  have := FinitePresentation.mvPolynomial_aux A ι; .trans _ A _

/--
Instance `self` / 实例 `self`

English:
instance self
  signature: : FinitePresentation R R
  body: have := FinitePresentation.mvPolynomial_aux R Empty
  equiv (MvPolynomial.isEmptyAlgEquiv R Empty)

中文:
实例 self
  签名: : FinitePresentation R R
  定义体: have := FinitePresentation.mvPolynomial_aux R Empty
  equiv (MvPolynomial.isEmptyAlgEquiv R Empty)

Depends on / 依赖: FinitePresentation, FinitePresentation.mvPolynomial_aux, MvPolynomial, MvPolynomial.isEmptyAlgEquiv, isEmptyAlgEquiv, mvPolynomial_aux
-/
instance self : FinitePresentation R R :=
  have := FinitePresentation.mvPolynomial_aux R Empty
  equiv (MvPolynomial.isEmptyAlgEquiv R Empty)

/--
Instance `polynomial` / 实例 `polynomial`

English:
instance polynomial
  signature: [FinitePresentation R A]
  body: letI := FinitePresentation.mvPolynomial R A Unit
  have := equiv (MvPolynomial.uniqueAlgEquiv.{_, 0} A PUnit)
  .trans _ A _

中文:
实例 polynomial
  签名: [FinitePresentation R A]
  定义体: letI := FinitePresentation.mvPolynomial R A Unit
  have := equiv (MvPolynomial.uniqueAlgEquiv.{_, 0} A PUnit)
  .trans _ A _

Depends on / 依赖: FinitePresentation, FinitePresentation.mvPolynomial, MvPolynomial, MvPolynomial.uniqueAlgEquiv, mvPolynomial, uniqueAlgEquiv
-/
instance polynomial [FinitePresentation R A] : FinitePresentation R A[X] :=
  letI := FinitePresentation.mvPolynomial R A Unit
  have := equiv (MvPolynomial.uniqueAlgEquiv.{_, 0} A PUnit)
  .trans _ A _

open MvPolynomial

-- TODO: extract out helper lemmas and tidy proof.
@[stacks 0561]
/--
theorem `of_restrict_scalars_finitePresentation` / 定理 `of_restrict_scalars_finitePresentation`

English:
theorem of_restrict_scalars_finitePresentation
  statement: [Algebra A B] [IsScalarTower R A B]
  proof: by
  classical
  obtain ⟨n, f, hf, s, hs⟩ := FinitePresentation.out (R := R) (A := B)
  let RX := MvPolynomial (Fin n) R
  let AX := MvPolynomial (Fin n) A
  refine ⟨n, MvPolynomial.aeval (f ∘ X), ?_, ?_⟩
  · rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval,
      Set.range_comp f Mv

中文:
定理 of_restrict_scalars_finitePresentation
  结论: [Algebra A B] [IsScalarTower R A B]
  证明: by
  classical
  obtain ⟨n, f, hf, s, hs⟩ := FinitePresentation.out (R := R) (A := B)
  let RX := MvPolynomial (Fin n) R
  let AX := MvPolynomial (Fin n) A
  refine ⟨n, MvPolynomial.aeval (f ∘ X), ?_, ?_⟩
  · rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval,
      Set.range_comp f Mv

Depends on / 依赖: AlgHom, AlgHom.range_eq_top, Algebra, Algebra.adjoin_range_eq_range_aeval, Algebra.map_top, FinitePresentation, FinitePresentation.out, FiniteType, FiniteType.out, MvPolynomial, MvPolynomial.X, MvPolynomial.aeval, Set.range_comp, adjoin_adjoin_of_tower, adjoin_image, adjoin_range_X, adjoin_range_eq_range_aeval, classical, eq_top_iff, map_top
-/
theorem of_restrict_scalars_finitePresentation [Algebra A B] [IsScalarTower R A B]
    [FinitePresentation.{w₁, w₃} R B] [FiniteType R A] :
    FinitePresentation.{w₂, w₃} A B := by
  classical
  obtain ⟨n, f, hf, s, hs⟩ := FinitePresentation.out (R := R) (A := B)
  let RX := MvPolynomial (Fin n) R
  let AX := MvPolynomial (Fin n) A
  refine ⟨n, MvPolynomial.aeval (f ∘ X), ?_, ?_⟩
  · rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval,
      Set.range_comp f MvPolynomial.X, eq_top_iff, ← @adjoin_adjoin_of_tower R A B,
      adjoin_image, adjoin_range_X, Algebra.map_top, (AlgHom.range_eq_top _).mpr hf]
    exact fun {x} => subset_adjoin ⟨⟩
  · obtain ⟨t, ht⟩ := FiniteType.out (R := R) (A := A)
    have := fun i : t => hf (algebraMap A B i)
    choose t' ht' using this
    have ht'' : Algebra.adjoin R (algebraMap A AX '' t union Set.range (X : _ -> AX)) = ⊤ := by
      rw [adjoin_union_eq_adjoin_adjoin]; rw [← Subalgebra.restrictScalars_top R (A := AX)
        (S := { x // x in adjoin R ((algebraMap A AX) '' t) })]
      refine congrArg (Subalgebra.restrictScalars R) ?_
      rw [adjoin_algebraMap]; rw [ht]
      apply Subalgebra.restrictScalars_injective R
      rw [← adjoin_restrictScalars]; rw [adjoin_range_X]; rw [Subalgebra.restrictScalars_top]; rw [Subalgebra.restrictScalars_top]
    let g : t -> AX := fun x => MvPolynomial.C (x : A) - map (algebraMap R A) (t' x)
    refine ⟨s.image (map (algebraMap R A)) union t.attach.image g, ?_⟩
    rw [Finset.coe_union]; rw [Finset.coe_image]; rw [Finset.coe_image]; rw [Finset.attach_eq_univ]; rw [Finset.coe_univ]; rw [Set.image_univ]
    let s₀ := (MvPolynomial.map (algebraMap R A)) '' s union Set.range g
    let I := RingHom.ker (MvPolynomial.aeval (R := A) (f ∘ MvPolynomial.X))
    change Ideal.span s₀ = I
    have leI : Ideal.span ((MvPolynomial.map (algebraMap R A)) '' s union Set.range g) <=
      RingHom.ker (MvPolynomial.aeval (R := A) (f ∘ MvPolynomial.X)) := by
      rw [Ideal.span_le]
      rintro _ (⟨x, hx, rfl⟩ | ⟨⟨x, hx⟩, rfl⟩) <;>
      rw [SetLike.mem_coe]; rw [RingHom.mem_ker]
      · rw [MvPolynomial.aeval_map_algebraMap (R := R) (A := A), ← aeval_unique]
        have := Ideal.subset_span hx
        rwa [hs] at this
      · rw [map_sub, MvPolynomial.aeval_map_algebraMap, ← aeval_unique,
          MvPolynomial.aeval_C, ht', Subtype.coe_mk, sub_self]
    apply leI.antisymm
    intro x hx
    rw [RingHom.mem_ker] at hx
    let s₀ := (MvPolynomial.map (algebraMap R A)) '' ↑s union Set.range g
    change x in Ideal.span s₀
    have : x in (MvPolynomial.map (algebraMap R A) : _ ->+* AX).range.toAddSubmonoid ⊔
      (Ideal.span s₀).toAddSubmonoid := by
      have : x in (⊤ : Subalgebra R AX) := trivial
      rw [← ht''] at this
      refine adjoin_induction ?_ ?_ ?_ ?_ this
      · rintro _ (⟨x, hx, rfl⟩ | ⟨i, rfl⟩)
        · rw [MvPolynomial.algebraMap_eq, ← sub_add_cancel (MvPolynomial.C x)
            (map (algebraMap R A) (t' ⟨x, hx⟩)), add_comm]
          apply AddSubmonoid.add_mem_sup
          · exact Set.mem_range_self _
          · apply Ideal.subset_span
            apply Set.mem_union_right
            exact Set.mem_range_self _
        · apply AddSubmonoid.mem_sup_left
          exact ⟨X i, map_X _ _⟩
      · intro r
        apply AddSubmonoid.mem_sup_left
        exact ⟨C r, map_C _ _⟩
      · intro _ _ _ _ h₁ h₂
        exact add_mem h₁ h₂
      · intro x₁ x₂ _ _ h₁ h₂
        obtain ⟨_, ⟨p₁, rfl⟩, q₁, hq₁, rfl⟩ := AddSubmonoid.mem_sup.mp h₁
        obtain ⟨_, ⟨p₂, rfl⟩, q₂, hq₂, rfl⟩ := AddSubmonoid.mem_sup.mp h₂
        rw [add_mul]; rw [mul_add]; rw [add_assoc]; rw [← map_mul]
        apply AddSubmonoid.add_mem_sup
        · exact Set.mem_range_self _
        · refine add_mem (Ideal.mul_mem_left _ _ hq₂) (Ideal.mul_mem_right _ _ hq₁)
    obtain ⟨_, ⟨p, rfl⟩, q, hq, rfl⟩ := AddSubmonoid.mem_sup.mp this
    rw [map_add]; rw [aeval_map_algebraMap]; rw [← aeval_unique]; rw [show MvPolynomial.aeval (f ∘ X) q = 0
      from leI hq]; rw [add_zero] at hx
    suffices Ideal.span (s : Set RX) <= (Ideal.span s₀).comap (MvPolynomial.map <| algebraMap R A) by
      refine add_mem ?_ hq
      rw [hs] at this
      exact this hx
    rw [Ideal.span_le]
    intro x hx
    apply Ideal.subset_span
    apply Set.mem_union_left
    exact Set.mem_image_of_mem _ hx

variable {R A B}

-- TODO: extract out helper lemmas and tidy proof.
/--
theorem `ker_fg_of_mvPolynomial` / 定理 `ker_fg_of_mvPolynomial`

English:
theorem ker_fg_of_mvPolynomial
  statement: {n : Nat} (f : MvPolynomial (Fin n) R ->ₐ[R] A)
  proof: by
  classical
    obtain ⟨m, f', hf', s, hs⟩ := FinitePresentation.out (R := R) (A := A)
    let RXn := MvPolynomial (Fin n) R
    let RXm := MvPolynomial (Fin m) R
    have := fun i : Fin n => hf' (f <| X i)
    choose g hg using this
    have := fun i : Fin m => hf (f' <| X i)
    choose h hh usi

中文:
定理 ker_fg_of_mvPolynomial
  结论: {n : 自然数} (f : MvPolynomial (Fin n) R ->ₐ[R] A)
  证明: by
  classical
    obtain ⟨m, f', hf', s, hs⟩ := FinitePresentation.out (R := R) (A := A)
    let RXn := MvPolynomial (Fin n) R
    let RXm := MvPolynomial (Fin m) R
    have := fun i : Fin n => hf' (f <| X i)
    choose g hg using this
    have := fun i : Fin m => hf (f' <| X i)
    choose h hh usi

Depends on / 依赖: FinitePresentation, FinitePresentation.out, Finset, Finset.coe_image, Finset.coe_union, Finset.coe_univ, Finset.univ.image, MvPolynomial, Set.imag, aeval_h, classical, coe_image, coe_union, coe_univ, s.image
-/
theorem ker_fg_of_mvPolynomial {n : Nat} (f : MvPolynomial (Fin n) R ->ₐ[R] A)
    (hf : Function.Surjective f) [FinitePresentation R A] : (RingHom.ker f.toRingHom).FG := by
  classical
    obtain ⟨m, f', hf', s, hs⟩ := FinitePresentation.out (R := R) (A := A)
    let RXn := MvPolynomial (Fin n) R
    let RXm := MvPolynomial (Fin m) R
    have := fun i : Fin n => hf' (f <| X i)
    choose g hg using this
    have := fun i : Fin m => hf (f' <| X i)
    choose h hh using this
    let aeval_h : RXm ->ₐ[R] RXn := aeval h
    let g' : Fin n -> RXn := fun i => X i - aeval_h (g i)
    refine ⟨Finset.univ.image g' union s.image aeval_h, ?_⟩
    simp only [Finset.coe_image, Finset.coe_union, Finset.coe_univ, Set.image_univ]
    have hh' : forall x, f (aeval_h x) = f' x := by
      intro x
      rw [← f.coe_toRingHom]; rw [map_aeval]
      simp_rw [AlgHom.coe_toRingHom, hh]
      rw [AlgHom.comp_algebraMap]; rw [← aeval_eq_eval₂Hom]; rw [-- Porting note: added line below
        ← funext fun i => Function.comp_apply (f := ↑f') (g := MvPolynomial.X)]; rw [← aeval_unique]
    let s' := Set.range g' union aeval_h '' s
    have leI : Ideal.span s' <= RingHom.ker f.toRingHom := by
      rw [Ideal.span_le]
      rintro _ (⟨i, rfl⟩ | ⟨x, hx, rfl⟩)
      · change f (g' i) = 0
        rw [map_sub]; rw [← hg]; rw [hh']; rw [sub_self]
      · change f (aeval_h x) = 0
        rw [hh']
        change x in RingHom.ker f'.toRingHom
        rw [← hs]
        exact Ideal.subset_span hx
    apply leI.antisymm
    intro x hx
    have : x in aeval_h.range.toAddSubmonoid ⊔ (Ideal.span s').toAddSubmonoid := by
      have : x in adjoin R (Set.range X : Set RXn) := by
        rw [adjoin_range_X]
        trivial
      refine adjoin_induction ?_ ?_ ?_ ?_ this
      · rintro _ ⟨i, rfl⟩
        rw [← sub_add_cancel (X i) (aeval h (g i))]; rw [add_comm]
        apply AddSubmonoid.add_mem_sup
        · exact Set.mem_range_self _
        · apply Submodule.subset_span
          apply Set.mem_union_left
          exact Set.mem_range_self _
      · intro r
        apply AddSubmonoid.mem_sup_left
        exact ⟨C r, aeval_C _ _⟩
      · intro _ _ _ _ h₁ h₂
        exact add_mem h₁ h₂
      · intro p₁ p₂ _ _ h₁ h₂
        obtain ⟨_, ⟨x₁, rfl⟩, y₁, hy₁, rfl⟩ := AddSubmonoid.mem_sup.mp h₁
        obtain ⟨_, ⟨x₂, rfl⟩, y₂, hy₂, rfl⟩ := AddSubmonoid.mem_sup.mp h₂
        rw [mul_add]; rw [add_mul]; rw [add_assoc]; rw [← map_mul]
        apply AddSubmonoid.add_mem_sup
        · exact Set.mem_range_self _
        · exact add_mem (Ideal.mul_mem_right _ _ hy₁) (Ideal.mul_mem_left _ _ hy₂)
    obtain ⟨_, ⟨x, rfl⟩, y, hy, rfl⟩ := AddSubmonoid.mem_sup.mp this
    refine add_mem ?_ hy
    simp only [RXn, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_add,
      show f y = 0 from leI hy, add_zero, hh'] at hx
    suffices Ideal.span (s : Set RXm) <= (Ideal.span s').comap aeval_h by
      apply this
      rwa [hs]
    rw [Ideal.span_le]
    intro x hx
    apply Submodule.subset_span
    apply Set.mem_union_right
    exact Set.mem_image_of_mem _ hx

/--
theorem `ker_fG_of_surjective` / 定理 `ker_fG_of_surjective`

English:
theorem ker_fG_of_surjective
  statement: (f : A ->ₐ[R] B) (hf : Function.Surjective f)
  proof: by
  obtain ⟨n, g, hg, _⟩ := FinitePresentation.out (R := R) (A := A)
  convert! (ker_fg_of_mvPolynomial (f.comp g) (hf.comp hg)).map g.toRingHom
  simp_rw [RingHom.ker_eq_comap_bot, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom]
  rw [← Ideal.comap_comap]; rw [Ideal.map_comap_of_surjective (g : Mv

中文:
定理 ker_fG_of_surjective
  结论: (f : A ->ₐ[R] B) (hf : Function.Surjective f)
  证明: by
  obtain ⟨n, g, hg, _⟩ := FinitePresentation.out (R := R) (A := A)
  convert! (ker_fg_of_mvPolynomial (f.comp g) (hf.comp hg)).map g.toRingHom
  simp_rw [RingHom.ker_eq_comap_bot, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom]
  rw [← Ideal.comap_comap]; rw [Ideal.map_comap_of_surjective (g : Mv

Depends on / 依赖: AlgHom, AlgHom.comp_toRingHom, AlgHom.toRingHom_eq_coe, FinitePresentation, FinitePresentation.out, Ideal.comap_comap, Ideal.map_comap_of_surjective, MvPolynomial, RingHom, RingHom.ker_eq_comap_bot, comap_comap, comp_toRingHom, convert, f.comp, g.toRingHom, hf.comp, ker_eq_comap_bot, ker_fg_of_mvPolynomial, map_comap_of_surjective, simp_rw
-/
theorem ker_fG_of_surjective (f : A ->ₐ[R] B) (hf : Function.Surjective f)
    [FinitePresentation R A] [FinitePresentation R B] : (RingHom.ker f.toRingHom).FG := by
  obtain ⟨n, g, hg, _⟩ := FinitePresentation.out (R := R) (A := A)
  convert! (ker_fg_of_mvPolynomial (f.comp g) (hf.comp hg)).map g.toRingHom
  simp_rw [RingHom.ker_eq_comap_bot, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom]
  rw [← Ideal.comap_comap]; rw [Ideal.map_comap_of_surjective (g : MvPolynomial (Fin n) R ->+* A) hg]

end FinitePresentation

end Algebra

end ModuleAndAlgebra

namespace RingHom

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- A ring morphism `A →+* B` is of `RingHom.FinitePresentation` if `B` is finitely presented as
`A`-algebra. -/
@[algebraize]
/--
Definition of `FinitePresentation` / `FinitePresentation` 的定义

English:
definition FinitePresentation
  signature: (f : A ->+* B)
  body: @Algebra.FinitePresentation A B _ _ f.toAlgebra

@[simp]

中文:
定义 FinitePresentation
  签名: (f : A ->+* B)
  定义体: @Algebra.FinitePresentation A B _ _ f.toAlgebra

@[simp]

Depends on / 依赖: Algebra, Algebra.FinitePresentation, FinitePresentation, f.toAlgebra, toAlgebra
-/
def FinitePresentation (f : A ->+* B) : Prop :=
  @Algebra.FinitePresentation A B _ _ f.toAlgebra

@[simp]
/--
lemma `finitePresentation_algebraMap` / 引理 `finitePresentation_algebraMap`

English:
lemma finitePresentation_algebraMap
  given: [Algebra A B]
  proof: by
  rw [RingHom.FinitePresentation]; rw [toAlgebra_algebraMap]

中文:
引理 finitePresentation_algebraMap
  条件: [Algebra A B]
  证明: by
  rw [RingHom.FinitePresentation]; rw [toAlgebra_algebraMap]

Depends on / 依赖: FinitePresentation, RingHom, RingHom.FinitePresentation, toAlgebra_algebraMap
-/
lemma finitePresentation_algebraMap [Algebra A B] :
    (algebraMap A B).FinitePresentation ↔ Algebra.FinitePresentation A B := by
  rw [RingHom.FinitePresentation]; rw [toAlgebra_algebraMap]

namespace FiniteType

/--
theorem `of_finitePresentation` / 定理 `of_finitePresentation`

English:
theorem of_finitePresentation
  given: {f : A ->+* B} (hf : f.FinitePresentation)
  statement: f.FiniteType
  proof: @Algebra.FiniteType.of_finitePresentation A B _ _ f.toAlgebra hf

中文:
定理 of_finitePresentation
  条件: {f : A ->+* B} (hf : f.FinitePresentation)
  结论: f.FiniteType
  证明: @Algebra.FiniteType.of_finitePresentation A B _ _ f.toAlgebra hf

Depends on / 依赖: Algebra, Algebra.FiniteType.of_finitePresentation, FiniteType, f.toAlgebra, of_finitePresentation, toAlgebra
-/
theorem of_finitePresentation {f : A ->+* B} (hf : f.FinitePresentation) : f.FiniteType :=
  @Algebra.FiniteType.of_finitePresentation A B _ _ f.toAlgebra hf

end FiniteType

namespace FinitePresentation

variable (A) in
/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: FinitePresentation (RingHom.id A)
  proof: Algebra.FinitePresentation.self A

中文:
定理 id
  结论: FinitePresentation (RingHom.id A)
  证明: Algebra.FinitePresentation.self A

Depends on / 依赖: Algebra, Algebra.FinitePresentation.self, FinitePresentation
-/
theorem id : FinitePresentation (RingHom.id A) :=
  Algebra.FinitePresentation.self A

/--
theorem `comp_surjective` / 定理 `comp_surjective`

English:
theorem comp_surjective
  statement: {f : A ->+* B} {g : B ->+* C} (hf : f.FinitePresentation) (hg : Surjective g)
  proof: by
  algebraize [f, g.comp f]
  exact Algebra.FinitePresentation.of_surjective
    (f :=
      { g with
        toFun := g
        commutes' := fun _ => rfl })
    hg hker

中文:
定理 comp_surjective
  结论: {f : A ->+* B} {g : B ->+* C} (hf : f.FinitePresentation) (hg : Surjective g)
  证明: by
  algebraize [f, g.comp f]
  exact Algebra.FinitePresentation.of_surjective
    (f :=
      { g with
        toFun := g
        commutes' := fun _ => rfl })
    hg hker

Depends on / 依赖: Algebra, Algebra.FinitePresentation.of_surjective, FinitePresentation, algebraize, commutes, g.comp, of_surjective
-/
theorem comp_surjective {f : A ->+* B} {g : B ->+* C} (hf : f.FinitePresentation) (hg : Surjective g)
    (hker : (RingHom.ker g).FG) : (g.comp f).FinitePresentation := by
  algebraize [f, g.comp f]
  exact Algebra.FinitePresentation.of_surjective
    (f :=
      { g with
        toFun := g
        commutes' := fun _ => rfl })
    hg hker

/--
theorem `of_surjective` / 定理 `of_surjective`

English:
theorem of_surjective
  given: (f : A ->+* B) (hf : Surjective f) (hker : (RingHom.ker f).FG)
  proof: by
  rw [← f.comp_id]
  exact (id A).comp_surjective hf hker

中文:
定理 of_surjective
  条件: (f : A ->+* B) (hf : Surjective f) (hker : (RingHom.ker f).FG)
  证明: by
  rw [← f.comp_id]
  exact (id A).comp_surjective hf hker

Depends on / 依赖: comp_id, comp_surjective, f.comp_id
-/
theorem of_surjective (f : A ->+* B) (hf : Surjective f) (hker : (RingHom.ker f).FG) :
    f.FinitePresentation := by
  rw [← f.comp_id]
  exact (id A).comp_surjective hf hker

/--
lemma `of_bijective` / 引理 `of_bijective`

English:
lemma of_bijective
  given: {f : A ->+* B} (hf : Function.Bijective f)
  statement: f.FinitePresentation
  proof: .of_surjective f hf.2 by
    have : ker f = ⊥ := by rw [← RingHom.injective_iff_ker_eq_bot]; exact hf.1
    rw [this]
    exact Submodule.fg_bot

中文:
引理 of_bijective
  条件: {f : A ->+* B} (hf : Function.Bijective f)
  结论: f.FinitePresentation
  证明: .of_surjective f hf.2 by
    have : ker f = ⊥ := by rw [← RingHom.injective_iff_ker_eq_bot]; exact hf.1
    rw [this]
    exact Submodule.fg_bot

Depends on / 依赖: RingHom, RingHom.injective_iff_ker_eq_bot, Submodule, Submodule.fg_bot, fg_bot, injective_iff_ker_eq_bot, of_surjective
-/
lemma of_bijective {f : A ->+* B} (hf : Function.Bijective f) : f.FinitePresentation :=
.of_surjective f hf.2 by
    have : ker f = ⊥ := by rw [← RingHom.injective_iff_ker_eq_bot]; exact hf.1
    rw [this]
    exact Submodule.fg_bot

/--
theorem `of_finiteType` / 定理 `of_finiteType`

English:
theorem of_finiteType
  given: [IsNoetherianRing A] {f : A ->+* B}
  statement: f.FiniteType ↔ f.FinitePresentation
  proof: @Algebra.FinitePresentation.of_finiteType A B _ _ f.toAlgebra _

中文:
定理 of_finiteType
  条件: [IsNoetherianRing A] {f : A ->+* B}
  结论: f.FiniteType ↔ f.FinitePresentation
  证明: @Algebra.FinitePresentation.of_finiteType A B _ _ f.toAlgebra _

Depends on / 依赖: Algebra, Algebra.FinitePresentation.of_finiteType, FinitePresentation, f.toAlgebra, of_finiteType, toAlgebra
-/
theorem of_finiteType [IsNoetherianRing A] {f : A ->+* B} : f.FiniteType ↔ f.FinitePresentation :=
  @Algebra.FinitePresentation.of_finiteType A B _ _ f.toAlgebra _

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: {g : B ->+* C} {f : A ->+* B} (hg : g.FinitePresentation) (hf : f.FinitePresentation)
  proof: by
  algebraize [f, g, g.comp f]
  exact Algebra.FinitePresentation.trans A B C

中文:
定理 comp
  条件: {g : B ->+* C} {f : A ->+* B} (hg : g.FinitePresentation) (hf : f.FinitePresentation)
  证明: by
  algebraize [f, g, g.comp f]
  exact Algebra.FinitePresentation.trans A B C

Depends on / 依赖: Algebra, Algebra.FinitePresentation.trans, FinitePresentation, algebraize, g.comp
-/
theorem comp {g : B ->+* C} {f : A ->+* B} (hg : g.FinitePresentation) (hf : f.FinitePresentation) :
    (g.comp f).FinitePresentation := by
  algebraize [f, g, g.comp f]
  exact Algebra.FinitePresentation.trans A B C

/--
theorem `of_comp_finiteType` / 定理 `of_comp_finiteType`

English:
theorem of_comp_finiteType
  statement: (f : A ->+* B) {g : B ->+* C} (hg : (g.comp f).FinitePresentation)
  proof: by
  algebraize [f, g, g.comp f]
  exact Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A B C

中文:
定理 of_comp_finiteType
  结论: (f : A ->+* B) {g : B ->+* C} (hg : (g.comp f).FinitePresentation)
  证明: by
  algebraize [f, g, g.comp f]
  exact Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A B C

Depends on / 依赖: Algebra, Algebra.FinitePresentation.of_restrict_scalars_finitePresentation, FinitePresentation, algebraize, g.comp, of_restrict_scalars_finitePresentation
-/
theorem of_comp_finiteType (f : A ->+* B) {g : B ->+* C} (hg : (g.comp f).FinitePresentation)
    (hf : f.FiniteType) : g.FinitePresentation := by
  algebraize [f, g, g.comp f]
  exact Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A B C

end FinitePresentation

end RingHom

namespace RingHom.FinitePresentation
universe u v

open Polynomial

/--
lemma `polynomial_induction` / 引理 `polynomial_induction`

English:
lemma polynomial_induction
  proof: by
  let := f.toAlgebra
  obtain ⟨n, g, hg, hg'⟩ := hf
  let g' := g.toRingHom
  change Surjective g' at hg
  change (ker g').FG at hg'
  have : g'.comp MvPolynomial.C = f := g.comp_algebraMap
  clear_value g'
  subst this
  clear g
  induction n generalizing R S with
  | zero =>
    refine fg_ker _

中文:
引理 polynomial_induction
  证明: by
  let := f.toAlgebra
  obtain ⟨n, g, hg, hg'⟩ := hf
  let g' := g.toRingHom
  change Surjective g' at hg
  change (ker g').FG at hg'
  have : g'.comp MvPolynomial.C = f := g.comp_algebraMap
  clear_value g'
  subst this
  clear g
  induction n generalizing R S with
  | zero =>
    refine fg_ker _

Depends on / 依赖: C_surjective, MvPolynomial, MvPolynomial.C, MvPolynomial.C_surjective, MvPolynomial.isEmptyRingEquiv, MvPolynomial.isEmptyRingEquiv_symm_to, RingEquiv, RingEquiv.toRingHom_eq_coe, Surjective, clear_value, comap_ker, comp_algebraMap, convert, f.toAlgebra, fg_ker, g.comp_algebraMap, g.toRingHom, generalizing, hg.comp, isEmptyRingEquiv
-/
lemma polynomial_induction
    (P : forall (R : Type u) [CommRing R] (S : Type u) [CommRing S], (R ->+* S) -> Prop)
    (Q : forall (R : Type u) [CommRing R] (S : Type v) [CommRing S], (R ->+* S) -> Prop)
    (polynomial : forall (R) [CommRing R], P R R[X] C)
    (fg_ker : forall (R : Type u) [CommRing R] (S : Type v) [CommRing S] (f : R ->+* S),
      Surjective f -> (ker f).FG -> Q R S f)
    (comp : forall (R) [CommRing R] (S) [CommRing S] (T) [CommRing T] (f : R ->+* S) (g : S ->+* T),
      P R S f -> Q S T g -> Q R T (g.comp f))
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R ->+* S) (hf : f.FinitePresentation) :
    Q R S f := by
  let := f.toAlgebra
  obtain ⟨n, g, hg, hg'⟩ := hf
  let g' := g.toRingHom
  change Surjective g' at hg
  change (ker g').FG at hg'
  have : g'.comp MvPolynomial.C = f := g.comp_algebraMap
  clear_value g'
  subst this
  clear g
  induction n generalizing R S with
  | zero =>
    refine fg_ker _ _ _ (hg.comp (MvPolynomial.C_surjective (Fin 0))) ?_
    rw [← comap_ker]
    convert! hg'.map (MvPolynomial.isEmptyRingEquiv R (Fin 0)).toRingHom using 1
    simp only [RingEquiv.toRingHom_eq_coe, ← MvPolynomial.isEmptyRingEquiv_symm_toRingHom]
    exact Ideal.comap_symm (MvPolynomial.isEmptyRingEquiv R (Fin 0))
  | succ n IH =>
    let e : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin n) R[X] :=
      (MvPolynomial.renameEquiv R (finSuccEquiv n)).trans (MvPolynomial.optionEquivRight R (Fin n))
    have he : (ker (g'.comp <| RingHomClass.toRingHom e.symm)).FG := by
      rw [← RingHom.comap_ker]
      convert! hg'.map e.toAlgHom.toRingHom using 1
      exact Ideal.comap_symm e.toRingEquiv
    have := IH (R := R[X]) (S := S) (g'.comp e.symm) (hg.comp e.symm.surjective) he
    convert! comp _ _ _ _ _ (polynomial _) this using 1
    rw [comp_assoc]; rw [comp_assoc]
    congr 1 with r
    simp [e]

end RingHom.FinitePresentation

namespace AlgHom

variable {R A B C : Type*} [CommRing R]
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

/--
Definition of `FinitePresentation` / `FinitePresentation` 的定义

English:
definition FinitePresentation
  signature: (f : A ->ₐ[R] B)
  body: f.toRingHom.FinitePresentation

中文:
定义 FinitePresentation
  签名: (f : A ->ₐ[R] B)
  定义体: f.toRingHom.FinitePresentation

Depends on / 依赖: FinitePresentation, f.toRingHom.FinitePresentation, toRingHom
-/
def FinitePresentation (f : A ->ₐ[R] B) : Prop :=
  f.toRingHom.FinitePresentation

namespace FiniteType

/--
theorem `of_finitePresentation` / 定理 `of_finitePresentation`

English:
theorem of_finitePresentation
  given: {f : A ->ₐ[R] B} (hf : f.FinitePresentation)
  statement: f.FiniteType
  proof: RingHom.FiniteType.of_finitePresentation hf

中文:
定理 of_finitePresentation
  条件: {f : A ->ₐ[R] B} (hf : f.FinitePresentation)
  结论: f.FiniteType
  证明: RingHom.FiniteType.of_finitePresentation hf

Depends on / 依赖: FiniteType, RingHom, RingHom.FiniteType.of_finitePresentation, of_finitePresentation
-/
theorem of_finitePresentation {f : A ->ₐ[R] B} (hf : f.FinitePresentation) : f.FiniteType :=
  RingHom.FiniteType.of_finitePresentation hf

end FiniteType

namespace FinitePresentation

variable (R A)

/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: FinitePresentation (AlgHom.id R A)
  proof: RingHom.FinitePresentation.id A

中文:
定理 id
  结论: FinitePresentation (AlgHom.id R A)
  证明: RingHom.FinitePresentation.id A

Depends on / 依赖: FinitePresentation, RingHom, RingHom.FinitePresentation.id
-/
theorem id : FinitePresentation (AlgHom.id R A) :=
  RingHom.FinitePresentation.id A

variable {R A}

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  statement: {g : B ->ₐ[R] C} {f : A ->ₐ[R] B} (hg : g.FinitePresentation)
  proof: RingHom.FinitePresentation.comp hg hf

中文:
定理 comp
  结论: {g : B ->ₐ[R] C} {f : A ->ₐ[R] B} (hg : g.FinitePresentation)
  证明: RingHom.FinitePresentation.comp hg hf

Depends on / 依赖: FinitePresentation, RingHom, RingHom.FinitePresentation.comp
-/
theorem comp {g : B ->ₐ[R] C} {f : A ->ₐ[R] B} (hg : g.FinitePresentation)
    (hf : f.FinitePresentation) : (g.comp f).FinitePresentation :=
  RingHom.FinitePresentation.comp hg hf

/--
theorem `comp_surjective` / 定理 `comp_surjective`

English:
theorem comp_surjective
  statement: {f : A ->ₐ[R] B} {g : B ->ₐ[R] C} (hf : f.FinitePresentation)
  proof: RingHom.FinitePresentation.comp_surjective hf hg hker

中文:
定理 comp_surjective
  结论: {f : A ->ₐ[R] B} {g : B ->ₐ[R] C} (hf : f.FinitePresentation)
  证明: RingHom.FinitePresentation.comp_surjective hf hg hker

Depends on / 依赖: FinitePresentation, RingHom, RingHom.FinitePresentation.comp_surjective, comp_surjective
-/
theorem comp_surjective {f : A ->ₐ[R] B} {g : B ->ₐ[R] C} (hf : f.FinitePresentation)
    (hg : Surjective g) (hker : (RingHom.ker g.toRingHom).FG) : (g.comp f).FinitePresentation :=
  RingHom.FinitePresentation.comp_surjective hf hg hker

/--
theorem `of_surjective` / 定理 `of_surjective`

English:
theorem of_surjective
  given: (f : A ->ₐ[R] B) (hf : Surjective f) (hker : (RingHom.ker f.toRingHom).FG)
  proof: by
  -- Porting note: added `convert`
  convert! RingHom.FinitePresentation.of_surjective f hf hker

中文:
定理 of_surjective
  条件: (f : A ->ₐ[R] B) (hf : Surjective f) (hker : (RingHom.ker f.toRingHom).FG)
  证明: by
  -- Porting note: added `convert`
  convert! RingHom.FinitePresentation.of_surjective f hf hker
-/
theorem of_surjective (f : A ->ₐ[R] B) (hf : Surjective f) (hker : (RingHom.ker f.toRingHom).FG) :
    f.FinitePresentation := by
  -- Porting note: added `convert`
  convert! RingHom.FinitePresentation.of_surjective f hf hker

/--
theorem `of_finiteType` / 定理 `of_finiteType`

English:
theorem of_finiteType
  given: [IsNoetherianRing A] {f : A ->ₐ[R] B}
  statement: f.FiniteType ↔ f.FinitePresentation
  proof: RingHom.FinitePresentation.of_finiteType

nonrec theorem of_comp_finiteType (f : A ->ₐ[R] B) {g : B ->ₐ[R] C}
    (h : (g.comp f).FinitePresentation) (h' : f.FiniteType) : g.FinitePresentation :=
  h.of_comp_finiteType _ h'

中文:
定理 of_finiteType
  条件: [IsNoetherianRing A] {f : A ->ₐ[R] B}
  结论: f.FiniteType ↔ f.FinitePresentation
  证明: RingHom.FinitePresentation.of_finiteType

nonrec theorem of_comp_finiteType (f : A ->ₐ[R] B) {g : B ->ₐ[R] C}
    (h : (g.comp f).FinitePresentation) (h' : f.FiniteType) : g.FinitePresentation :=
  h.of_comp_finiteType _ h'

Depends on / 依赖: FinitePresentation, RingHom, RingHom.FinitePresentation.of_finiteType, of_finiteType
-/
theorem of_finiteType [IsNoetherianRing A] {f : A ->ₐ[R] B} : f.FiniteType ↔ f.FinitePresentation :=
  RingHom.FinitePresentation.of_finiteType

nonrec theorem of_comp_finiteType (f : A ->ₐ[R] B) {g : B ->ₐ[R] C}
    (h : (g.comp f).FinitePresentation) (h' : f.FiniteType) : g.FinitePresentation :=
  h.of_comp_finiteType _ h'

end FinitePresentation

end AlgHom
