/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Jacobson.Polynomial

/-!
# Jacobson Rings

The following conditions are equivalent for a ring `R`:
1. Every radical ideal `I` is equal to its Jacobson radical
2. Every radical ideal `I` can be written as an intersection of maximal ideals
3. Every prime ideal `I` is equal to its Jacobson radical

Any ring satisfying any of these equivalent conditions is said to be Jacobson.
Some particular examples of Jacobson rings are also proven.
- `isJacobsonRing_quotient` says that the quotient of a Jacobson ring is Jacobson.
- `isJacobsonRing_localization` says the localization of a Jacobson ring
  to a single element is Jacobson.
- `isJacobsonRing_polynomial_iff_isJacobsonRing` says polynomials over a Jacobson ring
  form a Jacobson ring.

## Main definitions
Let `R` be a commutative ring. Jacobson rings are defined using the first of the above conditions
* `IsJacobsonRing R` is the proposition that `R` is a Jacobson ring. It is a class,
  implemented as the predicate that for any ideal, `I.isRadical` implies `I.jacobson = I`.

## Main statements
* `isJacobsonRing_iff_prime_eq` is the equivalence between conditions 1 and 3 above.
* `isJacobsonRing_iff_sInf_maximal` is the equivalence between conditions 1 and 2 above.
* `isJacobsonRing_of_surjective` says that if `R` is a Jacobson ring and
  `f : R →+* S` is surjective, then `S` is also a Jacobson ring
* `MvPolynomial.isJacobsonRing` says that multi-variate polynomials
  over a Jacobson ring are Jacobson.

## Tags
Jacobson, Jacobson Ring
-/

@[expose] public section

universe u

open Polynomial
open Ideal

section IsJacobsonRing

variable {R S : Type*} [CommRing R] [CommRing S] {I : Ideal R}

/--
Definition of `IsJacobsonRing` / `IsJacobsonRing` 的定义

English:
class IsJacobsonRing
  parameters: (R : Type*) [CommRing R]
  axioms and operations (1):
    - out' : forall I : Ideal R, I.IsRadical -> I.jacobson = I

中文:
类 是Jacobson环
  参数: (R : 类型) [交换环 R]
  公理与运算 (1 个):
    - out' : 对任意 I : 理想 R, I.IsRadical -> I.jacobson = I
-/
class IsJacobsonRing (R : Type*) [CommRing R] : Prop where
  out' : forall I : Ideal R, I.IsRadical -> I.jacobson = I

/--
theorem `isJacobsonRing_iff` / 定理 `isJacobsonRing_iff`

English:
theorem isJacobsonRing_iff
  given: {R} [CommRing R]
  proof: ⟨fun h => h.1, fun h => ⟨h⟩⟩

中文:
定理 isJacobsonRing_iff
  条件: {R} [交换环 R]
  证明: ⟨fun h => h.1, fun h => ⟨h⟩⟩
-/
theorem isJacobsonRing_iff {R} [CommRing R] :
    IsJacobsonRing R ↔ forall I : Ideal R, I.IsRadical -> I.jacobson = I :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/--
theorem `IsJacobsonRing.out` / 定理 `IsJacobsonRing.out`

English:
theorem IsJacobsonRing.out
  given: {R} [CommRing R]
  proof: isJacobsonRing_iff.1

中文:
定理 是Jacobson环.out
  条件: {R} [交换环 R]
  证明: isJacobsonRing_iff.1

Depends on / 依赖: isJacobsonRing_iff
-/
theorem IsJacobsonRing.out {R} [CommRing R] :
    IsJacobsonRing R -> forall {I : Ideal R}, I.IsRadical -> I.jacobson = I :=
  isJacobsonRing_iff.1

/--
theorem `isJacobsonRing_iff_prime_eq` / 定理 `isJacobsonRing_iff_prime_eq`

English:
theorem isJacobsonRing_iff_prime_eq
  proof: by
  refine isJacobsonRing_iff.trans ⟨fun h I hI => h I hI.isRadical, ?_⟩
  refine fun h I hI => le_antisymm (fun x hx => ?_) (fun x hx => mem_sInf.mpr fun _ hJ => hJ.left hx)
  rw [← hI.radical]; rw [radical_eq_sInf I]; rw [mem_sInf]
  intro P hP
  rw [Set.mem_ofPred_eq] at hP
  rw [jacobson]; rw [

中文:
定理 isJacobsonRing_iff_prime_eq
  证明: by
  refine isJacobsonRing_iff.trans ⟨fun h I hI => h I hI.isRadical, ?_⟩
  refine fun h I hI => le_antisymm (fun x hx => ?_) (fun x hx => mem_sInf.mpr fun _ hJ => hJ.left hx)
  rw [← hI.radical]; rw [radical_eq_sInf I]; rw [mem_sInf]
  intro P hP
  rw [Set.mem_ofPred_eq] at hP
  rw [jacobson]; rw [

Depends on / 依赖: Set.mem_ofPred_eq, hI.isRadical, hI.radical, hJ.left, hJ.right, hP.left, hP.right, isJacobsonRing_iff, isJacobsonRing_iff.trans, isRadical, jacobson, le_antisymm, le_trans, mem_ofPred_eq, mem_sInf, mem_sInf.mpr, radical, radical_eq_sInf
-/
theorem isJacobsonRing_iff_prime_eq :
    IsJacobsonRing R ↔ forall P : Ideal R, IsPrime P -> P.jacobson = P := by
  refine isJacobsonRing_iff.trans ⟨fun h I hI => h I hI.isRadical, ?_⟩
  refine fun h I hI => le_antisymm (fun x hx => ?_) (fun x hx => mem_sInf.mpr fun _ hJ => hJ.left hx)
  rw [← hI.radical]; rw [radical_eq_sInf I]; rw [mem_sInf]
  intro P hP
  rw [Set.mem_ofPred_eq] at hP
  rw [jacobson]; rw [mem_sInf] at hx
  rw [← h P hP.right]; rw [jacobson]; rw [mem_sInf]
  exact fun J hJ => hx ⟨le_trans hP.left hJ.left, hJ.right⟩

/--
theorem `isJacobsonRing_iff_sInf_maximal` / 定理 `isJacobsonRing_iff_sInf_maximal`

English:
theorem isJacobsonRing_iff_sInf_maximal
  statement: IsJacobsonRing R ↔ forall {I : Ideal R}, I.IsPrime ->
  proof: ⟨fun H _I h => eq_jacobson_iff_sInf_maximal.1 (H.out h.isRadical), fun H =>
    isJacobsonRing_iff_prime_eq.2 fun _P hP => eq_jacobson_iff_sInf_maximal.2 (H hP)⟩

中文:
定理 isJacobsonRing_iff_sInf_maximal
  结论: 是Jacobson环 R ↔ 对任意 {I : 理想 R}, I.是素 ->
  证明: ⟨fun H _I h => eq_jacobson_iff_sInf_maximal.1 (H.out h.isRadical), fun H =>
    isJacobsonRing_iff_prime_eq.2 fun _P hP => eq_jacobson_iff_sInf_maximal.2 (H hP)⟩

Depends on / 依赖: H.out, eq_jacobson_iff_sInf_maximal, h.isRadical, isJacobsonRing_iff_prime_eq, isRadical
-/
theorem isJacobsonRing_iff_sInf_maximal : IsJacobsonRing R ↔ forall {I : Ideal R}, I.IsPrime ->
    exists M : Set (Ideal R), (forall J in M, IsMaximal J ∨ J = ⊤) ∧ I = sInf M :=
  ⟨fun H _I h => eq_jacobson_iff_sInf_maximal.1 (H.out h.isRadical), fun H =>
    isJacobsonRing_iff_prime_eq.2 fun _P hP => eq_jacobson_iff_sInf_maximal.2 (H hP)⟩

/--
theorem `isJacobsonRing_iff_sInf_maximal'` / 定理 `isJacobsonRing_iff_sInf_maximal'`

English:
theorem isJacobsonRing_iff_sInf_maximal'
  statement: IsJacobsonRing R ↔ forall {I : Ideal R}, I.IsPrime ->
  proof: ⟨fun H _I h => eq_jacobson_iff_sInf_maximal'.1 (H.out h.isRadical), fun H =>
    isJacobsonRing_iff_prime_eq.2 fun _P hP => eq_jacobson_iff_sInf_maximal'.2 (H hP)⟩

中文:
定理 isJacobsonRing_iff_sInf_maximal'
  结论: 是Jacobson环 R ↔ 对任意 {I : 理想 R}, I.是素 ->
  证明: ⟨fun H _I h => eq_jacobson_iff_sInf_maximal'.1 (H.out h.isRadical), fun H =>
    isJacobsonRing_iff_prime_eq.2 fun _P hP => eq_jacobson_iff_sInf_maximal'.2 (H hP)⟩

Depends on / 依赖: H.out, eq_jacobson_iff_sInf_maximal, h.isRadical, isJacobsonRing_iff_prime_eq, isRadical
-/
theorem isJacobsonRing_iff_sInf_maximal' : IsJacobsonRing R ↔ forall {I : Ideal R}, I.IsPrime ->
    exists M : Set (Ideal R), (forall J in M, forall (K : Ideal R), J < K -> K = ⊤) ∧ I = sInf M :=
  ⟨fun H _I h => eq_jacobson_iff_sInf_maximal'.1 (H.out h.isRadical), fun H =>
    isJacobsonRing_iff_prime_eq.2 fun _P hP => eq_jacobson_iff_sInf_maximal'.2 (H hP)⟩

/--
theorem `Ideal.radical_eq_jacobson` / 定理 `Ideal.radical_eq_jacobson`

English:
theorem Ideal.radical_eq_jacobson
  given: [H : IsJacobsonRing R] (I : Ideal R)
  statement: I.radical = I.jacobson
  proof: le_antisymm (le_sInf fun _J ⟨hJ, hJ_max⟩ => (IsPrime.radical_le_iff hJ_max.isPrime).mpr hJ)
    (H.out (radical_isRadical I) ▸ jacobson_mono le_radical)

中文:
定理 理想.radical_eq_jacobson
  条件: [H : 是Jacobson环 R] (I : 理想 R)
  结论: I.radical = I.jacobson
  证明: le_antisymm (le_sInf fun _J ⟨hJ, hJ_max⟩ => (IsPrime.radical_le_iff hJ_max.isPrime).mpr hJ)
    (H.out (radical_isRadical I) ▸ jacobson_mono le_radical)

Depends on / 依赖: H.out, IsPrime, IsPrime.radical_le_iff, hJ_max, hJ_max.isPrime, isPrime, jacobson_mono, le_antisymm, le_radical, le_sInf, radical_isRadical, radical_le_iff
-/
theorem Ideal.radical_eq_jacobson [H : IsJacobsonRing R] (I : Ideal R) : I.radical = I.jacobson :=
  le_antisymm (le_sInf fun _J ⟨hJ, hJ_max⟩ => (IsPrime.radical_le_iff hJ_max.isPrime).mpr hJ)
    (H.out (radical_isRadical I) ▸ jacobson_mono le_radical)

instance (priority := 100) [IsArtinianRing R] : IsJacobsonRing R :=
  isJacobsonRing_iff_prime_eq.mpr fun _ _ => jacobson_eq_self_of_isMaximal

/--
theorem `isJacobsonRing_of_surjective` / 定理 `isJacobsonRing_of_surjective`

English:
theorem isJacobsonRing_of_surjective
  given: [H : IsJacobsonRing R]
  proof: by
  rintro ⟨f, hf⟩
  rw [isJacobsonRing_iff_sInf_maximal]
  intro p hp
  use map f '' { J : Ideal R | comap f p <= J ∧ J.IsMaximal }
  use fun j ⟨J, hJ, hmap⟩ => hmap ▸ (map_eq_top_or_isMaximal_of_surjective f hf hJ.right).symm
  have : p = map f (comap f p).jacobson :=
    (IsJacobsonRing.out' _ <

中文:
定理 isJacobsonRing_of_surjective
  条件: [H : 是Jacobson环 R]
  证明: by
  rintro ⟨f, hf⟩
  rw [isJacobsonRing_iff_sInf_maximal]
  intro p hp
  use map f '' { J : Ideal R | comap f p <= J ∧ J.IsMaximal }
  use fun j ⟨J, hJ, hmap⟩ => hmap ▸ (map_eq_top_or_isMaximal_of_surjective f hf hJ.right).symm
  have : p = map f (comap f p).jacobson :=
    (IsJacobsonRing.out' _ <

Depends on / 依赖: Ideal.ker_le_comap, IsJacobsonRing, IsJacobsonRing.out, IsMaximal, J.IsMaximal, hJ.right, hp.isRadical.comap, isJacobsonRing_iff_sInf_maximal, isRadical, jacobson, ker_le_comap, le_trans, map_comap_of_surjective, map_eq_top_or_isMaximal_of_surjective, map_sInf, this.trans
-/
theorem isJacobsonRing_of_surjective [H : IsJacobsonRing R] :
    (exists f : R ->+* S, Function.Surjective ↑f) -> IsJacobsonRing S := by
  rintro ⟨f, hf⟩
  rw [isJacobsonRing_iff_sInf_maximal]
  intro p hp
  use map f '' { J : Ideal R | comap f p <= J ∧ J.IsMaximal }
  use fun j ⟨J, hJ, hmap⟩ => hmap ▸ (map_eq_top_or_isMaximal_of_surjective f hf hJ.right).symm
  have : p = map f (comap f p).jacobson :=
    (IsJacobsonRing.out' _ <| hp.isRadical.comap f).symm ▸ (map_comap_of_surjective f hf p).symm
  exact this.trans (map_sInf hf fun J ⟨hJ, _⟩ => le_trans (Ideal.ker_le_comap f) hJ)

instance (priority := 100) isJacobsonRing_quotient [IsJacobsonRing R] : IsJacobsonRing (R ⧸ I) :=
  isJacobsonRing_of_surjective ⟨Ideal.Quotient.mk I, by
    rintro ⟨x⟩
    use x
    rfl⟩

/--
theorem `isJacobsonRing_iso` / 定理 `isJacobsonRing_iso`

English:
theorem isJacobsonRing_iso
  given: (e : R ≃+* S)
  statement: IsJacobsonRing R ↔ IsJacobsonRing S where
  proof: isJacobsonRing_of_surjective ⟨(e : R ->+* S), e.surjective⟩
  mpr _ := isJacobsonRing_of_surjective ⟨(e.symm : S ->+* R), e.symm.surjective⟩

中文:
定理 isJacobsonRing_iso
  条件: (e : R ≃+* S)
  结论: 是Jacobson环 R ↔ 是Jacobson环 S where
  证明: isJacobsonRing_of_surjective ⟨(e : R ->+* S), e.surjective⟩
  mpr _ := isJacobsonRing_of_surjective ⟨(e.symm : S ->+* R), e.symm.surjective⟩

Depends on / 依赖: e.surjective, isJacobsonRing_of_surjective, surjective
-/
theorem isJacobsonRing_iso (e : R ≃+* S) : IsJacobsonRing R ↔ IsJacobsonRing S where
  mp _ := isJacobsonRing_of_surjective ⟨(e : R ->+* S), e.surjective⟩
  mpr _ := isJacobsonRing_of_surjective ⟨(e.symm : S ->+* R), e.symm.surjective⟩

/--
theorem `isJacobsonRing_of_isIntegral` / 定理 `isJacobsonRing_of_isIntegral`

English:
theorem isJacobsonRing_of_isIntegral
  given: [Algebra R S] [Algebra.IsIntegral R S] [IsJacobsonRing R]
  proof: by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hP_top : comap (algebraMap R S) P = ⊤
  · simp [comap_eq_top_iff.1 hP_top]
  have : Nontrivial (R ⧸ comap (algebraMap R S) P) := by rwa [Quotient.nontrivial_iff]
  rw [jacobson_eq_iff_jacobson_quotient_eq_bot]
  refine eq_bot_of_comap_eq_

中文:
定理 isJacobsonRing_of_is整数egral
  条件: [代数 R S] [代数.是整 R S] [是Jacobson环 R]
  证明: by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hP_top : comap (algebraMap R S) P = ⊤
  · simp [comap_eq_top_iff.1 hP_top]
  have : Nontrivial (R ⧸ comap (algebraMap R S) P) := by rwa [Quotient.nontrivial_iff]
  rw [jacobson_eq_iff_jacobson_quotient_eq_bot]
  refine eq_bot_of_comap_eq_

Depends on / 依赖: Nontrivial, Quotient, Quotient.nontrivial_iff, algebraMap, comap_eq_top_iff, comap_isPrime, comap_jacobson, eq_bot_iff, eq_bot_of_comap_eq_bot, hP_top, isJacobsonRing_iff_prime_eq, jacobson_eq_iff_jacobson_quotient_eq_bot, nontrivial_iff
-/
theorem isJacobsonRing_of_isIntegral [Algebra R S] [Algebra.IsIntegral R S] [IsJacobsonRing R] :
    IsJacobsonRing S := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hP_top : comap (algebraMap R S) P = ⊤
  · simp [comap_eq_top_iff.1 hP_top]
  have : Nontrivial (R ⧸ comap (algebraMap R S) P) := by rwa [Quotient.nontrivial_iff]
  rw [jacobson_eq_iff_jacobson_quotient_eq_bot]
  refine eq_bot_of_comap_eq_bot (R := R ⧸ comap (algebraMap R S) P) ?_
  rw [eq_bot_iff]; rw [← jacobson_eq_iff_jacobson_quotient_eq_bot.1
    ((isJacobsonRing_iff_prime_eq.1 ‹_›) (comap (algebraMap R S) P) (comap_isPrime _ _))]; rw [comap_jacobson]
  refine sInf_le_sInf fun J hJ => ?_
  simp only [true_and, Set.mem_image, bot_le, Set.mem_ofPred_eq]
  have : J.IsMaximal := by simpa using hJ
  exact exists_ideal_over_maximal_of_isIntegral J
    (comap_bot_le_of_injective _ algebraMap_quotient_injective)

/--
theorem `isJacobsonRing_of_isIntegral'` / 定理 `isJacobsonRing_of_isIntegral'`

English:
theorem isJacobsonRing_of_isIntegral'
  given: (f : R ->+* S) (hf : f.IsIntegral) [IsJacobsonRing R]
  proof: let _ : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  isJacobsonRing_of_isIntegral (R := R)

中文:
定理 isJacobsonRing_of_is整数egral'
  条件: (f : R ->+* S) (hf : f.是整) [是Jacobson环 R]
  证明: let _ : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  isJacobsonRing_of_isIntegral (R := R)

Depends on / 依赖: Algebra, Algebra.IsIntegral, IsIntegral, f.toAlgebra, isJacobsonRing_of_isIntegral, toAlgebra
-/
theorem isJacobsonRing_of_isIntegral' (f : R ->+* S) (hf : f.IsIntegral) [IsJacobsonRing R] :
    IsJacobsonRing S :=
  let _ : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  isJacobsonRing_of_isIntegral (R := R)

end IsJacobsonRing

section Localization

open IsLocalization Submonoid

variable {R S : Type*} [CommRing R] [CommRing S]
variable (y : R) [Algebra R S] [IsLocalization.Away y S]

variable (S) in
/--
theorem `IsLocalization.isMaximal_iff_isMaximal_disjoint` / 定理 `IsLocalization.isMaximal_iff_isMaximal_disjoint`

English:
theorem IsLocalization.isMaximal_iff_isMaximal_disjoint
  given: [H : IsJacobsonRing R] (J : Ideal S)
  proof: by
  constructor
  · refine fun h => ⟨?_, fun hy =>
      h.ne_top (Ideal.eq_top_of_isUnit_mem _ hy (map_units _ ⟨y, Submonoid.mem_powers _⟩))⟩
    have hJ : J.IsPrime := IsMaximal.isPrime h
    rw [isPrime_iff_isPrime_disjoint (Submonoid.powers y)] at hJ
    have : y ∉ (J.under R).1 := Set.disjoint

中文:
定理 是Localization.isMaximal_iff_isMaximal_disjoint
  条件: [H : 是Jacobson环 R] (J : 理想 S)
  证明: by
  constructor
  · refine fun h => ⟨?_, fun hy =>
      h.ne_top (Ideal.eq_top_of_isUnit_mem _ hy (map_units _ ⟨y, Submonoid.mem_powers _⟩))⟩
    have hJ : J.IsPrime := IsMaximal.isPrime h
    rw [isPrime_iff_isPrime_disjoint (Submonoid.powers y)] at hJ
    have : y ∉ (J.under R).1 := Set.disjoint

Depends on / 依赖: H.out, Ideal.eq_top_of_isUnit_mem, Ideal.mem_sInf, IsMaximal, IsMaximal.isPrime, IsPrime, J.IsPrime, J.under, Set.disjoint_left, Submodule, Submodule.mem_toAddSubmonoid, Submonoid, Submonoid.mem_powers, Submonoid.powers, convert, disjoint_left, eq_top_of_isUnit_mem, h.ne_top, hJ.left.isRadical, hJ.right
-/
theorem IsLocalization.isMaximal_iff_isMaximal_disjoint [H : IsJacobsonRing R] (J : Ideal S) :
    J.IsMaximal ↔ (J.under R).IsMaximal ∧ y ∉ J.under R := by
  constructor
  · refine fun h => ⟨?_, fun hy =>
      h.ne_top (Ideal.eq_top_of_isUnit_mem _ hy (map_units _ ⟨y, Submonoid.mem_powers _⟩))⟩
    have hJ : J.IsPrime := IsMaximal.isPrime h
    rw [isPrime_iff_isPrime_disjoint (Submonoid.powers y)] at hJ
    have : y ∉ (J.under R).1 := Set.disjoint_left.1 hJ.right (Submonoid.mem_powers _)
    rw [← H.out hJ.left.isRadical]; rw [jacobson]; rw [Submodule.mem_toAddSubmonoid]; rw [Ideal.mem_sInf] at this
    push Not at this
    rcases this with ⟨I, ⟨hJI, hIm⟩, hI'⟩
    convert! hIm
    by_cases hJ : J = I.map (algebraMap R S)
    · rw [hJ, under_map_of_isPrime_disjoint (powers y) S hIm.isPrime]
      rwa [disjoint_powers_iff_notMem_of_isPrime]
    · have hI_p : (I.map (algebraMap R S)).IsPrime := by
        refine isPrime_of_isPrime_disjoint (powers y) _ I hIm.isPrime ?_
        rwa [disjoint_powers_iff_notMem_of_isPrime]
      have : J <= I.map (algebraMap R S) := map_under (Submonoid.powers y) S J ▸ map_mono hJI
      exact absurd (h.1.2 _ (lt_of_le_of_ne this hJ)) hI_p.1
  · simp only [Ideal.mem_comap, and_imp]
    exact (fun _ _ => IsMaximal.of_isLocalization_of_disjoint (powers y))

/--
theorem `IsLocalization.isMaximal_of_isMaximal_disjoint` / 定理 `IsLocalization.isMaximal_of_isMaximal_disjoint`

English:
theorem IsLocalization.isMaximal_of_isMaximal_disjoint
  proof: by
  rw [isMaximal_iff_isMaximal_disjoint S y]; rw [under_map_of_isPrime_disjoint (powers y) S hI.isPrime]
  · exact ⟨hI, hy⟩
  · rwa [disjoint_powers_iff_notMem_of_isPrime]

中文:
定理 是Localization.isMaximal_of_isMaximal_disjoint
  证明: by
  rw [isMaximal_iff_isMaximal_disjoint S y]; rw [under_map_of_isPrime_disjoint (powers y) S hI.isPrime]
  · exact ⟨hI, hy⟩
  · rwa [disjoint_powers_iff_notMem_of_isPrime]

Depends on / 依赖: disjoint_powers_iff_notMem_of_isPrime, hI.isPrime, isMaximal_iff_isMaximal_disjoint, isPrime, powers, under_map_of_isPrime_disjoint
-/
theorem IsLocalization.isMaximal_of_isMaximal_disjoint
    [IsJacobsonRing R] (I : Ideal R) (hI : I.IsMaximal)
    (hy : y ∉ I) : (I.map (algebraMap R S)).IsMaximal := by
  rw [isMaximal_iff_isMaximal_disjoint S y]; rw [under_map_of_isPrime_disjoint (powers y) S hI.isPrime]
  · exact ⟨hI, hy⟩
  · rwa [disjoint_powers_iff_notMem_of_isPrime]

/--
Definition of `IsLocalization.orderIsoOfMaximal` / `IsLocalization.orderIsoOfMaximal` 的定义

English:
definition IsLocalization.orderIsoOfMaximal
  signature: [IsJacobsonRing R]
  body: ⟨Ideal.comap (algebraMap R S) p.1, (isMaximal_iff_isMaximal_disjoint S y p.1).1 p.2⟩
  invFun p := ⟨Ideal.map (algebraMap R S) p.1, isMaximal_of_isMaximal_disjoint y p.1 p.2.1 p.2.2⟩
  left_inv J := Subtype.ext (map_under (powers y) S J)
right_inv := fun ⟨_, hIm, hI⟩ => Subtype.ext under_map_of_isPr

中文:
定义 是Localization.orderIsoOfMaximal
  签名: [是Jacobson环 R]
  定义体: ⟨Ideal.comap (algebraMap R S) p.1, (isMaximal_iff_isMaximal_disjoint S y p.1).1 p.2⟩
  invFun p := ⟨Ideal.map (algebraMap R S) p.1, isMaximal_of_isMaximal_disjoint y p.1 p.2.1 p.2.2⟩
  left_inv J := Subtype.ext (map_under (powers y) S J)
right_inv := fun ⟨_, hIm, hI⟩ => Subtype.ext under_map_of_isPr

Depends on / 依赖: Ideal.comap, algebraMap, isMaximal_iff_isMaximal_disjoint
-/
def IsLocalization.orderIsoOfMaximal [IsJacobsonRing R] :
    { p : Ideal S // p.IsMaximal } ≃o { p : Ideal R // p.IsMaximal ∧ y ∉ p } where
  toFun p := ⟨Ideal.comap (algebraMap R S) p.1, (isMaximal_iff_isMaximal_disjoint S y p.1).1 p.2⟩
  invFun p := ⟨Ideal.map (algebraMap R S) p.1, isMaximal_of_isMaximal_disjoint y p.1 p.2.1 p.2.2⟩
  left_inv J := Subtype.ext (map_under (powers y) S J)
right_inv := fun ⟨_, hIm, hI⟩ => Subtype.ext under_map_of_isPrime_disjoint _ S hIm.isPrime
    ((disjoint_powers_iff_notMem_of_isPrime y).2 hI)
  map_rel_iff' {I I'} := ⟨fun h => show I.val <= I'.val from
    map_under (powers y) S I.val ▸ map_under (powers y) S I'.val ▸ Ideal.map_mono h,
    fun h _ hx => h hx⟩

include y in
/--
theorem `isJacobsonRing_localization` / 定理 `isJacobsonRing_localization`

English:
theorem isJacobsonRing_localization
  given: [H : IsJacobsonRing R]
  statement: IsJacobsonRing S
  proof: by
  rw [isJacobsonRing_iff_prime_eq]
  refine fun P' hP' => le_antisymm ?_ le_jacobson
  obtain ⟨hP', hPM⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint (powers y) S P').mp hP'
  have hP := H.out hP'.isRadical
  refine (IsLocalization.map_under (powers y) S P'.jacobson).ge.trans
    ((map_mono ?_

中文:
定理 isJacobsonRing_localization
  条件: [H : 是Jacobson环 R]
  结论: 是Jacobson环 S
  证明: by
  rw [isJacobsonRing_iff_prime_eq]
  refine fun P' hP' => le_antisymm ?_ le_jacobson
  obtain ⟨hP', hPM⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint (powers y) S P').mp hP'
  have hP := H.out hP'.isRadical
  refine (IsLocalization.map_under (powers y) S P'.jacobson).ge.trans
    ((map_mono ?_

Depends on / 依赖: H.out, I.IsMaximal, IsLocalization, IsLocalization.isPrime_iff_isPrime_disjoint, IsLocalization.map_under, IsMaximal, algebraMap, ge.trans, isJacobsonRing_iff_prime_eq, isPrime_iff_isPrime_disjoint, isRadical, jacobson, le_antisymm, le_jacobson, map_mono, map_under, powers
-/
theorem isJacobsonRing_localization [H : IsJacobsonRing R] : IsJacobsonRing S := by
  rw [isJacobsonRing_iff_prime_eq]
  refine fun P' hP' => le_antisymm ?_ le_jacobson
  obtain ⟨hP', hPM⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint (powers y) S P').mp hP'
  have hP := H.out hP'.isRadical
  refine (IsLocalization.map_under (powers y) S P'.jacobson).ge.trans
    ((map_mono ?_).trans (IsLocalization.map_under (powers y) S P').le)
  have : sInf { I : Ideal R | comap (algebraMap R S) P' <= I ∧ I.IsMaximal ∧ y ∉ I } <=
      comap (algebraMap R S) P' := by
    intro x hx
    have hxy : x * y in (comap (algebraMap R S) P').jacobson := by
      rw [Ideal.jacobson]; rw [Ideal.mem_sInf]
      intro J hJ
      by_cases h : y in J
      · exact J.mul_mem_left x h
      · exact J.mul_mem_right y ((mem_sInf.1 hx) ⟨hJ.left, ⟨hJ.right, h⟩⟩)
    rw [hP] at hxy
    rcases hP'.mem_or_mem hxy with hxy | hxy
    · exact hxy
    · exact (hPM.le_bot ⟨Submonoid.mem_powers _, hxy⟩).elim
  refine le_trans ?_ this
  rw [Ideal.jacobson]; rw [under_def]; rw [comap_sInf']; rw [sInf_eq_iInf]
  refine iInf_le_iInf_of_subset fun I ⟨hI, hIm, hyI⟩ => ⟨map (algebraMap R S) I, ⟨?_, ?_⟩⟩
  · exact ⟨le_trans (IsLocalization.map_under (powers y) S P').symm.le (map_mono hI),
      isMaximal_of_isMaximal_disjoint y I hIm hyI⟩
· exact IsLocalization.under_map_of_isPrime_disjoint _ S hIm.isPrime
      (disjoint_powers_iff_notMem_of_isPrime y).2 hyI

end Localization

namespace Polynomial

section CommRing

-- Porting note: move to better place
/--
lemma `mem_closure_X_union_C` / 引理 `mem_closure_X_union_C`

English:
lemma mem_closure_X_union_C
  given: {R : Type*} [Ring R] (p : R[X])
  proof: by
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro r
    apply Subring.subset_closure
    apply Set.mem_insert_of_mem
    exact degree_C_le
  · intro p1 p2 h1 h2
    exact Subring.add_mem _ h1 h2
  · intro n r hr
    rw [pow_succ]; rw [← mul_assoc]
    apply Subring.mul_mem _ hr
    apply Subr

中文:
引理 mem_closure_X_union_C
  条件: {R : 类型} [环 R] (p : R[X])
  证明: by
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro r
    apply Subring.subset_closure
    apply Set.mem_insert_of_mem
    exact degree_C_le
  · intro p1 p2 h1 h2
    exact Subring.add_mem _ h1 h2
  · intro n r hr
    rw [pow_succ]; rw [← mul_assoc]
    apply Subring.mul_mem _ hr
    apply Subr

Depends on / 依赖: Polynomial, Polynomial.induction_on, Set.mem_insert, Set.mem_insert_of_mem, Subring, Subring.add_mem, Subring.mul_mem, Subring.subset_closure, add_mem, degree_C_le, induction_on, mem_insert, mem_insert_of_mem, mul_assoc, mul_mem, pow_succ, subset_closure
-/
lemma mem_closure_X_union_C {R : Type*} [Ring R] (p : R[X]) :
    p in Subring.closure (insert X {f | f.degree <= 0} : Set R[X]) := by
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro r
    apply Subring.subset_closure
    apply Set.mem_insert_of_mem
    exact degree_C_le
  · intro p1 p2 h1 h2
    exact Subring.add_mem _ h1 h2
  · intro n r hr
    rw [pow_succ]; rw [← mul_assoc]
    apply Subring.mul_mem _ hr
    apply Subring.subset_closure
    apply Set.mem_insert

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
variable {Rₘ Sₘ : Type*} [CommRing Rₘ] [CommRing Sₘ]

/--
theorem `isIntegral_isLocalization_polynomial_quotient` / 定理 `isIntegral_isLocalization_polynomial_quotient`

English:
theorem isIntegral_isLocalization_polynomial_quotient
  proof: by
  let P' : Ideal R := P.comap C
  let M : Submonoid (R ⧸ P') :=
    Submonoid.powers (pX.map (Ideal.Quotient.mk (P.comap (C : R ->+* R[X])))).leadingCoeff
  let M' : Submonoid (R[X] ⧸ P) :=
    (Submonoid.powers (pX.map (Ideal.Quotient.mk (P.comap (C : R ->+* R[X])))).leadingCoeff).map
      (quo

中文:
定理 is整数egral_isLocalization_polynomial_quotient
  证明: by
  let P' : Ideal R := P.comap C
  let M : Submonoid (R ⧸ P') :=
    Submonoid.powers (pX.map (Ideal.Quotient.mk (P.comap (C : R ->+* R[X])))).leadingCoeff
  let M' : Submonoid (R[X] ⧸ P) :=
    (Submonoid.powers (pX.map (Ideal.Quotient.mk (P.comap (C : R ->+* R[X])))).leadingCoeff).map
      (quo

Depends on / 依赖: Ideal.Quotient.mk, IsLocalization, IsLocalization.map, M.le_comap_map, P.comap, Quotient, Submonoid, Submonoid.powers, le_comap_map, le_rfl, leadingCoeff, pX.map, powers, quotientMap
-/
theorem isIntegral_isLocalization_polynomial_quotient
    (P : Ideal R[X]) (pX : R[X]) (hpX : pX in P) [Algebra (R ⧸ P.comap (C : R ->+* R[X])) Rₘ]
    [IsLocalization.Away (pX.map (Ideal.Quotient.mk (P.comap (C : R ->+* R[X])))).leadingCoeff Rₘ]
    [Algebra (R[X] ⧸ P) Sₘ] [IsLocalization ((Submonoid.powers (pX.map (Ideal.Quotient.mk (P.comap
      (C : R ->+* R[X])))).leadingCoeff).map (quotientMap P C le_rfl) : Submonoid (R[X] ⧸ P)) Sₘ] :
    (IsLocalization.map Sₘ (quotientMap P C le_rfl) (Submonoid.powers (pX.map (Ideal.Quotient.mk
      (P.comap (C : R ->+* R[X])))).leadingCoeff).le_comap_map : Rₘ ->+* Sₘ).IsIntegral := by
  let P' : Ideal R := P.comap C
  let M : Submonoid (R ⧸ P') :=
    Submonoid.powers (pX.map (Ideal.Quotient.mk (P.comap (C : R ->+* R[X])))).leadingCoeff
  let M' : Submonoid (R[X] ⧸ P) :=
    (Submonoid.powers (pX.map (Ideal.Quotient.mk (P.comap (C : R ->+* R[X])))).leadingCoeff).map
      (quotientMap P C le_rfl)
  let φ : R ⧸ P' ->+* R[X] ⧸ P := quotientMap P C le_rfl
  let φ' : Rₘ ->+* Sₘ := IsLocalization.map Sₘ φ M.le_comap_map
  have hφ' : φ.comp (Ideal.Quotient.mk P') = (Ideal.Quotient.mk P).comp C := rfl
  intro p
  obtain ⟨⟨p', ⟨q, hq⟩⟩, hp⟩ := IsLocalization.surj M' p
  suffices φ'.IsIntegralElem (algebraMap (R[X] ⧸ P) Sₘ p') by
    obtain ⟨q', hq', rfl⟩ := hq
    obtain ⟨q'', hq''⟩ := isUnit_iff_exists_inv'.1 (IsLocalization.map_units Rₘ (⟨q', hq'⟩ : M))
    refine (hp.symm ▸ this).of_mul_unit φ' p (algebraMap (R[X] ⧸ P) Sₘ (φ q')) q'' ?_
    rw [← φ'.map_one]; rw [← congr_arg φ' hq'']; rw [φ'.map_mul]; rw [← φ'.comp_apply]
    simp only [φ', IsLocalization.map_comp _, RingHom.comp_apply]
  dsimp at hp
  refine @IsIntegral.of_mem_closure'' Rₘ _ Sₘ _ φ'
    ((algebraMap (R[X] ⧸ P) Sₘ).comp (Ideal.Quotient.mk P) '' insert X { p | p.degree <= 0 }) ?_
    ((algebraMap (R[X] ⧸ P) Sₘ) p') ?_
  · rintro x ⟨p, hp, rfl⟩
    push _ in _ at hp
    rcases hp with hy | hy
    · rw [hy]
      refine φ.isIntegralElem_localization_at_leadingCoeff ((Ideal.Quotient.mk P) X)
        (pX.map (Ideal.Quotient.mk P')) ?_ M ?_
      · rwa [eval₂_map, hφ', ← hom_eval₂, Quotient.eq_zero_iff_mem, eval₂_C_X]
      · use 1
        simp only [P', pow_one]
    · rw [degree_le_zero_iff] at hy
      rw [hy]
      refine ⟨X - C (algebraMap _ _ ((Ideal.Quotient.mk P') (p.coeff 0))), monic_X_sub_C _, ?_⟩
      simp only [eval₂_sub, eval₂_X, eval₂_C]
      rw [sub_eq_zero]; rw [← φ'.comp_apply]
      simp [φ', IsLocalization.map_comp _, P', φ]
  · obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p'
    rw [← RingHom.comp_apply]
    apply Subring.mem_closure_image_of
    apply Polynomial.mem_closure_X_union_C

/--
theorem `jacobson_bot_of_integral_localization` / 定理 `jacobson_bot_of_integral_localization`

English:
theorem jacobson_bot_of_integral_localization
  proof: by
  have hM : ((Submonoid.powers x).map φ : Submonoid S) <= nonZeroDivisors S :=
    map_le_nonZeroDivisors_of_injective φ hφ (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
  let : IsDomain Sₘ := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  let φ' : Rₘ ->+* Sₘ := IsLocalization.map _ φ (S

中文:
定理 jacobson_bot_of_integral_localization
  证明: by
  have hM : ((Submonoid.powers x).map φ : Submonoid S) <= nonZeroDivisors S :=
    map_le_nonZeroDivisors_of_injective φ hφ (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
  let : IsDomain Sₘ := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  let φ' : Rₘ ->+* Sₘ := IsLocalization.map _ φ (S

Depends on / 依赖: I.IsMaximal, I.comap, IsDomain, IsLocalization, IsLocalization.isDomain_of_le_nonZeroDivisors, IsLocalization.map, IsMaximal, RingHom, RingHom.ker_eq, Submonoid, Submonoid.powers, algebraMap, isDomain_of_le_nonZeroDivisors, ker_eq, le_comap_map, map_le_nonZeroDivisors_of_injective, nonZeroDivisors, powers, powers_le_nonZeroDivisors_of_noZeroDivisors
-/
theorem jacobson_bot_of_integral_localization
    {R : Type*} [CommRing R] [IsDomain R] [IsJacobsonRing R]
    (Rₘ Sₘ : Type*) [CommRing Rₘ] [CommRing Sₘ] (φ : R ->+* S) (hφ : Function.Injective ↑φ) (x : R)
    (hx : x != 0) [Algebra R Rₘ] [IsLocalization.Away x Rₘ] [Algebra S Sₘ]
    [IsLocalization ((Submonoid.powers x).map φ : Submonoid S) Sₘ]
    (hφ' :
      RingHom.IsIntegral (IsLocalization.map Sₘ φ (Submonoid.powers x).le_comap_map : Rₘ ->+* Sₘ)) :
    (⊥ : Ideal S).jacobson = (⊥ : Ideal S) := by
  have hM : ((Submonoid.powers x).map φ : Submonoid S) <= nonZeroDivisors S :=
    map_le_nonZeroDivisors_of_injective φ hφ (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
  let : IsDomain Sₘ := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  let φ' : Rₘ ->+* Sₘ := IsLocalization.map _ φ (Submonoid.powers x).le_comap_map
  suffices forall I : Ideal Sₘ, I.IsMaximal -> (I.comap (algebraMap S Sₘ)).IsMaximal by
    have hϕ' : comap (algebraMap S Sₘ) (⊥ : Ideal Sₘ) = (⊥ : Ideal S) := by
      rw [← RingHom.ker_eq_comap_bot]; rw [← RingHom.injective_iff_ker_eq_bot]
      exact IsLocalization.injective Sₘ hM
    have hRₘ : IsJacobsonRing Rₘ := isJacobsonRing_localization x
    have hSₘ : IsJacobsonRing Sₘ := isJacobsonRing_of_isIntegral' φ' hφ'
    refine eq_bot_iff.mpr (le_trans ?_ (le_of_eq hϕ'))
    rw [← hSₘ.out isRadical_bot]; rw [comap_jacobson]
    exact sInf_le_sInf fun j hj => ⟨bot_le,
      let ⟨J, hJ⟩ := hj
      hJ.2 ▸ this J hJ.1.2⟩
  intro I hI
  -- Remainder of the proof is pulling and pushing ideals around the square and the quotient square
  have : (I.comap (algebraMap S Sₘ)).IsPrime := comap_isPrime _ I
  have : (I.comap φ').IsPrime := comap_isPrime φ' I
  have : (⊥ : Ideal (S ⧸ I.comap (algebraMap S Sₘ))).IsPrime := isPrime_bot
  have hcomm : φ'.comp (algebraMap R Rₘ) = (algebraMap S Sₘ).comp φ := IsLocalization.map_comp _
  let f := quotientMap (I.comap (algebraMap S Sₘ)) φ le_rfl
  let g := quotientMap I (algebraMap S Sₘ) le_rfl
  have := isMaximal_comap_of_isIntegral_of_isMaximal' φ' hφ' I
  have := ((IsLocalization.isMaximal_iff_isMaximal_disjoint Rₘ x _).1 this).left
  have : ((I.comap (algebraMap S Sₘ)).comap φ).IsMaximal := by
    rwa [under_def, comap_comap, hcomm, ← comap_comap] at this
  rw [← bot_quotient_isMaximal_iff] at this ⊢
  refine isMaximal_of_isIntegral_of_isMaximal_comap' f ?_ ⊥
    ((eq_bot_iff.2 (comap_bot_le_of_injective f quotientMap_injective)).symm ▸ this)
  apply RingHom.IsIntegral.tower_bot f g quotientMap_injective
  rw [comp_quotientMap_eq_of_comp_eq hcomm]
  refine RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ ?_) (hφ'.quotient _)
  apply IsLocalization.surjective_quotientMap_of_maximal_of_localization (Submonoid.powers x)
  rwa [under_def, comap_comap, hcomm, ← bot_quotient_isMaximal_iff]

/--
theorem `isJacobsonRing_polynomial_of_domain` / 定理 `isJacobsonRing_polynomial_of_domain`

English:
theorem isJacobsonRing_polynomial_of_domain
  statement: (R : Type*) [CommRing R] [IsDomain R]
  proof: by
  by_cases Pb : P = ⊥
  · exact Pb.symm ▸
      jacobson_bot_polynomial_of_jacobson_bot (hR.out isRadical_bot)
  · rw [jacobson_eq_iff_jacobson_quotient_eq_bot]
    let P' := P.comap (C : R ->+* R[X])
    have : P'.IsPrime := comap_isPrime C P
    have hR' : IsJacobsonRing (R ⧸ P') := by infer_in

中文:
定理 isJacobsonRing_polynomial_of_domain
  结论: (R : 类型) [交换环 R] [是整环 R]
  证明: by
  by_cases Pb : P = ⊥
  · exact Pb.symm ▸
      jacobson_bot_polynomial_of_jacobson_bot (hR.out isRadical_bot)
  · rw [jacobson_eq_iff_jacobson_quotient_eq_bot]
    let P' := P.comap (C : R ->+* R[X])
    have : P'.IsPrime := comap_isPrime C P
    have hR' : IsJacobsonRing (R ⧸ P') := by infer_in
-/
private theorem isJacobsonRing_polynomial_of_domain (R : Type*) [CommRing R] [IsDomain R]
    [hR : IsJacobsonRing R] (P : Ideal R[X]) [IsPrime P] (hP : forall x : R, C x in P -> x = 0) :
    P.jacobson = P := by
  by_cases Pb : P = ⊥
  · exact Pb.symm ▸
      jacobson_bot_polynomial_of_jacobson_bot (hR.out isRadical_bot)
  · rw [jacobson_eq_iff_jacobson_quotient_eq_bot]
    let P' := P.comap (C : R ->+* R[X])
    have : P'.IsPrime := comap_isPrime C P
    have hR' : IsJacobsonRing (R ⧸ P') := by infer_instance
    obtain ⟨p, pP, p0⟩ := exists_nonzero_mem_of_ne_bot Pb hP
    let x := (Polynomial.map (Ideal.Quotient.mk P') p).leadingCoeff
    have hx : x != 0 := by rwa [Ne, leadingCoeff_eq_zero]
    let φ : R ⧸ P' ->+* R[X] ⧸ P := Ideal.quotientMap P (C : R ->+* R[X]) le_rfl
    let hφ : Function.Injective ↑φ := quotientMap_injective
    let Rₘ := Localization.Away x
    let Sₘ := (Localization ((Submonoid.powers x).map φ : Submonoid (R[X] ⧸ P)))
    refine jacobson_bot_of_integral_localization (S := R[X] ⧸ P) (R := R ⧸ P') Rₘ Sₘ _ hφ _ hx ?_
    exact isIntegral_isLocalization_polynomial_quotient P p pP

/--
theorem `isJacobsonRing_polynomial_of_isJacobsonRing` / 定理 `isJacobsonRing_polynomial_of_isJacobsonRing`

English:
theorem isJacobsonRing_polynomial_of_isJacobsonRing
  given: (hR : IsJacobsonRing R)
  proof: by
  rw [isJacobsonRing_iff_prime_eq]
  intro I hI
  let R' : Subring (R[X] ⧸ I) := ((Ideal.Quotient.mk I).comp C).range
  let i : R ->+* R' := ((Ideal.Quotient.mk I).comp C).rangeRestrict
  have hi : Function.Surjective ↑i := ((Ideal.Quotient.mk I).comp C).rangeRestrict_surjective
  have hi' : Ring

中文:
定理 isJacobsonRing_polynomial_of_isJacobsonRing
  条件: (hR : 是Jacobson环 R)
  证明: by
  rw [isJacobsonRing_iff_prime_eq]
  intro I hI
  let R' : Subring (R[X] ⧸ I) := ((Ideal.Quotient.mk I).comp C).range
  let i : R ->+* R' := ((Ideal.Quotient.mk I).comp C).rangeRestrict
  have hi : Function.Surjective ↑i := ((Ideal.Quotient.mk I).comp C).rangeRestrict_surjective
  have hi' : Ring

Depends on / 依赖: Function, Function.Surjective, Ideal.Quotient.mk, Polynomial, Quotient, RingHom, RingHom.ker, Subring, Surjective, g.coeff, isJacobsonRing_iff_prime_eq, mapRingHom, polynomial_mem_ideal_of_coeff_mem_ideal, rangeRestrict, rangeRestrict_surjective, replace
-/
theorem isJacobsonRing_polynomial_of_isJacobsonRing (hR : IsJacobsonRing R) :
    IsJacobsonRing R[X] := by
  rw [isJacobsonRing_iff_prime_eq]
  intro I hI
  let R' : Subring (R[X] ⧸ I) := ((Ideal.Quotient.mk I).comp C).range
  let i : R ->+* R' := ((Ideal.Quotient.mk I).comp C).rangeRestrict
  have hi : Function.Surjective ↑i := ((Ideal.Quotient.mk I).comp C).rangeRestrict_surjective
  have hi' : RingHom.ker (mapRingHom i) <= I := by
    intro f hf
    apply polynomial_mem_ideal_of_coeff_mem_ideal I f
    intro n
    replace hf := congrArg (fun g : Polynomial ((Ideal.Quotient.mk I).comp C).range => g.coeff n) hf
    change (Polynomial.map ((Ideal.Quotient.mk I).comp C).rangeRestrict f).coeff n = 0 at hf
    rw [coeff_map]; rw [Subtype.ext_iff] at hf
    rwa [mem_comap, ← Quotient.eq_zero_iff_mem, ← RingHom.comp_apply]
  have R'_jacob : IsJacobsonRing R' := isJacobsonRing_of_surjective ⟨i, hi⟩
  let J := I.map (mapRingHom i)
  have h_surj : Function.Surjective (mapRingHom i) := Polynomial.map_surjective i hi
  have : IsPrime J := map_isPrime_of_surjective h_surj hi'
  suffices h : J.jacobson = J by
    replace h := congrArg (comap (Polynomial.mapRingHom i)) h
    rw [← map_jacobson_of_surjective h_surj hi']; rw [comap_map_of_surjective _ h_surj]; rw [comap_map_of_surjective _ h_surj] at h
    refine le_antisymm ?_ le_jacobson
    exact le_trans (le_sup_of_le_left le_rfl) (le_trans (le_of_eq h) (sup_le le_rfl hi'))
  apply isJacobsonRing_polynomial_of_domain R' J
  exact eq_zero_of_polynomial_mem_map_range I

/--
theorem `isJacobsonRing_polynomial_iff_isJacobsonRing` / 定理 `isJacobsonRing_polynomial_iff_isJacobsonRing`

English:
theorem isJacobsonRing_polynomial_iff_isJacobsonRing
  statement: IsJacobsonRing R[X] ↔ IsJacobsonRing R
  proof: by
  refine ⟨?_, isJacobsonRing_polynomial_of_isJacobsonRing⟩
  intro H
  exact isJacobsonRing_of_surjective ⟨eval₂RingHom (RingHom.id _) 1, fun x =>
    ⟨C x, by simp only [coe_eval₂RingHom, RingHom.id_apply, eval₂_C]⟩⟩

中文:
定理 isJacobsonRing_polynomial_iff_isJacobsonRing
  结论: 是Jacobson环 R[X] ↔ 是Jacobson环 R
  证明: by
  refine ⟨?_, isJacobsonRing_polynomial_of_isJacobsonRing⟩
  intro H
  exact isJacobsonRing_of_surjective ⟨eval₂RingHom (RingHom.id _) 1, fun x =>
    ⟨C x, by simp only [coe_eval₂RingHom, RingHom.id_apply, eval₂_C]⟩⟩

Depends on / 依赖: RingHom, RingHom.id, RingHom.id_apply, id_apply, isJacobsonRing_of_surjective, isJacobsonRing_polynomial_of_isJacobsonRing
-/
theorem isJacobsonRing_polynomial_iff_isJacobsonRing : IsJacobsonRing R[X] ↔ IsJacobsonRing R := by
  refine ⟨?_, isJacobsonRing_polynomial_of_isJacobsonRing⟩
  intro H
  exact isJacobsonRing_of_surjective ⟨eval₂RingHom (RingHom.id _) 1, fun x =>
    ⟨C x, by simp only [coe_eval₂RingHom, RingHom.id_apply, eval₂_C]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsJacobsonRing
  signature: R] : IsJacobsonRing R[X]
  body: isJacobsonRing_polynomial_iff_isJacobsonRing.mpr ‹IsJacobsonRing R›

中文:
实例 [是Jacobson环
  签名: R] : 是Jacobson环 R[X]
  定义体: isJacobsonRing_polynomial_iff_isJacobsonRing.mpr ‹IsJacobsonRing R›

Depends on / 依赖: IsJacobsonRing, isJacobsonRing_polynomial_iff_isJacobsonRing, isJacobsonRing_polynomial_iff_isJacobsonRing.mpr
-/
instance [IsJacobsonRing R] : IsJacobsonRing R[X] :=
  isJacobsonRing_polynomial_iff_isJacobsonRing.mpr ‹IsJacobsonRing R›

end CommRing

section

variable {R : Type*} [CommRing R]
variable (P : Ideal R[X]) [hP : P.IsMaximal]

/--
theorem `isMaximal_comap_C_of_isMaximal` / 定理 `isMaximal_comap_C_of_isMaximal`

English:
theorem isMaximal_comap_C_of_isMaximal
  statement: [IsJacobsonRing R] [Nontrivial R]
  proof: by
  let P' := comap (C : R ->+* R[X]) P
  have hP'_prime : P'.IsPrime := comap_isPrime C P
  obtain ⟨⟨m, hmem_P⟩, hm⟩ :=
    Submodule.nonzero_mem_of_bot_lt (bot_lt_of_maximal P (Polynomial.not_isField R))
  have hm' : m != 0 := by
    simpa [Submodule.coe_eq_zero] using hm
  let φ : R ⧸ P' ->+* R[

中文:
定理 isMaximal_comap_C_of_isMaximal
  结论: [是Jacobson环 R] [非平凡 R]
  证明: by
  let P' := comap (C : R ->+* R[X]) P
  have hP'_prime : P'.IsPrime := comap_isPrime C P
  obtain ⟨⟨m, hmem_P⟩, hm⟩ :=
    Submodule.nonzero_mem_of_bot_lt (bot_lt_of_maximal P (Polynomial.not_isField R))
  have hm' : m != 0 := by
    simpa [Submodule.coe_eq_zero] using hm
  let φ : R ⧸ P' ->+* R[

Depends on / 依赖: Ideal.Quotient.mk, IsPrime, Polynomial, Polynomial.not_isField, Quotient, Submodule, Submodule.coe_eq_zero, Submodule.nonzero_mem_of_bot_lt, Submonoid, Submonoid.powers, _prime, bot_lt_of_maximal, bot_quotient_isMaximal_iff, coe_eq_zero, comap_isPrime, hmem_P, le_rfl, leadingCoeff, m.map, nonzero_mem_of_bot_lt
-/
theorem isMaximal_comap_C_of_isMaximal [IsJacobsonRing R] [Nontrivial R]
    (hP' : forall x : R, C x in P -> x = 0) :
    IsMaximal (comap (C : R ->+* R[X]) P : Ideal R) := by
  let P' := comap (C : R ->+* R[X]) P
  have hP'_prime : P'.IsPrime := comap_isPrime C P
  obtain ⟨⟨m, hmem_P⟩, hm⟩ :=
    Submodule.nonzero_mem_of_bot_lt (bot_lt_of_maximal P (Polynomial.not_isField R))
  have hm' : m != 0 := by
    simpa [Submodule.coe_eq_zero] using hm
  let φ : R ⧸ P' ->+* R[X] ⧸ P := quotientMap P (C : R ->+* R[X]) le_rfl
  let a : R ⧸ P' := (m.map (Ideal.Quotient.mk P')).leadingCoeff
  let M : Submonoid (R ⧸ P') := Submonoid.powers a
  rw [← bot_quotient_isMaximal_iff]
  have hp0 : a != 0 := fun hp0' =>
hm' map_injective (Ideal.Quotient.mk (P.comap (C : R ->+* R[X]) : Ideal R))
      ((injective_iff_map_eq_zero (Ideal.Quotient.mk (P.comap (C : R ->+* R[X]) : Ideal R))).2
        fun x hx => by
          rwa [Quotient.eq_zero_iff_mem, (by rwa [eq_bot_iff] : (P.comap C : Ideal R) = ⊥)] at hx)
        (by simpa only [a, leadingCoeff_eq_zero, Polynomial.map_zero] using hp0')
  have hM : (0 : R ⧸ P') ∉ M := fun ⟨n, hn⟩ => hp0 (eq_zero_of_pow_eq_zero hn)
  suffices (⊥ : Ideal (Localization M)).IsMaximal by
    rw [← IsLocalization.under_map_of_isPrime_disjoint M (Localization M) isPrime_bot
      (disjoint_iff_inf_le.mpr fun x hx => hM (hx.2 ▸ hx.1))]
    exact ((IsLocalization.isMaximal_iff_isMaximal_disjoint (Localization M) a _).mp
      (by rwa [Ideal.map_bot])).1
  let M' : Submonoid (R[X] ⧸ P) := M.map φ
  have hM' : (0 : R[X] ⧸ P) ∉ M' := fun ⟨z, hz⟩ =>
    hM (quotientMap_injective (_root_.trans hz.2 φ.map_zero.symm) ▸ hz.1)
  suffices (⊥ : Ideal (Localization M')).IsMaximal by
    rw [le_antisymm bot_le (comap_bot_le_of_injective _
      (IsLocalization.map_injective_of_injective M (Localization M) (Localization M')
        quotientMap_injective))]
    refine isMaximal_comap_of_isIntegral_of_isMaximal' _ ?_ ⊥
    have isloc : IsLocalization (Submonoid.map φ M) (Localization M') := by infer_instance
    exact @isIntegral_isLocalization_polynomial_quotient R _
      (Localization M) (Localization M') _ _ P m hmem_P _ _ _ isloc
  rw [(map_bot.symm :
    (⊥ : Ideal (Localization M')) = Ideal.map (algebraMap (R[X] ⧸ P) (Localization M')) ⊥)]
  let bot_maximal := (bot_quotient_isMaximal_iff _).mpr hP
  refine bot_maximal.map_bijective (algebraMap (R[X] ⧸ P) (Localization M')) ?_
  apply IsField.localization_map_bijective hM'
  rwa [← Quotient.maximal_ideal_iff_isField_quotient, ← bot_quotient_isMaximal_iff]

/--
theorem `quotient_mk_comp_C_isIntegral_of_jacobson'` / 定理 `quotient_mk_comp_C_isIntegral_of_jacobson'`

English:
theorem quotient_mk_comp_C_isIntegral_of_jacobson'
  statement: [Nontrivial R] (hR : IsJacobsonRing R)
  proof: by
  refine (isIntegral_quotientMap_iff _).mp ?_
  let P' : Ideal R := P.comap C
  obtain ⟨pX, hpX, hp0⟩ := exists_nonzero_mem_of_ne_bot
    (ne_of_lt (bot_lt_of_maximal P (Polynomial.not_isField R))).symm hP'
  let a : R ⧸ P' := (pX.map (Ideal.Quotient.mk P')).leadingCoeff
  let M : Submonoid (R ⧸ 

中文:
定理 quotient_mk_comp_C_is整数egral_of_jacobson'
  结论: [非平凡 R] (hR : 是Jacobson环 R)
  证明: by
  refine (isIntegral_quotientMap_iff _).mp ?_
  let P' : Ideal R := P.comap C
  obtain ⟨pX, hpX, hp0⟩ := exists_nonzero_mem_of_ne_bot
    (ne_of_lt (bot_lt_of_maximal P (Polynomial.not_isField R))).symm hP'
  let a : R ⧸ P' := (pX.map (Ideal.Quotient.mk P')).leadingCoeff
  let M : Submonoid (R ⧸ 
-/
private theorem quotient_mk_comp_C_isIntegral_of_jacobson' [Nontrivial R] (hR : IsJacobsonRing R)
    (hP' : forall x : R, C x in P -> x = 0) :
    ((Ideal.Quotient.mk P).comp C : R ->+* R[X] ⧸ P).IsIntegral := by
  refine (isIntegral_quotientMap_iff _).mp ?_
  let P' : Ideal R := P.comap C
  obtain ⟨pX, hpX, hp0⟩ := exists_nonzero_mem_of_ne_bot
    (ne_of_lt (bot_lt_of_maximal P (Polynomial.not_isField R))).symm hP'
  let a : R ⧸ P' := (pX.map (Ideal.Quotient.mk P')).leadingCoeff
  let M : Submonoid (R ⧸ P') := Submonoid.powers a
  let φ : R ⧸ P' ->+* R[X] ⧸ P := quotientMap P C le_rfl
  have hP'_prime : P'.IsPrime := comap_isPrime C P
  have hM : (0 : R ⧸ P') ∉ M := fun ⟨n, hn⟩ =>
hp0 leadingCoeff_eq_zero.mp (eq_zero_of_pow_eq_zero hn)
  let M' : Submonoid (R[X] ⧸ P) := M.map φ
  refine RingHom.IsIntegral.tower_bot φ (algebraMap _ (Localization M')) ?_ ?_
  · refine IsLocalization.injective (Localization M')
      (show M' <= _ from le_nonZeroDivisors_of_noZeroDivisors fun hM' => hM ?_)
    exact
      let ⟨z, zM, z0⟩ := hM'
      quotientMap_injective (_root_.trans z0 φ.map_zero.symm) ▸ zM
  · suffices RingHom.comp (algebraMap (R[X] ⧸ P) (Localization M')) φ =
      (IsLocalization.map (Localization M') φ M.le_comap_map).comp
        (algebraMap (R ⧸ P') (Localization M)) by
      rw [this]
      refine RingHom.IsIntegral.trans (algebraMap (R ⧸ P') (Localization M))
        (IsLocalization.map (Localization M') φ M.le_comap_map) ?_ ?_
      · exact (algebraMap (R ⧸ P') (Localization M)).isIntegral_of_surjective
          (IsField.localization_map_bijective hM ((Quotient.maximal_ideal_iff_isField_quotient _).mp
            (isMaximal_comap_C_of_isMaximal P hP'))).2
      · -- `convert` here is faster than `exact`, and this proof is near the time limit.
        -- convert isIntegral_isLocalization_polynomial_quotient P pX hpX
        have isloc : IsLocalization M' (Localization M') := by infer_instance
        exact @isIntegral_isLocalization_polynomial_quotient R _
          (Localization M) (Localization M') _ _ P pX hpX _ _ _ isloc
    rw [IsLocalization.map_comp M.le_comap_map]

variable [IsJacobsonRing R]

/--
theorem `quotient_mk_comp_C_isIntegral_of_isJacobsonRing` / 定理 `quotient_mk_comp_C_isIntegral_of_isJacobsonRing`

English:
theorem quotient_mk_comp_C_isIntegral_of_isJacobsonRing
  proof: by
  let P' : Ideal R := P.comap C
  have : P'.IsPrime := comap_isPrime C P
  let f : R[X] ->+* Polynomial (R ⧸ P') := Polynomial.mapRingHom (Ideal.Quotient.mk P')
  have hf : Function.Surjective ↑f := map_surjective (Ideal.Quotient.mk P') Quotient.mk_surjective
  have hPJ : P = (P.map f).comap f :=

中文:
定理 quotient_mk_comp_C_is整数egral_of_isJacobsonRing
  证明: by
  let P' : Ideal R := P.comap C
  have : P'.IsPrime := comap_isPrime C P
  let f : R[X] ->+* Polynomial (R ⧸ P') := Polynomial.mapRingHom (Ideal.Quotient.mk P')
  have hf : Function.Surjective ↑f := map_surjective (Ideal.Quotient.mk P') Quotient.mk_surjective
  have hPJ : P = (P.map f).comap f :=

Depends on / 依赖: Function, Function.Surjective, Ideal.Quotient.mk, IsPrime, P.comap, P.map, Polynomial, Polynomial.mapRingHom, Quotient, Quotient.eq_zero_iff_mem.mp, Quotient.mk_surjective, Surjective, comap_isPrime, comap_map_of_surjective, eq_zero_iff_mem, le_antisymm, le_rfl, le_sup_of_le_left, mapRingHom, map_surjective
-/
theorem quotient_mk_comp_C_isIntegral_of_isJacobsonRing :
    ((Ideal.Quotient.mk P).comp C : R ->+* R[X] ⧸ P).IsIntegral := by
  let P' : Ideal R := P.comap C
  have : P'.IsPrime := comap_isPrime C P
  let f : R[X] ->+* Polynomial (R ⧸ P') := Polynomial.mapRingHom (Ideal.Quotient.mk P')
  have hf : Function.Surjective ↑f := map_surjective (Ideal.Quotient.mk P') Quotient.mk_surjective
  have hPJ : P = (P.map f).comap f := by
    rw [comap_map_of_surjective _ hf]
    refine le_antisymm (le_sup_of_le_left le_rfl) (sup_le le_rfl ?_)
    refine fun p hp =>
      polynomial_mem_ideal_of_coeff_mem_ideal P p fun n => Quotient.eq_zero_iff_mem.mp ?_
    simpa only [f, coeff_map, coe_mapRingHom] using! (Polynomial.ext_iff.mp hp) n
  refine RingHom.IsIntegral.tower_bot
    (T := (R ⧸ comap C P)[X] ⧸ _) _ _ (injective_quotient_le_comap_map P) ?_
  rw [← quotient_mk_maps_eq]
  refine ((Ideal.Quotient.mk P').isIntegral_of_surjective Quotient.mk_surjective).trans _ _ ?_
  have : IsMaximal (Ideal.map (mapRingHom (Ideal.Quotient.mk (comap C P))) P) :=
    Or.recOn (map_eq_top_or_isMaximal_of_surjective f hf hP)
      (fun h => absurd (_root_.trans (h ▸ hPJ : P = comap f ⊤) comap_top : P = ⊤) hP.ne_top) id
  apply quotient_mk_comp_C_isIntegral_of_jacobson' _ ?_ (fun x hx => ?_)
  any_goals exact isJacobsonRing_quotient
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  rwa [Quotient.eq_zero_iff_mem, mem_comap, hPJ, mem_comap, coe_mapRingHom, map_C]

/--
theorem `isMaximal_comap_C_of_isJacobsonRing` / 定理 `isMaximal_comap_C_of_isJacobsonRing`

English:
theorem isMaximal_comap_C_of_isJacobsonRing
  statement: (P.comap (C : R ->+* R[X])).IsMaximal
  proof: by
  rw [← @mk_ker _ _ P]; rw [RingHom.ker_eq_comap_bot]; rw [comap_comap]
  have := (bot_quotient_isMaximal_iff _).mpr hP
  exact isMaximal_comap_of_isIntegral_of_isMaximal' _
    (quotient_mk_comp_C_isIntegral_of_isJacobsonRing P) ⊥

中文:
定理 isMaximal_comap_C_of_isJacobsonRing
  结论: (P.comap (C : R ->+* R[X])).是极大
  证明: by
  rw [← @mk_ker _ _ P]; rw [RingHom.ker_eq_comap_bot]; rw [comap_comap]
  have := (bot_quotient_isMaximal_iff _).mpr hP
  exact isMaximal_comap_of_isIntegral_of_isMaximal' _
    (quotient_mk_comp_C_isIntegral_of_isJacobsonRing P) ⊥

Depends on / 依赖: RingHom, RingHom.ker_eq_comap_bot, bot_quotient_isMaximal_iff, comap_comap, isMaximal_comap_of_isIntegral_of_isMaximal, ker_eq_comap_bot, mk_ker, quotient_mk_comp_C_isIntegral_of_isJacobsonRing
-/
theorem isMaximal_comap_C_of_isJacobsonRing : (P.comap (C : R ->+* R[X])).IsMaximal := by
  rw [← @mk_ker _ _ P]; rw [RingHom.ker_eq_comap_bot]; rw [comap_comap]
  have := (bot_quotient_isMaximal_iff _).mpr hP
  exact isMaximal_comap_of_isIntegral_of_isMaximal' _
    (quotient_mk_comp_C_isIntegral_of_isJacobsonRing P) ⊥

/--
theorem `comp_C_integral_of_surjective_of_isJacobsonRing` / 定理 `comp_C_integral_of_surjective_of_isJacobsonRing`

English:
theorem comp_C_integral_of_surjective_of_isJacobsonRing
  statement: {S : Type*} [Field S] (f : R[X] ->+* S)
  proof: by
  have : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hf
  let g : R[X] ⧸ (RingHom.ker f) ->+* S := Ideal.Quotient.lift (RingHom.ker f) f fun _ h => h
  have hfg : g.comp (Ideal.Quotient.mk (RingHom.ker f)) = f := ringHom_ext' rfl rfl
  rw [← hfg]; rw [RingHom.comp_assoc]
  

中文:
定理 comp_C_integral_of_surjective_of_isJacobsonRing
  结论: {S : 类型} [域 S] (f : R[X] ->+* S)
  证明: by
  have : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hf
  let g : R[X] ⧸ (RingHom.ker f) ->+* S := Ideal.Quotient.lift (RingHom.ker f) f fun _ h => h
  have hfg : g.comp (Ideal.Quotient.mk (RingHom.ker f)) = f := ringHom_ext' rfl rfl
  rw [← hfg]; rw [RingHom.comp_assoc]
  

Depends on / 依赖: Function, Function.Surjective.of_comp, Ideal.Quotient.lift, Ideal.Quotient.mk, IsMaximal, Quotient, RingHom, RingHom.coe_comp, RingHom.comp_assoc, RingHom.ker, RingHom.ker_isMaximal_of_surjective, Surjective, coe_comp, comp_assoc, g.comp, g.isIntegral_of_surjective, isIntegral_of_surjective, ker_isMaximal_of_surjective, of_comp, quotient_mk_comp_C_isIntegral_of_isJacobsonRing
-/
theorem comp_C_integral_of_surjective_of_isJacobsonRing {S : Type*} [Field S] (f : R[X] ->+* S)
    (hf : Function.Surjective ↑f) : (f.comp C).IsIntegral := by
  have : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hf
  let g : R[X] ⧸ (RingHom.ker f) ->+* S := Ideal.Quotient.lift (RingHom.ker f) f fun _ h => h
  have hfg : g.comp (Ideal.Quotient.mk (RingHom.ker f)) = f := ringHom_ext' rfl rfl
  rw [← hfg]; rw [RingHom.comp_assoc]
  refine (quotient_mk_comp_C_isIntegral_of_isJacobsonRing (RingHom.ker f)).trans _ g
    (g.isIntegral_of_surjective ?_)
  rw [← hfg]; rw [RingHom.coe_comp] at hf
  exact Function.Surjective.of_comp hf

end

end Polynomial

open MvPolynomial RingHom

namespace MvPolynomial

/--
theorem `isJacobsonRing_MvPolynomial_fin` / 定理 `isJacobsonRing_MvPolynomial_fin`

English:
theorem isJacobsonRing_MvPolynomial_fin
  given: {R : Type u} [CommRing R] [H : IsJacobsonRing R]

中文:
定理 isJacobsonRing_MvPolynomial_fin
  条件: {R : 类型u} [交换环 R] [H : 是Jacobson环 R]
-/
theorem isJacobsonRing_MvPolynomial_fin {R : Type u} [CommRing R] [H : IsJacobsonRing R] :
    forall n : Nat, IsJacobsonRing (MvPolynomial (Fin n) R)
  | 0 => (isJacobsonRing_iso ((renameEquiv R (Equiv.equivPEmpty (Fin 0))).toRingEquiv.trans
    (isEmptyRingEquiv R PEmpty.{u + 1}))).mpr H
  | n + 1 => (isJacobsonRing_iso (finSuccEquiv R n).toRingEquiv).2
    (Polynomial.isJacobsonRing_polynomial_iff_isJacobsonRing.2 (isJacobsonRing_MvPolynomial_fin n))

/--
Instance `isJacobsonRing` / 实例 `isJacobsonRing`

English:
instance isJacobsonRing
  signature: {R : Type*} [CommRing R] {ι : Type*} [Finite ι] [IsJacobsonRing R]
  body: by
  cases nonempty_fintype ι
  let e := Fintype.equivFin ι
  rw [isJacobsonRing_iso (renameEquiv R e).toRingEquiv]
  exact isJacobsonRing_MvPolynomial_fin _

中文:
实例 isJacobsonRing
  签名: {R : 类型} [交换环 R] {ι : 类型} [有限 ι] [是Jacobson环 R]
  定义体: by
  cases nonempty_fintype ι
  let e := Fintype.equivFin ι
  rw [isJacobsonRing_iso (renameEquiv R e).toRingEquiv]
  exact isJacobsonRing_MvPolynomial_fin _

Depends on / 依赖: Fintype, Fintype.equivFin, equivFin, isJacobsonRing_MvPolynomial_fin, isJacobsonRing_iso, nonempty_fintype, renameEquiv, toRingEquiv
-/
instance isJacobsonRing {R : Type*} [CommRing R] {ι : Type*} [Finite ι] [IsJacobsonRing R] :
    IsJacobsonRing (MvPolynomial ι R) := by
  cases nonempty_fintype ι
  let e := Fintype.equivFin ι
  rw [isJacobsonRing_iso (renameEquiv R e).toRingEquiv]
  exact isJacobsonRing_MvPolynomial_fin _

variable {n : Nat}

universe v w

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Cₐ (R : Type u) (S : Type v)
  body: { Polynomial.C with commutes' := fun r => by rfl }

中文:
定义 noncomputable
  签名: def Cₐ (R : 类型u) (S : 类型v)
  定义体: { Polynomial.C with commutes' := fun r => by rfl }
-/
private noncomputable def Cₐ (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] : S ->ₐ[R] S[X] :=
  { Polynomial.C with commutes' := fun r => by rfl }

/--
lemma `aux_IH` / 引理 `aux_IH`

English:
lemma aux_IH
  statement: {R : Type u} {S : Type v} {T : Type w}
  proof: by
  let Q := P.comap v.toAlgHom.toRingHom
  have hw : Ideal.map v Q = P := map_comap_of_surjective v v.surjective P
  have hQ : IsMaximal Q := comap_isMaximal_of_surjective _ v.surjective
  let w : (S[X] ⧸ Q) ≃ₐ[R] (T ⧸ P) := Ideal.quotientEquivAlg Q P v hw.symm
  let Q' := Q.comap (Polynomial.C)
 

中文:
引理 aux_IH
  结论: {R : 类型u} {S : 类型v} {T : 类型 w}
  证明: by
  let Q := P.comap v.toAlgHom.toRingHom
  have hw : Ideal.map v Q = P := map_comap_of_surjective v v.surjective P
  have hQ : IsMaximal Q := comap_isMaximal_of_surjective _ v.surjective
  let w : (S[X] ⧸ Q) ≃ₐ[R] (T ⧸ P) := Ideal.quotientEquivAlg Q P v hw.symm
  let Q' := Q.comap (Polynomial.C)
 
-/
private lemma aux_IH {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] [IsJacobsonRing S] [Algebra R S] [Algebra R T]
    (IH : forall (Q : Ideal S), (IsMaximal Q) -> RingHom.IsIntegral (algebraMap R (S ⧸ Q)))
    (v : S[X] ≃ₐ[R] T) (P : Ideal T) (hP : P.IsMaximal) :
    RingHom.IsIntegral (algebraMap R (T ⧸ P)) := by
  let Q := P.comap v.toAlgHom.toRingHom
  have hw : Ideal.map v Q = P := map_comap_of_surjective v v.surjective P
  have hQ : IsMaximal Q := comap_isMaximal_of_surjective _ v.surjective
  let w : (S[X] ⧸ Q) ≃ₐ[R] (T ⧸ P) := Ideal.quotientEquivAlg Q P v hw.symm
  let Q' := Q.comap (Polynomial.C)
  let w' : (S ⧸ Q') ->ₐ[R] (S[X] ⧸ Q) := Ideal.quotientMapₐ Q (Cₐ R S) le_rfl
  have h_eq : algebraMap R (T ⧸ P) =
    w.toRingEquiv.toRingHom.comp (w'.toRingHom.comp (algebraMap R (S ⧸ Q'))) := by
    ext r
    simp only [AlgHom.toRingHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower, coe_comp, coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes]
  rw [h_eq]
  apply RingHom.IsIntegral.trans
  · apply RingHom.IsIntegral.trans
    · apply IH
      apply Polynomial.isMaximal_comap_C_of_isJacobsonRing
    · suffices w'.toRingHom = Ideal.quotientMap Q (Polynomial.C) le_rfl by
        rw [this]
        rw [isIntegral_quotientMap_iff _]
        apply Polynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing
      rfl
  · apply RingHom.isIntegral_of_surjective
    exact w.surjective

/--
theorem `quotient_mk_comp_C_isIntegral_of_isJacobsonRing'` / 定理 `quotient_mk_comp_C_isIntegral_of_isJacobsonRing'`

English:
theorem quotient_mk_comp_C_isIntegral_of_isJacobsonRing'
  proof: by
  induction n with
  | zero =>
    apply RingHom.isIntegral_of_surjective
    apply Function.Surjective.comp Quotient.mk_surjective
    exact C_surjective (Fin 0)
  | succ n IH => apply aux_IH IH (finSuccEquiv R n).symm P hP

中文:
定理 quotient_mk_comp_C_is整数egral_of_isJacobsonRing'
  证明: by
  induction n with
  | zero =>
    apply RingHom.isIntegral_of_surjective
    apply Function.Surjective.comp Quotient.mk_surjective
    exact C_surjective (Fin 0)
  | succ n IH => apply aux_IH IH (finSuccEquiv R n).symm P hP
-/
private theorem quotient_mk_comp_C_isIntegral_of_isJacobsonRing'
    {R : Type*} [CommRing R] [IsJacobsonRing R]
    (P : Ideal (MvPolynomial (Fin n) R)) (hP : P.IsMaximal) :
    RingHom.IsIntegral (algebraMap R (MvPolynomial (Fin n) R ⧸ P)) := by
  induction n with
  | zero =>
    apply RingHom.isIntegral_of_surjective
    apply Function.Surjective.comp Quotient.mk_surjective
    exact C_surjective (Fin 0)
  | succ n IH => apply aux_IH IH (finSuccEquiv R n).symm P hP

/--
theorem `quotient_mk_comp_C_isIntegral_of_isJacobsonRing` / 定理 `quotient_mk_comp_C_isIntegral_of_isJacobsonRing`

English:
theorem quotient_mk_comp_C_isIntegral_of_isJacobsonRing
  statement: {R : Type*} [CommRing R] [IsJacobsonRing R]
  proof: by
  change RingHom.IsIntegral (algebraMap R (MvPolynomial (Fin n) R ⧸ P))
  apply quotient_mk_comp_C_isIntegral_of_isJacobsonRing'
  infer_instance

中文:
定理 quotient_mk_comp_C_is整数egral_of_isJacobsonRing
  结论: {R : 类型} [交换环 R] [是Jacobson环 R]
  证明: by
  change RingHom.IsIntegral (algebraMap R (MvPolynomial (Fin n) R ⧸ P))
  apply quotient_mk_comp_C_isIntegral_of_isJacobsonRing'
  infer_instance

Depends on / 依赖: IsIntegral, MvPolynomial, RingHom, RingHom.IsIntegral, algebraMap, infer_instance, quotient_mk_comp_C_isIntegral_of_isJacobsonRing
-/
theorem quotient_mk_comp_C_isIntegral_of_isJacobsonRing {R : Type*} [CommRing R] [IsJacobsonRing R]
    (P : Ideal (MvPolynomial (Fin n) R)) [hP : P.IsMaximal] :
    RingHom.IsIntegral (RingHom.comp (Ideal.Quotient.mk P) (MvPolynomial.C)) := by
  change RingHom.IsIntegral (algebraMap R (MvPolynomial (Fin n) R ⧸ P))
  apply quotient_mk_comp_C_isIntegral_of_isJacobsonRing'
  infer_instance

/--
theorem `comp_C_integral_of_surjective_of_isJacobsonRing` / 定理 `comp_C_integral_of_surjective_of_isJacobsonRing`

English:
theorem comp_C_integral_of_surjective_of_isJacobsonRing
  statement: {R : Type*} [CommRing R] [IsJacobsonRing R]
  proof: by
  cases nonempty_fintype σ
  have e := (Fintype.equivFin σ).symm
  let f' : MvPolynomial (Fin _) R ->+* S := f.comp (renameEquiv R e).toRingEquiv.toRingHom
  have hf' := Function.Surjective.comp hf (renameEquiv R e).surjective
  change Function.Surjective ↑f' at hf'
  have : (f'.comp C).IsIntegra

中文:
定理 comp_C_integral_of_surjective_of_isJacobsonRing
  结论: {R : 类型} [交换环 R] [是Jacobson环 R]
  证明: by
  cases nonempty_fintype σ
  have e := (Fintype.equivFin σ).symm
  let f' : MvPolynomial (Fin _) R ->+* S := f.comp (renameEquiv R e).toRingEquiv.toRingHom
  have hf' := Function.Surjective.comp hf (renameEquiv R e).surjective
  change Function.Surjective ↑f' at hf'
  have : (f'.comp C).IsIntegra

Depends on / 依赖: Fintype, Fintype.equivFin, Function, Function.Surjective, Function.Surjective.comp, Ideal.Quotient.lift, IsIntegral, IsMaximal, MvPolynomial, Quotient, RingHom, RingHom.ker, Surjective, equivFin, f.comp, g.comp, ker_isMaximal_of_surjective, nonempty_fintype, renameEquiv, surjective
-/
theorem comp_C_integral_of_surjective_of_isJacobsonRing {R : Type*} [CommRing R] [IsJacobsonRing R]
    {σ : Type*} [Finite σ] {S : Type*} [Field S] (f : MvPolynomial σ R ->+* S)
    (hf : Function.Surjective ↑f) : (f.comp C).IsIntegral := by
  cases nonempty_fintype σ
  have e := (Fintype.equivFin σ).symm
  let f' : MvPolynomial (Fin _) R ->+* S := f.comp (renameEquiv R e).toRingEquiv.toRingHom
  have hf' := Function.Surjective.comp hf (renameEquiv R e).surjective
  change Function.Surjective ↑f' at hf'
  have : (f'.comp C).IsIntegral := by
    have : (RingHom.ker f').IsMaximal := ker_isMaximal_of_surjective f' hf'
    let g : MvPolynomial _ R ⧸ (RingHom.ker f') ->+* S :=
      Ideal.Quotient.lift (RingHom.ker f') f' fun _ h => h
    have hfg : g.comp (Ideal.Quotient.mk (RingHom.ker f')) = f' :=
      ringHom_ext (fun r => rfl) fun i => rfl
    rw [← hfg]; rw [RingHom.comp_assoc]
    refine (quotient_mk_comp_C_isIntegral_of_isJacobsonRing (RingHom.ker f')).trans _ g
      (g.isIntegral_of_surjective ?_)
    rw [← hfg]; rw [coe_comp] at hf'
    exact Function.Surjective.of_comp hf'
  rw [RingHom.comp_assoc] at this
  convert! this
  refine RingHom.ext fun x => ?_
  exact ((renameEquiv R e).commutes' x).symm

end MvPolynomial

/--
lemma `isJacobsonRing_of_finiteType` / 引理 `isJacobsonRing_of_finiteType`

English:
lemma isJacobsonRing_of_finiteType
  statement: {A B : Type*} [CommRing A] [CommRing B]
  proof: by
  obtain ⟨ι, hι, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp ‹_›
  exact isJacobsonRing_of_surjective ⟨f.toRingHom, hf⟩

中文:
引理 isJacobsonRing_of_finiteType
  结论: {A B : 类型} [交换环 A] [交换环 B]
  证明: by
  obtain ⟨ι, hι, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp ‹_›
  exact isJacobsonRing_of_surjective ⟨f.toRingHom, hf⟩

Depends on / 依赖: Algebra, Algebra.FiniteType.iff_quotient_mvPolynomial, FiniteType, f.toRingHom, iff_quotient_mvPolynomial, isJacobsonRing_of_surjective, toRingHom
-/
lemma isJacobsonRing_of_finiteType {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [IsJacobsonRing A] [Algebra.FiniteType A B] : IsJacobsonRing B := by
  obtain ⟨ι, hι, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp ‹_›
  exact isJacobsonRing_of_surjective ⟨f.toRingHom, hf⟩

/--
lemma `RingHom.FiniteType.isJacobsonRing` / 引理 `RingHom.FiniteType.isJacobsonRing`

English:
lemma RingHom.FiniteType.isJacobsonRing
  statement: {A B : Type*} [CommRing A] [CommRing B]
  proof: @isJacobsonRing_of_finiteType A B _ _ f.toAlgebra _ H

@[stacks 0CY7 "See also https://en.wikipedia.org/wiki/Zariski%27s_lemma."]

中文:
引理 环态射.有限型.isJacobsonRing
  结论: {A B : 类型} [交换环 A] [交换环 B]
  证明: @isJacobsonRing_of_finiteType A B _ _ f.toAlgebra _ H

@[stacks 0CY7 "See also https://en.wikipedia.org/wiki/Zariski%27s_lemma."]

Depends on / 依赖: f.toAlgebra, isJacobsonRing_of_finiteType, toAlgebra
-/
lemma RingHom.FiniteType.isJacobsonRing {A B : Type*} [CommRing A] [CommRing B]
    {f : A ->+* B} [IsJacobsonRing A] (H : f.FiniteType) : IsJacobsonRing B :=
  @isJacobsonRing_of_finiteType A B _ _ f.toAlgebra _ H

@[stacks 0CY7 "See also https://en.wikipedia.org/wiki/Zariski%27s_lemma."]
/--
lemma `finite_of_finite_type_of_isJacobsonRing` / 引理 `finite_of_finite_type_of_isJacobsonRing`

English:
lemma finite_of_finite_type_of_isJacobsonRing
  statement: (R S : Type*) [CommRing R] [Field S]
  proof: by
  obtain ⟨ι, hι, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp ‹_›
  have : (algebraMap R S).IsIntegral := by
    rw [← f.comp_algebraMap]
    -- We need to write `f.toRingHom` instead of just `f`, to avoid unification issues.
    exact MvPolynomial.comp_C_integral_of_surjective_of_i

中文:
引理 finite_of_finite_type_of_isJacobsonRing
  结论: (R S : 类型) [交换环 R] [域 S]
  证明: by
  obtain ⟨ι, hι, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp ‹_›
  have : (algebraMap R S).IsIntegral := by
    rw [← f.comp_algebraMap]
    -- We need to write `f.toRingHom` instead of just `f`, to avoid unification issues.
    exact MvPolynomial.comp_C_integral_of_surjective_of_i

Depends on / 依赖: Algebra, Algebra.FiniteType.iff_quotient_mvPolynomial, FiniteType, IsIntegral, algebraMap, comp_algebraMap, f.comp_algebraMap, iff_quotient_mvPolynomial
-/
lemma finite_of_finite_type_of_isJacobsonRing (R S : Type*) [CommRing R] [Field S]
    [Algebra R S] [IsJacobsonRing R] [Algebra.FiniteType R S] :
    Module.Finite R S := by
  obtain ⟨ι, hι, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp ‹_›
  have : (algebraMap R S).IsIntegral := by
    rw [← f.comp_algebraMap]
    -- We need to write `f.toRingHom` instead of just `f`, to avoid unification issues.
    exact MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing f.toRingHom hf
  have : Algebra.IsIntegral R S := Algebra.isIntegral_def.mpr this
  exact Algebra.IsIntegral.finite

/--
lemma `RingHom.finite_iff_finiteType_of_isJacobsonRing` / 引理 `RingHom.finite_iff_finiteType_of_isJacobsonRing`

English:
lemma RingHom.finite_iff_finiteType_of_isJacobsonRing
  proof: ⟨RingHom.FiniteType.of_finite,
    by intro; algebraize [f]; exact finite_of_finite_type_of_isJacobsonRing R S⟩

中文:
引理 环态射.finite_iff_finiteType_of_isJacobsonRing
  证明: ⟨RingHom.FiniteType.of_finite,
    by intro; algebraize [f]; exact finite_of_finite_type_of_isJacobsonRing R S⟩

Depends on / 依赖: FiniteType, RingHom, RingHom.FiniteType.of_finite, algebraize, finite_of_finite_type_of_isJacobsonRing, of_finite
-/
lemma RingHom.finite_iff_finiteType_of_isJacobsonRing
    {R S : Type*} [CommRing R] [IsJacobsonRing R] [Field S]
    {f : R ->+* S} : f.Finite ↔ f.FiniteType :=
  ⟨RingHom.FiniteType.of_finite,
    by intro; algebraize [f]; exact finite_of_finite_type_of_isJacobsonRing R S⟩

/--
theorem `finite_of_algHom_finiteType_of_isJacobsonRing` / 定理 `finite_of_algHom_finiteType_of_isJacobsonRing`

English:
theorem finite_of_algHom_finiteType_of_isJacobsonRing
  proof: by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let := Ideal.Quotient.field m
  have := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  exact Module.Finite.of_injective ((Ideal.Quotient.mkₐ K m).comp f).toLinearMap
    (RingHom.injective _)

中文:
定理 finite_of_algHom_finiteType_of_isJacobsonRing
  证明: by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let := Ideal.Quotient.field m
  have := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  exact Module.Finite.of_injective ((Ideal.Quotient.mkₐ K m).comp f).toLinearMap
    (RingHom.injective _)

Depends on / 依赖: Finite, Ideal.Quotient.field, Ideal.Quotient.mk, Ideal.exists_maximal, Module, Module.Finite.of_injective, Quotient, RingHom, RingHom.injective, exists_maximal, finite_of_finite_type_of_isJacobsonRing, injective, of_injective, toLinearMap
-/
theorem finite_of_algHom_finiteType_of_isJacobsonRing
    {K L A : Type*} [CommRing K] [DivisionRing L] [CommRing A]
    [IsJacobsonRing K] [IsNoetherianRing K] [Nontrivial A]
    [Algebra K L] [Algebra K A]
    [Algebra.FiniteType K A] (f : L ->ₐ[K] A) :
    Module.Finite K L := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let := Ideal.Quotient.field m
  have := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  exact Module.Finite.of_injective ((Ideal.Quotient.mkₐ K m).comp f).toLinearMap
    (RingHom.injective _)

/-- If `K` is a Jacobson Noetherian ring, `A` a nontrivial `K`-algebra of finite type,
then any `K`-subfield of `A` is finite over `K`. -/
nonrec theorem RingHom.finite_of_algHom_finiteType_of_isJacobsonRing
    {K L A : Type*} [CommRing K] [Field L] [CommRing A]
    [IsJacobsonRing K] [IsNoetherianRing K] [Nontrivial A]
    (f : K ->+* L) (g : L ->+* A) (hfg : (g.comp f).FiniteType) :
    f.Finite := by
  algebraize [f, (g.comp f)]
  exact finite_of_algHom_finiteType_of_isJacobsonRing ⟨g, fun _ => rfl⟩
