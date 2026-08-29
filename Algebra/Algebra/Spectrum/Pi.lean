/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Group.Pi.Units

/-!
# Spectrum and quasispectrum of products

This file contains results regarding the spectra and quasispectra of (indexed) products of
elements of a (non-unital) ring. The main result is that the (quasi)spectrum of a product is the
union of the (quasi)spectra.

## Main declarations

+ `Pi.spectrum_eq`: `spectrum R a = ⋃ i, spectrum R (a i)` for `a : ∀ i, κ i`
+ `Prod.spectrum_eq`: `spectrum R ⟨a, b⟩ = spectrum R a ∪ spectrum R b`
+ `Pi.quasispectrum_eq`: `quasispectrum R a = ⋃ i, quasispectrum R (a i)` for `a : ∀ i, κ i`
+ `Prod.quasispectrum_eq`: `quasispectrum R ⟨a, b⟩ = quasispectrum R a ∪ quasispectrum R b`

## TODO

+ Apply these results to block matrices.

-/

@[expose] public section

variable {ι A B R : Type*} {κ : ι -> Type*}

section quasiregular

variable (κ) in
/--
Definition of `PreQuasiregular.toPi` / `PreQuasiregular.toPi` 的定义

English:
definition PreQuasiregular.toPi
  signature: [forall i, NonUnitalSemiring (κ i)]
  body: fun x i => .mk x.val i
invFun := fun x => .mk fun i => (x i).val
  map_mul' _ _ := rfl

中文:
定义 PreQuasiregular.toPi
  签名: [对任意 i, NonUnitalSemiring (κ i)]
  定义体: fun x i => .mk x.val i
invFun := fun x => .mk fun i => (x i).val
  map_mul' _ _ := rfl

Depends on / 依赖: x.val
-/
def PreQuasiregular.toPi [forall i, NonUnitalSemiring (κ i)] :
    PreQuasiregular (forall i, κ i) ≃* forall i, PreQuasiregular (κ i) where
toFun := fun x i => .mk x.val i
invFun := fun x => .mk fun i => (x i).val
  map_mul' _ _ := rfl

variable (A B) in
/--
Definition of `PreQuasiregular.toProd` / `PreQuasiregular.toProd` 的定义

English:
definition PreQuasiregular.toProd
  signature: [NonUnitalSemiring A] [NonUnitalSemiring B]
  body: fun p => ⟨.mk p.val.1, .mk p.val.2⟩
  invFun := fun ⟨a, b⟩ => .mk ⟨a.val, b.val⟩
  map_mul' _ _ := rfl

中文:
定义 PreQuasiregular.toProd
  签名: [NonUnitalSemiring A] [NonUnitalSemiring B]
  定义体: fun p => ⟨.mk p.val.1, .mk p.val.2⟩
  invFun := fun ⟨a, b⟩ => .mk ⟨a.val, b.val⟩
  map_mul' _ _ := rfl

Depends on / 依赖: p.val
-/
def PreQuasiregular.toProd [NonUnitalSemiring A] [NonUnitalSemiring B] :
    PreQuasiregular (A × B) ≃* PreQuasiregular A × PreQuasiregular B where
  toFun := fun p => ⟨.mk p.val.1, .mk p.val.2⟩
  invFun := fun ⟨a, b⟩ => .mk ⟨a.val, b.val⟩
  map_mul' _ _ := rfl

/--
lemma `isQuasiregular_pi_iff` / 引理 `isQuasiregular_pi_iff`

English:
lemma isQuasiregular_pi_iff
  given: [forall i, NonUnitalSemiring (κ i)] (x : forall i, κ i)
  proof: by
  simp only [isQuasiregular_iff', ← isUnit_map_iff (PreQuasiregular.toPi κ), Pi.isUnit_iff]
  congr!

中文:
引理 isQuasiregular_pi_iff
  条件: [对任意 i, NonUnitalSemiring (κ i)] (x : 对任意 i, κ i)
  证明: by
  simp only [isQuasiregular_iff', ← isUnit_map_iff (PreQuasiregular.toPi κ), Pi.isUnit_iff]
  congr!

Depends on / 依赖: Pi.isUnit_iff, PreQuasiregular, PreQuasiregular.toPi, isQuasiregular_iff, isUnit_iff, isUnit_map_iff
-/
lemma isQuasiregular_pi_iff [forall i, NonUnitalSemiring (κ i)] (x : forall i, κ i) :
    IsQuasiregular x ↔ forall i, IsQuasiregular (x i) := by
  simp only [isQuasiregular_iff', ← isUnit_map_iff (PreQuasiregular.toPi κ), Pi.isUnit_iff]
  congr!

/--
lemma `isQuasiregular_prod_iff` / 引理 `isQuasiregular_prod_iff`

English:
lemma isQuasiregular_prod_iff
  given: [NonUnitalSemiring A] [NonUnitalSemiring B] (a : A) (b : B)
  proof: by
  simp only [isQuasiregular_iff', ← isUnit_map_iff (PreQuasiregular.toProd A B), Prod.isUnit_iff]
  congr!

中文:
引理 isQuasiregular_prod_iff
  条件: [NonUnitalSemiring A] [NonUnitalSemiring B] (a : A) (b : B)
  证明: by
  simp only [isQuasiregular_iff', ← isUnit_map_iff (PreQuasiregular.toProd A B), Prod.isUnit_iff]
  congr!

Depends on / 依赖: PreQuasiregular, PreQuasiregular.toProd, Prod.isUnit_iff, isQuasiregular_iff, isUnit_iff, isUnit_map_iff, toProd
-/
lemma isQuasiregular_prod_iff [NonUnitalSemiring A] [NonUnitalSemiring B] (a : A) (b : B) :
    IsQuasiregular (⟨a, b⟩ : A × B) ↔ IsQuasiregular a ∧ IsQuasiregular b := by
  simp only [isQuasiregular_iff', ← isUnit_map_iff (PreQuasiregular.toProd A B), Prod.isUnit_iff]
  congr!

/--
lemma `quasispectrum.mem_iff_of_isUnit` / 引理 `quasispectrum.mem_iff_of_isUnit`

English:
lemma quasispectrum.mem_iff_of_isUnit
  statement: [CommSemiring R] [NonUnitalRing A]
  proof: ⟨fun h => h hr, fun h _ => h⟩

中文:
引理 quasispectrum.mem_iff_of_isUnit
  结论: [CommSemiring R] [NonUnitalRing A]
  证明: ⟨fun h => h hr, fun h _ => h⟩
-/
lemma quasispectrum.mem_iff_of_isUnit [CommSemiring R] [NonUnitalRing A]
    [Module R A] {a : A} {r : R} (hr : IsUnit r) :
    r in quasispectrum R a ↔ ¬ IsQuasiregular (-(hr.unit⁻¹ • a)) :=
  ⟨fun h => h hr, fun h _ => h⟩

end quasiregular

section spectrum

/--
lemma `Pi.spectrum_eq` / 引理 `Pi.spectrum_eq`

English:
lemma Pi.spectrum_eq
  statement: [CommSemiring R] [forall i, Ring (κ i)] [forall i, Algebra R (κ i)]
  proof: by
  apply compl_injective
  simp_rw [spectrum, Set.compl_iUnion, compl_compl, resolventSet, Set.iInter_ofPred,
    Pi.isUnit_iff, sub_apply, algebraMap_apply]

中文:
引理 Pi.spectrum_eq
  结论: [CommSemiring R] [对任意 i, Ring (κ i)] [对任意 i, Algebra R (κ i)]
  证明: by
  apply compl_injective
  simp_rw [spectrum, Set.compl_iUnion, compl_compl, resolventSet, Set.iInter_ofPred,
    Pi.isUnit_iff, sub_apply, algebraMap_apply]

Depends on / 依赖: Pi.isUnit_iff, Set.compl_iUnion, Set.iInter_ofPred, algebraMap_apply, compl_compl, compl_iUnion, compl_injective, iInter_ofPred, isUnit_iff, resolventSet, simp_rw, spectrum, sub_apply
-/
lemma Pi.spectrum_eq [CommSemiring R] [forall i, Ring (κ i)] [forall i, Algebra R (κ i)]
    (a : forall i, κ i) : spectrum R a = ⋃ i, spectrum R (a i) := by
  apply compl_injective
  simp_rw [spectrum, Set.compl_iUnion, compl_compl, resolventSet, Set.iInter_ofPred,
    Pi.isUnit_iff, sub_apply, algebraMap_apply]

/--
lemma `Prod.spectrum_eq` / 引理 `Prod.spectrum_eq`

English:
lemma Prod.spectrum_eq
  statement: [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  proof: by
  apply compl_injective
  simp_rw [spectrum, Set.compl_union, compl_compl, resolventSet, ← Set.ofPred_and,
    Prod.isUnit_iff, algebraMap_apply, mk_sub_mk]

中文:
引理 Prod.spectrum_eq
  结论: [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  证明: by
  apply compl_injective
  simp_rw [spectrum, Set.compl_union, compl_compl, resolventSet, ← Set.ofPred_and,
    Prod.isUnit_iff, algebraMap_apply, mk_sub_mk]

Depends on / 依赖: Prod.isUnit_iff, Set.compl_union, Set.ofPred_and, algebraMap_apply, compl_compl, compl_injective, compl_union, isUnit_iff, mk_sub_mk, ofPred_and, resolventSet, simp_rw, spectrum
-/
lemma Prod.spectrum_eq [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (a : A) (b : B) : spectrum R (⟨a, b⟩ : A × B) = spectrum R a union spectrum R b := by
  apply compl_injective
  simp_rw [spectrum, Set.compl_union, compl_compl, resolventSet, ← Set.ofPred_and,
    Prod.isUnit_iff, algebraMap_apply, mk_sub_mk]

/--
lemma `Pi.quasispectrum_eq` / 引理 `Pi.quasispectrum_eq`

English:
lemma Pi.quasispectrum_eq
  statement: [Nonempty ι] [CommSemiring R] [forall i, NonUnitalRing (κ i)]
  proof: by
  ext r
  simp only [quasispectrum, Set.mem_ofPred_eq, Set.mem_iUnion]
  by_cases hr : IsUnit r
  · lift r to Rˣ using hr with r' hr'
    simp [isQuasiregular_pi_iff]
  · simp [hr]

中文:
引理 Pi.quasispectrum_eq
  结论: [Nonempty ι] [CommSemiring R] [对任意 i, NonUnitalRing (κ i)]
  证明: by
  ext r
  simp only [quasispectrum, Set.mem_ofPred_eq, Set.mem_iUnion]
  by_cases hr : IsUnit r
  · lift r to Rˣ using hr with r' hr'
    simp [isQuasiregular_pi_iff]
  · simp [hr]

Depends on / 依赖: IsUnit, Set.mem_iUnion, Set.mem_ofPred_eq, isQuasiregular_pi_iff, mem_iUnion, mem_ofPred_eq, quasispectrum
-/
lemma Pi.quasispectrum_eq [Nonempty ι] [CommSemiring R] [forall i, NonUnitalRing (κ i)]
    [forall i, Module R (κ i)] (a : forall i, κ i) :
    quasispectrum R a = ⋃ i, quasispectrum R (a i) := by
  ext r
  simp only [quasispectrum, Set.mem_ofPred_eq, Set.mem_iUnion]
  by_cases hr : IsUnit r
  · lift r to Rˣ using hr with r' hr'
    simp [isQuasiregular_pi_iff]
  · simp [hr]

/--
lemma `Prod.quasispectrum_eq` / 引理 `Prod.quasispectrum_eq`

English:
lemma Prod.quasispectrum_eq
  statement: [CommSemiring R] [NonUnitalRing A] [NonUnitalRing B]
  proof: by
  apply compl_injective
  ext r
  simp only [quasispectrum, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not,
    Set.mem_union]
  by_cases hr : IsUnit r
  · lift r to Rˣ using hr with r' hr'
    simp [isQuasiregular_prod_iff]
  · simp [hr]

中文:
引理 Prod.quasispectrum_eq
  结论: [CommSemiring R] [NonUnitalRing A] [NonUnitalRing B]
  证明: by
  apply compl_injective
  ext r
  simp only [quasispectrum, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not,
    Set.mem_union]
  by_cases hr : IsUnit r
  · lift r to Rˣ using hr with r' hr'
    simp [isQuasiregular_prod_iff]
  · simp [hr]

Depends on / 依赖: IsUnit, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union, compl_injective, isQuasiregular_prod_iff, mem_compl_iff, mem_ofPred_eq, mem_union, not_forall, not_not, quasispectrum
-/
lemma Prod.quasispectrum_eq [CommSemiring R] [NonUnitalRing A] [NonUnitalRing B]
    [Module R A] [Module R B] (a : A) (b : B) :
    quasispectrum R (⟨a, b⟩ : A × B) = quasispectrum R a union quasispectrum R b := by
  apply compl_injective
  ext r
  simp only [quasispectrum, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not,
    Set.mem_union]
  by_cases hr : IsUnit r
  · lift r to Rˣ using hr with r' hr'
    simp [isQuasiregular_prod_iff]
  · simp [hr]

end spectrum
