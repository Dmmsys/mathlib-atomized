/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Order.SuccPred.WithBot
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Constructible sets in the prime spectrum

This file provides tooling for manipulating constructible sets in the prime spectrum of a ring.

-/

@[expose] public section

open Finset Topology
open scoped Polynomial

namespace PrimeSpectrum
variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (R) in
/-- The data of a basic constructible set `s` is a tuple `(f, g₁, ..., gₙ)` -/
@[ext]
/--
Definition of `BasicConstructibleSetData` / `BasicConstructibleSetData` 的定义

English:
structure BasicConstructibleSetData
  parameters: where
  axioms and operations (3):
    - f : R
    - n : Nat
    - g : Fin n -> R

中文:
结构 BasicConstructibleSetData
  参数: where
  公理与运算 (3 个):
    - f : R
    - n : 自然数
    - g : Fin n -> R
-/
structure BasicConstructibleSetData where
  /-- Given the data of a basic constructible set `s = V(g₁, ..., gₙ) \ V(f)`, return `f`. -/
  protected f : R
  /-- Given the data of a basic constructible set `s = V(g₁, ..., gₙ) \ V(f)`, return `n`. -/
  protected n : Nat
  /-- Given the data of a basic constructible set `s = V(g₁, ..., gₙ) \ V(f)`, return `g`. -/
  protected g : Fin n -> R

namespace BasicConstructibleSetData

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableEq (BasicConstructibleSetData R)
  body: Classical.decEq _

中文:
实例 :
  签名: DecidableEq (BasicConstructibleSetData R)
  定义体: Classical.decEq _

Depends on / 依赖: Classical, Classical.decEq
-/
noncomputable instance : DecidableEq (BasicConstructibleSetData R) := Classical.decEq _

/-- Given the data of the constructible set `s`, build the data of the constructible set
`{I | {x | φ x ∈ I} ∈ s}`. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (φ : R ->+* S) (C : BasicConstructibleSetData R)
  body: φ C.f
  n := C.n
  g := φ ∘ C.g

中文:
定义 map
  签名: (φ : R ->+* S) (C : BasicConstructibleSetData R)
  定义体: φ C.f
  n := C.n
  g := φ ∘ C.g
-/
noncomputable def map (φ : R ->+* S) (C : BasicConstructibleSetData R) :
    BasicConstructibleSetData S where
  f := φ C.f
  n := C.n
  g := φ ∘ C.g

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (C : BasicConstructibleSetData R)
  statement: C.map (.id _) = C
  proof: by simp [map]

中文:
引理 map_id
  条件: (C : BasicConstructibleSetData R)
  结论: C.map (.id _) = C
  证明: by simp [map]
-/
@[simp] lemma map_id (C : BasicConstructibleSetData R) : C.map (.id _) = C := by simp [map]

/--
lemma `map_id'` / 引理 `map_id'`

English:
lemma map_id'
  statement: map (.id R) = id
  proof: by ext : 1; simp

中文:
引理 map_id'
  结论: map (.id R) = id
  证明: by ext : 1; simp
-/
@[simp] lemma map_id' : map (.id R) = id := by ext : 1; simp

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: (φ : S ->+* T) (ψ : R ->+* S) (C : BasicConstructibleSetData R)
  proof: by simp [map, Function.comp_def]

中文:
引理 map_comp
  条件: (φ : S ->+* T) (ψ : R ->+* S) (C : BasicConstructibleSetData R)
  证明: by simp [map, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def
-/
lemma map_comp (φ : S ->+* T) (ψ : R ->+* S) (C : BasicConstructibleSetData R) :
    C.map (φ.comp ψ) = (C.map ψ).map φ := by simp [map, Function.comp_def]

/--
lemma `map_comp'` / 引理 `map_comp'`

English:
lemma map_comp'
  given: (φ : S ->+* T) (ψ : R ->+* S)
  statement: map (φ.comp ψ) = map φ ∘ map ψ
  proof: by
  ext : 1; simp [map_comp]

中文:
引理 map_comp'
  条件: (φ : S ->+* T) (ψ : R ->+* S)
  结论: map (φ.comp ψ) = map φ ∘ map ψ
  证明: by
  ext : 1; simp [map_comp]

Depends on / 依赖: map_comp
-/
lemma map_comp' (φ : S ->+* T) (ψ : R ->+* S) : map (φ.comp ψ) = map φ ∘ map ψ := by
  ext : 1; simp [map_comp]

/--
Definition of `toSet` / `toSet` 的定义

English:
definition toSet
  signature: (C : BasicConstructibleSetData R)
  body: zeroLocus (Set.range C.g) \ zeroLocus {C.f}

@[simp]

中文:
定义 toSet
  签名: (C : BasicConstructibleSetData R)
  定义体: zeroLocus (Set.range C.g) \ zeroLocus {C.f}

@[simp]

Depends on / 依赖: Set.range, zeroLocus
-/
def toSet (C : BasicConstructibleSetData R) : Set (PrimeSpectrum R) :=
  zeroLocus (Set.range C.g) \ zeroLocus {C.f}

@[simp]
/--
lemma `toSet_map` / 引理 `toSet_map`

English:
lemma toSet_map
  given: (φ : R ->+* S) (C : BasicConstructibleSetData R)
  proof: by simp [toSet, map, ← Set.range_comp]

中文:
引理 toSet_map
  条件: (φ : R ->+* S) (C : BasicConstructibleSetData R)
  证明: by simp [toSet, map, ← Set.range_comp]

Depends on / 依赖: Set.range_comp, range_comp
-/
lemma toSet_map (φ : R ->+* S) (C : BasicConstructibleSetData R) :
    (C.map φ).toSet = comap φ ⁻¹' C.toSet := by simp [toSet, map, ← Set.range_comp]

end BasicConstructibleSetData

variable (R) in
/--
Definition of `ConstructibleSetData` / `ConstructibleSetData` 的定义

English:
abbreviation ConstructibleSetData
  body: Finset (BasicConstructibleSetData R)

中文:
缩写 ConstructibleSetData
  定义体: Finset (BasicConstructibleSetData R)

Depends on / 依赖: BasicConstructibleSetData, Finset
-/
abbrev ConstructibleSetData := Finset (BasicConstructibleSetData R)

namespace ConstructibleSetData

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (φ : R ->+* S) (s : ConstructibleSetData R)
  body: s.image (.map φ)

@[simp]

中文:
定义 map
  签名: (φ : R ->+* S) (s : ConstructibleSetData R)
  定义体: s.image (.map φ)

@[simp]

Depends on / 依赖: s.image
-/
noncomputable def map (φ : R ->+* S) (s : ConstructibleSetData R) : ConstructibleSetData S :=
  s.image (.map φ)

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (s : ConstructibleSetData R)
  statement: s.map (.id _) = s
  proof: by simp [map]

中文:
引理 map_id
  条件: (s : ConstructibleSetData R)
  结论: s.map (.id _) = s
  证明: by simp [map]
-/
lemma map_id (s : ConstructibleSetData R) : s.map (.id _) = s := by simp [map]

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: (f : S ->+* T) (g : R ->+* S) (s : ConstructibleSetData R)
  proof: by
  simp [map, image_image, Function.comp_def, BasicConstructibleSetData.map_comp']

中文:
引理 map_comp
  条件: (f : S ->+* T) (g : R ->+* S) (s : ConstructibleSetData R)
  证明: by
  simp [map, image_image, Function.comp_def, BasicConstructibleSetData.map_comp']

Depends on / 依赖: BasicConstructibleSetData, BasicConstructibleSetData.map_comp, Function, Function.comp_def, comp_def, image_image, map_comp
-/
lemma map_comp (f : S ->+* T) (g : R ->+* S) (s : ConstructibleSetData R) :
    s.map (f.comp g) = (s.map g).map f := by
  simp [map, image_image, Function.comp_def, BasicConstructibleSetData.map_comp']

/--
Definition of `toSet` / `toSet` 的定义

English:
definition toSet
  signature: (S : ConstructibleSetData R)
  body: ⋃ C in S, C.toSet

@[simp]

中文:
定义 toSet
  签名: (S : ConstructibleSetData R)
  定义体: ⋃ C in S, C.toSet

@[simp]

Depends on / 依赖: C.toSet
-/
def toSet (S : ConstructibleSetData R) : Set (PrimeSpectrum R) := ⋃ C in S, C.toSet

@[simp]
/--
lemma `toSet_map` / 引理 `toSet_map`

English:
lemma toSet_map
  given: (f : R ->+* S) (s : ConstructibleSetData R)
  proof: by
  unfold toSet map
  rw [set_biUnion_finset_image]
  simp

中文:
引理 toSet_map
  条件: (f : R ->+* S) (s : ConstructibleSetData R)
  证明: by
  unfold toSet map
  rw [set_biUnion_finset_image]
  simp

Depends on / 依赖: set_biUnion_finset_image
-/
lemma toSet_map (f : R ->+* S) (s : ConstructibleSetData R) :
    (s.map f).toSet = comap f ⁻¹' s.toSet := by
  unfold toSet map
  rw [set_biUnion_finset_image]
  simp

/--
Definition of `degBound` / `degBound` 的定义

English:
definition degBound
  signature: (S : ConstructibleSetData R[X])
  body: S.sup fun C => ∑ i, (C.g i).degree.succ

中文:
定义 degBound
  签名: (S : ConstructibleSetData R[X])
  定义体: S.sup fun C => ∑ i, (C.g i).degree.succ

Depends on / 依赖: S.sup, degree, degree.succ
-/
def degBound (S : ConstructibleSetData R[X]) : Nat := S.sup fun C => ∑ i, (C.g i).degree.succ

/--
lemma `isConstructible_toSet` / 引理 `isConstructible_toSet`

English:
lemma isConstructible_toSet
  given: (S : ConstructibleSetData R)
  proof: by
  refine .biUnion S.finite_toSet fun _ _ => .sdiff ?_ ?_
  · rw [← isConstructible_compl]
    exact (isRetrocompact_zeroLocus_compl (Set.finite_range _)).isConstructible
      (isClosed_zeroLocus _).isOpen_compl
  · rw [← isConstructible_compl]
    exact (isRetrocompact_zeroLocus_compl (Set.finit

中文:
引理 isConstructible_toSet
  条件: (S : ConstructibleSetData R)
  证明: by
  refine .biUnion S.finite_toSet fun _ _ => .sdiff ?_ ?_
  · rw [← isConstructible_compl]
    exact (isRetrocompact_zeroLocus_compl (Set.finite_range _)).isConstructible
      (isClosed_zeroLocus _).isOpen_compl
  · rw [← isConstructible_compl]
    exact (isRetrocompact_zeroLocus_compl (Set.finit

Depends on / 依赖: S.finite_toSet, Set.finite_range, Set.finite_singleton, biUnion, finite_range, finite_singleton, finite_toSet, isClosed_zeroLocus, isConstructible, isConstructible_compl, isOpen_compl, isRetrocompact_zeroLocus_compl
-/
lemma isConstructible_toSet (S : ConstructibleSetData R) :
    IsConstructible S.toSet := by
  refine .biUnion S.finite_toSet fun _ _ => .sdiff ?_ ?_
  · rw [← isConstructible_compl]
    exact (isRetrocompact_zeroLocus_compl (Set.finite_range _)).isConstructible
      (isClosed_zeroLocus _).isOpen_compl
  · rw [← isConstructible_compl]
    exact (isRetrocompact_zeroLocus_compl (Set.finite_singleton _)).isConstructible
      (isClosed_zeroLocus _).isOpen_compl

end ConstructibleSetData

/--
lemma `exists_constructibleSetData_iff` / 引理 `exists_constructibleSetData_iff`

English:
lemma exists_constructibleSetData_iff
  given: {s : Set (PrimeSpectrum R)}
  proof: by
  refine ⟨fun ⟨S, H⟩ => H ▸ S.isConstructible_toSet, fun H => ?_⟩
  induction s, H using IsConstructible.induction_of_isTopologicalBasis
      _ (isTopologicalBasis_basic_opens (R := R)) with
  | isCompact_basis i => exact isCompact_basicOpen _
  | sdiff i s hs =>
    have : Finite s := hs
    re

中文:
引理 exists_constructibleSetData_iff
  条件: {s : Set (PrimeSpectrum R)}
  证明: by
  refine ⟨fun ⟨S, H⟩ => H ▸ S.isConstructible_toSet, fun H => ?_⟩
  induction s, H using IsConstructible.induction_of_isTopologicalBasis
      _ (isTopologicalBasis_basic_opens (R := R)) with
  | isCompact_basis i => exact isCompact_basicOpen _
  | sdiff i s hs =>
    have : Finite s := hs
    re

Depends on / 依赖: BasicConstructibleSetData, BasicConstructibleSetData.toSet, ConstructibleSetData, ConstructibleSetData.toSet, Finite, Finite.equivFin, Finset, Finset.mem_singleton, IsConstructible, IsConstructible.induction_of_isTopologicalBasis, Nat.card, S.isConstructible_toSet, Set.iUnion_iUnion_eq_left, basicOpen_eq_zeroLocus_compl, equivFin, iUnion_iUnion_eq_left, induction_of_isTopologicalBasis, isCompact_basicOpen, isCompact_basis, isConstructible_toSet
-/
lemma exists_constructibleSetData_iff {s : Set (PrimeSpectrum R)} :
    (exists S : ConstructibleSetData R, S.toSet = s) ↔ IsConstructible s := by
  refine ⟨fun ⟨S, H⟩ => H ▸ S.isConstructible_toSet, fun H => ?_⟩
  induction s, H using IsConstructible.induction_of_isTopologicalBasis
      _ (isTopologicalBasis_basic_opens (R := R)) with
  | isCompact_basis i => exact isCompact_basicOpen _
  | sdiff i s hs =>
    have : Finite s := hs
    refine ⟨{⟨i, Nat.card s, fun i => ((Finite.equivFin s).symm i).1⟩}, ?_⟩
    simp only [ConstructibleSetData.toSet, Finset.mem_singleton, BasicConstructibleSetData.toSet,
      Set.iUnion_iUnion_eq_left, basicOpen_eq_zeroLocus_compl, ← Set.compl_iInter₂,
        compl_sdiff_compl, ← zeroLocus_iUnion₂, Set.biUnion_of_singleton]
    congr! 2
    ext
    simp [← (Finite.equivFin s).exists_congr_right, -Nat.card_coe_set_eq]
  | union s hs t ht Hs Ht =>
    obtain ⟨S, rfl⟩ := Hs
    obtain ⟨T, rfl⟩ := Ht
    refine ⟨S union T, ?_⟩
    simp only [ConstructibleSetData.toSet, Set.biUnion_union, ← Finset.mem_coe, Finset.coe_union]

universe u in
@[stacks 00F8 "without the finite presentation part"]
-- TODO: show that the constructed `f` is of finite presentation
/--
lemma `exists_range_eq_of_isConstructible` / 引理 `exists_range_eq_of_isConstructible`

English:
lemma exists_range_eq_of_isConstructible
  statement: {R : Type u} [CommRing R]
  proof: by
  obtain ⟨s, rfl⟩ := exists_constructibleSetData_iff.mpr hs
  refine ⟨Π i : s, Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range i.1.g)) i.1.f),
    inferInstance, algebraMap _ _, ?_⟩
  rw [← iUnion_range_comap_comp_evalRingHom]; rw [ConstructibleSetData.toSet]
  simp_rw [← Finset.mem_c

中文:
引理 exists_range_eq_of_isConstructible
  结论: {R : 类型u} [CommRing R]
  证明: by
  obtain ⟨s, rfl⟩ := exists_constructibleSetData_iff.mpr hs
  refine ⟨Π i : s, Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range i.1.g)) i.1.f),
    inferInstance, algebraMap _ _, ?_⟩
  rw [← iUnion_range_comap_comp_evalRingHom]; rw [ConstructibleSetData.toSet]
  simp_rw [← Finset.mem_c

Depends on / 依赖: ConstructibleSetData, ConstructibleSetData.toSet, Finset, Finset.mem_coe, Ideal.Quotient.mk, Ideal.span, Localization, Localization.Away, Quotient, Set.biUnion_eq_iUnion, Set.range, algebraMap, biUnion_eq_iUnion, exists_constructibleSetData_iff, exists_constructibleSetData_iff.mpr, iUnion_range_comap_comp_evalRingHom, mem_coe, simp_rw
-/
lemma exists_range_eq_of_isConstructible {R : Type u} [CommRing R]
    {s : Set (PrimeSpectrum R)} (hs : IsConstructible s) :
    exists (S : Type u) (_ : CommRing S) (f : R ->+* S), Set.range (comap f) = s := by
  obtain ⟨s, rfl⟩ := exists_constructibleSetData_iff.mpr hs
  refine ⟨Π i : s, Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range i.1.g)) i.1.f),
    inferInstance, algebraMap _ _, ?_⟩
  rw [← iUnion_range_comap_comp_evalRingHom]; rw [ConstructibleSetData.toSet]
  simp_rw [← Finset.mem_coe, Set.biUnion_eq_iUnion]
  congr! with _ _ C
  let I := Ideal.span (Set.range C.1.g)
  let f := Ideal.Quotient.mk I C.1.f
  trans comap (Ideal.Quotient.mk I) '' (Set.range (comap (algebraMap _ (Localization.Away f))))
  · rw [← Set.range_comp]; rfl
  · rw [localization_away_comap_range _ f, ← comap_basicOpen, TopologicalSpace.Opens.coe_comap,
      ContinuousMap.coe_mk, Set.image_preimage_eq_inter_range,
      range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, BasicConstructibleSetData.toSet,
      Set.sdiff_eq_compl_inter, basicOpen_eq_zeroLocus_compl, Ideal.mk_ker, zeroLocus_span]

@[stacks 00I0 "(1)"]
/--
lemma `isClosed_of_stableUnderSpecialization_of_isConstructible` / 引理 `isClosed_of_stableUnderSpecialization_of_isConstructible`

English:
lemma isClosed_of_stableUnderSpecialization_of_isConstructible
  statement: {R : Type*} [CommRing R]
  proof: by
  obtain ⟨S, _, f, rfl⟩ := exists_range_eq_of_isConstructible hs'
  exact isClosed_range_of_stableUnderSpecialization _ hs

@[stacks 00I0 "(1)"]

中文:
引理 isClosed_of_stableUnderSpecialization_of_isConstructible
  结论: {R : 类型} [CommRing R]
  证明: by
  obtain ⟨S, _, f, rfl⟩ := exists_range_eq_of_isConstructible hs'
  exact isClosed_range_of_stableUnderSpecialization _ hs

@[stacks 00I0 "(1)"]

Depends on / 依赖: exists_range_eq_of_isConstructible, isClosed_range_of_stableUnderSpecialization
-/
lemma isClosed_of_stableUnderSpecialization_of_isConstructible {R : Type*} [CommRing R]
    {s : Set (PrimeSpectrum R)} (hs : StableUnderSpecialization s) (hs' : IsConstructible s) :
    IsClosed s := by
  obtain ⟨S, _, f, rfl⟩ := exists_range_eq_of_isConstructible hs'
  exact isClosed_range_of_stableUnderSpecialization _ hs

@[stacks 00I0 "(1)"]
/--
lemma `isOpen_of_stableUnderGeneralization_of_isConstructible` / 引理 `isOpen_of_stableUnderGeneralization_of_isConstructible`

English:
lemma isOpen_of_stableUnderGeneralization_of_isConstructible
  statement: {R : Type*} [CommRing R]
  proof: by
  rw [← isClosed_compl_iff]
  exact isClosed_of_stableUnderSpecialization_of_isConstructible hs.compl hs'.compl

中文:
引理 isOpen_of_stableUnderGeneralization_of_isConstructible
  结论: {R : 类型} [CommRing R]
  证明: by
  rw [← isClosed_compl_iff]
  exact isClosed_of_stableUnderSpecialization_of_isConstructible hs.compl hs'.compl

Depends on / 依赖: hs.compl, isClosed_compl_iff, isClosed_of_stableUnderSpecialization_of_isConstructible
-/
lemma isOpen_of_stableUnderGeneralization_of_isConstructible {R : Type*} [CommRing R]
    {s : Set (PrimeSpectrum R)} (hs : StableUnderGeneralization s) (hs' : IsConstructible s) :
    IsOpen s := by
  rw [← isClosed_compl_iff]
  exact isClosed_of_stableUnderSpecialization_of_isConstructible hs.compl hs'.compl

end PrimeSpectrum
