/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic

/-!
# Relation of smoothness and `Ω[S⁄R]`

## Main results

- `retractionKerToTensorEquivSection`:
  Given a surjective algebra homomorphism `f : P →ₐ[R] S` with square-zero kernel `I`,
  there is a one-to-one correspondence between `P`-linear retractions of `I →ₗ[P] S ⊗[P] Ω[P/R]`
  and algebra homomorphism sections of `f`.
- `retractionKerCotangentToTensorEquivSection`:
  Given a surjective algebra homomorphism `f : P →ₐ[R] S` with kernel `I`,
  there is a one-to-one correspondence between `P`-linear retractions of `I/I² →ₗ[P] S ⊗[P] Ω[P/R]`
  and algebra homomorphism sections of `f‾ : P/I² → S`.

## Future projects

- Show that being smooth is local on stalks.
- Show that being formally smooth is Zariski-local (very hard).

## References

- https://stacks.math.columbia.edu/tag/00TH
- [B. Iversen, *Generic Local Structure of the Morphisms in Commutative Algebra*][iversen]


-/

@[expose] public section

universe u

open TensorProduct KaehlerDifferential

open Function (Surjective)

variable {R P S : Type*} [CommRing R] [CommRing P] [CommRing S]
variable [Algebra R P] [Algebra P S]

section ofSection

variable [Algebra R S] [IsScalarTower R P S]
-- Suppose we have a section (as an algebra homomorphism) of `P →ₐ[R] S`.
variable (g : S ->ₐ[R] P)

/--
Given a surjective algebra homomorphism `f : P →ₐ[R] S` with square-zero kernel `I`,
and a section `g : S →ₐ[R] P` (as an algebra homomorphism),
we get an `R`-derivation `P → I` via `x ↦ x - g (f x)`.
-/
@[simps]
/--
Definition of `derivationOfSectionOfKerSqZero` / `derivationOfSectionOfKerSqZero` 的定义

English:
definition derivationOfSectionOfKerSqZero
  signature: (f : P ->ₐ[R] S) (hf' : (RingHom.ker f) ^ 2 = ⊥) (g : S ->ₐ[R] P)
  body: ⟨x - g (f x), by
    simpa [RingHom.mem_ker, sub_eq_zero] using AlgHom.congr_fun hg.symm (f x)⟩
  map_add' x y := by simp only [map_add, AddMemClass.mk_add_mk, Subtype.mk.injEq]; ring
  map_smul' x y := by
    ext
    simp only [Algebra.smul_def, map_mul, AlgHom.commutes,
      RingHom.id_apply, Sub

中文:
定义 derivationOfSectionOfKerSqZero
  签名: (f : P ->ₐ[R] S) (hf' : (环态射.ker f) ^ 2 = ⊥) (g : S ->ₐ[R] P)
  定义体: ⟨x - g (f x), by
    simpa [RingHom.mem_ker, sub_eq_zero] using AlgHom.congr_fun hg.symm (f x)⟩
  map_add' x y := by simp only [map_add, AddMemClass.mk_add_mk, Subtype.mk.injEq]; ring
  map_smul' x y := by
    ext
    simp only [Algebra.smul_def, map_mul, AlgHom.commutes,
      RingHom.id_apply, Sub

Depends on / 依赖: AddHom, AddHom.coe_mk, AddMemClass, AddMemClass.mk_add_mk, AlgHom, AlgHom.commutes, AlgHom.congr_fun, Algebra, Algebra.smul_def, Ideal.mem_b, LinearMap, LinearMap.coe_mk, RingHom, RingHom.id_apply, RingHom.mem_ker, Submodule, Submodule.coe_smul_of_tower, Submodule.mk_eq_zero, Subtype, Subtype.mk.injEq
-/
def derivationOfSectionOfKerSqZero (f : P ->ₐ[R] S) (hf' : (RingHom.ker f) ^ 2 = ⊥) (g : S ->ₐ[R] P)
    (hg : f.comp g = AlgHom.id R S) : Derivation R P (RingHom.ker f) where
  toFun x := ⟨x - g (f x), by
    simpa [RingHom.mem_ker, sub_eq_zero] using AlgHom.congr_fun hg.symm (f x)⟩
  map_add' x y := by simp only [map_add, AddMemClass.mk_add_mk, Subtype.mk.injEq]; ring
  map_smul' x y := by
    ext
    simp only [Algebra.smul_def, map_mul, AlgHom.commutes,
      RingHom.id_apply, Submodule.coe_smul_of_tower]
    ring
  map_one_eq_zero' := by simp only [LinearMap.coe_mk, AddHom.coe_mk, map_one, sub_self,
    Submodule.mk_eq_zero]
  leibniz' a b := by
    have : (a - g (f a)) * (b - g (f b)) = 0 := by
      rw [← Ideal.mem_bot]; rw [← hf']; rw [pow_two]
      apply Ideal.mul_mem_mul
      · simpa [RingHom.mem_ker, sub_eq_zero] using AlgHom.congr_fun hg.symm (f a)
      · simpa [RingHom.mem_ker, sub_eq_zero] using AlgHom.congr_fun hg.symm (f b)
    ext
    rw [← sub_eq_zero]
    conv_rhs => rw [← neg_zero, ← this]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, SetLike.mk_smul_mk, smul_eq_mul, mul_sub,
      AddMemClass.mk_add_mk, sub_mul, neg_sub]
    ring

variable (hf' : (RingHom.ker (algebraMap P S)) ^ 2 = ⊥)
  (hg : (IsScalarTower.toAlgHom R P S).comp g = AlgHom.id R S)
include hf' hg

/--
lemma `isScalarTower_of_section_of_ker_sqZero` / 引理 `isScalarTower_of_section_of_ker_sqZero`

English:
lemma isScalarTower_of_section_of_ker_sqZero
  proof: g.toRingHom.toAlgebra; IsScalarTower P S (RingHom.ker (algebraMap P S)) := by
  let := g.toRingHom.toAlgebra
  constructor
  intro p s m
  ext
  change g (p • s) * m = p * (g s * m)
  simp only [Algebra.smul_def, map_mul, mul_assoc, mul_left_comm _ (g s)]
  congr 1
  rw [← sub_eq_zero]; rw [← Ideal.

中文:
引理 isScalarTower_of_section_of_ker_sqZero
  证明: g.toRingHom.toAlgebra; IsScalarTower P S (RingHom.ker (algebraMap P S)) := by
  let := g.toRingHom.toAlgebra
  constructor
  intro p s m
  ext
  change g (p • s) * m = p * (g s * m)
  simp only [Algebra.smul_def, map_mul, mul_assoc, mul_left_comm _ (g s)]
  congr 1
  rw [← sub_eq_zero]; rw [← Ideal.

Depends on / 依赖: AlgHom, AlgHom.congr_fun, Algebra, Algebra.smul_def, Ideal.mem_bot, Ideal.mul_mem_mul, IsScalarTower, RingHom, RingHom.ker, RingHom.mem_ker, algebraMap, congr_fun, g.toRingHom.toAlgebra, map_mul, mem_bot, mem_ker, mul_assoc, mul_left_comm, mul_mem_mul, pow_two
-/
lemma isScalarTower_of_section_of_ker_sqZero :
    letI := g.toRingHom.toAlgebra; IsScalarTower P S (RingHom.ker (algebraMap P S)) := by
  let := g.toRingHom.toAlgebra
  constructor
  intro p s m
  ext
  change g (p • s) * m = p * (g s * m)
  simp only [Algebra.smul_def, map_mul, mul_assoc, mul_left_comm _ (g s)]
  congr 1
  rw [← sub_eq_zero]; rw [← Ideal.mem_bot]; rw [← hf']; rw [pow_two]; rw [← sub_mul]
  refine Ideal.mul_mem_mul ?_ m.2
  simpa [RingHom.mem_ker, sub_eq_zero] using AlgHom.congr_fun hg (algebraMap P S p)

/--
Given a surjective algebra hom `f : P →ₐ[R] S` with square-zero kernel `I`,
and a section `g : S →ₐ[R] P` (as algebra homs),
we get a retraction of the injection `I → S ⊗[P] Ω[P/R]`.
-/
noncomputable
/--
Definition of `retractionOfSectionOfKerSqZero` / `retractionOfSectionOfKerSqZero` 的定义

English:
definition retractionOfSectionOfKerSqZero
  signature: : S otimes[P] Ω[P⁄R] ->ₗ[P] RingHom.ker (algebraMap P S)
  body: letI := g.toRingHom.toAlgebra
  haveI := isScalarTower_of_section_of_ker_sqZero g hf' hg
  letI f : _ ->ₗ[P] RingHom.ker (algebraMap P S) := (derivationOfSectionOfKerSqZero
    (IsScalarTower.toAlgHom R P S) hf' g hg).liftKaehlerDifferential
  (f.liftBaseChange S).restrictScalars P

中文:
定义 retractionOfSectionOfKerSqZero
  签名: : S otimes[P] Ω[P⁄R] ->ₗ[P] 环态射.ker (algebraMap P S)
  定义体: letI := g.toRingHom.toAlgebra
  haveI := isScalarTower_of_section_of_ker_sqZero g hf' hg
  letI f : _ ->ₗ[P] RingHom.ker (algebraMap P S) := (derivationOfSectionOfKerSqZero
    (IsScalarTower.toAlgHom R P S) hf' g hg).liftKaehlerDifferential
  (f.liftBaseChange S).restrictScalars P

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, RingHom, RingHom.ker, algebraMap, derivationOfSectionOfKerSqZero, f.liftBaseChange, g.toRingHom.toAlgebra, isScalarTower_of_section_of_ker_sqZero, liftBaseChange, liftKaehlerDifferential, restrictScalars, toAlgHom, toAlgebra, toRingHom
-/
def retractionOfSectionOfKerSqZero : S otimes[P] Ω[P⁄R] ->ₗ[P] RingHom.ker (algebraMap P S) :=
  letI := g.toRingHom.toAlgebra
  haveI := isScalarTower_of_section_of_ker_sqZero g hf' hg
  letI f : _ ->ₗ[P] RingHom.ker (algebraMap P S) := (derivationOfSectionOfKerSqZero
    (IsScalarTower.toAlgHom R P S) hf' g hg).liftKaehlerDifferential
  (f.liftBaseChange S).restrictScalars P

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `retractionOfSectionOfKerSqZero_tmul_D` / 引理 `retractionOfSectionOfKerSqZero_tmul_D`

English:
lemma retractionOfSectionOfKerSqZero_tmul_D
  given: (s : S) (t : P)
  proof: by
  let := g.toRingHom.toAlgebra
  have := isScalarTower_of_section_of_ker_sqZero g hf' hg
  simp only [retractionOfSectionOfKerSqZero, LinearMap.coe_restrictScalars,
    LinearMap.liftBaseChange_tmul, SetLike.val_smul_of_tower]
  -- The issue is a mismatch between `RingHom.ker (algebraMap P S)` an

中文:
引理 retractionOfSectionOfKerSqZero_tmul_D
  条件: (s : S) (t : P)
  证明: by
  let := g.toRingHom.toAlgebra
  have := isScalarTower_of_section_of_ker_sqZero g hf' hg
  simp only [retractionOfSectionOfKerSqZero, LinearMap.coe_restrictScalars,
    LinearMap.liftBaseChange_tmul, SetLike.val_smul_of_tower]
  -- The issue is a mismatch between `RingHom.ker (algebraMap P S)` an

Depends on / 依赖: LinearMap, LinearMap.coe_restrictScalars, LinearMap.liftBaseChange_tmul, SetLike, SetLike.val_smul_of_tower, coe_restrictScalars, g.toRingHom.toAlgebra, isScalarTower_of_section_of_ker_sqZero, liftBaseChange_tmul, retractionOfSectionOfKerSqZero, toAlgebra, toRingHom, val_smul_of_tower
-/
lemma retractionOfSectionOfKerSqZero_tmul_D (s : S) (t : P) :
    retractionOfSectionOfKerSqZero g hf' hg (s otimesₜ .D _ _ t) =
      g s * t - g s * g (algebraMap _ _ t) := by
  let := g.toRingHom.toAlgebra
  have := isScalarTower_of_section_of_ker_sqZero g hf' hg
  simp only [retractionOfSectionOfKerSqZero, LinearMap.coe_restrictScalars,
    LinearMap.liftBaseChange_tmul, SetLike.val_smul_of_tower]
  -- The issue is a mismatch between `RingHom.ker (algebraMap P S)` and
  -- `RingHom.ker (IsScalarTower.toAlgHom R P S)`, but `rw` and `simp` can't rewrite it away...
  erw [Derivation.liftKaehlerDifferential_comp_D]
  exact mul_sub (g s) t (g (algebraMap P S t))

/--
lemma `retractionOfSectionOfKerSqZero_comp_kerToTensor` / 引理 `retractionOfSectionOfKerSqZero_comp_kerToTensor`

English:
lemma retractionOfSectionOfKerSqZero_comp_kerToTensor
  proof: by
  ext x; simp [RingHom.mem_ker.mp x.2]

中文:
引理 retractionOfSectionOfKerSqZero_comp_kerToTensor
  证明: by
  ext x; simp [RingHom.mem_ker.mp x.2]

Depends on / 依赖: RingHom, RingHom.mem_ker.mp, mem_ker
-/
lemma retractionOfSectionOfKerSqZero_comp_kerToTensor :
    (retractionOfSectionOfKerSqZero g hf' hg).comp (kerToTensor R P S) = LinearMap.id := by
  ext x; simp [RingHom.mem_ker.mp x.2]

end ofSection

section ofRetraction

variable (l : S otimes[P] Ω[P⁄R] ->ₗ[P] RingHom.ker (algebraMap P S))
variable (hl : l.comp (kerToTensor R P S) = LinearMap.id)
include hl

-- suppose we have a (set-theoretic) section
variable (σ : S -> P) (hσ : forall x, algebraMap P S (σ x) = x)

/--
lemma `sectionOfRetractionKerToTensorAux_prop` / 引理 `sectionOfRetractionKerToTensorAux_prop`

English:
lemma sectionOfRetractionKerToTensorAux_prop
  given: (x y) (h : algebraMap P S x = algebraMap P S y)
  proof: by
  rw [sub_eq_iff_eq_add]; rw [sub_add_comm]; rw [← sub_eq_iff_eq_add]; rw [← Submodule.coe_sub]; rw [← map_sub]; rw [← tmul_sub]; rw [← map_sub]
  exact congr_arg Subtype.val (LinearMap.congr_fun hl.symm ⟨x - y, by simp [RingHom.mem_ker, h]⟩)

中文:
引理 sectionOfRetractionKerToTensorAux_prop
  条件: (x y) (h : algebraMap P S x = algebraMap P S y)
  证明: by
  rw [sub_eq_iff_eq_add]; rw [sub_add_comm]; rw [← sub_eq_iff_eq_add]; rw [← Submodule.coe_sub]; rw [← map_sub]; rw [← tmul_sub]; rw [← map_sub]
  exact congr_arg Subtype.val (LinearMap.congr_fun hl.symm ⟨x - y, by simp [RingHom.mem_ker, h]⟩)

Depends on / 依赖: LinearMap, LinearMap.congr_fun, RingHom, RingHom.mem_ker, Submodule, Submodule.coe_sub, Subtype, Subtype.val, coe_sub, congr_arg, congr_fun, hl.symm, map_sub, mem_ker, sub_add_comm, sub_eq_iff_eq_add, tmul_sub
-/
lemma sectionOfRetractionKerToTensorAux_prop (x y) (h : algebraMap P S x = algebraMap P S y) :
    x - l (1 otimesₜ .D _ _ x) = y - l (1 otimesₜ .D _ _ y) := by
  rw [sub_eq_iff_eq_add]; rw [sub_add_comm]; rw [← sub_eq_iff_eq_add]; rw [← Submodule.coe_sub]; rw [← map_sub]; rw [← tmul_sub]; rw [← map_sub]
  exact congr_arg Subtype.val (LinearMap.congr_fun hl.symm ⟨x - y, by simp [RingHom.mem_ker, h]⟩)

variable [Algebra R S] [IsScalarTower R P S]
variable (hf' : (RingHom.ker (algebraMap P S)) ^ 2 = ⊥)
include hf'

/--
Given a surjective algebra homomorphism `f : P →ₐ[R] S` with square-zero kernel `I`.
Let `σ` be an arbitrary (set-theoretic) section of `f`.
Suppose we have a retraction `l` of the injection `I →ₗ[P] S ⊗[P] Ω[P/R]`, then
`x ↦ σ x - l (1 ⊗ D (σ x))` is an algebra homomorphism and a section to `f`.
-/
noncomputable
/--
Definition of `sectionOfRetractionKerToTensorAux` / `sectionOfRetractionKerToTensorAux` 的定义

English:
definition sectionOfRetractionKerToTensorAux
  signature: : S ->ₐ[R] P where
  body: σ x - l (1 otimesₜ .D _ _ (σ x))
  map_one' := by simp [sectionOfRetractionKerToTensorAux_prop l hl (σ 1) 1 (by simp [hσ])]
  map_mul' a b := by
    have (x y : _) : (l x).1 * (l y).1 = 0 := by
      rw [← Ideal.mem_bot]; rw [← hf']; rw [pow_two]; exact Ideal.mul_mem_mul (l x).2 (l y).2
    simp onl

中文:
定义 sectionOfRetractionKerToTensorAux
  签名: : S ->ₐ[R] P where
  定义体: σ x - l (1 otimesₜ .D _ _ (σ x))
  map_one' := by simp [sectionOfRetractionKerToTensorAux_prop l hl (σ 1) 1 (by simp [hσ])]
  map_mul' a b := by
    have (x y : _) : (l x).1 * (l y).1 = 0 := by
      rw [← Ideal.mem_bot]; rw [← hf']; rw [pow_two]; exact Ideal.mul_mem_mul (l x).2 (l y).2
    simp onl
-/
def sectionOfRetractionKerToTensorAux : S ->ₐ[R] P where
  toFun x := σ x - l (1 otimesₜ .D _ _ (σ x))
  map_one' := by simp [sectionOfRetractionKerToTensorAux_prop l hl (σ 1) 1 (by simp [hσ])]
  map_mul' a b := by
    have (x y : _) : (l x).1 * (l y).1 = 0 := by
      rw [← Ideal.mem_bot]; rw [← hf']; rw [pow_two]; exact Ideal.mul_mem_mul (l x).2 (l y).2
    simp only [sectionOfRetractionKerToTensorAux_prop l hl (σ (a * b)) (σ a * σ b) (by simp [hσ]),
      Derivation.leibniz, tmul_add, tmul_smul, map_add, map_smul, Submodule.coe_add,
      SetLike.val_smul, smul_eq_mul, mul_sub, sub_mul, this, sub_zero]
    ring
  map_add' a b := by
    simp only [sectionOfRetractionKerToTensorAux_prop l hl (σ (a + b)) (σ a + σ b) (by simp [hσ]),
      map_add, tmul_add, Submodule.coe_add, add_sub_add_comm]
  map_zero' := by simp [sectionOfRetractionKerToTensorAux_prop l hl (σ 0) 0 (by simp [hσ])]
  commutes' r := by
    simp [sectionOfRetractionKerToTensorAux_prop l hl
      (σ (algebraMap R S r)) (algebraMap R P r) (by simp [hσ, ← IsScalarTower.algebraMap_apply])]

/--
lemma `sectionOfRetractionKerToTensorAux_algebraMap` / 引理 `sectionOfRetractionKerToTensorAux_algebraMap`

English:
lemma sectionOfRetractionKerToTensorAux_algebraMap
  given: (x : P)
  proof: sectionOfRetractionKerToTensorAux_prop l hl _ x (by simp [hσ])

中文:
引理 sectionOfRetractionKerToTensorAux_algebraMap
  条件: (x : P)
  证明: sectionOfRetractionKerToTensorAux_prop l hl _ x (by simp [hσ])
-/
lemma sectionOfRetractionKerToTensorAux_algebraMap (x : P) :
    sectionOfRetractionKerToTensorAux l hl σ hσ hf' (algebraMap P S x) = x - l (1 otimesₜ .D _ _ x) :=
  sectionOfRetractionKerToTensorAux_prop l hl _ x (by simp [hσ])

variable (hf : Surjective (algebraMap P S))
include hf

/--
lemma `toAlgHom_comp_sectionOfRetractionKerToTensorAux` / 引理 `toAlgHom_comp_sectionOfRetractionKerToTensorAux`

English:
lemma toAlgHom_comp_sectionOfRetractionKerToTensorAux
  proof: by
  ext x
  obtain ⟨x, rfl⟩ := hf x
  simp [sectionOfRetractionKerToTensorAux_algebraMap, RingHom.mem_ker.mp]

中文:
引理 toAlgHom_comp_sectionOfRetractionKerToTensorAux
  证明: by
  ext x
  obtain ⟨x, rfl⟩ := hf x
  simp [sectionOfRetractionKerToTensorAux_algebraMap, RingHom.mem_ker.mp]

Depends on / 依赖: RingHom, RingHom.mem_ker.mp, mem_ker, sectionOfRetractionKerToTensorAux_algebraMap
-/
lemma toAlgHom_comp_sectionOfRetractionKerToTensorAux :
    (IsScalarTower.toAlgHom R P S).comp
      (sectionOfRetractionKerToTensorAux l hl σ hσ hf') = AlgHom.id _ _ := by
  ext x
  obtain ⟨x, rfl⟩ := hf x
  simp [sectionOfRetractionKerToTensorAux_algebraMap, RingHom.mem_ker.mp]

/--
Definition of `sectionOfRetractionKerToTensor` / `sectionOfRetractionKerToTensor` 的定义

English:
definition sectionOfRetractionKerToTensor
  signature: : S ->ₐ[R] P
  body: sectionOfRetractionKerToTensorAux l hl _ (fun x => (hf x).choose_spec) hf'

@[simp]

中文:
定义 sectionOfRetractionKerToTensor
  签名: : S ->ₐ[R] P
  定义体: sectionOfRetractionKerToTensorAux l hl _ (fun x => (hf x).choose_spec) hf'

@[simp]

Depends on / 依赖: CompactSpace, CompactSpace.sigmaCompact, SigmaCompactSpace, sigmaCompact
-/
noncomputable def sectionOfRetractionKerToTensor : S ->ₐ[R] P :=
  sectionOfRetractionKerToTensorAux l hl _ (fun x => (hf x).choose_spec) hf'

@[simp]
/--
lemma `sectionOfRetractionKerToTensor_algebraMap` / 引理 `sectionOfRetractionKerToTensor_algebraMap`

English:
lemma sectionOfRetractionKerToTensor_algebraMap
  given: (x : P)
  proof: sectionOfRetractionKerToTensorAux_algebraMap l hl _ _ hf' x

@[simp]

中文:
引理 sectionOfRetractionKerToTensor_algebraMap
  条件: (x : P)
  证明: sectionOfRetractionKerToTensorAux_algebraMap l hl _ _ hf' x

@[simp]
-/
lemma sectionOfRetractionKerToTensor_algebraMap (x : P) :
    sectionOfRetractionKerToTensor l hl hf' hf (algebraMap P S x) = x - l (1 otimesₜ .D _ _ x) :=
  sectionOfRetractionKerToTensorAux_algebraMap l hl _ _ hf' x

@[simp]
/--
lemma `toAlgHom_comp_sectionOfRetractionKerToTensor` / 引理 `toAlgHom_comp_sectionOfRetractionKerToTensor`

English:
lemma toAlgHom_comp_sectionOfRetractionKerToTensor
  proof: toAlgHom_comp_sectionOfRetractionKerToTensorAux (hf := hf) ..

中文:
引理 toAlgHom_comp_sectionOfRetractionKerToTensor
  证明: toAlgHom_comp_sectionOfRetractionKerToTensorAux (hf := hf) ..

Depends on / 依赖: sigmaCompactSpace_of_locallyCompact_secondCountable, toAlgHom_comp_sectionOfRetractionKerToTensorAux
-/
lemma toAlgHom_comp_sectionOfRetractionKerToTensor :
    (IsScalarTower.toAlgHom R P S).comp
      (sectionOfRetractionKerToTensor l hl hf' hf) = AlgHom.id _ _ :=
  toAlgHom_comp_sectionOfRetractionKerToTensorAux (hf := hf) ..

end ofRetraction

variable [Algebra R S] [IsScalarTower R P S]
variable (hf' : (RingHom.ker (algebraMap P S)) ^ 2 = ⊥) (hf : Surjective (algebraMap P S))

/--
Given a surjective algebra homomorphism `f : P →ₐ[R] S` with square-zero kernel `I`,
there is a one-to-one correspondence between `P`-linear retractions of `I →ₗ[P] S ⊗[P] Ω[P/R]`
and algebra homomorphism sections of `f`.
-/
noncomputable
/--
Definition of `retractionKerToTensorEquivSection` / `retractionKerToTensorEquivSection` 的定义

English:
definition retractionKerToTensorEquivSection
  signature: :
  body: ⟨_, toAlgHom_comp_sectionOfRetractionKerToTensor _ l.2 hf' hf⟩
  invFun g := ⟨_, retractionOfSectionOfKerSqZero_comp_kerToTensor _ hf' g.2⟩
  left_inv l := by
    ext s p
    obtain ⟨s, rfl⟩ := hf s
    have (x y : _) : (l.1 x).1 * (l.1 y).1 = 0 := by
      rw [← Ideal.mem_bot]; rw [← hf']; rw [pow_

中文:
定义 retractionKerToTensorEquivSection
  签名: :
  定义体: ⟨_, toAlgHom_comp_sectionOfRetractionKerToTensor _ l.2 hf' hf⟩
  invFun g := ⟨_, retractionOfSectionOfKerSqZero_comp_kerToTensor _ hf' g.2⟩
  left_inv l := by
    ext s p
    obtain ⟨s, rfl⟩ := hf s
    have (x y : _) : (l.1 x).1 * (l.1 y).1 = 0 := by
      rw [← Ideal.mem_bot]; rw [← hf']; rw [pow_

Depends on / 依赖: toAlgHom_comp_sectionOfRetractionKerToTensor
-/
def retractionKerToTensorEquivSection :
    { l // l ∘ₗ (kerToTensor R P S) = LinearMap.id } ≃
      { g // (IsScalarTower.toAlgHom R P S).comp g = AlgHom.id R S } where
  toFun l := ⟨_, toAlgHom_comp_sectionOfRetractionKerToTensor _ l.2 hf' hf⟩
  invFun g := ⟨_, retractionOfSectionOfKerSqZero_comp_kerToTensor _ hf' g.2⟩
  left_inv l := by
    ext s p
    obtain ⟨s, rfl⟩ := hf s
    have (x y : _) : (l.1 x).1 * (l.1 y).1 = 0 := by
      rw [← Ideal.mem_bot]; rw [← hf']; rw [pow_two]; exact Ideal.mul_mem_mul (l.1 x).2 (l.1 y).2
    simp only [AlgebraTensorModule.curry_apply,
      Derivation.coe_comp, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Derivation.coeFn_coe,
      Function.comp_apply, curry_apply, retractionOfSectionOfKerSqZero_tmul_D,
      sectionOfRetractionKerToTensor_algebraMap, ← mul_sub, sub_sub_cancel]
    rw [sub_mul]
    simp only [this, Algebra.algebraMap_eq_smul_one, ← smul_tmul', LinearMapClass.map_smul,
      SetLike.val_smul, smul_eq_mul, sub_zero]
  right_inv g := by ext s; obtain ⟨s, rfl⟩ := hf s; simp

variable (R P S) in
/--
Given a tower of algebras `S/P/R`, with `I = ker(P → S)`,
this is the `R`-derivative `P/I² → S ⊗[P] Ω[P⁄R]` given by `[x] ↦ 1 ⊗ D x`.
-/
noncomputable
/--
Definition of `derivationQuotKerSq` / `derivationQuotKerSq` 的定义

English:
definition derivationQuotKerSq
  signature: :
  body: by
  letI := Submodule.liftQ ((RingHom.ker (algebraMap P S) ^ 2).restrictScalars R)
    (((mk P S _ 1).restrictScalars R).comp (KaehlerDifferential.D R P).toLinearMap)
  refine ⟨this ?_, ?_, ?_⟩
  · rintro x hx
    simp only [Submodule.restrictScalars_mem, pow_two] at hx
    simp only [LinearMap.mem

中文:
定义 derivationQuotKerSq
  签名: :
  定义体: by
  letI := Submodule.liftQ ((RingHom.ker (algebraMap P S) ^ 2).restrictScalars R)
    (((mk P S _ 1).restrictScalars R).comp (KaehlerDifferential.D R P).toLinearMap)
  refine ⟨this ?_, ?_, ?_⟩
  · rintro x hx
    simp only [Submodule.restrictScalars_mem, pow_two] at hx
    simp only [LinearMap.mem

Depends on / 依赖: Derivation, Derivation.coeFn_coe, Derivation.leibniz, Function, Function.comp_apply, KaehlerDifferential, KaehlerDifferential.D, LinearMap, LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearMap.mem_ker, RingHom, RingHom.ker, Submodule, Submodule.liftQ, Submodule.restrictScalars_mem, Submodule.smul_induction_on, algebraMap, coeFn_coe, coe_comp
-/
def derivationQuotKerSq :
    Derivation R (P ⧸ (RingHom.ker (algebraMap P S) ^ 2)) (S otimes[P] Ω[P⁄R]) := by
  letI := Submodule.liftQ ((RingHom.ker (algebraMap P S) ^ 2).restrictScalars R)
    (((mk P S _ 1).restrictScalars R).comp (KaehlerDifferential.D R P).toLinearMap)
  refine ⟨this ?_, ?_, ?_⟩
  · rintro x hx
    simp only [Submodule.restrictScalars_mem, pow_two] at hx
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Derivation.coeFn_coe, Function.comp_apply, mk_apply]
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro x hx y hy
      simp only [smul_eq_mul, Derivation.leibniz, tmul_add, ← smul_tmul, Algebra.smul_def,
        mul_one, RingHom.mem_ker.mp hx, RingHom.mem_ker.mp hy, zero_tmul, zero_add]
    · intro x y hx hy; simp only [map_add, hx, hy, tmul_add, zero_add]
  · change (1 : S) otimesₜ[P] KaehlerDifferential.D R P 1 = 0; simp
  · intro a b
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    change (1 : S) otimesₜ[P] KaehlerDifferential.D R P (a * b) =
      Ideal.Quotient.mk _ a • ((1 : S) otimesₜ[P] KaehlerDifferential.D R P b) +
      Ideal.Quotient.mk _ b • ((1 : S) otimesₜ[P] KaehlerDifferential.D R P a)
    simp only [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul,
      Derivation.leibniz, tmul_add, tmul_smul]

@[simp]
/--
lemma `derivationQuotKerSq_mk` / 引理 `derivationQuotKerSq_mk`

English:
lemma derivationQuotKerSq_mk
  given: (x : P)
  proof: rfl

中文:
引理 derivationQuotKerSq_mk
  条件: (x : P)
  证明: rfl
-/
lemma derivationQuotKerSq_mk (x : P) :
    derivationQuotKerSq R P S x = 1 otimesₜ .D R P x := rfl

variable (R P S) in
/--
Given a tower of algebras `S/P/R`, with `I = ker(P → S)` and `Q := P/I²`,
there is an isomorphism of `S`-modules `S ⊗[Q] Ω[Q/R] ≃ S ⊗[P] Ω[P/R]`.
-/
noncomputable
/--
Definition of `tensorKaehlerQuotKerSqEquiv` / `tensorKaehlerQuotKerSqEquiv` 的定义

English:
definition tensorKaehlerQuotKerSqEquiv
  signature: :
  body: letI f₁ := (derivationQuotKerSq R P S).liftKaehlerDifferential
  letI f₂ := AlgebraTensorModule.lift ((LinearMap.ringLmapEquivSelf S S _).symm f₁)
  letI f₃ := KaehlerDifferential.map R R P (P ⧸ (RingHom.ker (algebraMap P S) ^ 2))
  letI f₄ := ((mk (P ⧸ RingHom.ker (algebraMap P S) ^ 2) S _ 1).restr

中文:
定义 tensorKaehlerQuotKerSqEquiv
  签名: :
  定义体: letI f₁ := (derivationQuotKerSq R P S).liftKaehlerDifferential
  letI f₂ := AlgebraTensorModule.lift ((LinearMap.ringLmapEquivSelf S S _).symm f₁)
  letI f₃ := KaehlerDifferential.map R R P (P ⧸ (RingHom.ker (algebraMap P S) ^ 2))
  letI f₄ := ((mk (P ⧸ RingHom.ker (algebraMap P S) ^ 2) S _ 1).restr

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.lift, KaehlerDifferential, KaehlerDifferential.map, LinearMap, LinearMap.congr_fun, LinearMap.id, LinearMap.ringLmapEquivSelf, RingHom, RingHom.ker, algebraMap, congr_fun, derivationQuotKerSq, invFun, left_inv, liftKaehlerDifferential, restrictScalars, ringLmapEquivSelf
-/
def tensorKaehlerQuotKerSqEquiv :
    S otimes[P ⧸ (RingHom.ker (algebraMap P S) ^ 2)] Ω[(P ⧸ (RingHom.ker (algebraMap P S) ^ 2))⁄R] ≃ₗ[S]
      S otimes[P] Ω[P⁄R] :=
  letI f₁ := (derivationQuotKerSq R P S).liftKaehlerDifferential
  letI f₂ := AlgebraTensorModule.lift ((LinearMap.ringLmapEquivSelf S S _).symm f₁)
  letI f₃ := KaehlerDifferential.map R R P (P ⧸ (RingHom.ker (algebraMap P S) ^ 2))
  letI f₄ := ((mk (P ⧸ RingHom.ker (algebraMap P S) ^ 2) S _ 1).restrictScalars P).comp f₃
  letI f₅ := AlgebraTensorModule.lift ((LinearMap.ringLmapEquivSelf S S _).symm f₄)
  { __ := f₂
    invFun := f₅
    left_inv := by
      suffices f₅.comp f₂ = LinearMap.id from LinearMap.congr_fun this
      ext a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      simp [f₁, f₂, f₃, f₄, f₅]
    right_inv := by
      suffices f₂.comp f₅ = LinearMap.id from LinearMap.congr_fun this
      ext a
      simp [f₁, f₂, f₃, f₄, f₅] }

@[simp]
/--
lemma `tensorKaehlerQuotKerSqEquiv_tmul_D` / 引理 `tensorKaehlerQuotKerSqEquiv_tmul_D`

English:
lemma tensorKaehlerQuotKerSqEquiv_tmul_D
  given: (s t)
  proof: by
  change s • (derivationQuotKerSq R P S).liftKaehlerDifferential
    (.D _ _ (Ideal.Quotient.mk _ t)) = _
  simp [smul_tmul']

@[simp]

中文:
引理 tensorKaehlerQuotKerSqEquiv_tmul_D
  条件: (s t)
  证明: by
  change s • (derivationQuotKerSq R P S).liftKaehlerDifferential
    (.D _ _ (Ideal.Quotient.mk _ t)) = _
  simp [smul_tmul']

@[simp]

Depends on / 依赖: Ideal.Quotient.mk, Quotient, derivationQuotKerSq, liftKaehlerDifferential, smul_tmul
-/
lemma tensorKaehlerQuotKerSqEquiv_tmul_D (s t) :
    tensorKaehlerQuotKerSqEquiv R P S (s otimesₜ .D _ _ (Ideal.Quotient.mk _ t)) = s otimesₜ .D _ _ t := by
  change s • (derivationQuotKerSq R P S).liftKaehlerDifferential
    (.D _ _ (Ideal.Quotient.mk _ t)) = _
  simp [smul_tmul']

@[simp]
/--
lemma `tensorKaehlerQuotKerSqEquiv_symm_tmul_D` / 引理 `tensorKaehlerQuotKerSqEquiv_symm_tmul_D`

English:
lemma tensorKaehlerQuotKerSqEquiv_symm_tmul_D
  given: (s t)
  proof: by
  apply (tensorKaehlerQuotKerSqEquiv R P S).injective
  simp

中文:
引理 tensorKaehlerQuotKerSqEquiv_symm_tmul_D
  条件: (s t)
  证明: by
  apply (tensorKaehlerQuotKerSqEquiv R P S).injective
  simp

Depends on / 依赖: injective, tensorKaehlerQuotKerSqEquiv
-/
lemma tensorKaehlerQuotKerSqEquiv_symm_tmul_D (s t) :
    (tensorKaehlerQuotKerSqEquiv R P S).symm (s otimesₜ .D _ _ t) =
      s otimesₜ .D _ _ (Ideal.Quotient.mk _ t) := by
  apply (tensorKaehlerQuotKerSqEquiv R P S).injective
  simp

set_option backward.isDefEq.respectTransparency false in
/--
Given a surjective algebra homomorphism `f : P →ₐ[R] S` with kernel `I`,
there is a one-to-one correspondence between `P`-linear retractions of `I/I² →ₗ[P] S ⊗[P] Ω[P/R]`
and algebra homomorphism sections of `f‾ : P/I² → S`.
-/
noncomputable
/--
Definition of `retractionKerCotangentToTensorEquivSection` / `retractionKerCotangentToTensorEquivSection` 的定义

English:
definition retractionKerCotangentToTensorEquivSection
  signature: :
  body: by
  let P' := P ⧸ (RingHom.ker (algebraMap P S) ^ 2)
  have h₁ : Surjective (algebraMap P' S) := Function.Surjective.of_comp (g := algebraMap P P') hf
  have h₂ : RingHom.ker (algebraMap P' S) ^ 2 = ⊥ := by
    rw [RingHom.algebraMap_toAlgebra]; rw [AlgHom.ker_kerSquareLift]; rw [Ideal.cotangentIde

中文:
定义 retractionKerCotangentToTensorEquivSection
  签名: :
  定义体: by
  let P' := P ⧸ (RingHom.ker (algebraMap P S) ^ 2)
  have h₁ : Surjective (algebraMap P' S) := Function.Surjective.of_comp (g := algebraMap P P') hf
  have h₂ : RingHom.ker (algebraMap P' S) ^ 2 = ⊥ := by
    rw [RingHom.algebraMap_toAlgebra]; rw [AlgHom.ker_kerSquareLift]; rw [Ideal.cotangentIde

Depends on / 依赖: AlgHom, AlgHom.ker_kerSquareLift, Cotangent, Function, Function.Surjective.of_comp, Ideal.cotangentEquivIdeal, Ideal.cotangentIdeal_square, IsScalarTower, IsScalarTower.toAlgHom, LinearEquiv, LinearEquiv.ofEq, RingHom, RingHom.algebraMap_toAlgebra, RingHom.ker, Surjective, algebraMap, algebraMap_toAlgebra, cotangentEquivIdeal, cotangentIdeal_square, ker_kerSquareLift
-/
def retractionKerCotangentToTensorEquivSection :
    { l // l ∘ₗ (kerCotangentToTensor R P S) = LinearMap.id } ≃
      { g // (IsScalarTower.toAlgHom R P S).kerSquareLift.comp g = AlgHom.id R S } := by
  let P' := P ⧸ (RingHom.ker (algebraMap P S) ^ 2)
  have h₁ : Surjective (algebraMap P' S) := Function.Surjective.of_comp (g := algebraMap P P') hf
  have h₂ : RingHom.ker (algebraMap P' S) ^ 2 = ⊥ := by
    rw [RingHom.algebraMap_toAlgebra]; rw [AlgHom.ker_kerSquareLift]; rw [Ideal.cotangentIdeal_square]
  let e₁ : (RingHom.ker (algebraMap P S)).Cotangent ≃ₗ[P] (RingHom.ker (algebraMap P' S)) :=
    (Ideal.cotangentEquivIdeal _).trans ((LinearEquiv.ofEq _ _
      (IsScalarTower.toAlgHom R P S).ker_kerSquareLift.symm).restrictScalars P)
  let e₂ : S otimes[P'] Ω[P'⁄R] ≃ₗ[P] S otimes[P] Ω[P⁄R] :=
    (tensorKaehlerQuotKerSqEquiv R P S).restrictScalars P
  have H : kerCotangentToTensor R P S =
      e₂.toLinearMap ∘ₗ (kerToTensor R P' S).restrictScalars P ∘ₗ e₁.toLinearMap := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
    exact (tensorKaehlerQuotKerSqEquiv_tmul_D 1 x.1).symm
  refine Equiv.trans ?_ (retractionKerToTensorEquivSection (R := R) h₂ h₁)
  refine ⟨fun ⟨l, hl⟩ => ⟨⟨e₁.toLinearMap ∘ₗ l ∘ₗ e₂.toLinearMap, ?_⟩, ?_⟩,
    fun ⟨l, hl⟩ => ⟨e₁.symm.toLinearMap ∘ₗ l.restrictScalars P ∘ₗ e₂.symm.toLinearMap, ?_⟩, ?_, ?_⟩
  · rintro x y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [P', ← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]
    exact (e₁.toLinearMap ∘ₗ l ∘ₗ e₂.toLinearMap).map_smul x y
  · ext1 x
    rw [H] at hl
    obtain ⟨x, rfl⟩ := e₁.surjective x
    exact DFunLike.congr_arg e₁ (LinearMap.congr_fun hl x)
  · ext x
    rw [H]
    apply e₁.injective
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars,
      Function.comp_apply, LinearEquiv.symm_apply_apply, LinearMap.id_coe, id_eq,
      LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun hl (e₁ x)
  · intro f
    ext x
    simp only [AlgebraTensorModule.curry_apply, Derivation.coe_comp, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Derivation.coeFn_coe, Function.comp_apply, curry_apply,
      LinearEquiv.coe_coe, LinearMap.coe_mk, AddHom.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  · intro f
    ext x
    simp only [AlgebraTensorModule.curry_apply, Derivation.coe_comp, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Derivation.coeFn_coe, Function.comp_apply, curry_apply,
      LinearMap.coe_mk, AddHom.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

namespace Algebra.Extension

set_option backward.defeqAttrib.useBackward true in
/--
lemma `CotangentSpace.map_toInfinitesimal_bijective` / 引理 `CotangentSpace.map_toInfinitesimal_bijective`

English:
lemma CotangentSpace.map_toInfinitesimal_bijective
  given: (P : Extension.{u} R S)
  proof: by
  suffices CotangentSpace.map P.toInfinitesimal =
      (tensorKaehlerQuotKerSqEquiv _ _ _).symm.toLinearMap by
    rw [this]; exact (tensorKaehlerQuotKerSqEquiv _ _ _).symm.bijective
  let : Algebra P.Ring P.infinitesimal.Ring := inferInstanceAs (Algebra P.Ring (P.Ring ⧸ _))
  have : IsScalarTow

中文:
引理 CotangentSpace.map_toInfinitesimal_bijective
  条件: (P : 扩张.{u} R S)
  证明: by
  suffices CotangentSpace.map P.toInfinitesimal =
      (tensorKaehlerQuotKerSqEquiv _ _ _).symm.toLinearMap by
    rw [this]; exact (tensorKaehlerQuotKerSqEquiv _ _ _).symm.bijective
  let : Algebra P.Ring P.infinitesimal.Ring := inferInstanceAs (Algebra P.Ring (P.Ring ⧸ _))
  have : IsScalarTow

Depends on / 依赖: Algebra, CotangentSpace, CotangentSpace.map, Hom.toAlgHom_apply, IsScalarTower, LinearMap, LinearMap.restrictScalars_injective, P.Ring, P.infinitesimal.Ring, P.toInfinitesimal, RingHom, RingHom.id_apply, algebraMap_self, bijective, id_apply, infinitesimal, map_tmul, of_algebraMap_eq, restrictScalars_injective, symm.bijective
-/
lemma CotangentSpace.map_toInfinitesimal_bijective (P : Extension.{u} R S) :
    Function.Bijective (CotangentSpace.map P.toInfinitesimal) := by
  suffices CotangentSpace.map P.toInfinitesimal =
      (tensorKaehlerQuotKerSqEquiv _ _ _).symm.toLinearMap by
    rw [this]; exact (tensorKaehlerQuotKerSqEquiv _ _ _).symm.bijective
  let : Algebra P.Ring P.infinitesimal.Ring := inferInstanceAs (Algebra P.Ring (P.Ring ⧸ _))
  have : IsScalarTower P.Ring P.infinitesimal.Ring S := .of_algebraMap_eq' rfl
  apply LinearMap.restrictScalars_injective P.Ring
  ext x a
  dsimp
  simp only [map_tmul, algebraMap_self, RingHom.id_apply, Hom.toAlgHom_apply]
  exact (tensorKaehlerQuotKerSqEquiv_symm_tmul_D _ _).symm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Cotangent.map_toInfinitesimal_bijective` / 引理 `Cotangent.map_toInfinitesimal_bijective`

English:
lemma Cotangent.map_toInfinitesimal_bijective
  given: (P : Extension.{u} R S)
  proof: by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    have hx : x.1 in P.ker ^ 2 := by
      apply_fun Cotangent.val at hx
      simp only [map_mk, Hom.toAlgHom_apply, val_mk, val_zero, Ideal.toCotangent_eq_zero,
        Extension.ker

中文:
引理 余切.map_toInfinitesimal_bijective
  条件: (P : 扩张.{u} R S)
  证明: by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    have hx : x.1 in P.ker ^ 2 := by
      apply_fun Cotangent.val at hx
      simp only [map_mk, Hom.toAlgHom_apply, val_mk, val_zero, Ideal.toCotangent_eq_zero,
        Extension.ker

Depends on / 依赖: Cotangent, Cotangent.mk_surjective, Cotangent.val, Extension, Extension.ker_infinitesimal, Hom.toAlgHom_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.cotangentIdeal_square, Ideal.mem_bot, Ideal.toCotangent_eq_zero, P.ker, Quotient, apply_fun, cotangentIdeal_square, eq_zero_iff_mem, infinitesimal, injective_iff_map_eq_zero, ker_infinitesimal, map_mk, mem_bot
-/
lemma Cotangent.map_toInfinitesimal_bijective (P : Extension.{u} R S) :
    Function.Bijective (Cotangent.map P.toInfinitesimal) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    have hx : x.1 in P.ker ^ 2 := by
      apply_fun Cotangent.val at hx
      simp only [map_mk, Hom.toAlgHom_apply, val_mk, val_zero, Ideal.toCotangent_eq_zero,
        Extension.ker_infinitesimal] at hx
      rw [Ideal.cotangentIdeal_square] at hx
      simpa only [toInfinitesimal, Ideal.mem_bot, infinitesimal,
        Ideal.Quotient.eq_zero_iff_mem] using hx
    ext
    simpa [Ideal.toCotangent_eq_zero]
  · intro x
    obtain ⟨⟨x, hx⟩, rfl⟩ := Cotangent.mk_surjective x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [ker_infinitesimal]; rw [Ideal.mk_mem_cotangentIdeal] at hx
    exact ⟨.mk ⟨x, hx⟩, rfl⟩

/--
lemma `H1Cotangent.map_toInfinitesimal_bijective` / 引理 `H1Cotangent.map_toInfinitesimal_bijective`

English:
lemma H1Cotangent.map_toInfinitesimal_bijective
  given: (P : Extension.{u} R S)
  proof: by
  constructor
  · intro x y e
    ext1
    exact (Cotangent.map_toInfinitesimal_bijective P).1 (congr_arg Subtype.val e)
  · intro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := (Cotangent.map_toInfinitesimal_bijective P).2 x
    refine ⟨⟨x, ?_⟩, rfl⟩
    simpa [← CotangentSpace.map_cotangentComplex,
      map_e

中文:
引理 H1Cotangent.map_toInfinitesimal_bijective
  条件: (P : 扩张.{u} R S)
  证明: by
  constructor
  · intro x y e
    ext1
    exact (Cotangent.map_toInfinitesimal_bijective P).1 (congr_arg Subtype.val e)
  · intro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := (Cotangent.map_toInfinitesimal_bijective P).2 x
    refine ⟨⟨x, ?_⟩, rfl⟩
    simpa [← CotangentSpace.map_cotangentComplex,
      map_e

Depends on / 依赖: Cotangent, Cotangent.map_toInfinitesimal_bijective, CotangentSpace, CotangentSpace.map_cotangentComplex, CotangentSpace.map_toInfinitesimal_bijective, Subtype, Subtype.val, congr_arg, injective, map_cotangentComplex, map_eq_zero_iff, map_toInfinitesimal_bijective
-/
lemma H1Cotangent.map_toInfinitesimal_bijective (P : Extension.{u} R S) :
    Function.Bijective (H1Cotangent.map P.toInfinitesimal) := by
  constructor
  · intro x y e
    ext1
    exact (Cotangent.map_toInfinitesimal_bijective P).1 (congr_arg Subtype.val e)
  · intro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := (Cotangent.map_toInfinitesimal_bijective P).2 x
    refine ⟨⟨x, ?_⟩, rfl⟩
    simpa [← CotangentSpace.map_cotangentComplex,
      map_eq_zero_iff _ (CotangentSpace.map_toInfinitesimal_bijective P).injective] using hx

end Algebra.Extension
