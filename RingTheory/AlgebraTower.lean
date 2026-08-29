/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Towers of algebras

We set up the basic theory of algebra towers.
An algebra tower A/S/R is expressed by having instances of `Algebra A S`,
`Algebra R S`, `Algebra R A` and `IsScalarTower R S A`, the later asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

In `Mathlib/FieldTheory/Tower.lean` we use this to prove the tower law for finite extensions,
that if `R` and `S` are both fields, then `[A:R] = [A:S] [S:A]`.

In this file we prepare the main lemma:
if `{bi | i ∈ I}` is an `R`-basis of `S` and `{cj | j ∈ J}` is an `S`-basis
of `A`, then `{bi cj | i ∈ I, j ∈ J}` is an `R`-basis of `A`. This statement does not require the
base rings to be a field, so we also generalize the lemma to rings in this file.
-/

@[expose] public section

open Module
open scoped Pointwise

variable (R S A B : Type*)

namespace IsScalarTower

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra S A] [Algebra S B] [Algebra R A] [Algebra R B]
variable [IsScalarTower R S A] [IsScalarTower R S B]

/-- Suppose that `R → S → A` is a tower of algebras.
If an element `r : R` is invertible in `S`, then it is invertible in `A`. -/
@[instance_reducible]
/--
Definition of `Invertible.algebraTower` / `Invertible.algebraTower` 的定义

English:
definition Invertible.algebraTower
  signature: (r : R) [Invertible (algebraMap R S r)]
  body: Invertible.copy (Invertible.map (algebraMap S A) (algebraMap R S r)) (algebraMap R A r)
    (IsScalarTower.algebraMap_apply R S A r)

中文:
定义 可逆.algebraTower
  签名: (r : R) [可逆 (algebraMap R S r)]
  定义体: Invertible.copy (Invertible.map (algebraMap S A) (algebraMap R S r)) (algebraMap R A r)
    (IsScalarTower.algebraMap_apply R S A r)

Depends on / 依赖: Invertible, Invertible.copy, Invertible.map, IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap, algebraMap_apply
-/
def Invertible.algebraTower (r : R) [Invertible (algebraMap R S r)] :
    Invertible (algebraMap R A r) :=
  Invertible.copy (Invertible.map (algebraMap S A) (algebraMap R S r)) (algebraMap R A r)
    (IsScalarTower.algebraMap_apply R S A r)

/-- A natural number that is invertible when coerced to `R` is also invertible
when coerced to any `R`-algebra. -/
@[instance_reducible]
/--
Definition of `invertibleAlgebraCoeNat` / `invertibleAlgebraCoeNat` 的定义

English:
definition invertibleAlgebraCoeNat
  signature: (n : Nat) [inv : Invertible (n : R)]
  body: haveI : Invertible (algebraMap Nat R n) := inv
  fast_instance% Invertible.algebraTower Nat R A n

中文:
定义 invertibleAlgebraCoe自然数
  签名: (n : 自然数) [inv : 可逆 (n : R)]
  定义体: haveI : Invertible (algebraMap Nat R n) := inv
  fast_instance% Invertible.algebraTower Nat R A n

Depends on / 依赖: Invertible, Invertible.algebraTower, algebraMap, algebraTower, fast_instance
-/
def invertibleAlgebraCoeNat (n : Nat) [inv : Invertible (n : R)] : Invertible (n : A) :=
  haveI : Invertible (algebraMap Nat R n) := inv
  fast_instance% Invertible.algebraTower Nat R A n

end Semiring
end IsScalarTower

section AlgebraMapCoeffs
namespace Module.Basis
variable {R} {ι M : Type*} [CommSemiring R] [Semiring A] [AddCommMonoid M]
variable [Algebra R A] [Module A M] [Module R M] [IsScalarTower R A M]
variable (b : Basis ι R M) (h : Function.Bijective (algebraMap R A))


/-- If `R` and `A` have a bijective `algebraMap R A` and act identically on `M`,
then a basis for `M` as `R`-module is also a basis for `M` as `R'`-module. -/
@[simps! -isSimp repr_apply_apply]
/--
Definition of `algebraMapCoeffs` / `algebraMapCoeffs` 的定义

English:
definition algebraMapCoeffs
  signature: : Basis ι A M
  body: b.mapCoeffs (RingEquiv.ofBijective _ h) fun c x => by simp

@[simp]

中文:
定义 algebraMapCoeffs
  签名: : 基 ι A M
  定义体: b.mapCoeffs (RingEquiv.ofBijective _ h) fun c x => by simp

@[simp]

Depends on / 依赖: RingEquiv, RingEquiv.ofBijective, b.mapCoeffs, mapCoeffs, ofBijective
-/
noncomputable def algebraMapCoeffs : Basis ι A M :=
  b.mapCoeffs (RingEquiv.ofBijective _ h) fun c x => by simp

@[simp]
/--
theorem `algebraMapCoeffs_repr` / 定理 `algebraMapCoeffs_repr`

English:
theorem algebraMapCoeffs_repr
  given: (m : M)
  proof: by
  rfl

中文:
定理 algebraMapCoeffs_repr
  条件: (m : M)
  证明: by
  rfl
-/
theorem algebraMapCoeffs_repr (m : M) :
    (b.algebraMapCoeffs A h).repr m = (b.repr m).mapRange (algebraMap R A) (map_zero _) := by
  rfl

/--
theorem `algebraMapCoeffs_apply` / 定理 `algebraMapCoeffs_apply`

English:
theorem algebraMapCoeffs_apply
  given: (i : ι)
  statement: b.algebraMapCoeffs A h i = b i
  proof: b.mapCoeffs_apply _ _ _

@[simp]

中文:
定理 algebraMapCoeffs_apply
  条件: (i : ι)
  结论: b.algebraMapCoeffs A h i = b i
  证明: b.mapCoeffs_apply _ _ _

@[simp]

Depends on / 依赖: b.mapCoeffs_apply, mapCoeffs_apply
-/
theorem algebraMapCoeffs_apply (i : ι) : b.algebraMapCoeffs A h i = b i :=
  b.mapCoeffs_apply _ _ _

@[simp]
/--
theorem `coe_algebraMapCoeffs` / 定理 `coe_algebraMapCoeffs`

English:
theorem coe_algebraMapCoeffs
  statement: (b.algebraMapCoeffs A h : ι -> M) = b
  proof: b.coe_mapCoeffs _ _

中文:
定理 coe_algebraMapCoeffs
  结论: (b.algebraMapCoeffs A h : ι -> M) = b
  证明: b.coe_mapCoeffs _ _

Depends on / 依赖: b.coe_mapCoeffs, coe_mapCoeffs
-/
theorem coe_algebraMapCoeffs : (b.algebraMapCoeffs A h : ι -> M) = b :=
  b.coe_mapCoeffs _ _

end Module.Basis
end AlgebraMapCoeffs

section Semiring

open Finsupp

variable {R S A}
variable [Semiring R] [Semiring S] [AddCommMonoid A]
variable [Module R S] [Module S A] [Module R A] [IsScalarTower R S A]

/--
theorem `linearIndependent_smul` / 定理 `linearIndependent_smul`

English:
theorem linearIndependent_smul
  statement: {ι : Type*} {b : ι -> S} {ι' : Type*} {c : ι' -> A}
  proof: by
  rw [← linearIndependent_equiv' (.prodComm ..) (g := fun p : ι' × ι => b p.2 • c p.1) rfl]; rw [LinearIndependent]; rw [linearCombination_smul]
  simpa using! Function.Injective.comp hc
    ((mapRange_injective _ (map_zero _) hb).comp <| Equiv.injective _)

中文:
定理 linearIndependent_smul
  结论: {ι : 类型} {b : ι -> S} {ι' : 类型} {c : ι' -> A}
  证明: by
  rw [← linearIndependent_equiv' (.prodComm ..) (g := fun p : ι' × ι => b p.2 • c p.1) rfl]; rw [LinearIndependent]; rw [linearCombination_smul]
  simpa using! Function.Injective.comp hc
    ((mapRange_injective _ (map_zero _) hb).comp <| Equiv.injective _)

Depends on / 依赖: Equiv.injective, Function, Function.Injective.comp, Injective, LinearIndependent, injective, linearCombination_smul, linearIndependent_equiv, mapRange_injective, map_zero, prodComm
-/
theorem linearIndependent_smul {ι : Type*} {b : ι -> S} {ι' : Type*} {c : ι' -> A}
    (hb : LinearIndependent R b) (hc : LinearIndependent S c) :
    LinearIndependent R fun p : ι × ι' => b p.1 • c p.2 := by
  rw [← linearIndependent_equiv' (.prodComm ..) (g := fun p : ι' × ι => b p.2 • c p.1) rfl]; rw [LinearIndependent]; rw [linearCombination_smul]
  simpa using! Function.Injective.comp hc
    ((mapRange_injective _ (map_zero _) hb).comp <| Equiv.injective _)

variable (R)

namespace Module.Basis

-- LinearIndependent is enough if S is a ring rather than semiring.
/--
theorem `isScalarTower_of_nonempty` / 定理 `isScalarTower_of_nonempty`

English:
theorem isScalarTower_of_nonempty
  given: {ι} [Nonempty ι] (b : Basis ι S A)
  statement: IsScalarTower R S S
  proof: (b.repr.symm.comp <| lsingle <| Classical.arbitrary ι).isScalarTower_of_injective R
    (b.repr.symm.injective.comp <| single_injective _)

中文:
定理 isScalarTower_of_nonempty
  条件: {ι} [非空 ι] (b : 基 ι S A)
  结论: 标量塔 R S S
  证明: (b.repr.symm.comp <| lsingle <| Classical.arbitrary ι).isScalarTower_of_injective R
    (b.repr.symm.injective.comp <| single_injective _)

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, b.repr.symm.comp, b.repr.symm.injective.comp, injective, isScalarTower_of_injective, lsingle, single_injective
-/
theorem isScalarTower_of_nonempty {ι} [Nonempty ι] (b : Basis ι S A) : IsScalarTower R S S :=
  (b.repr.symm.comp <| lsingle <| Classical.arbitrary ι).isScalarTower_of_injective R
    (b.repr.symm.injective.comp <| single_injective _)

/--
theorem `isScalarTower_finsupp` / 定理 `isScalarTower_finsupp`

English:
theorem isScalarTower_finsupp
  given: {ι} (b : Basis ι S A)
  statement: IsScalarTower R S (ι ->₀ S)
  proof: b.repr.symm.isScalarTower_of_injective R b.repr.symm.injective

中文:
定理 isScalarTower_finsupp
  条件: {ι} (b : 基 ι S A)
  结论: 标量塔 R S (ι ->₀ S)
  证明: b.repr.symm.isScalarTower_of_injective R b.repr.symm.injective

Depends on / 依赖: b.repr.symm.injective, b.repr.symm.isScalarTower_of_injective, injective, isScalarTower_of_injective
-/
theorem isScalarTower_finsupp {ι} (b : Basis ι S A) : IsScalarTower R S (ι ->₀ S) :=
  b.repr.symm.isScalarTower_of_injective R b.repr.symm.injective

variable {R} {ι ι' : Type*} (b : Basis ι R S) (c : Basis ι' S A)

/-- `Basis.smulTower (b : Basis ι R S) (c : Basis ι S A)` is the `R`-basis on `A`
where the `(i, j)`th basis vector is `b i • c j`. -/
noncomputable
/--
Definition of `smulTower` / `smulTower` 的定义

English:
definition smulTower
  signature: : Basis (ι × ι') R A
  body: haveI := c.isScalarTower_finsupp R
  .ofRepr
    (c.repr.restrictScalars R ≪≫ₗ
      (Finsupp.lcongr (Equiv.refl _) b.repr ≪≫ₗ
        ((curryLinearEquiv R).symm ≪≫ₗ
          Finsupp.lcongr (Equiv.prodComm ι' ι) (LinearEquiv.refl _ _))))

@[simp]

中文:
定义 smulTower
  签名: : 基 (ι × ι') R A
  定义体: haveI := c.isScalarTower_finsupp R
  .ofRepr
    (c.repr.restrictScalars R ≪≫ₗ
      (Finsupp.lcongr (Equiv.refl _) b.repr ≪≫ₗ
        ((curryLinearEquiv R).symm ≪≫ₗ
          Finsupp.lcongr (Equiv.prodComm ι' ι) (LinearEquiv.refl _ _))))

@[simp]

Depends on / 依赖: Equiv.prodComm, Equiv.refl, Finsupp, Finsupp.lcongr, LinearEquiv, LinearEquiv.refl, b.repr, c.isScalarTower_finsupp, c.repr.restrictScalars, curryLinearEquiv, isScalarTower_finsupp, lcongr, ofRepr, prodComm, restrictScalars
-/
def smulTower : Basis (ι × ι') R A :=
  haveI := c.isScalarTower_finsupp R
  .ofRepr
    (c.repr.restrictScalars R ≪≫ₗ
      (Finsupp.lcongr (Equiv.refl _) b.repr ≪≫ₗ
        ((curryLinearEquiv R).symm ≪≫ₗ
          Finsupp.lcongr (Equiv.prodComm ι' ι) (LinearEquiv.refl _ _))))

@[simp]
/--
theorem `smulTower_repr` / 定理 `smulTower_repr`

English:
theorem smulTower_repr
  given: (x ij)
  proof: by
  simp [smulTower, Finsupp.uncurry_apply]

中文:
定理 smulTower_repr
  条件: (x ij)
  证明: by
  simp [smulTower, Finsupp.uncurry_apply]

Depends on / 依赖: Finsupp, Finsupp.uncurry_apply, smulTower, uncurry_apply
-/
theorem smulTower_repr (x ij) :
    (b.smulTower c).repr x ij = b.repr (c.repr x ij.2) ij.1 := by
  simp [smulTower, Finsupp.uncurry_apply]

/--
theorem `smulTower_repr_mk` / 定理 `smulTower_repr_mk`

English:
theorem smulTower_repr_mk
  given: (x i j)
  statement: (b.smulTower c).repr x (i, j) = b.repr (c.repr x j) i
  proof: b.smulTower_repr c x (i, j)

@[simp]

中文:
定理 smulTower_repr_mk
  条件: (x i j)
  结论: (b.smulTower c).repr x (i, j) = b.repr (c.repr x j) i
  证明: b.smulTower_repr c x (i, j)

@[simp]

Depends on / 依赖: b.smulTower_repr, smulTower_repr
-/
theorem smulTower_repr_mk (x i j) : (b.smulTower c).repr x (i, j) = b.repr (c.repr x j) i :=
  b.smulTower_repr c x (i, j)

@[simp]
/--
theorem `smulTower_apply` / 定理 `smulTower_apply`

English:
theorem smulTower_apply
  given: (ij)
  statement: (b.smulTower c) ij = b ij.1 • c ij.2
  proof: by
  classical
  obtain ⟨i, j⟩ := ij
  rw [Basis.apply_eq_iff]
  ext ⟨i', j'⟩
  rw [Basis.smulTower_repr]; rw [map_smul]; rw [Basis.repr_self]; rw [Finsupp.smul_apply]; rw [Finsupp.single_apply]
  dsimp only
  split_ifs with hi
  · simp [hi, Finsupp.single_apply]
  · simp [hi]

中文:
定理 smulTower_apply
  条件: (ij)
  结论: (b.smulTower c) ij = b ij.1 • c ij.2
  证明: by
  classical
  obtain ⟨i, j⟩ := ij
  rw [Basis.apply_eq_iff]
  ext ⟨i', j'⟩
  rw [Basis.smulTower_repr]; rw [map_smul]; rw [Basis.repr_self]; rw [Finsupp.smul_apply]; rw [Finsupp.single_apply]
  dsimp only
  split_ifs with hi
  · simp [hi, Finsupp.single_apply]
  · simp [hi]

Depends on / 依赖: Basis.apply_eq_iff, Basis.repr_self, Basis.smulTower_repr, Finsupp, Finsupp.single_apply, Finsupp.smul_apply, apply_eq_iff, classical, map_smul, repr_self, single_apply, smulTower_repr, smul_apply, split_ifs
-/
theorem smulTower_apply (ij) : (b.smulTower c) ij = b ij.1 • c ij.2 := by
  classical
  obtain ⟨i, j⟩ := ij
  rw [Basis.apply_eq_iff]
  ext ⟨i', j'⟩
  rw [Basis.smulTower_repr]; rw [map_smul]; rw [Basis.repr_self]; rw [Finsupp.smul_apply]; rw [Finsupp.single_apply]
  dsimp only
  split_ifs with hi
  · simp [hi, Finsupp.single_apply]
  · simp [hi]

/--
Definition of `smulTower'` / `smulTower'` 的定义

English:
definition smulTower'
  signature: : Basis (ι' × ι) R A
  body: (b.smulTower c).reindex (.prodComm ..)

中文:
定义 smulTower'
  签名: : 基 (ι' × ι) R A
  定义体: (b.smulTower c).reindex (.prodComm ..)

Depends on / 依赖: b.smulTower, prodComm, reindex, smulTower
-/
noncomputable def smulTower' : Basis (ι' × ι) R A :=
  (b.smulTower c).reindex (.prodComm ..)

/--
theorem `smulTower'_repr` / 定理 `smulTower'_repr`

English:
theorem smulTower'_repr
  given: (x ij)
  proof: by
  rw [smulTower']; rw [repr_reindex_apply]; rw [smulTower_repr]; rfl

中文:
定理 smulTower'_repr
  条件: (x ij)
  证明: by
  rw [smulTower']; rw [repr_reindex_apply]; rw [smulTower_repr]; rfl
-/
theorem smulTower'_repr (x ij) :
    (b.smulTower' c).repr x ij = b.repr (c.repr x ij.1) ij.2 := by
  rw [smulTower']; rw [repr_reindex_apply]; rw [smulTower_repr]; rfl

/--
theorem `smulTower'_repr_mk` / 定理 `smulTower'_repr_mk`

English:
theorem smulTower'_repr_mk
  given: (x i j)
  statement: (b.smulTower' c).repr x (i, j) = b.repr (c.repr x i) j
  proof: b.smulTower'_repr c x (i, j)

中文:
定理 smulTower'_repr_mk
  条件: (x i j)
  结论: (b.smulTower' c).repr x (i, j) = b.repr (c.repr x i) j
  证明: b.smulTower'_repr c x (i, j)
-/
theorem smulTower'_repr_mk (x i j) : (b.smulTower' c).repr x (i, j) = b.repr (c.repr x i) j :=
  b.smulTower'_repr c x (i, j)

/--
theorem `smulTower'_apply` / 定理 `smulTower'_apply`

English:
theorem smulTower'_apply
  given: (ij)
  statement: b.smulTower' c ij = b ij.2 • c ij.1
  proof: by
  rw [smulTower']; rw [reindex_apply]; rw [smulTower_apply]; rfl

中文:
定理 smulTower'_apply
  条件: (ij)
  结论: b.smulTower' c ij = b ij.2 • c ij.1
  证明: by
  rw [smulTower']; rw [reindex_apply]; rw [smulTower_apply]; rfl
-/
theorem smulTower'_apply (ij) : b.smulTower' c ij = b ij.2 • c ij.1 := by
  rw [smulTower']; rw [reindex_apply]; rw [smulTower_apply]; rfl

end Module.Basis
end Semiring

section Ring

variable {R S}
variable [CommRing R] [IsDomain R] [Ring S] [Nontrivial S] [Algebra R S]

/--
theorem `Module.Basis.algebraMap_injective` / 定理 `Module.Basis.algebraMap_injective`

English:
theorem Module.Basis.algebraMap_injective
  given: {ι : Type*} (b : Basis ι R S)
  proof: have : IsTorsionFree R S := b.isTorsionFree
  FaithfulSMul.algebraMap_injective R S

中文:
定理 模.基.algebraMap_injective
  条件: {ι : 类型} (b : 基 ι R S)
  证明: have : IsTorsionFree R S := b.isTorsionFree
  FaithfulSMul.algebraMap_injective R S

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsTorsionFree, algebraMap_injective, b.isTorsionFree, isTorsionFree
-/
theorem Module.Basis.algebraMap_injective {ι : Type*} (b : Basis ι R S) :
    Function.Injective (algebraMap R S) :=
  have : IsTorsionFree R S := b.isTorsionFree
  FaithfulSMul.algebraMap_injective R S

end Ring

section AlgHomTower

variable {A} {C D : Type*} [CommSemiring A] [CommSemiring C] [CommSemiring D] [Algebra A C]
  [Algebra A D]

variable [CommSemiring B] [Algebra A B] [Algebra B C] [IsScalarTower A B C] (f : C ->ₐ[A] D)

/--
Definition of `AlgHom.domRestrict` / `AlgHom.domRestrict` 的定义

English:
definition AlgHom.domRestrict
  signature: : B ->ₐ[A] D
  body: f.comp (IsScalarTower.toAlgHom A B C)

@[deprecated (since := "2026-07-19")] alias AlgHom.restrictDomain := AlgHom.domRestrict

中文:
定义 代数态射.domRestrict
  签名: : B ->ₐ[A] D
  定义体: f.comp (IsScalarTower.toAlgHom A B C)

@[deprecated (since := "2026-07-19")] alias AlgHom.restrictDomain := AlgHom.domRestrict

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, f.comp, toAlgHom
-/
def AlgHom.domRestrict : B ->ₐ[A] D :=
  f.comp (IsScalarTower.toAlgHom A B C)

@[deprecated (since := "2026-07-19")] alias AlgHom.restrictDomain := AlgHom.domRestrict

/--
Definition of `AlgHom.extendScalars` / `AlgHom.extendScalars` 的定义

English:
definition AlgHom.extendScalars
  signature: : @AlgHom B C D _ _ _ _ (f.domRestrict B).toRingHom.toAlgebra where
  body: f
  commutes' := fun _ => rfl
  __ := (f.domRestrict B).toRingHom.toAlgebra

中文:
定义 代数态射.extendScalars
  签名: : @代数态射 B C D _ _ _ _ (f.domRestrict B).toRingHom.toAlgebra where
  定义体: f
  commutes' := fun _ => rfl
  __ := (f.domRestrict B).toRingHom.toAlgebra
-/
def AlgHom.extendScalars : @AlgHom B C D _ _ _ _ (f.domRestrict B).toRingHom.toAlgebra where
  __ := f
  commutes' := fun _ => rfl
  __ := (f.domRestrict B).toRingHom.toAlgebra

variable {B}

/--
Definition of `algHomEquivSigma` / `algHomEquivSigma` 的定义

English:
definition algHomEquivSigma
  signature: :
  body: ⟨f.domRestrict B, f.extendScalars B⟩
  invFun fg :=
    let _ := fg.1.toRingHom.toAlgebra
    fg.2.restrictScalars A
  left_inv f := by
    dsimp only
    ext
    rfl
  right_inv := by
    rintro ⟨⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩, ⟨⟨⟨⟨g, _⟩, _⟩, _⟩, hg⟩⟩
    obtain rfl : f = fun x => g (algebraMap B C x) := by

中文:
定义 algHomEquivSigma
  签名: :
  定义体: ⟨f.domRestrict B, f.extendScalars B⟩
  invFun fg :=
    let _ := fg.1.toRingHom.toAlgebra
    fg.2.restrictScalars A
  left_inv f := by
    dsimp only
    ext
    rfl
  right_inv := by
    rintro ⟨⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩, ⟨⟨⟨⟨g, _⟩, _⟩, _⟩, hg⟩⟩
    obtain rfl : f = fun x => g (algebraMap B C x) := by

Depends on / 依赖: domRestrict, extendScalars, f.domRestrict, f.extendScalars
-/
def algHomEquivSigma :
    (C ->ₐ[A] D) ≃ Σ f : B ->ₐ[A] D, @AlgHom B C D _ _ _ _ f.toRingHom.toAlgebra where
  toFun f := ⟨f.domRestrict B, f.extendScalars B⟩
  invFun fg :=
    let _ := fg.1.toRingHom.toAlgebra
    fg.2.restrictScalars A
  left_inv f := by
    dsimp only
    ext
    rfl
  right_inv := by
    rintro ⟨⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩, ⟨⟨⟨⟨g, _⟩, _⟩, _⟩, hg⟩⟩
    obtain rfl : f = fun x => g (algebraMap B C x) := by
      ext x
      exact (hg x).symm
    rfl

end AlgHomTower
