/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Finsupp.Span
public import Mathlib.LinearAlgebra.Projection

/-!
# Linear structures on function with finite support `ι →₀ M`

This file contains results on the `R`-module structure on functions of finite support from a type
`ι` to an `R`-module `M`, in particular in the case that `R` is a field.

-/

@[expose] public section


noncomputable section

open Set LinearMap Module Submodule

universe u v w

namespace DFinsupp

variable {ι : Type*} {R : Type*} {M : ι -> Type*}
variable [Semiring R] [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)]

/--
Definition of `basis` / `basis` 的定义

English:
definition basis
  signature: {η : ι -> Type*} (b : forall i, Basis (η i) R (M i))
  body: .ofRepr
    ((mapRange.linearEquiv fun i => (b i).repr).trans (sigmaFinsuppLequivDFinsupp R).symm)

中文:
定义 basis
  签名: {η : ι -> 类型} (b : 对任意 i, 基 (η i) R (M i))
  定义体: .ofRepr
    ((mapRange.linearEquiv fun i => (b i).repr).trans (sigmaFinsuppLequivDFinsupp R).symm)

Depends on / 依赖: linearEquiv, mapRange, mapRange.linearEquiv, ofRepr, sigmaFinsuppLequivDFinsupp
-/
noncomputable def basis {η : ι -> Type*} (b : forall i, Basis (η i) R (M i)) :
    Basis (Σ i, η i) R (Π₀ i, M i) :=
  .ofRepr
    ((mapRange.linearEquiv fun i => (b i).repr).trans (sigmaFinsuppLequivDFinsupp R).symm)

variable (R M) in
/--
Instance `_root_.Module.Free.dfinsupp` / 实例 `_root_.Module.Free.dfinsupp`

English:
instance _root_.Module.Free.dfinsupp
  signature: [forall i : ι, Module.Free R (M i)]
  body: .of_basis DFinsupp.basis fun i => Module.Free.chooseBasis R (M i)

中文:
实例 _root_.模.自由.dfinsupp
  签名: [对任意 i : ι, 模.自由 R (M i)]
  定义体: .of_basis DFinsupp.basis fun i => Module.Free.chooseBasis R (M i)

Depends on / 依赖: DFinsupp, DFinsupp.basis, Module, Module.Free.chooseBasis, chooseBasis, of_basis
-/
instance _root_.Module.Free.dfinsupp [forall i : ι, Module.Free R (M i)] : Module.Free R (Π₀ i, M i) :=
.of_basis DFinsupp.basis fun i => Module.Free.chooseBasis R (M i)

variable [DecidableEq ι] {φ : ι -> Type*} (f : forall i, φ i -> M i)

open Finsupp (linearCombination)

/--
theorem `linearIndependent_single` / 定理 `linearIndependent_single`

English:
theorem linearIndependent_single
  given: (hf : forall i, LinearIndependent R (f i))
  proof: by
  have : linearCombination R (fun ix : Σ i, φ i => single ix.1 (f ix.1 ix.2)) =
    DFinsupp.mapRange.linearMap (fun i => linearCombination R (f i)) ∘ₗ
    (sigmaFinsuppLequivDFinsupp R).toLinearMap := by ext; simp
  rw [LinearIndependent]; rw [this]
  exact ((DFinsupp.mapRange_injective _ fun _ => map_zero _).mpr hf).comp (Equiv.injective _)

中文:
定理 linearIndependent_single
  条件: (hf : 对任意 i, LinearIndependent R (f i))
  证明: by
  have : linearCombination R (fun ix : Σ i, φ i => single ix.1 (f ix.1 ix.2)) =
    DFinsupp.mapRange.linearMap (fun i => linearCombination R (f i)) ∘ₗ
    (sigmaFinsuppLequivDFinsupp R).toLinearMap := by ext; simp
  rw [LinearIndependent]; rw [this]
  exact ((DFinsupp.mapRange_injective _ fun _ => map_zero _).mpr hf).comp (Equiv.injective _)

Depends on / 依赖: DFinsupp, DFinsupp.mapRange.linearMap, DFinsupp.mapRange_injective, Equiv.injective, LinearIndependent, injective, linearCombination, linearMap, mapRange, mapRange_injective, map_zero, sigmaFinsuppLequivDFinsupp, single, toLinearMap
-/
theorem linearIndependent_single (hf : forall i, LinearIndependent R (f i)) :
    LinearIndependent R fun ix : Σ i, φ i => single ix.1 (f ix.1 ix.2) := by
  have : linearCombination R (fun ix : Σ i, φ i => single ix.1 (f ix.1 ix.2)) =
    DFinsupp.mapRange.linearMap (fun i => linearCombination R (f i)) ∘ₗ
    (sigmaFinsuppLequivDFinsupp R).toLinearMap := by ext; simp
  rw [LinearIndependent]; rw [this]
  exact ((DFinsupp.mapRange_injective _ fun _ => map_zero _).mpr hf).comp (Equiv.injective _)

/--
lemma `linearIndependent_single_iff` / 引理 `linearIndependent_single_iff`

English:
lemma linearIndependent_single_iff
  proof: ⟨fun h i => (h.comp _ sigma_mk_injective).of_comp (lsingle i), linearIndependent_single _⟩

中文:
引理 linearIndependent_single_iff
  证明: ⟨fun h i => (h.comp _ sigma_mk_injective).of_comp (lsingle i), linearIndependent_single _⟩

Depends on / 依赖: h.comp, linearIndependent_single, lsingle, of_comp, sigma_mk_injective
-/
lemma linearIndependent_single_iff :
    LinearIndependent R (fun ix : Σ i, φ i => single ix.1 (f ix.1 ix.2)) ↔
      forall i, LinearIndependent R (f i) :=
  ⟨fun h i => (h.comp _ sigma_mk_injective).of_comp (lsingle i), linearIndependent_single _⟩

end DFinsupp

namespace Finsupp

section Semiring

variable {R : Type*} {M : Type*} {ι : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M]

/--
theorem `linearIndependent_single` / 定理 `linearIndependent_single`

English:
theorem linearIndependent_single
  statement: {φ : ι -> Type*} (f : forall i, φ i -> M)
  proof: by
  classical
  convert!
    (DFinsupp.linearIndependent_single _ hf).map_injOn _
      (finsuppLequivDFinsupp R).symm.injective.injOn
  simp

中文:
定理 linearIndependent_single
  结论: {φ : ι -> 类型} (f : 对任意 i, φ i -> M)
  证明: by
  classical
  convert!
    (DFinsupp.linearIndependent_single _ hf).map_injOn _
      (finsuppLequivDFinsupp R).symm.injective.injOn
  simp

Depends on / 依赖: DFinsupp, DFinsupp.linearIndependent_single, classical, convert, finsuppLequivDFinsupp, injective, linearIndependent_single, map_injOn, symm.injective.injOn
-/
theorem linearIndependent_single {φ : ι -> Type*} (f : forall i, φ i -> M)
    (hf : forall i, LinearIndependent R (f i)) :
    LinearIndependent R fun ix : Σ i, φ i => single ix.1 (f ix.1 ix.2) := by
  classical
  convert!
    (DFinsupp.linearIndependent_single _ hf).map_injOn _
      (finsuppLequivDFinsupp R).symm.injective.injOn
  simp

/--
lemma `linearIndependent_single_iff` / 引理 `linearIndependent_single_iff`

English:
lemma linearIndependent_single_iff
  given: {φ : ι -> Type*} {f : forall i, φ i -> M}
  proof: ⟨fun h i => (h.comp _ sigma_mk_injective).of_comp (lsingle i), linearIndependent_single _⟩

中文:
引理 linearIndependent_single_iff
  条件: {φ : ι -> 类型} {f : 对任意 i, φ i -> M}
  证明: ⟨fun h i => (h.comp _ sigma_mk_injective).of_comp (lsingle i), linearIndependent_single _⟩

Depends on / 依赖: h.comp, linearIndependent_single, lsingle, of_comp, sigma_mk_injective
-/
lemma linearIndependent_single_iff {φ : ι -> Type*} {f : forall i, φ i -> M} :
    LinearIndependent R (fun ix : Σ i, φ i => single ix.1 (f ix.1 ix.2)) ↔
      forall i, LinearIndependent R (f i) :=
  ⟨fun h i => (h.comp _ sigma_mk_injective).of_comp (lsingle i), linearIndependent_single _⟩

open LinearMap Submodule

open scoped Classical in
/--
Definition of `basis` / `basis` 的定义

English:
definition basis
  signature: {φ : ι -> Type*} (b : forall i, Basis (φ i) R M)
  body: .ofRepr (finsuppLequivDFinsupp R).trans
    (DFinsupp.mapRange.linearEquiv fun i => (b i).repr).trans (sigmaFinsuppLequivDFinsupp R).symm

@[simp]

中文:
定义 basis
  签名: {φ : ι -> 类型} (b : 对任意 i, 基 (φ i) R M)
  定义体: .ofRepr (finsuppLequivDFinsupp R).trans
    (DFinsupp.mapRange.linearEquiv fun i => (b i).repr).trans (sigmaFinsuppLequivDFinsupp R).symm

@[simp]
-/
protected def basis {φ : ι -> Type*} (b : forall i, Basis (φ i) R M) : Basis (Σ i, φ i) R (ι ->₀ M) :=
.ofRepr (finsuppLequivDFinsupp R).trans
    (DFinsupp.mapRange.linearEquiv fun i => (b i).repr).trans (sigmaFinsuppLequivDFinsupp R).symm

@[simp]
/--
theorem `basis_repr` / 定理 `basis_repr`

English:
theorem basis_repr
  given: {φ : ι -> Type*} (b : forall i, Basis (φ i) R M) (g : ι ->₀ M) (ix)
  proof: rfl

@[simp]

中文:
定理 basis_repr
  条件: {φ : ι -> 类型} (b : 对任意 i, 基 (φ i) R M) (g : ι ->₀ M) (ix)
  证明: rfl

@[simp]
-/
theorem basis_repr {φ : ι -> Type*} (b : forall i, Basis (φ i) R M) (g : ι ->₀ M) (ix) :
    (Finsupp.basis b).repr g ix = (b ix.1).repr (g ix.1) ix.2 :=
  rfl

@[simp]
/--
theorem `coe_basis` / 定理 `coe_basis`

English:
theorem coe_basis
  given: {φ : ι -> Type*} (b : forall i, Basis (φ i) R M)
  proof: funext fun ⟨i, x⟩ =>
Basis.apply_eq_iff.mpr by
      ext ⟨j, y⟩
      by_cases h : i = j
      · cases h
        simp [Finsupp.single_apply_left sigma_mk_injective]
      · simp_all

中文:
定理 coe_basis
  条件: {φ : ι -> 类型} (b : 对任意 i, 基 (φ i) R M)
  证明: funext fun ⟨i, x⟩ =>
Basis.apply_eq_iff.mpr by
      ext ⟨j, y⟩
      by_cases h : i = j
      · cases h
        simp [Finsupp.single_apply_left sigma_mk_injective]
      · simp_all

Depends on / 依赖: Basis.apply_eq_iff.mpr, Finsupp, Finsupp.single_apply_left, apply_eq_iff, sigma_mk_injective, single_apply_left
-/
theorem coe_basis {φ : ι -> Type*} (b : forall i, Basis (φ i) R M) :
    ⇑(Finsupp.basis b) = fun ix : Σ i, φ i => single ix.1 (b ix.1 ix.2) :=
  funext fun ⟨i, x⟩ =>
Basis.apply_eq_iff.mpr by
      ext ⟨j, y⟩
      by_cases h : i = j
      · cases h
        simp [Finsupp.single_apply_left sigma_mk_injective]
      · simp_all

variable (ι R M) in
/--
Instance `_root_.Module.Free.finsupp` / 实例 `_root_.Module.Free.finsupp`

English:
instance _root_.Module.Free.finsupp
  signature: [Module.Free R M]
  body: .of_basis (Finsupp.basis fun _ => Module.Free.chooseBasis R M)

中文:
实例 _root_.模.自由.finsupp
  签名: [模.自由 R M]
  定义体: .of_basis (Finsupp.basis fun _ => Module.Free.chooseBasis R M)

Depends on / 依赖: Finsupp, Finsupp.basis, Module, Module.Free.chooseBasis, chooseBasis, of_basis
-/
instance _root_.Module.Free.finsupp [Module.Free R M] : Module.Free R (ι ->₀ M) :=
  .of_basis (Finsupp.basis fun _ => Module.Free.chooseBasis R M)

/-- The basis on `ι →₀ R` with basis vectors `fun i ↦ single i 1`. -/
@[simps]
/--
Definition of `basisSingleOne` / `basisSingleOne` 的定义

English:
definition basisSingleOne
  signature: : Basis ι R (ι ->₀ R)
  body: Basis.ofRepr (LinearEquiv.refl _ _)

@[simp]

中文:
定义 basisSingleOne
  签名: : 基 ι R (ι ->₀ R)
  定义体: Basis.ofRepr (LinearEquiv.refl _ _)

@[simp]
-/
protected def basisSingleOne : Basis ι R (ι ->₀ R) :=
  Basis.ofRepr (LinearEquiv.refl _ _)

@[simp]
/--
theorem `coe_basisSingleOne` / 定理 `coe_basisSingleOne`

English:
theorem coe_basisSingleOne
  statement: (Finsupp.basisSingleOne : ι -> ι ->₀ R) = fun i => Finsupp.single i 1
  proof: funext fun _ => Basis.apply_eq_iff.mpr rfl

中文:
定理 coe_basisSingleOne
  结论: (有限支撑.basisSingleOne : ι -> ι ->₀ R) = fun i => 有限支撑.single i 1
  证明: funext fun _ => Basis.apply_eq_iff.mpr rfl

Depends on / 依赖: Basis.apply_eq_iff.mpr, apply_eq_iff
-/
theorem coe_basisSingleOne : (Finsupp.basisSingleOne : ι -> ι ->₀ R) = fun i => Finsupp.single i 1 :=
  funext fun _ => Basis.apply_eq_iff.mpr rfl

variable (ι R) in
/--
lemma `linearIndependent_single_one` / 引理 `linearIndependent_single_one`

English:
lemma linearIndependent_single_one
  statement: LinearIndependent R fun i : ι => single i (1 : R)
  proof: Finsupp.basisSingleOne.linearIndependent

中文:
引理 linearIndependent_single_one
  结论: LinearIndependent R fun i : ι => single i (1 : R)
  证明: Finsupp.basisSingleOne.linearIndependent

Depends on / 依赖: Finsupp, Finsupp.basisSingleOne.linearIndependent, basisSingleOne, linearIndependent
-/
lemma linearIndependent_single_one : LinearIndependent R fun i : ι => single i (1 : R) :=
  Finsupp.basisSingleOne.linearIndependent

/--
lemma `isCompl_range_lmapDomain_span` / 引理 `isCompl_range_lmapDomain_span`

English:
lemma isCompl_range_lmapDomain_span
  statement: {α β : Type*}
  proof: by
  rw [range_lmapDomain]
  have := (Finsupp.basisSingleOne (R := R)).linearIndependent.isCompl_span_image
     (Module.Basis.span_eq _) huv
  rwa [← Set.range_comp, ← Set.range_comp, Function.comp_def] at this

中文:
引理 isCompl_range_lmapDomain_span
  结论: {α β : 类型}
  证明: by
  rw [range_lmapDomain]
  have := (Finsupp.basisSingleOne (R := R)).linearIndependent.isCompl_span_image
     (Module.Basis.span_eq _) huv
  rwa [← Set.range_comp, ← Set.range_comp, Function.comp_def] at this

Depends on / 依赖: Finsupp, Finsupp.basisSingleOne, Function, Function.comp_def, Module, Module.Basis.span_eq, Set.range_comp, basisSingleOne, comp_def, isCompl_span_image, linearIndependent, linearIndependent.isCompl_span_image, range_comp, range_lmapDomain, span_eq
-/
lemma isCompl_range_lmapDomain_span {α β : Type*}
    {u : α -> ι} {v : β -> ι} (huv : IsCompl (Set.range u) (Set.range v)) :
    IsCompl (LinearMap.range (lmapDomain R R u)) (.span R (.range fun x => single (v x) 1)) := by
  rw [range_lmapDomain]
  have := (Finsupp.basisSingleOne (R := R)).linearIndependent.isCompl_span_image
     (Module.Basis.span_eq _) huv
  rwa [← Set.range_comp, ← Set.range_comp, Function.comp_def] at this

end Semiring

section Ring
variable {R M ι : Type*} [Ring R] [AddCommGroup M]

/--
lemma `linearIndependent_single_of_ne_zero` / 引理 `linearIndependent_single_of_ne_zero`

English:
lemma linearIndependent_single_of_ne_zero
  statement: [IsDomain R] [Module R M] [IsTorsionFree R M] {v : ι -> M}
  proof: by
  rw [← linearIndependent_equiv (Equiv.sigmaPUnit ι)]
exact linearIndependent_single (f := fun i (_ : Unit) => v i) by simp +contextual [hv]

中文:
引理 linearIndependent_single_of_ne_zero
  结论: [是整环 R] [模 R M] [是无挠 R M] {v : ι -> M}
  证明: by
  rw [← linearIndependent_equiv (Equiv.sigmaPUnit ι)]
exact linearIndependent_single (f := fun i (_ : Unit) => v i) by simp +contextual [hv]

Depends on / 依赖: Equiv.sigmaPUnit, contextual, linearIndependent_equiv, linearIndependent_single, sigmaPUnit
-/
lemma linearIndependent_single_of_ne_zero [IsDomain R] [Module R M] [IsTorsionFree R M] {v : ι -> M}
    (hv : forall i, v i != 0) : LinearIndependent R fun i : ι => single i (v i) := by
  rw [← linearIndependent_equiv (Equiv.sigmaPUnit ι)]
exact linearIndependent_single (f := fun i (_ : Unit) => v i) by simp +contextual [hv]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `lcomapDomain_eq_linearProjOfIsCompl` / 引理 `lcomapDomain_eq_linearProjOfIsCompl`

English:
lemma lcomapDomain_eq_linearProjOfIsCompl
  statement: {α β : Type*}
  proof: by
  classical
  refine Finsupp.basisSingleOne.ext fun i => ?_
  obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ : i in Set.range u ⊔ .range v := by rw [codisjoint_iff.mp h.2]; trivial
  · have : single (u i) 1 = lmapDomain R R u (.single i 1) := by simp
    simp only [coe_basisSingleOne, lcomapDomain_apply, comapDomain_single]
    rw [this]; rw [LinearMap.linearProjOfIsCompl_apply_left]
  · rw [LinearMap.linearProjOfIsCompl_apply_right']
    · ext j
      simp only [coe_basisSingleOne, lcomapDomain_apply, comapDomain_apply, single_apply,
        coe_zero, Pi.zero_apply, ite_eq_right_iff]
      intro hij
      exact (Set.disjoint_range_iff.mp h.1 j i hij.symm).elim
    · exact Submodule.subset_span ⟨i, rfl⟩

中文:
引理 lcomapDomain_eq_linearProjOfIsCompl
  结论: {α β : 类型}
  证明: by
  classical
  refine Finsupp.basisSingleOne.ext fun i => ?_
  obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ : i in Set.range u ⊔ .range v := by rw [codisjoint_iff.mp h.2]; trivial
  · have : single (u i) 1 = lmapDomain R R u (.single i 1) := by simp
    simp only [coe_basisSingleOne, lcomapDomain_apply, comapDomain_single]
    rw [this]; rw [LinearMap.linearProjOfIsCompl_apply_left]
  · rw [LinearMap.linearProjOfIsCompl_apply_right']
    · ext j
      simp only [coe_basisSingleOne, lcomapDomain_apply, comapDomain_apply, single_apply,
        coe_zero, Pi.zero_apply, ite_eq_right_iff]
      intro hij
      exact (Set.disjoint_range_iff.mp h.1 j i hij.symm).elim
    · exact Submodule.subset_span ⟨i, rfl⟩

Depends on / 依赖: Finsupp, Finsupp.basisSingleOne.ext, LinearMap, LinearMap.linearProjOfIsCompl_apply_left, LinearMap.linearProjOfIsCompl_apply_right, Set.range, basisSingleOne, classical, codisjoint_iff, codisjoint_iff.mp, coe_, coe_basisSingleOne, comapDomain_apply, comapDomain_single, lcomapDomain_apply, linearProjOfIsCompl_apply_left, linearProjOfIsCompl_apply_right, lmapDomain, single, single_apply
-/
lemma lcomapDomain_eq_linearProjOfIsCompl {α β : Type*}
    {u : α -> ι} {v : β -> ι} (hu : u.Injective) (h : IsCompl (Set.range u) (Set.range v)) :
    lcomapDomain u hu =
      LinearMap.linearProjOfIsCompl (.span R (Set.range fun x : β => single (v x) (1 : R)))
        (lmapDomain _ _ u) (mapDomain_injective hu) (isCompl_range_lmapDomain_span h) := by
  classical
  refine Finsupp.basisSingleOne.ext fun i => ?_
  obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ : i in Set.range u ⊔ .range v := by rw [codisjoint_iff.mp h.2]; trivial
  · have : single (u i) 1 = lmapDomain R R u (.single i 1) := by simp
    simp only [coe_basisSingleOne, lcomapDomain_apply, comapDomain_single]
    rw [this]; rw [LinearMap.linearProjOfIsCompl_apply_left]
  · rw [LinearMap.linearProjOfIsCompl_apply_right']
    · ext j
      simp only [coe_basisSingleOne, lcomapDomain_apply, comapDomain_apply, single_apply,
        coe_zero, Pi.zero_apply, ite_eq_right_iff]
      intro hij
      exact (Set.disjoint_range_iff.mp h.1 j i hij.symm).elim
    · exact Submodule.subset_span ⟨i, rfl⟩

end Ring

end Finsupp

/--
lemma `Module.Free.trans` / 引理 `Module.Free.trans`

English:
lemma Module.Free.trans
  statement: {R S M : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
  proof: let e : (ChooseBasisIndex S M ->₀ S) ≃ₗ[R] ChooseBasisIndex S M ->₀ (ChooseBasisIndex R S ->₀ R) :=
    Finsupp.mapRange.linearEquiv (chooseBasis R S).repr
  let e : M ≃ₗ[R] ChooseBasisIndex S M ->₀ (ChooseBasisIndex R S ->₀ R) :=
    (chooseBasis S M).repr.restrictScalars R ≪≫ₗ e
  .of_equiv e.symm

中文:
引理 模.自由.trans
  结论: {R S M : 类型} [交换半环 R] [半环 S] [代数 R S]
  证明: let e : (ChooseBasisIndex S M ->₀ S) ≃ₗ[R] ChooseBasisIndex S M ->₀ (ChooseBasisIndex R S ->₀ R) :=
    Finsupp.mapRange.linearEquiv (chooseBasis R S).repr
  let e : M ≃ₗ[R] ChooseBasisIndex S M ->₀ (ChooseBasisIndex R S ->₀ R) :=
    (chooseBasis S M).repr.restrictScalars R ≪≫ₗ e
  .of_equiv e.symm

Depends on / 依赖: ChooseBasisIndex, Finsupp, Finsupp.mapRange.linearEquiv, chooseBasis, e.symm, linearEquiv, mapRange, of_equiv, repr.restrictScalars, restrictScalars
-/
lemma Module.Free.trans {R S M : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Free S M]
    [Module.Free R S] : Module.Free R M :=
  let e : (ChooseBasisIndex S M ->₀ S) ≃ₗ[R] ChooseBasisIndex S M ->₀ (ChooseBasisIndex R S ->₀ R) :=
    Finsupp.mapRange.linearEquiv (chooseBasis R S).repr
  let e : M ≃ₗ[R] ChooseBasisIndex S M ->₀ (ChooseBasisIndex R S ->₀ R) :=
    (chooseBasis S M).repr.restrictScalars R ≪≫ₗ e
  .of_equiv e.symm

/-! TODO: move this section to an earlier file. -/


namespace Basis

variable {R M n : Type*}
variable [DecidableEq n]
variable [Semiring R] [AddCommMonoid M] [Module R M]

/--
theorem `_root_.Finset.sum_single_ite` / 定理 `_root_.Finset.sum_single_ite`

English:
theorem _root_.Finset.sum_single_ite
  given: [Fintype n] (a : R) (i : n)
  proof: by
  simp only [apply_ite (Finsupp.single _), Finsupp.single_zero, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ _)]

@[simp]

中文:
定理 _root_.有限集.sum_single_ite
  条件: [有限类型 n] (a : R) (i : n)
  证明: by
  simp only [apply_ite (Finsupp.single _), Finsupp.single_zero, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ _)]

@[simp]

Depends on / 依赖: Finset, Finset.mem_univ, Finset.sum_ite_eq, Finsupp, Finsupp.single, Finsupp.single_zero, apply_ite, if_pos, mem_univ, single, single_zero, sum_ite_eq
-/
theorem _root_.Finset.sum_single_ite [Fintype n] (a : R) (i : n) :
    (∑ x : n, Finsupp.single x (if i = x then a else 0)) = Finsupp.single i a := by
  simp only [apply_ite (Finsupp.single _), Finsupp.single_zero, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ _)]

@[simp]
/--
theorem `equivFun_symm_single` / 定理 `equivFun_symm_single`

English:
theorem equivFun_symm_single
  given: [Finite n] (b : Basis n R M) (i : n)
  proof: by
  cases nonempty_fintype n
  simp [Pi.single_apply]

中文:
定理 equivFun_symm_single
  条件: [有限 n] (b : 基 n R M) (i : n)
  证明: by
  cases nonempty_fintype n
  simp [Pi.single_apply]

Depends on / 依赖: Pi.single_apply, nonempty_fintype, single_apply
-/
theorem equivFun_symm_single [Finite n] (b : Basis n R M) (i : n) :
    b.equivFun.symm (Pi.single i 1) = b i := by
  cases nonempty_fintype n
  simp [Pi.single_apply]

end Basis

section Algebra

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] {ι : Type*} (B : Basis ι R S)

/--
theorem `Module.Basis.repr_smul'` / 定理 `Module.Basis.repr_smul'`

English:
theorem Module.Basis.repr_smul'
  given: (i : ι) (r : R) (s : S)
  proof: by
  rw [← smul_eq_mul]; rw [← smul_eq_mul]; rw [algebraMap_smul]; rw [map_smul]; rw [Finsupp.smul_apply]

中文:
定理 模.基.repr_smul'
  条件: (i : ι) (r : R) (s : S)
  证明: by
  rw [← smul_eq_mul]; rw [← smul_eq_mul]; rw [algebraMap_smul]; rw [map_smul]; rw [Finsupp.smul_apply]

Depends on / 依赖: Finsupp, Finsupp.smul_apply, algebraMap_smul, map_smul, smul_apply, smul_eq_mul
-/
theorem Module.Basis.repr_smul' (i : ι) (r : R) (s : S) :
    B.repr (algebraMap R S r * s) i = r * B.repr s i := by
  rw [← smul_eq_mul]; rw [← smul_eq_mul]; rw [algebraMap_smul]; rw [map_smul]; rw [Finsupp.smul_apply]

end Algebra

namespace FreeAbelianGroup

instance {σ : Type*} : Module.Free Int (FreeAbelianGroup σ) where
  exists_basis := ⟨σ, ⟨(FreeAbelianGroup.equivFinsupp _).toIntLinearEquiv⟩⟩

end FreeAbelianGroup

namespace AddMonoidAlgebra
variable {M R S : Type*} [Semiring R] [Semiring S] [Module R S] [Module.Free R S]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Free R S[M]
  body: .of_equiv (coeffLinearEquiv _).symm

中文:
实例 :
  签名: 模.自由 R S[M]
  定义体: .of_equiv (coeffLinearEquiv _).symm

Depends on / 依赖: coeffLinearEquiv, of_equiv
-/
instance : Module.Free R S[M] := .of_equiv (coeffLinearEquiv _).symm

end AddMonoidAlgebra

namespace MonoidAlgebra
variable {M R S : Type*} [Semiring R] [Semiring S] [Module R S] [Module.Free R S]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Free R S[M]
  body: .of_equiv (coeffLinearEquiv _).symm

中文:
实例 :
  签名: 模.自由 R S[M]
  定义体: .of_equiv (coeffLinearEquiv _).symm

Depends on / 依赖: coeffLinearEquiv, of_equiv
-/
instance : Module.Free R S[M] := .of_equiv (coeffLinearEquiv _).symm

end MonoidAlgebra

namespace Polynomial
variable {R S : Type*} [Semiring R] [Semiring S] [Module R S] [Module.Free R S]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Free R R[X]
  body: .of_equiv (Polynomial.toFinsuppIsoLinear _).symm

中文:
实例 :
  签名: 模.自由 R R[X]
  定义体: .of_equiv (Polynomial.toFinsuppIsoLinear _).symm

Depends on / 依赖: Polynomial, Polynomial.toFinsuppIsoLinear, of_equiv, toFinsuppIsoLinear
-/
instance : Module.Free R R[X] := .of_equiv (Polynomial.toFinsuppIsoLinear _).symm

end Polynomial
