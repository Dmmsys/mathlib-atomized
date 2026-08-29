/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Data.Finsupp.Fintype
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Logic.Small.Basic

/-!
# Free modules

We introduce a class `Module.Free R M`, for `R` a `Semiring` and `M` an `R`-module and we provide
several basic instances for this class.

Use `Finsupp.linearCombination_id_surjective` to prove that any module is the quotient of a free
module.

## Main definition

* `Module.Free R M` : the class of free `R`-modules.
-/

@[expose] public section

assert_not_exists DirectSum Matrix TensorProduct

universe u v w z

variable {ι : Type*} (R : Type u) (M : Type v) (N : Type z)

namespace Module
section Basic

variable [Semiring R] [AddCommMonoid M] [Module R M]

/--
Definition of `Free` / `Free` 的定义

English:
class Free
  parameters: (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]
  axioms and operations (1):
    - exists_basis((R M)) : Nonempty (I : Type v) × Basis I R M

中文:
类 自由
  参数: (R : 类型u) (M : 类型v) [半环 R] [加法交换幺半群 M] [模 R M]
  公理与运算 (1 个):
    - exists_basis((R M)) : 非空 (I : 类型v) × 基 I R M
-/
class Free (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
exists_basis (R M) : Nonempty (I : Type v) × Basis I R M

/--
lemma `Free.exists_set` / 引理 `Free.exists_set`

English:
lemma Free.exists_set
  given: [Free R M]
  statement: exists S : Set M, Nonempty (Basis S R M)
  proof: let ⟨_I, b⟩ := exists_basis R M; ⟨Set.range b, ⟨b.reindexRange⟩⟩

中文:
引理 自由.存在_set
  条件: [自由 R M]
  结论: 存在 S : 集合 M, 非空 (基 S R M)
  证明: let ⟨_I, b⟩ := exists_basis R M; ⟨Set.range b, ⟨b.reindexRange⟩⟩

Depends on / 依赖: Set.range, b.reindexRange, exists_basis, reindexRange
-/
lemma Free.exists_set [Free R M] : exists S : Set M, Nonempty (Basis S R M) :=
  let ⟨_I, b⟩ := exists_basis R M; ⟨Set.range b, ⟨b.reindexRange⟩⟩

/--
theorem `free_iff_set` / 定理 `free_iff_set`

English:
theorem free_iff_set
  statement: Free R M ↔ exists S : Set M, Nonempty (Basis S R M)
  proof: ⟨fun _ => Free.exists_set .., fun ⟨S, hS⟩ => ⟨nonempty_sigma.2 ⟨S, hS⟩⟩⟩

中文:
定理 free_iff_set
  结论: 自由 R M ↔ 存在 S : 集合 M, 非空 (基 S R M)
  证明: ⟨fun _ => Free.exists_set .., fun ⟨S, hS⟩ => ⟨nonempty_sigma.2 ⟨S, hS⟩⟩⟩

Depends on / 依赖: Free.exists_set, exists_set, nonempty_sigma
-/
theorem free_iff_set : Free R M ↔ exists S : Set M, Nonempty (Basis S R M) :=
  ⟨fun _ => Free.exists_set .., fun ⟨S, hS⟩ => ⟨nonempty_sigma.2 ⟨S, hS⟩⟩⟩

/--
theorem `free_def` / 定理 `free_def`

English:
theorem free_def
  given: [Small.{w, v} M]
  statement: Free R M ↔ exists I : Type w, Nonempty (Basis I R M) where
  proof: ⟨Shrink (Set.range h.exists_basis.some.2),
      ⟨(Basis.reindexRange h.exists_basis.some.2).reindex (equivShrink _)⟩⟩
  mpr h := ⟨(nonempty_sigma.2 h).map fun ⟨_, b⟩ => ⟨Set.range b, b.reindexRange⟩⟩

中文:
定理 free_def
  条件: [Small.{w, v} M]
  结论: 自由 R M ↔ 存在 I : 类型 w, 非空 (基 I R M) where
  证明: ⟨Shrink (Set.range h.exists_basis.some.2),
      ⟨(Basis.reindexRange h.exists_basis.some.2).reindex (equivShrink _)⟩⟩
  mpr h := ⟨(nonempty_sigma.2 h).map fun ⟨_, b⟩ => ⟨Set.range b, b.reindexRange⟩⟩

Depends on / 依赖: Basis.reindexRange, Set.range, Shrink, b.reindexRange, equivShrink, exists_basis, h.exists_basis.some, nonempty_sigma, reindex, reindexRange
-/
theorem free_def [Small.{w, v} M] : Free R M ↔ exists I : Type w, Nonempty (Basis I R M) where
  mp h :=
    ⟨Shrink (Set.range h.exists_basis.some.2),
      ⟨(Basis.reindexRange h.exists_basis.some.2).reindex (equivShrink _)⟩⟩
  mpr h := ⟨(nonempty_sigma.2 h).map fun ⟨_, b⟩ => ⟨Set.range b, b.reindexRange⟩⟩

variable {R M}

/--
theorem `Free.of_basis` / 定理 `Free.of_basis`

English:
theorem Free.of_basis
  given: {ι : Type w} (b : Basis ι R M)
  statement: Free R M
  proof: (free_def R M).2 ⟨Set.range b, ⟨b.reindexRange⟩⟩

中文:
定理 自由.of_basis
  条件: {ι : 类型 w} (b : 基 ι R M)
  结论: 自由 R M
  证明: (free_def R M).2 ⟨Set.range b, ⟨b.reindexRange⟩⟩

Depends on / 依赖: Set.range, b.reindexRange, free_def, reindexRange
-/
theorem Free.of_basis {ι : Type w} (b : Basis ι R M) : Free R M :=
  (free_def R M).2 ⟨Set.range b, ⟨b.reindexRange⟩⟩

end Basic

namespace Free

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M] [Module.Free R M]
variable [AddCommMonoid N] [Module R N]

/--
Definition of `ChooseBasisIndex` / `ChooseBasisIndex` 的定义

English:
definition ChooseBasisIndex
  signature: : Type _
  body: ((Module.free_iff_set R M).mp ‹_›).choose

中文:
定义 ChooseBasisIndex
  签名: : 类型 _
  定义体: ((Module.free_iff_set R M).mp ‹_›).choose

Depends on / 依赖: Module, Module.free_iff_set, free_iff_set
-/
def ChooseBasisIndex : Type _ :=
  ((Module.free_iff_set R M).mp ‹_›).choose

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableEq (ChooseBasisIndex R M)
  body: Classical.decEq _

中文:
实例 :
  签名: DecidableEq (ChooseBasisIndex R M)
  定义体: Classical.decEq _

Depends on / 依赖: Classical, Classical.decEq
-/
noncomputable instance : DecidableEq (ChooseBasisIndex R M) := Classical.decEq _

/--
Definition of `chooseBasis` / `chooseBasis` 的定义

English:
definition chooseBasis
  signature: : Basis (ChooseBasisIndex R M) R M
  body: ((Module.free_iff_set R M).mp ‹_›).choose_spec.some

中文:
定义 chooseBasis
  签名: : 基 (ChooseBasisIndex R M) R M
  定义体: ((Module.free_iff_set R M).mp ‹_›).choose_spec.some

Depends on / 依赖: Module, Module.free_iff_set, choose_spec, choose_spec.some, free_iff_set
-/
noncomputable def chooseBasis : Basis (ChooseBasisIndex R M) R M :=
  ((Module.free_iff_set R M).mp ‹_›).choose_spec.some

/--
Definition of `constr` / `constr` 的定义

English:
definition constr
  signature: {S : Type z} [Semiring S] [Module S N] [SMulCommClass R S N]
  body: Basis.constr (chooseBasis R M) S

中文:
定义 constr
  签名: {S : 类型 z} [半环 S] [模 S N] [标量交换类 R S N]
  定义体: Basis.constr (chooseBasis R M) S

Depends on / 依赖: Basis.constr, chooseBasis, constr
-/
noncomputable def constr {S : Type z} [Semiring S] [Module S N] [SMulCommClass R S N] :
    (ChooseBasisIndex R M -> N) ≃ₗ[S] M ->ₗ[R] N :=
  Basis.constr (chooseBasis R M) S

instance (priority := 100) instIsTorsionFree : IsTorsionFree R M :=
  let ⟨⟨_, b⟩⟩ := exists_basis (R := R) (M := M)
  b.isTorsionFree

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: M] : Nonempty (Module.Free.ChooseBasisIndex R M)
  body: (Module.Free.chooseBasis R M).index_nonempty

中文:
实例 [非平凡
  签名: M] : 非空 (模.自由.ChooseBasisIndex R M)
  定义体: (Module.Free.chooseBasis R M).index_nonempty

Depends on / 依赖: Module, Module.Free.chooseBasis, chooseBasis, index_nonempty
-/
instance [Nontrivial M] : Nonempty (Module.Free.ChooseBasisIndex R M) :=
  (Module.Free.chooseBasis R M).index_nonempty

/--
theorem `infinite` / 定理 `infinite`

English:
theorem infinite
  given: [Infinite R] [Nontrivial M]
  statement: Infinite M
  proof: (Equiv.infinite_iff (chooseBasis R M).repr.toEquiv).mpr Finsupp.infinite_of_right

中文:
定理 infinite
  条件: [无限 R] [非平凡 M]
  结论: 无限 M
  证明: (Equiv.infinite_iff (chooseBasis R M).repr.toEquiv).mpr Finsupp.infinite_of_right

Depends on / 依赖: Equiv.infinite_iff, Finsupp, Finsupp.infinite_of_right, chooseBasis, infinite_iff, infinite_of_right, repr.toEquiv, toEquiv
-/
theorem infinite [Infinite R] [Nontrivial M] : Infinite M :=
  (Equiv.infinite_iff (chooseBasis R M).repr.toEquiv).mpr Finsupp.infinite_of_right

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: M] : FaithfulSMul R M
  body: .of_injective _ (chooseBasis R M).repr.symm.injective

中文:
实例 [非平凡
  签名: M] : 忠实标量乘法 R M
  定义体: .of_injective _ (chooseBasis R M).repr.symm.injective

Depends on / 依赖: chooseBasis, injective, of_injective, repr.symm.injective
-/
instance [Nontrivial M] : FaithfulSMul R M :=
  .of_injective _ (chooseBasis R M).repr.symm.injective

variable {R M N}

/--
lemma `of_equiv` / 引理 `of_equiv`

English:
lemma of_equiv
  statement: {R R' M M' : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  proof: by
  let e₁ : R ≃+* R' := RingHomInvPair.toRingEquiv σ σ'
  let I := Module.Free.ChooseBasisIndex R M
  obtain ⟨e₃ : M ≃ₗ[R] I ->₀ R⟩ := Module.Free.chooseBasis R M
  let e : M' ≃+ (I ->₀ R') :=
    (e₂.symm.trans e₃).toAddEquiv.trans (Finsupp.mapRange.addEquiv (ι := I) e₁.toAddEquiv)
  have he (x) 

中文:
引理 of_equiv
  结论: {R R' M M' : 类型} [半环 R] [加法交换幺半群 M] [模 R M]
  证明: by
  let e₁ : R ≃+* R' := RingHomInvPair.toRingEquiv σ σ'
  let I := Module.Free.ChooseBasisIndex R M
  obtain ⟨e₃ : M ≃ₗ[R] I ->₀ R⟩ := Module.Free.chooseBasis R M
  let e : M' ≃+ (I ->₀ R') :=
    (e₂.symm.trans e₃).toAddEquiv.trans (Finsupp.mapRange.addEquiv (ι := I) e₁.toAddEquiv)
  have he (x) 

Depends on / 依赖: ChooseBasisIndex, Finsupp, Finsupp.ext, Finsupp.mapRange.addEquiv, Module, Module.Free.ChooseBasisIndex, Module.Free.chooseBasis, RingHomInvPair, RingHomInvPair.toRingEquiv, addEquiv, chooseBasis, mapRange, map_smul, of_basi, symm.trans, toAddEquiv, toAddEquiv.trans, toRingEquiv
-/
lemma of_equiv {R R' M M' : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring R'] [AddCommMonoid M'] [Module R' M']
    {σ : R ->+* R'} {σ' : R' ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e₂ : M ≃ₛₗ[σ] M') [Module.Free R M] :
    Module.Free R' M' := by
  let e₁ : R ≃+* R' := RingHomInvPair.toRingEquiv σ σ'
  let I := Module.Free.ChooseBasisIndex R M
  obtain ⟨e₃ : M ≃ₗ[R] I ->₀ R⟩ := Module.Free.chooseBasis R M
  let e : M' ≃+ (I ->₀ R') :=
    (e₂.symm.trans e₃).toAddEquiv.trans (Finsupp.mapRange.addEquiv (ι := I) e₁.toAddEquiv)
  have he (x) : e x = Finsupp.mapRange.addEquiv (ι := I) e₁.toAddEquiv (e₃ (e₂.symm x)) := rfl
  let e' : M' ≃ₗ[R'] (I ->₀ R') :=
    { __ := e, map_smul' := fun m x => Finsupp.ext fun i => by simp [e₁, he, map_smulₛₗ] }
  exact of_basis (.ofRepr e')

/--
theorem `of_equiv'` / 定理 `of_equiv'`

English:
theorem of_equiv'
  statement: {P : Type v} [AddCommMonoid P] [Module R P] (_ : Module.Free R P)
  proof: of_equiv e

中文:
定理 of_equiv'
  结论: {P : 类型v} [加法交换幺半群 P] [模 R P] (_ : 模.自由 R P)
  证明: of_equiv e

Depends on / 依赖: of_equiv
-/
theorem of_equiv' {P : Type v} [AddCommMonoid P] [Module R P] (_ : Module.Free R P)
    (e : P ≃ₗ[R] N) : Module.Free R N :=
  of_equiv e

/--
lemma `iff_of_equiv` / 引理 `iff_of_equiv`

English:
lemma iff_of_equiv
  statement: {R R' M M'} [Semiring R] [AddCommMonoid M] [Module R M]
  proof: ⟨fun _ => of_equiv e₂, fun _ => of_equiv e₂.symm⟩

@[deprecated (since := "2026-02-14")] alias of_ringEquiv := of_equiv
@[deprecated (since := "2026-02-14")] alias iff_of_ringEquiv := iff_of_equiv

中文:
引理 iff_of_equiv
  结论: {R R' M M'} [半环 R] [加法交换幺半群 M] [模 R M]
  证明: ⟨fun _ => of_equiv e₂, fun _ => of_equiv e₂.symm⟩

@[deprecated (since := "2026-02-14")] alias of_ringEquiv := of_equiv
@[deprecated (since := "2026-02-14")] alias iff_of_ringEquiv := iff_of_equiv

Depends on / 依赖: of_equiv
-/
lemma iff_of_equiv {R R' M M'} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring R'] [AddCommMonoid M'] [Module R' M']
    {σ : R ->+* R'} {σ' : R' ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e₂ : M ≃ₛₗ[σ] M') :
    Module.Free R M ↔ Module.Free R' M' :=
  ⟨fun _ => of_equiv e₂, fun _ => of_equiv e₂.symm⟩

@[deprecated (since := "2026-02-14")] alias of_ringEquiv := of_equiv
@[deprecated (since := "2026-02-14")] alias iff_of_ringEquiv := iff_of_equiv

/--
Instance `shrink` / 实例 `shrink`

English:
instance shrink
  signature: [Small.{w} M]
  body: Module.Free.of_equiv (Shrink.linearEquiv R M).symm

中文:
实例 shrink
  签名: [Small.{w} M]
  定义体: Module.Free.of_equiv (Shrink.linearEquiv R M).symm

Depends on / 依赖: Module, Module.Free.of_equiv, Shrink, Shrink.linearEquiv, linearEquiv, of_equiv
-/
instance shrink [Small.{w} M] : Module.Free R (Shrink.{w} M) :=
  Module.Free.of_equiv (Shrink.linearEquiv R M).symm

set_option linter.dupNamespace false in
@[deprecated (since := "2026-04-18")] alias Module.free_shrink := shrink

variable (R M N)

/--
Instance `self` / 实例 `self`

English:
instance self
  signature: : Module.Free R R
  body: of_basis (Basis.singleton Unit R)

中文:
实例 self
  签名: : 模.自由 R R
  定义体: of_basis (Basis.singleton Unit R)

Depends on / 依赖: Basis.singleton, of_basis, singleton
-/
instance self : Module.Free R R :=
  of_basis (Basis.singleton Unit R)

/--
Instance `ulift` / 实例 `ulift`

English:
instance ulift
  signature: : Free R (ULift M)
  body: of_equiv ULift.moduleEquiv.symm

中文:
实例 ulift
  签名: : 自由 R (类型层提升 M)
  定义体: of_equiv ULift.moduleEquiv.symm

Depends on / 依赖: ULift.moduleEquiv.symm, moduleEquiv, of_equiv
-/
instance ulift : Free R (ULift M) := of_equiv ULift.moduleEquiv.symm

instance (priority := 100) of_subsingleton [Subsingleton N] : Module.Free R N :=
  of_basis.{u, z, z} (Basis.empty N : Basis PEmpty R N)

-- This was previously a global instance,
-- but it doesn't appear to be used and has been implicated in slow typeclass resolutions.
/--
lemma `of_subsingleton'` / 引理 `of_subsingleton'`

English:
lemma of_subsingleton'
  given: [Subsingleton R]
  statement: Module.Free R N
  proof: letI := Module.subsingleton R N
  Module.Free.of_subsingleton R N

中文:
引理 of_subsingleton'
  条件: [子单例 R]
  结论: 模.自由 R N
  证明: letI := Module.subsingleton R N
  Module.Free.of_subsingleton R N

Depends on / 依赖: Module, Module.Free.of_subsingleton, Module.subsingleton, of_subsingleton, subsingleton
-/
lemma of_subsingleton' [Subsingleton R] : Module.Free R N :=
  letI := Module.subsingleton R N
  Module.Free.of_subsingleton R N

end Semiring

end Free

namespace Basis

open Finset

variable {S : Type*} [CommRing R] [Ring S] [Algebra R S]

set_option backward.isDefEq.respectTransparency false in
variable {R} in
/--
theorem `repr_algebraMap` / 定理 `repr_algebraMap`

English:
theorem repr_algebraMap
  given: {ι : Type*} {B : Basis ι R S} {i : ι} (hBi : B i = 1) (r : R)
  proof: by
  ext j; simp [Algebra.algebraMap_eq_smul_one, ← hBi]

中文:
定理 repr_algebraMap
  条件: {ι : 类型} {B : 基 ι R S} {i : ι} (hBi : B i = 1) (r : R)
  证明: by
  ext j; simp [Algebra.algebraMap_eq_smul_one, ← hBi]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one
-/
theorem repr_algebraMap {ι : Type*} {B : Basis ι R S} {i : ι} (hBi : B i = 1) (r : R) :
    B.repr (algebraMap R S r) = Finsupp.single i r := by
  ext j; simp [Algebra.algebraMap_eq_smul_one, ← hBi]

end Basis

namespace End
variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Free R M]

/--
theorem `mem_center_iff` / 定理 `mem_center_iff`

English:
theorem mem_center_iff
  given: {f : End R M}
  proof: by
  simp only [Semigroup.mem_center_iff, LinearMap.ext_iff, mul_apply]
  refine ⟨fun h => ?_, by simp_all⟩
  by_cases! Subsingleton M
  · exact ⟨0, by simp, fun _ => Subsingleton.allEq _ _⟩
  let b := Free.chooseBasis R M
  let i := b.index_nonempty.some
  have H x : f x = b.repr (f (b i)) i • x :=

中文:
定理 mem_center_iff
  条件: {f : End R M}
  证明: by
  simp only [Semigroup.mem_center_iff, LinearMap.ext_iff, mul_apply]
  refine ⟨fun h => ?_, by simp_all⟩
  by_cases! Subsingleton M
  · exact ⟨0, by simp, fun _ => Subsingleton.allEq _ _⟩
  let b := Free.chooseBasis R M
  let i := b.index_nonempty.some
  have H x : f x = b.repr (f (b i)) i • x :=

Depends on / 依赖: Free.chooseBasis, LinearMap, LinearMap.ext_iff, Semigroup, Semigroup.mem_center_iff, Subsingleton, Subsingleton.allEq, b.coord, b.index_nonempty.some, b.repr, chooseBasis, ext_iff, index_nonempty, mem_center_iff, mul_apply, smulRight
-/
theorem mem_center_iff {f : End R M} :
    f in Set.center (End R M) ↔ exists (α : R) (hα : α in Set.center R), f = smulLeft α hα := by
  simp only [Semigroup.mem_center_iff, LinearMap.ext_iff, mul_apply]
  refine ⟨fun h => ?_, by simp_all⟩
  by_cases! Subsingleton M
  · exact ⟨0, by simp, fun _ => Subsingleton.allEq _ _⟩
  let b := Free.chooseBasis R M
  let i := b.index_nonempty.some
  have H x : f x = b.repr (f (b i)) i • x := by simpa using (h ((b.coord i).smulRight x) (b i)).symm
exact ⟨b.coord i f b i, fun r => by simpa using congr(b.coord i $(H <| r • b i)), H⟩

/--
theorem `mem_submonoidCenter_iff` / 定理 `mem_submonoidCenter_iff`

English:
theorem mem_submonoidCenter_iff
  given: {f : End R M}
  proof: mem_center_iff

中文:
定理 mem_submonoidCenter_iff
  条件: {f : End R M}
  证明: mem_center_iff

Depends on / 依赖: mem_center_iff
-/
theorem mem_submonoidCenter_iff {f : End R M} :
    f in Submonoid.center (End R M) ↔ exists (α : R) (hα : α in Submonoid.center R), f = smulLeft α hα :=
  mem_center_iff

/--
theorem `mem_subsemigroupCenter_iff` / 定理 `mem_subsemigroupCenter_iff`

English:
theorem mem_subsemigroupCenter_iff
  given: {f : End R M}
  proof: mem_center_iff

中文:
定理 mem_subsemigroupCenter_iff
  条件: {f : End R M}
  证明: mem_center_iff

Depends on / 依赖: mem_center_iff
-/
theorem mem_subsemigroupCenter_iff {f : End R M} :
    f in Subsemigroup.center (End R M) ↔
      exists (α : R) (hα : α in Subsemigroup.center R), f = smulLeft α hα :=
  mem_center_iff

end Module.End
