/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.GradedMulAction

/-!
# Homogeneous submodules of a graded module

This file defines homogeneous submodule of a graded module `⨁ᵢ ℳᵢ` over graded ring `⨁ᵢ 𝒜ᵢ` and
operations on them.

## Main definitions

For any `p : Submodule A M`:
* `Submodule.IsHomogeneous ℳ p`: The property that a submodule is closed under `GradedModule.proj`.
* `HomogeneousSubmodule 𝒜 ℳ`: The structure extending submodules which satisfy
  `Submodule.IsHomogeneous`.

## Implementation notes

The **notion** of homogeneous submodule does not rely on a graded ring, only a decomposition of the
module. However, most interesting properties of homogeneous submodules do rely on the base ring
being a graded ring. For technical reasons, we make `HomogeneousSubmodule` depend on a graded ring.
For example, if the definition of a homogeneous submodule does not depend on a graded ring, the
instance that `HomogeneousSubmodule` is a complete lattice cannot be synthesized due to
synthesization order.

## Tags

graded algebra, homogeneous
-/

@[expose] public section

open SetLike DirectSum Pointwise Set

variable {ιA ιM σA σM A M : Type*}

variable [Semiring A] [AddCommMonoid M] [Module A M]

section HomogeneousDef

/--
Definition of `Submodule.IsHomogeneous` / `Submodule.IsHomogeneous` 的定义

English:
definition Submodule.IsHomogeneous
  signature: (p : Submodule A M) (ℳ : ιM -> σM)
  body: SetLike.IsHomogeneous ℳ p

中文:
定义 Submodule.IsHomogeneous
  签名: (p : Submodule A M) (ℳ : ιM -> σM)
  定义体: SetLike.IsHomogeneous ℳ p

Depends on / 依赖: IsHomogeneous, SetLike, SetLike.IsHomogeneous
-/
def Submodule.IsHomogeneous (p : Submodule A M) (ℳ : ιM -> σM)
    [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ] : Prop :=
  SetLike.IsHomogeneous ℳ p

/--
theorem `Submodule.IsHomogeneous.mem_iff` / 定理 `Submodule.IsHomogeneous.mem_iff`

English:
theorem Submodule.IsHomogeneous.mem_iff
  statement: {p : Submodule A M}
  proof: AddSubmonoidClass.IsHomogeneous.mem_iff ℳ _ hp

中文:
定理 Submodule.IsHomogeneous.mem_iff
  结论: {p : Submodule A M}
  证明: AddSubmonoidClass.IsHomogeneous.mem_iff ℳ _ hp

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.IsHomogeneous.mem_iff, IsHomogeneous, mem_iff
-/
theorem Submodule.IsHomogeneous.mem_iff {p : Submodule A M}
    (ℳ : ιM -> σM)
    [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
    (hp : p.IsHomogeneous ℳ) {x} :
    x in p ↔ forall i, (decompose ℳ x i : M) in p :=
  AddSubmonoidClass.IsHomogeneous.mem_iff ℳ _ hp

/--
Definition of `HomogeneousSubmodule` / `HomogeneousSubmodule` 的定义

English:
structure HomogeneousSubmodule
  parameters: (𝒜 : ιA -> σA) (ℳ : ιM -> σM)
  extends: Submodule A M
  axioms and operations (1):
    - is_homogeneous' : toSubmodule.IsHomogeneous ℳ

中文:
结构 HomogeneousSubmodule
  参数: (𝒜 : ιA -> σA) (ℳ : ιM -> σM)
  继承: Submodule A M
  公理与运算 (1 个):
    - is_homogeneous' : toSubmodule.IsHomogeneous ℳ
-/
structure HomogeneousSubmodule (𝒜 : ιA -> σA) (ℳ : ιM -> σM)
    [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
    [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
    [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]
    extends Submodule A M where
  is_homogeneous' : toSubmodule.IsHomogeneous ℳ

variable (𝒜 : ιA -> σA) (ℳ : ιM -> σM)
variable [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
variable [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (HomogeneousSubmodule 𝒜 ℳ) M
  body: X.toSubmodule
  coe_injective := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ (h : (p : Set M) = q)
    simpa using h

中文:
实例 :
  签名: SetLike (HomogeneousSubmodule 𝒜 ℳ) M
  定义体: X.toSubmodule
  coe_injective := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ (h : (p : Set M) = q)
    simpa using h

Depends on / 依赖: X.toSubmodule, toSubmodule
-/
instance : SetLike (HomogeneousSubmodule 𝒜 ℳ) M where
  coe X := X.toSubmodule
  coe_injective := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ (h : (p : Set M) = q)
    simpa using h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (HomogeneousSubmodule 𝒜 ℳ)
  body: .ofSetLike (HomogeneousSubmodule 𝒜 ℳ) M

中文:
实例 :
  签名: PartialOrder (HomogeneousSubmodule 𝒜 ℳ)
  定义体: .ofSetLike (HomogeneousSubmodule 𝒜 ℳ) M

Depends on / 依赖: HomogeneousSubmodule, ofSetLike
-/
instance : PartialOrder (HomogeneousSubmodule 𝒜 ℳ) := .ofSetLike (HomogeneousSubmodule 𝒜 ℳ) M

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddSubmonoidClass (HomogeneousSubmodule 𝒜 ℳ) M
  body: p.toSubmodule.zero_mem
  add_mem hx hy := Submodule.add_mem _ hx hy

中文:
实例 :
  签名: AddSubmonoidClass (HomogeneousSubmodule 𝒜 ℳ) M
  定义体: p.toSubmodule.zero_mem
  add_mem hx hy := Submodule.add_mem _ hx hy

Depends on / 依赖: p.toSubmodule.zero_mem, toSubmodule, zero_mem
-/
instance : AddSubmonoidClass (HomogeneousSubmodule 𝒜 ℳ) M where
  zero_mem p := p.toSubmodule.zero_mem
  add_mem hx hy := Submodule.add_mem _ hx hy

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulMemClass (HomogeneousSubmodule 𝒜 ℳ) A M
  body: by
    intro x r m hm
    exact Submodule.smul_mem x.toSubmodule r hm

中文:
实例 :
  签名: SMulMemClass (HomogeneousSubmodule 𝒜 ℳ) A M
  定义体: by
    intro x r m hm
    exact Submodule.smul_mem x.toSubmodule r hm

Depends on / 依赖: Submodule, Submodule.smul_mem, smul_mem, toSubmodule, x.toSubmodule
-/
instance : SMulMemClass (HomogeneousSubmodule 𝒜 ℳ) A M where
  smul_mem := by
    intro x r m hm
    exact Submodule.smul_mem x.toSubmodule r hm

variable {𝒜 ℳ} in
/--
theorem `HomogeneousSubmodule.isHomogeneous` / 定理 `HomogeneousSubmodule.isHomogeneous`

English:
theorem HomogeneousSubmodule.isHomogeneous
  given: (p : HomogeneousSubmodule 𝒜 ℳ)
  proof: p.is_homogeneous'

中文:
定理 HomogeneousSubmodule.isHomogeneous
  条件: (p : HomogeneousSubmodule 𝒜 ℳ)
  证明: p.is_homogeneous'

Depends on / 依赖: is_homogeneous, p.is_homogeneous
-/
theorem HomogeneousSubmodule.isHomogeneous (p : HomogeneousSubmodule 𝒜 ℳ) :
    p.toSubmodule.IsHomogeneous ℳ :=
  p.is_homogeneous'

/--
theorem `HomogeneousSubmodule.toSubmodule_injective` / 定理 `HomogeneousSubmodule.toSubmodule_injective`

English:
theorem HomogeneousSubmodule.toSubmodule_injective
  proof: fun ⟨x, hx⟩ ⟨y, hy⟩ => fun (h : x = y) => by simp [h]

中文:
定理 HomogeneousSubmodule.toSubmodule_injective
  证明: fun ⟨x, hx⟩ ⟨y, hy⟩ => fun (h : x = y) => by simp [h]
-/
theorem HomogeneousSubmodule.toSubmodule_injective :
    Function.Injective
      (HomogeneousSubmodule.toSubmodule : HomogeneousSubmodule 𝒜 ℳ -> Submodule A M) :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ => fun (h : x = y) => by simp [h]

/--
Instance `HomogeneousSubmodule.setLike` / 实例 `HomogeneousSubmodule.setLike`

English:
instance HomogeneousSubmodule.setLike
  signature: : SetLike (HomogeneousSubmodule 𝒜 ℳ) M where
  body: p.toSubmodule
coe_injective _ _ h := HomogeneousSubmodule.toSubmodule_injective 𝒜 ℳ SetLike.coe_injective h

中文:
实例 HomogeneousSubmodule.setLike
  签名: : SetLike (HomogeneousSubmodule 𝒜 ℳ) M where
  定义体: p.toSubmodule
coe_injective _ _ h := HomogeneousSubmodule.toSubmodule_injective 𝒜 ℳ SetLike.coe_injective h

Depends on / 依赖: p.toSubmodule, toSubmodule
-/
instance HomogeneousSubmodule.setLike : SetLike (HomogeneousSubmodule 𝒜 ℳ) M where
  coe p := p.toSubmodule
coe_injective _ _ h := HomogeneousSubmodule.toSubmodule_injective 𝒜 ℳ SetLike.coe_injective h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (HomogeneousSubmodule 𝒜 ℳ)
  body: .ofSetLike (HomogeneousSubmodule 𝒜 ℳ) M

@[ext]

中文:
实例 :
  签名: PartialOrder (HomogeneousSubmodule 𝒜 ℳ)
  定义体: .ofSetLike (HomogeneousSubmodule 𝒜 ℳ) M

@[ext]

Depends on / 依赖: HomogeneousSubmodule, ofSetLike
-/
instance : PartialOrder (HomogeneousSubmodule 𝒜 ℳ) := .ofSetLike (HomogeneousSubmodule 𝒜 ℳ) M

@[ext]
/--
theorem `HomogeneousSubmodule.ext` / 定理 `HomogeneousSubmodule.ext`

English:
theorem HomogeneousSubmodule.ext
  proof: HomogeneousSubmodule.toSubmodule_injective _ _ h

中文:
定理 HomogeneousSubmodule.ext
  证明: HomogeneousSubmodule.toSubmodule_injective _ _ h

Depends on / 依赖: HomogeneousSubmodule, HomogeneousSubmodule.toSubmodule_injective, toSubmodule_injective
-/
theorem HomogeneousSubmodule.ext
    {I J : HomogeneousSubmodule 𝒜 ℳ} (h : I.toSubmodule = J.toSubmodule) : I = J :=
  HomogeneousSubmodule.toSubmodule_injective _ _ h

/--
theorem `HomogeneousSubmodule.ext'` / 定理 `HomogeneousSubmodule.ext'`

English:
theorem HomogeneousSubmodule.ext'
  statement: {I J : HomogeneousSubmodule 𝒜 ℳ}
  proof: by
  ext
  rw [I.isHomogeneous.mem_iff]; rw [J.isHomogeneous.mem_iff]
  apply forall_congr'
  exact fun i => h i _ (decompose ℳ _ i).2

@[simp]

中文:
定理 HomogeneousSubmodule.ext'
  结论: {I J : HomogeneousSubmodule 𝒜 ℳ}
  证明: by
  ext
  rw [I.isHomogeneous.mem_iff]; rw [J.isHomogeneous.mem_iff]
  apply forall_congr'
  exact fun i => h i _ (decompose ℳ _ i).2

@[simp]

Depends on / 依赖: I.isHomogeneous.mem_iff, J.isHomogeneous.mem_iff, decompose, forall_congr, isHomogeneous, mem_iff
-/
theorem HomogeneousSubmodule.ext' {I J : HomogeneousSubmodule 𝒜 ℳ}
    (h : forall i, forall x in ℳ i, x in I ↔ x in J) :
    I = J := by
  ext
  rw [I.isHomogeneous.mem_iff]; rw [J.isHomogeneous.mem_iff]
  apply forall_congr'
  exact fun i => h i _ (decompose ℳ _ i).2

@[simp]
/--
theorem `HomogeneousSubmodule.mem_toSubmodule_iff` / 定理 `HomogeneousSubmodule.mem_toSubmodule_iff`

English:
theorem HomogeneousSubmodule.mem_toSubmodule_iff
  given: {I : HomogeneousSubmodule 𝒜 ℳ} {x : M}
  proof: Iff.rfl

中文:
定理 HomogeneousSubmodule.mem_toSubmodule_iff
  条件: {I : HomogeneousSubmodule 𝒜 ℳ} {x : M}
  证明: Iff.rfl
-/
theorem HomogeneousSubmodule.mem_toSubmodule_iff {I : HomogeneousSubmodule 𝒜 ℳ} {x : M} :
    x in I.toSubmodule (A := A) ↔ x in I :=
  Iff.rfl

end HomogeneousDef
