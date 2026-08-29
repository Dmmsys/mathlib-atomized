/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.TransferInstance
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

@[expose] public section

assert_not_exists Algebra

universe u v
variable {R α β : Type*} [Semiring R]

namespace Equiv
variable (e : α ≃ β)

variable (R : Type*) [Zero R] in
/--
lemma `noZeroSMulDivisors` / 引理 `noZeroSMulDivisors`

English:
lemma noZeroSMulDivisors
  given: [Zero β] [SMul R β] [NoZeroSMulDivisors R β]
  proof: e.zero
    let := e.smul R
    NoZeroSMulDivisors R α := by
  extract_lets
  refine ⟨fun {r} m => ?_⟩
  simpa [smul_def, zero_def, Equiv.eq_symm_apply] using eq_zero_or_eq_zero_of_smul_eq_zero

中文:
引理 noZeroSMulDivisors
  条件: [零 β] [标量乘法 R β] [无零标量乘因子 R β]
  证明: e.zero
    let := e.smul R
    NoZeroSMulDivisors R α := by
  extract_lets
  refine ⟨fun {r} m => ?_⟩
  simpa [smul_def, zero_def, Equiv.eq_symm_apply] using eq_zero_or_eq_zero_of_smul_eq_zero
-/
protected lemma noZeroSMulDivisors [Zero β] [SMul R β] [NoZeroSMulDivisors R β] :
    let := e.zero
    let := e.smul R
    NoZeroSMulDivisors R α := by
  extract_lets
  refine ⟨fun {r} m => ?_⟩
  simpa [smul_def, zero_def, Equiv.eq_symm_apply] using eq_zero_or_eq_zero_of_smul_eq_zero

variable (R) in
/--
Definition of `module` / `module` 的定义

English:
abbreviation module
  signature: (e : α ≃ β) [AddCommMonoid β] [Module R β]
  body: Equiv.addCommMonoid e
    Module R α :=
  letI := Equiv.addCommMonoid e
  { Equiv.distribMulAction R e with
    zero_smul := by simp [smul_def, zero_smul, zero_def]
    add_smul := by simp [add_def, smul_def, add_smul] }

中文:
缩写 module
  签名: (e : α ≃ β) [加法交换幺半群 β] [模 R β]
  定义体: Equiv.addCommMonoid e
    Module R α :=
  letI := Equiv.addCommMonoid e
  { Equiv.distribMulAction R e with
    zero_smul := by simp [smul_def, zero_smul, zero_def]
    add_smul := by simp [add_def, smul_def, add_smul] }
-/
protected abbrev module (e : α ≃ β) [AddCommMonoid β] [Module R β] :
    letI := Equiv.addCommMonoid e
    Module R α :=
  letI := Equiv.addCommMonoid e
  { Equiv.distribMulAction R e with
    zero_smul := by simp [smul_def, zero_smul, zero_def]
    add_smul := by simp [add_def, smul_def, add_smul] }

variable (R) in
/--
Definition of `linearEquiv` / `linearEquiv` 的定义

English:
definition linearEquiv
  signature: (e : α ≃ β) [AddCommMonoid β] [Module R β]
  body: Equiv.addCommMonoid e
    letI := Equiv.module R e
    α ≃ₗ[R] β :=
  letI := Equiv.addCommMonoid e
  letI module := Equiv.module R e
  { Equiv.addEquiv e with
    map_smul' := fun r x => by
      apply e.symm.injective
      simp only [toFun_as_coe, RingHom.id_apply, EmbeddingLike.apply_eq_iff_eq]
      exact Iff.mp (eq_symm_apply _) rfl }

@[simp]

中文:
定义 linearEquiv
  签名: (e : α ≃ β) [加法交换幺半群 β] [模 R β]
  定义体: Equiv.addCommMonoid e
    letI := Equiv.module R e
    α ≃ₗ[R] β :=
  letI := Equiv.addCommMonoid e
  letI module := Equiv.module R e
  { Equiv.addEquiv e with
    map_smul' := fun r x => by
      apply e.symm.injective
      simp only [toFun_as_coe, RingHom.id_apply, EmbeddingLike.apply_eq_iff_eq]
      exact Iff.mp (eq_symm_apply _) rfl }

@[simp]

Depends on / 依赖: Equiv.addCommMonoid, addCommMonoid
-/
def linearEquiv (e : α ≃ β) [AddCommMonoid β] [Module R β] :
    letI := Equiv.addCommMonoid e
    letI := Equiv.module R e
    α ≃ₗ[R] β :=
  letI := Equiv.addCommMonoid e
  letI module := Equiv.module R e
  { Equiv.addEquiv e with
    map_smul' := fun r x => by
      apply e.symm.injective
      simp only [toFun_as_coe, RingHom.id_apply, EmbeddingLike.apply_eq_iff_eq]
      exact Iff.mp (eq_symm_apply _) rfl }

@[simp]
/--
lemma `linearEquiv_apply` / 引理 `linearEquiv_apply`

English:
lemma linearEquiv_apply
  given: (a : α) [AddCommMonoid β] [Module R β]
  proof: rfl

@[simp]

中文:
引理 linearEquiv_apply
  条件: (a : α) [加法交换幺半群 β] [模 R β]
  证明: rfl

@[simp]
-/
lemma linearEquiv_apply (a : α) [AddCommMonoid β] [Module R β] :
    e.linearEquiv R a = e a := rfl

@[simp]
/--
lemma `linearEquiv_symm_apply` / 引理 `linearEquiv_symm_apply`

English:
lemma linearEquiv_symm_apply
  given: (b : β) [AddCommMonoid β] [Module R β]
  proof: Equiv.addCommMonoid e
    letI := Equiv.module R e
    (e.linearEquiv R).symm b = e.symm b := rfl

中文:
引理 linearEquiv_symm_apply
  条件: (b : β) [加法交换幺半群 β] [模 R β]
  证明: Equiv.addCommMonoid e
    letI := Equiv.module R e
    (e.linearEquiv R).symm b = e.symm b := rfl

Depends on / 依赖: Equiv.addCommMonoid, addCommMonoid
-/
lemma linearEquiv_symm_apply (b : β) [AddCommMonoid β] [Module R β] :
    letI := Equiv.addCommMonoid e
    letI := Equiv.module R e
    (e.linearEquiv R).symm b = e.symm b := rfl

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/--
lemma `moduleIsTorsionFree` / 引理 `moduleIsTorsionFree`

English:
lemma moduleIsTorsionFree
  statement: (e : α ≃ β) [AddCommMonoid β] [Module R β]
  proof: e.addCommMonoid
    let := e.module R
    Module.IsTorsionFree R α := by
  extract_lets; exact (e.linearEquiv R).injective.moduleIsTorsionFree _ (by simp)

中文:
引理 moduleIsTorsionFree
  结论: (e : α ≃ β) [加法交换幺半群 β] [模 R β]
  证明: e.addCommMonoid
    let := e.module R
    Module.IsTorsionFree R α := by
  extract_lets; exact (e.linearEquiv R).injective.moduleIsTorsionFree _ (by simp)
-/
protected lemma moduleIsTorsionFree (e : α ≃ β) [AddCommMonoid β] [Module R β]
    [Module.IsTorsionFree R β] :
    let := e.addCommMonoid
    let := e.module R
    Module.IsTorsionFree R α := by
  extract_lets; exact (e.linearEquiv R).injective.moduleIsTorsionFree _ (by simp)

end Equiv

variable (A) [Semiring A] [Module R A] [AddCommMonoid α] [AddCommMonoid β] [Module A β]

/--
Definition of `AddEquiv.module` / `AddEquiv.module` 的定义

English:
abbreviation AddEquiv.module
  signature: (e : α ≃+ β)
  body: e.toEquiv.smul A
  one_smul := by simp [Equiv.smul_def]
  mul_smul := by simp [Equiv.smul_def, mul_smul]
  smul_zero := by simp [Equiv.smul_def]
  smul_add := by simp [Equiv.smul_def]
  add_smul := by simp [Equiv.smul_def, add_smul]
  zero_smul := by simp [Equiv.smul_def]

中文:
缩写 加法等价.module
  签名: (e : α ≃+ β)
  定义体: e.toEquiv.smul A
  one_smul := by simp [Equiv.smul_def]
  mul_smul := by simp [Equiv.smul_def, mul_smul]
  smul_zero := by simp [Equiv.smul_def]
  smul_add := by simp [Equiv.smul_def]
  add_smul := by simp [Equiv.smul_def, add_smul]
  zero_smul := by simp [Equiv.smul_def]

Depends on / 依赖: e.toEquiv.smul, toEquiv
-/
abbrev AddEquiv.module (e : α ≃+ β) : Module A α where
  toSMul := e.toEquiv.smul A
  one_smul := by simp [Equiv.smul_def]
  mul_smul := by simp [Equiv.smul_def, mul_smul]
  smul_zero := by simp [Equiv.smul_def]
  smul_add := by simp [Equiv.smul_def]
  add_smul := by simp [Equiv.smul_def, add_smul]
  zero_smul := by simp [Equiv.smul_def]

/--
lemma `LinearEquiv.isScalarTower` / 引理 `LinearEquiv.isScalarTower`

English:
lemma LinearEquiv.isScalarTower
  statement: [Module R α] [Module R β] [IsScalarTower R A β]
  proof: e.toAddEquiv.module A
    IsScalarTower R A α := by
  let := e.toAddEquiv.module A
  constructor
  intro x y z
  simp only [Equiv.smul_def, smul_assoc]
  apply e.symm.map_smul

中文:
引理 线性等价.isScalarTower
  结论: [模 R α] [模 R β] [标量塔 R A β]
  证明: e.toAddEquiv.module A
    IsScalarTower R A α := by
  let := e.toAddEquiv.module A
  constructor
  intro x y z
  simp only [Equiv.smul_def, smul_assoc]
  apply e.symm.map_smul

Depends on / 依赖: e.toAddEquiv.module, module, toAddEquiv
-/
lemma LinearEquiv.isScalarTower [Module R α] [Module R β] [IsScalarTower R A β]
    (e : α ≃ₗ[R] β) :
    letI := e.toAddEquiv.module A
    IsScalarTower R A α := by
  let := e.toAddEquiv.module A
  constructor
  intro x y z
  simp only [Equiv.smul_def, smul_assoc]
  apply e.symm.map_smul

/-- When `α` is equipped with the `A`-module structure transferred via `e : α ≃+ β`,
this isomorphism is `A`-linear. -/
@[simps]
/--
Definition of `AddEquiv.linearEquiv` / `AddEquiv.linearEquiv` 的定义

English:
definition AddEquiv.linearEquiv
  signature: (e : α ≃+ β)
  body: e.module A
    α ≃ₗ[A] β :=
  letI := e.module A
  { __ := e
    map_smul' _ _ := e.apply_symm_apply _ }

中文:
定义 加法等价.linearEquiv
  签名: (e : α ≃+ β)
  定义体: e.module A
    α ≃ₗ[A] β :=
  letI := e.module A
  { __ := e
    map_smul' _ _ := e.apply_symm_apply _ }

Depends on / 依赖: e.module, module
-/
def AddEquiv.linearEquiv (e : α ≃+ β) :
    letI := e.module A
    α ≃ₗ[A] β :=
  letI := e.module A
  { __ := e
    map_smul' _ _ := e.apply_symm_apply _ }
