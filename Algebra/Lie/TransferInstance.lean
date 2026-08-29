/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
-/

module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Transfer Lie brackets along AddEquiv, LinearEquiv and Equiv

Main definitions:
* `AddEquiv.lieRing` transferring a LieRing structure along an additive equivalence.
* `LinearEquiv.lieAlgebra` transferring a Lie algebra structure along a linear equivalence.
* `Equiv.lieRing` transferring a LieRing structure along an equivalence (transfers the additive
  structure using `Equiv.addCommGroup` and then the bracket using `AddEquiv.lieRing`)
* `Equiv.lieAlgebra` transferring a Lie algebra structure along an equivalence

-/

@[expose] public section

section

variable {R M L : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LieRing L] [LieAlgebra R L]

/--
Definition of `AddEquiv.lieRing` / `AddEquiv.lieRing` 的定义

English:
abbreviation AddEquiv.lieRing
  signature: (e : M ≃+ L)
  body: e.symm ⁅e x, e y⁆
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp

中文:
缩写 加法等价.lieRing
  签名: (e : M ≃+ L)
  定义体: e.symm ⁅e x, e y⁆
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp
-/
protected abbrev AddEquiv.lieRing (e : M ≃+ L) : LieRing M where
  bracket x y := e.symm ⁅e x, e y⁆
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp

/--
lemma `AddEquiv.bracket_def` / 引理 `AddEquiv.bracket_def`

English:
lemma AddEquiv.bracket_def
  given: (e : M ≃+ L) (x y : M)
  proof: e.lieRing
    ⁅x, y⁆ = e.symm ⁅e x, e y⁆ := rfl

中文:
引理 加法等价.bracket_def
  条件: (e : M ≃+ L) (x y : M)
  证明: e.lieRing
    ⁅x, y⁆ = e.symm ⁅e x, e y⁆ := rfl

Depends on / 依赖: e.lieRing, lieRing
-/
lemma AddEquiv.bracket_def (e : M ≃+ L) (x y : M) :
    letI := e.lieRing
    ⁅x, y⁆ = e.symm ⁅e x, e y⁆ := rfl

/--
Definition of `LinearEquiv.lieAlgebra` / `LinearEquiv.lieAlgebra` 的定义

English:
abbreviation LinearEquiv.lieAlgebra
  signature: (e : M ≃ₗ[R] L)
  body: e.toAddEquiv.lieRing
    LieAlgebra R M :=
  letI := e.toAddEquiv.lieRing
  { lie_smul _ _ _ := by simp [AddEquiv.bracket_def] }

中文:
缩写 线性等价.lieAlgebra
  签名: (e : M ≃ₗ[R] L)
  定义体: e.toAddEquiv.lieRing
    LieAlgebra R M :=
  letI := e.toAddEquiv.lieRing
  { lie_smul _ _ _ := by simp [AddEquiv.bracket_def] }
-/
protected abbrev LinearEquiv.lieAlgebra (e : M ≃ₗ[R] L) :
    letI := e.toAddEquiv.lieRing
    LieAlgebra R M :=
  letI := e.toAddEquiv.lieRing
  { lie_smul _ _ _ := by simp [AddEquiv.bracket_def] }

variable (R) in
/--
Definition of `LinearEquiv.lieEquiv` / `LinearEquiv.lieEquiv` 的定义

English:
definition LinearEquiv.lieEquiv
  signature: (e : M ≃ₗ[R] L)
  body: e.toAddEquiv.lieRing
    letI := e.lieAlgebra
    M ≃ₗ⁅R⁆ L :=
  letI := e.toAddEquiv.lieRing
  letI := e.lieAlgebra
  { e with map_lie' := by simp [AddEquiv.bracket_def] }

@[simp]

中文:
定义 线性等价.lieEquiv
  签名: (e : M ≃ₗ[R] L)
  定义体: e.toAddEquiv.lieRing
    letI := e.lieAlgebra
    M ≃ₗ⁅R⁆ L :=
  letI := e.toAddEquiv.lieRing
  letI := e.lieAlgebra
  { e with map_lie' := by simp [AddEquiv.bracket_def] }

@[simp]

Depends on / 依赖: e.toAddEquiv.lieRing, lieRing, toAddEquiv
-/
def LinearEquiv.lieEquiv (e : M ≃ₗ[R] L) :
    letI := e.toAddEquiv.lieRing
    letI := e.lieAlgebra
    M ≃ₗ⁅R⁆ L :=
  letI := e.toAddEquiv.lieRing
  letI := e.lieAlgebra
  { e with map_lie' := by simp [AddEquiv.bracket_def] }

@[simp]
/--
lemma `LinearEquiv.lieEquiv_apply` / 引理 `LinearEquiv.lieEquiv_apply`

English:
lemma LinearEquiv.lieEquiv_apply
  given: (e : M ≃ₗ[R] L) (a : M)
  proof: rfl

@[simp]

中文:
引理 线性等价.lieEquiv_apply
  条件: (e : M ≃ₗ[R] L) (a : M)
  证明: rfl

@[simp]
-/
lemma LinearEquiv.lieEquiv_apply (e : M ≃ₗ[R] L) (a : M) :
    e.lieEquiv R a = e a := rfl

@[simp]
/--
lemma `LinearEquiv.lieEquiv_symm_apply` / 引理 `LinearEquiv.lieEquiv_symm_apply`

English:
lemma LinearEquiv.lieEquiv_symm_apply
  given: (e : M ≃ₗ[R] L) (b : L)
  proof: e.toAddEquiv.lieRing
    letI := e.lieAlgebra
    (e.lieEquiv R).symm b = e.symm b := rfl

中文:
引理 线性等价.lieEquiv_symm_apply
  条件: (e : M ≃ₗ[R] L) (b : L)
  证明: e.toAddEquiv.lieRing
    letI := e.lieAlgebra
    (e.lieEquiv R).symm b = e.symm b := rfl

Depends on / 依赖: e.toAddEquiv.lieRing, lieRing, toAddEquiv
-/
lemma LinearEquiv.lieEquiv_symm_apply (e : M ≃ₗ[R] L) (b : L) :
    letI := e.toAddEquiv.lieRing
    letI := e.lieAlgebra
    (e.lieEquiv R).symm b = e.symm b := rfl

end

namespace Equiv

variable {R L' L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (e : L' ≃ L)

/--
Definition of `lieRing` / `lieRing` 的定义

English:
abbreviation lieRing
  signature: : LieRing L'
  body: letI := e.addCommGroup
  e.addEquiv.lieRing

中文:
缩写 lieRing
  签名: : Lie环 L'
  定义体: letI := e.addCommGroup
  e.addEquiv.lieRing
-/
protected abbrev lieRing : LieRing L' :=
  letI := e.addCommGroup
  e.addEquiv.lieRing

/--
lemma `bracket_def` / 引理 `bracket_def`

English:
lemma bracket_def
  given: (x y : L')
  proof: e.lieRing
    ⁅x, y⁆ = e.symm ⁅e x, e y⁆ := rfl

中文:
引理 bracket_def
  条件: (x y : L')
  证明: e.lieRing
    ⁅x, y⁆ = e.symm ⁅e x, e y⁆ := rfl

Depends on / 依赖: e.lieRing, lieRing
-/
lemma bracket_def (x y : L') :
    letI := e.lieRing
    ⁅x, y⁆ = e.symm ⁅e x, e y⁆ := rfl

variable (R) in
/--
Definition of `lieAlgebra` / `lieAlgebra` 的定义

English:
abbreviation lieAlgebra
  signature: :
  body: e.lieRing
    LieAlgebra R L' :=
  letI := e.lieRing
  letI := e.module R
  { lie_smul _ _ _ := by simp [Equiv.smul_def, AddEquiv.bracket_def] }

中文:
缩写 lieAlgebra
  签名: :
  定义体: e.lieRing
    LieAlgebra R L' :=
  letI := e.lieRing
  letI := e.module R
  { lie_smul _ _ _ := by simp [Equiv.smul_def, AddEquiv.bracket_def] }
-/
protected abbrev lieAlgebra :
    letI := e.lieRing
    LieAlgebra R L' :=
  letI := e.lieRing
  letI := e.module R
  { lie_smul _ _ _ := by simp [Equiv.smul_def, AddEquiv.bracket_def] }

variable (R) in
/--
Definition of `lieEquiv` / `lieEquiv` 的定义

English:
definition lieEquiv
  signature: :
  body: e.lieRing
    letI := e.lieAlgebra R
    L' ≃ₗ⁅R⁆ L :=
  letI := e.lieRing
  letI := e.lieAlgebra R
  { e.linearEquiv R with map_lie' {x y} := by simp [AddEquiv.bracket_def] }

中文:
定义 lieEquiv
  签名: :
  定义体: e.lieRing
    letI := e.lieAlgebra R
    L' ≃ₗ⁅R⁆ L :=
  letI := e.lieRing
  letI := e.lieAlgebra R
  { e.linearEquiv R with map_lie' {x y} := by simp [AddEquiv.bracket_def] }

Depends on / 依赖: e.lieRing, lieRing
-/
def lieEquiv :
    letI := e.lieRing
    letI := e.lieAlgebra R
    L' ≃ₗ⁅R⁆ L :=
  letI := e.lieRing
  letI := e.lieAlgebra R
  { e.linearEquiv R with map_lie' {x y} := by simp [AddEquiv.bracket_def] }

/--
lemma `lieEquiv_apply` / 引理 `lieEquiv_apply`

English:
lemma lieEquiv_apply
  given: (a : L')
  statement: e.lieEquiv R a = e a
  proof: rfl

中文:
引理 lieEquiv_apply
  条件: (a : L')
  结论: e.lieEquiv R a = e a
  证明: rfl
-/
@[simp] lemma lieEquiv_apply (a : L') : e.lieEquiv R a = e a := rfl

/--
lemma `lieEquiv_symm_apply` / 引理 `lieEquiv_symm_apply`

English:
lemma lieEquiv_symm_apply
  given: (b : L)
  proof: e.lieRing
    letI := e.lieAlgebra R
    (e.lieEquiv R).symm b = e.symm b := rfl

中文:
引理 lieEquiv_symm_apply
  条件: (b : L)
  证明: e.lieRing
    letI := e.lieAlgebra R
    (e.lieEquiv R).symm b = e.symm b := rfl
-/
@[simp] lemma lieEquiv_symm_apply (b : L) :
    letI := e.lieRing
    letI := e.lieAlgebra R
    (e.lieEquiv R).symm b = e.symm b := rfl

end Equiv
