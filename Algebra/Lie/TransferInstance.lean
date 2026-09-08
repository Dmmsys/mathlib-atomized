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

/-- Transfer `LieRing` across an `AddEquiv` -/
/-
**AddEquiv.lieRing** 是 Mathlib 中的一个定义，位于命名空间 `AddEquiv`。
形式化陈述：{M : Type u_2} → {L : Type u_3} → [inst : AddCommGroup M] → [inst_1 : LieR
ing L] → M ≃+ L → LieRing M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `LieRing` across an `AddEquiv`
-/
protected abbrev AddEquiv.lieRing (e : M ≃+ L) : LieRing M where
  bracket x y := e.symm ⁅e x, e y⁆
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp
/-
**AddEquiv.bracket_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AddEquiv.bracket_def (e : M ≃+ L) (x y : M) : letI
参数：e : M ≃+ L；x y : M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma AddEquiv.bracket_def (e : M ≃+ L) (x y : M) :
    letI := e.lieRing
    ⁅x, y⁆ = e.symm ⁅e x, e y⁆ := rfl

/-- Transfer `LieAlgebra` across a `LinearEquiv` -/
/-
**LinearEquiv.lieAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     {L : Type u_3} →       [inst : Com
mRing R] →         [inst_1 : AddCommGroup M] →           [inst_2 : _root_.Module
 R M] →             [inst_3 : LieRing L] → [inst_4 : LieAlgebra R L] → (e : M ≃ₗ
[R] L) → LieAlgebra R M
参数：e : M ≃ₗ[R] L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `LieAlgebra` across a `LinearEquiv`
-/
protected abbrev LinearEquiv.lieAlgebra (e : M ≃ₗ[R] L) :
    letI := e.toAddEquiv.lieRing
    LieAlgebra R M :=
  letI := e.toAddEquiv.lieRing
  { lie_smul _ _ _ := by simp [AddEquiv.bracket_def] }

variable (R) in
/-- An equivalence `e : M ≃ₗ[R] L` gives a Lie algebra equivalence `M ≃ₗ⁅R⁆ L` where the Lie bracket
on `M` is the one obtained by transporting a Lie Bracket on `L` back along `e`. -/
/-
**LinearEquiv.lieEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearEquiv.lieEquiv (e : M ≃ₗ[R] L) : letI
参数：e : M ≃ₗ[R] L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence `e : M ≃ₗ[R] L` gives a Lie algebra equivalence `M ≃ₗ⁅R⁆ L` where
 the Lie bracket
on `M` is the one obtained by transporting a Lie Bracket on `L` back along `e`.
-/
def LinearEquiv.lieEquiv (e : M ≃ₗ[R] L) :
    letI := e.toAddEquiv.lieRing
    letI := e.lieAlgebra
    M ≃ₗ⁅R⁆ L :=
  letI := e.toAddEquiv.lieRing
  letI := e.lieAlgebra
  { e with map_lie' := by simp [AddEquiv.bracket_def] }

@[simp]
/-
**LinearEquiv.lieEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearEquiv.lieEquiv_apply (e : M ≃ₗ[R] L) (a : M) : e.lieEquiv R a = e a
参数：e : M ≃ₗ[R] L；a : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LinearEquiv.lieEquiv_apply (e : M ≃ₗ[R] L) (a : M) :
    e.lieEquiv R a = e a := rfl

@[simp]
/-
**LinearEquiv.lieEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearEquiv.lieEquiv_symm_apply (e : M ≃ₗ[R] L) (b : L) : letI
参数：e : M ≃ₗ[R] L；b : L。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LinearEquiv.lieEquiv_symm_apply (e : M ≃ₗ[R] L) (b : L) :
    letI := e.toAddEquiv.lieRing
    letI := e.lieAlgebra
    (e.lieEquiv R).symm b = e.symm b := rfl

end

namespace Equiv

variable {R L' L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (e : L' ≃ L)

/-- Transfer `LieRing` across an `Equiv` -/
/-
**Equiv.lieRing** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{L' : Type u_2} → {L : Type u_3} → [LieRing L] → L' ≃ L → LieRing L'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `LieRing` across an `Equiv`
-/
protected abbrev lieRing : LieRing L' :=
  letI := e.addCommGroup
  e.addEquiv.lieRing
/-
**Equiv.bracket_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：bracket_def (x y : L') : letI
参数：x y : L'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma bracket_def (x y : L') :
    letI := e.lieRing
    ⁅x, y⁆ = e.symm ⁅e x, e y⁆ := rfl

variable (R) in
/-- Transfer `LieAlgebra` across an `Equiv` -/
/-
**Equiv.lieAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：(R : Type u_1) →   {L' : Type u_2} →     {L : Type u_3} → [inst : CommRing
 R] → [inst_1 : LieRing L] → [LieAlgebra R L] → (e : L' ≃ L) → LieAlgebra R L'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `LieAlgebra` across an `Equiv`
-/
protected abbrev lieAlgebra :
    letI := e.lieRing
    LieAlgebra R L' :=
  letI := e.lieRing
  letI := e.module R
  { lie_smul _ _ _ := by simp [Equiv.smul_def, AddEquiv.bracket_def] }

variable (R) in
/-- An equivalence `e : L' ≃ L` gives a Lie algebra equivalence `L' ≃ₗ⁅R⁆ L` where the algebraic
structures on `L'` are obtained by transporting the structures on `L` back along `e`. -/
/-
**Equiv.lieEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：lieEquiv : letI
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence `e : L' ≃ L` gives a Lie algebra equivalence `L' ≃ₗ⁅R⁆ L` where t
he algebraic
structures on `L'` are obtained by transporting the structures on `L` back along
 `e`.
-/
def lieEquiv :
    letI := e.lieRing
    letI := e.lieAlgebra R
    L' ≃ₗ⁅R⁆ L :=
  letI := e.lieRing
  letI := e.lieAlgebra R
  { e.linearEquiv R with map_lie' {x y} := by simp [AddEquiv.bracket_def] }
/-
**Equiv.lieEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {R : Type u_1} {L' : Type u_2} {L : Type u_3} [inst : CommRing R] [inst_
1 : LieRing L] [inst_2 : LieAlgebra R L]   (e : L' ≃ L) (a : L'), (Equiv.lieEqui
v R e) a = e a
参数：e : L' ≃ L；a : L'；Equiv.lieEquiv R e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lieEquiv_apply (a : L') : e.lieEquiv R a = e a := rfl
/-
**Equiv.lieEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {R : Type u_1} {L' : Type u_2} {L : Type u_3} [inst : CommRing R] [inst_
1 : LieRing L] [inst_2 : LieAlgebra R L]   (e : L' ≃ L) (b : L), (Equiv.lieEquiv
 R e).symm b = e.symm b
参数：e : L' ≃ L；b : L；Equiv.lieEquiv R e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lieEquiv_symm_apply (b : L) :
    letI := e.lieRing
    letI := e.lieAlgebra R
    (e.lieEquiv R).symm b = e.symm b := rfl

end Equiv

