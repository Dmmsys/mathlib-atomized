/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Ring.TransferInstance

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

@[expose] public section

universe v
variable {R α β : Type*} [CommSemiring R]

namespace Equiv
variable (e : α ≃ β)

-- See note [instance transfer via equivalence]
variable (R) in
/-- Transfer `Algebra` across an `Equiv` -/
/-
**Equiv.algebra** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：(R : Type u_1) →   {α : Type u_2} →     {β : Type u_3} →       [inst : Com
mSemiring R] →         (e : α ≃ β) →           [inst_1 : Semiring β] →          
   have x := e.semiring;             [Algebra R β] → Algebra R α
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `Algebra` across an `Equiv`
-/
protected abbrev algebra (e : α ≃ β) [Semiring β] :
    let _ := Equiv.semiring e
    ∀ [Algebra R β], Algebra R α := fast_instance%
  letI := Equiv.semiring e
  letI := e.smul R
  { algebraMap :=
    { toFun r := e.invFun (algebraMap R β r)
      __ := e.ringEquiv.symm.toRingHom.comp (algebraMap R β) }
    commutes' r x :=
      show e.symm ((e (e.symm (algebraMap R β r)) * e x)) =
          e.symm (e x * e (e.symm (algebraMap R β r))) by
        simp [Algebra.commutes]
    smul_def' r x :=
      show e.symm (r • e x) = e.symm (e (e.symm (algebraMap R β r)) * e x) by
        simp [Algebra.smul_def] }
/-
**Equiv.algebraMap_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：algebraMap_def (e : α ≃ β) [Semiring β] [Algebra R β] (r : R) : letI
参数：e : α ≃ β；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma algebraMap_def (e : α ≃ β) [Semiring β] [Algebra R β] (r : R) :
    letI := Equiv.semiring e
    letI := Equiv.algebra R e
    algebraMap R α r = e.symm (algebraMap R β r) := rfl

variable (R) in
/-- An equivalence `e : α ≃ β` gives an algebra equivalence `α ≃ₐ[R] β`
where the `R`-algebra structure on `α` is
the one obtained by transporting an `R`-algebra structure on `β` back along `e`. -/
/-
**Equiv.algEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：algEquiv (e : α ≃ β) [Semiring β] [Algebra R β] : by let semiring
参数：e : α ≃ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence `e : α ≃ β` gives an algebra equivalence `α ≃ₐ[R] β`
where the `R`-algebra structure on `α` is
the one obtained by transporting an `R`-algebra structure on `β` back along `e`.
-/
def algEquiv (e : α ≃ β) [Semiring β] [Algebra R β] : by
    let semiring := Equiv.semiring e
    let algebra := Equiv.algebra R e
    exact α ≃ₐ[R] β := by
  intros
  exact
    { Equiv.ringEquiv e with
      commutes' := fun r => by
        apply e.symm.injective
        simp only [RingEquiv.toEquiv_eq_coe, toFun_as_coe, EquivLike.coe_coe, ringEquiv_apply,
          symm_apply_apply, algebraMap_def] }

@[simp]
/-
**Equiv.algEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：algEquiv_apply (e : α ≃ β) [Semiring β] [Algebra R β] (a : α) : (algEquiv 
R e) a = e a
参数：e : α ≃ β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algEquiv_apply (e : α ≃ β) [Semiring β] [Algebra R β] (a : α) : (algEquiv R e) a = e a :=
  rfl
/-
**Equiv.algEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：algEquiv_symm_apply (e : α ≃ β) [Semiring β] [Algebra R β] (b : β) : by le
tI
参数：e : α ≃ β；b : β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algEquiv_symm_apply (e : α ≃ β) [Semiring β] [Algebra R β] (b : β) : by
    letI := Equiv.semiring e
    letI := Equiv.algebra R e
    exact (algEquiv R e).symm b = e.symm b := rfl

end Equiv

