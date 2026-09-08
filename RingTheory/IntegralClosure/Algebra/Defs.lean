/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
# Integral algebras

## Main definitions

Let `R` be a `CommRing` and let `A` be an R-algebra.

* `Algebra.IsIntegral R A` : An algebra is integral if every element of the extension is integral
  over the base ring.
-/

public section


open Polynomial Submodule

section Ring

variable {R S A : Type*}
variable [CommRing R] [Ring A] [Ring S] (f : R →+* S)

variable [Algebra R A] (R)

variable (A)

/-- An algebra is integral if every element of the extension is integral over the base ring. -/
/-
**Algebra.IsIntegral** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u_1) → (A : Type u_3) → [inst : CommRing R] → [inst_1 : Ring A] 
→ [Algebra R A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An algebra is integral if every element of the extension is integral over the ba
se ring.
-/
@[mk_iff] protected class Algebra.IsIntegral : Prop where
  isIntegral : ∀ x : A, IsIntegral R x

variable {R A}
/-
**Algebra.isIntegral_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.isIntegral_def : Algebra.IsIntegral R A ↔ forall x : A, IsIntegral
 R x
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Algebra.isIntegral_def : Algebra.IsIntegral R A ↔ ∀ x : A, IsIntegral R x :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩
/-
**algebraMap_isIntegral_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：algebraMap_isIntegral_iff : (algebraMap R A).IsIntegral ↔ Algebra.IsIntegr
al R A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Algebra.isIntegral_iff`：∀ (R : Type u_1) (A : Type u_3) [inst : CommRing
 R] [inst_1 : Ring A] [inst_2 : Algebra R A],   Algebra.IsIntegral R A ↔ ∀ (x : 
A), IsIntegr…
-/
lemma algebraMap_isIntegral_iff : (algebraMap R A).IsIntegral ↔ Algebra.IsIntegral R A :=
  (Algebra.isIntegral_iff ..).symm

end Ring

