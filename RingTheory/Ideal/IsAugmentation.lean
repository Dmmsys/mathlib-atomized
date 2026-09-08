/-
Copyright (c) 2026 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-! # Augmentation ideals

* `Ideal.IsAugmentation` :  An ideal `I` of an `A`-algebra `S` is an augmentation ideal
  if its underlying submodule is a complement of `1 : Submodule A S`.

* `Ideal.isAugmentation_subalgebra_iff` : If `S` is a subalgebra of an `R`-algebra `A`,
  then an ideal `I`of `A` is an augmentation ideal for the `R`-algebra structure if and only if
  it is an augmentation ideal for the `S`-algebra structure.

-/

@[expose] public section

namespace Ideal

variable (R : Type*) [CommSemiring R] {A : Type*}

open Submodule Subalgebra

/-- An ideal `I` of an `R`-algebra `A` is an augmentation ideal
if its underlying module is a complement to `1 : Submodule R A`. -/
/-
**Ideal.IsAugmentation** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：IsAugmentation [Semiring A] [Algebra R A] (I : Ideal A) : Prop
参数：I : Ideal A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
An ideal `I` of an `R`-algebra `A` is an augmentation ideal
if its underlying module is a complement to `1 : Submodule R A`.
-/
def IsAugmentation [Semiring A] [Algebra R A] (I : Ideal A) : Prop :=
  IsCompl 1 (I.restrictScalars R)
/-
**Ideal.isAugmentation_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：isAugmentation_iff [Semiring A] [Algebra R A] (I : Ideal A) : I.IsAugmenta
tion R ↔ IsCompl 1 (I.restrictScalars R)
参数：I : Ideal A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isAugmentation_iff [Semiring A] [Algebra R A] (I : Ideal A) :
    I.IsAugmentation R ↔ IsCompl 1 (I.restrictScalars R) := Iff.rfl

/-- If `S` is a subalgebra of an `R`-algebra `A`, then an ideal `I`of `A` is an augmentation ideal
for the `R`-algebra structure
if and only if it is an augmentation ideal for the `S`-algebra structure. -/
/-
**Ideal.isAugmentation_subalgebra_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isAugmentation_subalgebra_iff [CommSemiring A] [Algebra R A] {S : Subalgeb
ra R A} {I : Ideal A} : I.IsAugmentation S ↔ IsCompl S.toSubmodule (I.restrictSc
alars R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.isCompl_restrictScalars_iff`：isCompl_restrictScalars_iff {s t 
: Submodule R M} : IsCompl (s.restrictScalars S) (t.restrictScalars S) ↔ IsCompl
 s t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subalgebra.restrictScalars_one`：restrictScalars_one : Submodule.restrict
Scalars R (1 : Submodule S A) = Subalgebra.toSubmodule S
· 使用定理 `Submodule.restrictScalars_self`：restrictScalars_self (V : Submodule R M)
 : V.restrictScalars R = V
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `S` is a subalgebra of an `R`-algebra `A`, then an ideal `I`of `A` is an augm
entation ideal
for the `R`-algebra structure
if and only if it is an augmentation ideal for the `S`-algebra structure.
-/
theorem isAugmentation_subalgebra_iff [CommSemiring A] [Algebra R A]
    {S : Subalgebra R A} {I : Ideal A} :
    I.IsAugmentation S ↔ IsCompl S.toSubmodule (I.restrictScalars R) := by
  simp [Ideal.IsAugmentation, ← Submodule.isCompl_restrictScalars_iff R]

end Ideal

end

