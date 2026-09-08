/-
Copyright (c) 2026 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov
-/
module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity

/-!
# Semisimple representations

This file defines the typeclass `IsSemisimpleRepresentation` for semisimple monoid representations.

-/

namespace Representation

variable {k G V : Type*}

public section

open scoped MonoidAlgebra

variable [Monoid G] [Field k] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- A representation is semisimple when every subrepresentation has a complement. -/
/-
**Representation.IsSemisimpleRepresentation** 是 Mathlib 中的一个缩写定义，位于命名空间 `Represe
ntation`。
形式化陈述：IsSemisimpleRepresentation
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A representation is semisimple when every subrepresentation has a complement.
-/
abbrev IsSemisimpleRepresentation :=
  ComplementedLattice (Subrepresentation ρ)
/-
**Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule** 是 
Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：isSemisimpleRepresentation_iff_isSemisimpleModule_asModule : IsSemisimpleR
epresentation ρ ↔ IsSemisimpleModule k[G] ρ.asModule
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isSemisimpleModule_iff`：∀ (R : Type u_2) [inst : Ring R] (M : Type u_4) 
[inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsSemisimpleModule R M
 ↔ Complemen…
· 使用定理 `OrderIso.complementedLattice_iff`：OrderIso.complementedLattice_iff (f : 
α ≃o β) : ComplementedLattice α ↔ ComplementedLattice β
-/
theorem isSemisimpleRepresentation_iff_isSemisimpleModule_asModule :
    IsSemisimpleRepresentation ρ ↔ IsSemisimpleModule k[G] ρ.asModule := by
  rw [isSemisimpleModule_iff]
  exact OrderIso.complementedLattice_iff Subrepresentation.subrepresentationSubmoduleOrderIso

set_option backward.isDefEq.respectTransparency false in
/-
**Representation.isSemisimpleModule_iff_isSemisimpleRepresentation_ofModule** 是 
Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：isSemisimpleModule_iff_isSemisimpleRepresentation_ofModule (M : Type*) [Ad
dCommGroup M] [Module k[G] M] : IsSemisimpleModule k[G] M ↔ IsSemisimpleRepresen
tation (ofModule (k
参数：M : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isSemisimpleModule_iff`：∀ (R : Type u_2) [inst : Ring R] (M : Type u_4) 
[inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsSemisimpleModule R M
 ↔ Complemen…
· 使用定理 `OrderIso.complementedLattice_iff`：OrderIso.complementedLattice_iff (f : 
α ≃o β) : ComplementedLattice α ↔ ComplementedLattice β
-/
theorem isSemisimpleModule_iff_isSemisimpleRepresentation_ofModule (M : Type*) [AddCommGroup M]
    [Module k[G] M] :
    IsSemisimpleModule k[G] M ↔ IsSemisimpleRepresentation (ofModule (k := k) (G := G) M) := by
  rw [isSemisimpleModule_iff]
  exact OrderIso.complementedLattice_iff Subrepresentation.submoduleSubrepresentationOrderIso

end

end Representation

