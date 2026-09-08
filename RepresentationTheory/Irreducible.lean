/-
Copyright (c) 2025 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic

/-!
# Irreducible representations

This file defines irreducible monoid representations.

-/

public section

namespace Representation

open scoped MonoidAlgebra

variable {G k V W : Type*} [Monoid G] [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (ρ : Representation k G V) (σ : Representation k G W)

/-- A representation `ρ` is irreducible if it is non-trivial and has no proper non-trivial
subrepresentations. -/
/-
**Representation.IsIrreducible** 是 Mathlib 中的一个缩写定义，位于命名空间 `Representation`。
形式化陈述：IsIrreducible
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A representation `ρ` is irreducible if it is non-trivial and has no proper non-t
rivial
subrepresentations.
-/
abbrev IsIrreducible :=
  IsSimpleOrder (Subrepresentation ρ)
/-
**Representation.irreducible_iff_isSimpleModule_asModule** 是 Mathlib 中的一个定理，位于命名
空间 `Representation`。
形式化陈述：irreducible_iff_isSimpleModule_asModule : IsIrreducible ρ ↔ IsSimpleModule
 k[G] ρ.asModule
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isSimpleModule_iff`：∀ (R : Type u_2) [inst : Ring R] (M : Type u_4) [ins
t_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsSimpleModule R M ↔ IsSim
pleOrder…
· 使用定理 `OrderIso.isSimpleOrder_iff`：isSimpleOrder_iff [BoundedOrder α] [BoundedO
rder β] (f : α ≃o β) : IsSimpleOrder α ↔ IsSimpleOrder β
-/
theorem irreducible_iff_isSimpleModule_asModule :
    IsIrreducible ρ ↔ IsSimpleModule k[G] ρ.asModule := by
  rw [isSimpleModule_iff]
  exact OrderIso.isSimpleOrder_iff Subrepresentation.subrepresentationSubmoduleOrderIso

set_option backward.isDefEq.respectTransparency false in
/-
**Representation.isSimpleModule_iff_irreducible_ofModule** 是 Mathlib 中的一个定理，位于命名
空间 `Representation`。
形式化陈述：isSimpleModule_iff_irreducible_ofModule (M : Type*) [AddCommGroup M] [Modu
le k[G] M] : IsSimpleModule k[G] M ↔ IsIrreducible (ofModule (k
参数：M : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isSimpleModule_iff`：∀ (R : Type u_2) [inst : Ring R] (M : Type u_4) [ins
t_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsSimpleModule R M ↔ IsSim
pleOrder…
· 使用定理 `OrderIso.isSimpleOrder_iff`：isSimpleOrder_iff [BoundedOrder α] [BoundedO
rder β] (f : α ≃o β) : IsSimpleOrder α ↔ IsSimpleOrder β
-/
theorem isSimpleModule_iff_irreducible_ofModule (M : Type*) [AddCommGroup M] [Module k[G] M] :
    IsSimpleModule k[G] M ↔ IsIrreducible (ofModule (k := k) (G := G) M) := by
  rw [isSimpleModule_iff]
  exact OrderIso.isSimpleOrder_iff Subrepresentation.submoduleSubrepresentationOrderIso

@[deprecated (since := "2026-02-09")]
alias is_simple_module_iff_irreducible_ofModule := isSimpleModule_iff_irreducible_ofModule

namespace IsIrreducible

variable {ρ σ} (f : IntertwiningMap ρ σ) [IsIrreducible ρ]

/-
**Representation.IsIrreducible.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.IsIrre
ducible`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSimpleModule k[G] ρ.asModule :=
  (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance

open Function IntertwiningMap
/-
**Representation.IsIrreducible.injective_or_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `R
epresentation.IsIrreducible`。
形式化陈述：injective_or_eq_zero : Injective f ∨ f = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Representation.instIsScalarTowerMonoidAlgebraAsModule`：∀ {k : Type u_1} 
{G : Type u_2} {V : Type u_3} [inst : CommSemiring k] [inst_1 : Monoid G] [inst_
2 : AddCommMonoid V]   [inst_3 : _root_.Mod…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.map_eq_zero_iff`：map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0
· 使用定理 `LinearMap.injective_or_eq_zero`：injective_or_eq_zero [IsSimpleModule R M
] (f : M ->ₗ[R] N) : Function.Injective f ∨ f = 0
· 使用定理 `Representation.IsIrreducible.instIsSimpleModuleMonoidAlgebraAsModule`：∀ 
{G : Type u_1} {k : Type u_2} {V : Type u_3} [inst : Monoid G] [inst_1 : Field k
] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module k V]…
-/
theorem injective_or_eq_zero : Injective f ∨ f = 0 := by
  rw [← LinearEquiv.map_eq_zero_iff (equivLinearMapAsModule ρ σ)]
  exact LinearMap.injective_or_eq_zero (equivLinearMapAsModule ρ σ f)
/-
**Representation.IsIrreducible.surjective_or_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `
Representation.IsIrreducible`。
形式化陈述：surjective_or_eq_zero (g : IntertwiningMap σ ρ) : Surjective g ∨ g = 0
参数：g : IntertwiningMap σ ρ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Representation.instIsScalarTowerMonoidAlgebraAsModule`：∀ {k : Type u_1} 
{G : Type u_2} {V : Type u_3} [inst : CommSemiring k] [inst_1 : Monoid G] [inst_
2 : AddCommMonoid V]   [inst_3 : _root_.Mod…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.map_eq_zero_iff`：map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0
· 使用定理 `LinearMap.surjective_or_eq_zero`：surjective_or_eq_zero [IsSimpleModule R
 N] (f : M ->ₗ[R] N) : Function.Surjective f ∨ f = 0
· 使用定理 `Representation.IsIrreducible.instIsSimpleModuleMonoidAlgebraAsModule`：∀ 
{G : Type u_1} {k : Type u_2} {V : Type u_3} [inst : Monoid G] [inst_1 : Field k
] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module k V]…
-/
theorem surjective_or_eq_zero (g : IntertwiningMap σ ρ) : Surjective g ∨ g = 0 := by
  rw [← LinearEquiv.map_eq_zero_iff (equivLinearMapAsModule σ ρ)]
  exact LinearMap.surjective_or_eq_zero (equivLinearMapAsModule σ ρ g)
/-
**Representation.IsIrreducible.bijective_or_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `R
epresentation.IsIrreducible`。
形式化陈述：bijective_or_eq_zero [IsIrreducible σ] : Bijective f ∨ f = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Representation.instIsScalarTowerMonoidAlgebraAsModule`：∀ {k : Type u_1} 
{G : Type u_2} {V : Type u_3} [inst : CommSemiring k] [inst_1 : Monoid G] [inst_
2 : AddCommMonoid V]   [inst_3 : _root_.Mod…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.map_eq_zero_iff`：map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0
· 使用定理 `LinearMap.bijective_or_eq_zero`：bijective_or_eq_zero [IsSimpleModule R M
] [IsSimpleModule R N] (f : M ->ₗ[R] N) : Function.Bijective f ∨ f = 0
· 使用定理 `Representation.IsIrreducible.instIsSimpleModuleMonoidAlgebraAsModule`：∀ 
{G : Type u_1} {k : Type u_2} {V : Type u_3} [inst : Monoid G] [inst_1 : Field k
] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module k V]…
-/
theorem bijective_or_eq_zero [IsIrreducible σ] : Bijective f ∨ f = 0 := by
  rw [← LinearEquiv.map_eq_zero_iff (equivLinearMapAsModule ρ σ)]
  exact LinearMap.bijective_or_eq_zero (equivLinearMapAsModule ρ σ f)
/-
**Representation.IsIrreducible.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.IsIrre
ducible`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsIrreducible σ] [IsEmpty (Equiv ρ σ)] : Subsingleton (IntertwiningMap ρ σ) :=
  ⟨fun f g ↦ sub_eq_zero.mp <| (bijective_or_eq_zero _).resolve_left
    fun h ↦ isEmpty_iff.mp inferInstance <| (f - g).ofBijective h⟩
variable [FiniteDimensional k V] [IsAlgClosed k]

variable (f : IntertwiningMap ρ ρ) in
/-
**Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClos
ed** 是 Mathlib 中的一个定理，位于命名空间 `Representation.IsIrreducible`。
形式化陈述：algebraMap_intertwiningMap_bijective_of_isAlgClosed : Bijective (algebraMa
p k (IntertwiningMap ρ ρ))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Representation.instIsScalarTowerMonoidAlgebraAsModule`：∀ {k : Type u_1} 
{G : Type u_2} {V : Type u_3} [inst : CommSemiring k] [inst_1 : Monoid G] [inst_
2 : AddCommMonoid V]   [inst_3 : _root_.Mod…
· 使用定理 `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`：IsSimpleModule.a
lgebraMap_end_bijective_of_isAlgClosed : Function.Bijective (algebraMap k (Modul
e.End A V))
· 使用定理 `Representation.IsIrreducible.instIsSimpleModuleMonoidAlgebraAsModule`：∀ 
{G : Type u_1} {k : Type u_2} {V : Type u_3} [inst : Monoid G] [inst_1 : Field k
] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module k V]…
· 使用定理 `Representation.instFiniteAsModule`：∀ {k : Type u_4} {G : Type u_5} {V : 
Type u_6} [inst : Semiring k] [inst_1 : Monoid G] [inst_2 : AddCommMonoid V]   [
inst_3 : _root_.Module …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
-/
theorem algebraMap_intertwiningMap_bijective_of_isAlgClosed :
    Bijective (algebraMap k (IntertwiningMap ρ ρ)) := by
  have : Bijective (algebraMap k (Module.End k[G] ρ.asModule)) :=
    IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k
  exact (Bijective.of_comp_iff' (IntertwiningMap.equivAlgEnd (ρ := ρ)).bijective _).1 this

variable (ρ) in
/-
**Representation.IsIrreducible.finrank_intertwiningMap_self** 是 Mathlib 中的一个定理，位
于命名空间 `Representation.IsIrreducible`。
形式化陈述：∀ {G : Type u_1} {k : Type u_2} {V : Type u_3} [inst : Monoid G] [inst_1 :
 Field k] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module k V] (ρ : Represen
tation k G V) [ρ.IsIrreducible] [FiniteDimensional k V] [IsAlgClosed k],   Modul
e.finrank k (ρ.IntertwiningMap ρ) = 1
参数：ρ : Representation k G V；ρ.IntertwiningMap ρ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isA
lgClosed`：algebraMap_intertwiningMap_bijective_of_isAlgClosed : Bijective (algeb
raMap k (IntertwiningMap ρ ρ))
· 使用定理 `CommSemiring.finrank_self`：CommSemiring.finrank_self (R) [CommSemiring R
] : Module.finrank R R = 1
-/
@[simp] theorem finrank_intertwiningMap_self : Module.finrank k (IntertwiningMap ρ ρ) = 1 := by
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Algebra.linearMap k (IntertwiningMap ρ ρ))
      algebraMap_intertwiningMap_bijective_of_isAlgClosed).symm]
  exact CommSemiring.finrank_self k

open scoped IsMulCommutative in
include ρ in
variable (ρ) in
/-
**Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative** 是 Mathlib 中的
一个定理，位于命名空间 `Representation.IsIrreducible`。
形式化陈述：finrank_eq_one_of_isMulCommutative [IsMulCommutative G] : Module.finrank k
 V = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSimpleModule.finrank_eq_one_of_isMulCommutative`：IsSimpleModule.finran
k_eq_one_of_isMulCommutative [IsMulCommutative A] : Module.finrank k V = 1
· 使用定理 `Representation.instIsScalarTowerMonoidAlgebraAsModule`：∀ {k : Type u_1} 
{G : Type u_2} {V : Type u_3} [inst : CommSemiring k] [inst_1 : Monoid G] [inst_
2 : AddCommMonoid V]   [inst_3 : _root_.Mod…
· 使用定理 `Representation.IsIrreducible.instIsSimpleModuleMonoidAlgebraAsModule`：∀ 
{G : Type u_1} {k : Type u_2} {V : Type u_3} [inst : Monoid G] [inst_1 : Field k
] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module k V]…
· 使用定理 `Representation.instFiniteAsModule`：∀ {k : Type u_4} {G : Type u_5} {V : 
Type u_6} [inst : Semiring k] [inst_1 : Monoid G] [inst_2 : AddCommMonoid V]   [
inst_3 : _root_.Module …
-/
theorem finrank_eq_one_of_isMulCommutative [IsMulCommutative G] : Module.finrank k V = 1 := by
  exact IsSimpleModule.finrank_eq_one_of_isMulCommutative k[G] ρ.asModule k

end IsIrreducible

end Representation

