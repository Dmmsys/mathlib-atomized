/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Monoid representations

This file introduces monoid representations and their characters and defines a few ways to construct
representations.

## Main definitions

  * `Representation`
  * `Representation.directSum`
  * `Representation.prod`
  * `Representation.tprod`
  * `Representation.linHom`
  * `Representation.dual`
  * `Representation.free`

## Implementation notes

Representations of a monoid `G` on a `k`-module `V` are implemented as
homomorphisms `G →* (V →ₗ[k] V)`. We use the abbreviation `Representation` for this hom space.

The theorem `asAlgebraHom_def` constructs a module over the group `k`-algebra of `G` (implemented
as `k[G]`) corresponding to a representation. If `ρ : Representation k G V`, this
module can be accessed via `ρ.asModule`. Conversely, given a `k[G]`-module `M`,
`M.ofModule` is the associated representation seen as a homomorphism.
-/

@[expose] public section

open MonoidAlgebra
open LinearMap Module

section

variable (k G V : Type*) [Semiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- A representation of `G` on the `k`-module `V` is a homomorphism `G →* (V →ₗ[k] V)`.
-/
/-
**Representation** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Representation
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A representation of `G` on the `k`-module `V` is a homomorphism `G →* (V →ₗ[k] V
)`.
-/
abbrev Representation :=
  G →* V →ₗ[k] V

end

namespace Representation

section trivial

variable (k G V : Type*) [Semiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- The trivial representation of `G` on a `k`-module V.
-/
/-
**Representation.trivial** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：trivial : Representation k G V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial representation of `G` on a `k`-module V.
-/
def trivial : Representation k G V :=
  1

variable {G V}

@[simp]
/-
**Representation.trivial_apply** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：trivial_apply (g : G) (v : V) : trivial k G V g v = v
参数：g : G；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trivial_apply (g : G) (v : V) : trivial k G V g v = v :=
  rfl

variable {k}

/-- A predicate for representations that fix every element. -/
/-
**Representation.IsTrivial** 是 Mathlib 中的一个类，位于命名空间 `Representation`。
形式化陈述：IsTrivial (ρ : Representation k G V) : Prop where out : forall g, ρ g = Li
nearMap.id
参数：ρ : Representation k G V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate for representations that fix every element.
-/
class IsTrivial (ρ : Representation k G V) : Prop where
  out : ∀ g, ρ g = LinearMap.id := by aesop
/-
**Representation.** 是 Mathlib 中的一个实例，位于命名空间 `Representation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTrivial (trivial k G V) where

@[simp]
/-
**Representation.isTrivial_def** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：isTrivial_def (ρ : Representation k G V) [IsTrivial ρ] (g : G) : ρ g = Lin
earMap.id
参数：ρ : Representation k G V；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Representation.IsTrivial.out`：∀ {k : Type u_1} {G : Type u_2} {V : Type 
u_3} {inst : Semiring k} {inst_1 : Monoid G} {inst_2 : AddCommMonoid V}   {inst_
3 : _root_.Module …
-/
theorem isTrivial_def (ρ : Representation k G V) [IsTrivial ρ] (g : G) :
    ρ g = LinearMap.id := IsTrivial.out g
/-
**Representation.isTrivial_apply** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：isTrivial_apply (ρ : Representation k G V) [IsTrivial ρ] (g : G) (x : V) :
 ρ g x = x
参数：ρ : Representation k G V；g : G；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Representation.isTrivial_def`：isTrivial_def (ρ : Representation k G V) [
IsTrivial ρ] (g : G) : ρ g = LinearMap.id
-/
theorem isTrivial_apply (ρ : Representation k G V) [IsTrivial ρ] (g : G) (x : V) :
    ρ g x = x := congr($(isTrivial_def ρ g) x)

end trivial

section Group

variable {k G V : Type*} [Semiring k] [Group G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)

@[simp]
/-
**Representation.inv_self_apply** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：inv_self_apply (g : G) (x : V) : ρ g⁻¹ (ρ g x) = x
参数：g : G；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_self_apply (g : G) (x : V) :
    ρ g⁻¹ (ρ g x) = x := by
  simp [← Module.End.mul_apply, ← map_mul]

@[simp]
/-
**Representation.self_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：self_inv_apply (g : G) (x : V) : ρ g (ρ g⁻¹ x) = x
参数：g : G；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem self_inv_apply (g : G) (x : V) :
    ρ g (ρ g⁻¹ x) = x := by
  simp [← Module.End.mul_apply, ← map_mul]
/-
**Representation.inv_apply_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Representation`。
形式化陈述：inv_apply_eq_iff {g : G} {x y : V} : ρ g⁻¹ x = y ↔ x = ρ g y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Representation.self_inv_apply`：self_inv_apply (g : G) (x : V) : ρ g (ρ g
⁻¹ x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Representation.inv_self_apply`：inv_self_apply (g : G) (x : V) : ρ g⁻¹ (ρ
 g x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma inv_apply_eq_iff {g : G} {x y : V} :
    ρ g⁻¹ x = y ↔ x = ρ g y := by
  constructor <;> rintro rfl <;> simp
/-
**Representation.apply_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Representation`。
形式化陈述：apply_bijective (g : G) : Function.Bijective (ρ g)
参数：g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Representation.inv_self_apply`：inv_self_apply (g : G) (x : V) : ρ g⁻¹ (ρ
 g x) = x
· 使用定理 `Representation.self_inv_apply`：self_inv_apply (g : G) (x : V) : ρ g (ρ g
⁻¹ x) = x
-/
lemma apply_bijective (g : G) :
    Function.Bijective (ρ g) :=
  Equiv.bijective ⟨ρ g, ρ g⁻¹, inv_self_apply ρ g, self_inv_apply ρ g⟩

end Group

section MonoidAlgebra

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V)

/-- A `k`-linear representation of `G` on `V` can be thought of as
an algebra map from `k[G]` into the `k`-linear endomorphisms of `V`.
-/
/-
**Representation.asAlgebraHom** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：asAlgebraHom : k[G] ->ₐ[k] Module.End k V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `k`-linear representation of `G` on `V` can be thought of as
an algebra map from `k[G]` into the `k`-linear endomorphisms of `V`.
-/
noncomputable def asAlgebraHom : k[G] →ₐ[k] Module.End k V := lift k _ G ρ
/-
**Representation.asAlgebraHom_def** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：asAlgebraHom_def : asAlgebraHom ρ = lift k _ G ρ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem asAlgebraHom_def : asAlgebraHom ρ = lift k _ G ρ := rfl

@[simp]
/-
**Representation.asAlgebraHom_single** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：asAlgebraHom_single (g : G) (r : k) : asAlgebraHom ρ (MonoidAlgebra.single
 g r) = r • ρ g
参数：g : G；r : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.lift_single`：lift_single (F : M ->* A) (a b) : lift R A M 
F (single a b) = b • F a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem asAlgebraHom_single (g : G) (r : k) :
    asAlgebraHom ρ (MonoidAlgebra.single g r) = r • ρ g := by
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_single]
/-
**Representation.asAlgebraHom_single_one** 是 Mathlib 中的一个定理，位于命名空间 `Representati
on`。
形式化陈述：asAlgebraHom_single_one (g : G) : asAlgebraHom ρ (MonoidAlgebra.single g 1
) = ρ g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Representation.asAlgebraHom_single`：asAlgebraHom_single (g : G) (r : k) 
: asAlgebraHom ρ (MonoidAlgebra.single g r) = r • ρ g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem asAlgebraHom_single_one (g : G) : asAlgebraHom ρ (MonoidAlgebra.single g 1) = ρ g := by simp
/-
**Representation.asAlgebraHom_of** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：asAlgebraHom_of (g : G) : asAlgebraHom ρ (of k G g) = ρ g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用定理 `Representation.asAlgebraHom_single`：asAlgebraHom_single (g : G) (r : k) 
: asAlgebraHom ρ (MonoidAlgebra.single g r) = r • ρ g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem asAlgebraHom_of (g : G) : asAlgebraHom ρ (of k G g) = ρ g := by
  simp only [MonoidAlgebra.of_apply, asAlgebraHom_single, one_smul]

section

variable {k G V : Type*} [Semiring k] [Monoid G] [AddCommMonoid V] [Module k V]
/-- If `ρ : Representation k G V`, then `ρ.asModule` is a type synonym for `V`,
which we equip with an instance `Module k[G] ρ.asModule`.

You should use `asModuleEquiv : ρ.asModule ≃+ V` to translate terms.
-/
@[nolint unusedArguments]
/-
**Representation.asModule** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：asModule (_ : Representation k G V)
参数：_ : Representation k G V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `ρ : Representation k G V`, then `ρ.asModule` is a type synonym for `V`,
which we equip with an instance `Module k[G] ρ.asModule`.

You should use `asModuleEquiv : ρ.asModule ≃+ V` to translate terms.
-/
def asModule (_ : Representation k G V) := V
deriving AddCommMonoid, Module k
/-
**Representation.** 是 Mathlib 中的一个实例，位于命名空间 `Representation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (ρ : Representation k G V) : Inhabited ρ.asModule where
  default := 0

/-- The additive equivalence from the `Module k[G]` to the original vector space
of the representative.

This is just the identity, but it is helpful for typechecking and keeping track of instances.
-/
/-
**Representation.asModuleEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：asModuleEquiv (ρ : Representation k G V) : ρ.asModule ≃ₗ[k] V
参数：ρ : Representation k G V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive equivalence from the `Module k[G]` to the original vector space
of the representative.

This is just the identity, but it is helpful for typechecking and keeping track 
of instances.
-/
def asModuleEquiv (ρ : Representation k G V) : ρ.asModule ≃ₗ[k] V :=
  LinearEquiv.refl _ _
/-
**Representation.** 是 Mathlib 中的一个实例，位于命名空间 `Representation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module.Finite k V] (ρ : Representation k G V) : Module.Finite k ρ.asModule :=
  .equiv ρ.asModuleEquiv.symm

end

/-- A `k`-linear representation of `G` on `V` can be thought of as a module over `k[G]`.
-/
/-
**Representation.** 是 Mathlib 中的一个实例，位于命名空间 `Representation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `k`-linear representation of `G` on `V` can be thought of as a module over `k[
G]`.
-/
noncomputable instance : Module k[G] ρ.asModule :=
  Module.compHom V (asAlgebraHom ρ).toRingHom

@[simp]
/-
**Representation.asModuleEquiv_map_smul** 是 Mathlib 中的一个定理，位于命名空间 `Representatio
n`。
形式化陈述：asModuleEquiv_map_smul (r : k[G]) (x : ρ.asModule) : ρ.asModuleEquiv (r • 
x) = ρ.asAlgebraHom r (ρ.asModuleEquiv x)
参数：r : k[G]；x : ρ.asModule。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem asModuleEquiv_map_smul (r : k[G]) (x : ρ.asModule) :
    ρ.asModuleEquiv (r • x) = ρ.asAlgebraHom r (ρ.asModuleEquiv x) :=
  rfl
/-
**Representation.asModuleEquiv_symm_map_smul** 是 Mathlib 中的一个定理，位于命名空间 `Represen
tation`。
形式化陈述：asModuleEquiv_symm_map_smul (r : k) (x : V) : ρ.asModuleEquiv.symm (r • x)
 = algebraMap k k[G] r • ρ.asModuleEquiv.symm x
参数：r : k；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Representation.asAlgebraHom_single`：asAlgebraHom_single (g : G) (r : k) 
: asAlgebraHom ρ (MonoidAlgebra.single g r) = r • ρ g
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem asModuleEquiv_symm_map_smul (r : k) (x : V) :
    ρ.asModuleEquiv.symm (r • x) = algebraMap k k[G] r • ρ.asModuleEquiv.symm x := by
  rw [LinearEquiv.symm_apply_eq]
  simp

@[simp]
/-
**Representation.asModuleEquiv_symm_map_rho** 是 Mathlib 中的一个定理，位于命名空间 `Represent
ation`。
形式化陈述：asModuleEquiv_symm_map_rho (g : G) (x : V) : ρ.asModuleEquiv.symm (ρ g x) 
= MonoidAlgebra.of k G g • ρ.asModuleEquiv.symm x
参数：g : G；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Representation.asAlgebraHom_single`：asAlgebraHom_single (g : G) (r : k) 
: asAlgebraHom ρ (MonoidAlgebra.single g r) = r • ρ g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem asModuleEquiv_symm_map_rho (g : G) (x : V) :
    ρ.asModuleEquiv.symm (ρ g x) = MonoidAlgebra.of k G g • ρ.asModuleEquiv.symm x := by
  rw [LinearEquiv.symm_apply_eq]
  simp

/-- Build a `Representation k G M` from a `[Module k[G] M]`.

This version is not always what we want, as it relies on an existing `[Module k M]` instance,
along with a `[IsScalarTower k k[G] M]` instance.

We remedy this below in `ofModule`
(with the tradeoff that the representation is defined
only on a type synonym of the original module.)
-/
/-
**Representation.ofModule'** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：ofModule' (M : Type*) [AddCommMonoid M] [Module k M] [Module k[G] M] [IsSc
alarTower k k[G] M] : Representation k G M
参数：M : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Build a `Representation k G M` from a `[Module k[G] M]`.

This version is not always what we want, as it relies on an existing `[Module k 
M]` instance,
along with a `[IsScalarTower k k[G] M]` instance.

We remedy this below in `ofModule`
(with the tradeoff that the representation is defined
only on a type synonym of the original module.)
-/
noncomputable def ofModule' (M : Type*) [AddCommMonoid M] [Module k M] [Module k[G] M]
    [IsScalarTower k k[G] M] : Representation k G M :=
  (MonoidAlgebra.lift k (M →ₗ[k] M) G).symm (Algebra.lsmul k k M)

section

variable (M : Type*) [AddCommMonoid M] [Module k[G] M]

/-- Build a `Representation` from a `[Module k[G] M]`.

Note that the representation is built on `restrictScalars k k[G] M`,
rather than on `M` itself.
-/
/-
**Representation.ofModule** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：ofModule : Representation k G (RestrictScalars k k[G] M)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Build a `Representation` from a `[Module k[G] M]`.

Note that the representation is built on `restrictScalars k k[G] M`,
rather than on `M` itself.
-/
noncomputable def ofModule : Representation k G (RestrictScalars k k[G] M) :=
  (MonoidAlgebra.lift k _ G).symm (RestrictScalars.lsmul k k[G] M)

/-!
## `ofModule` and `asModule` are inverses.

This requires a little care in both directions:
this is a categorical equivalence, not an isomorphism.

See `Rep.equivalenceModuleMonoidAlgebra` for the full statement.

Starting with `ρ : Representation k G V`, converting to a module and back again
we have a `Representation k G (restrictScalars k k[G] ρ.asModule)`.
To compare these, we use the composition of `restrictScalarsAddEquiv` and `ρ.asModuleEquiv`.

Similarly, starting with `Module k[G] M`,
after we convert to a representation and back to a module,
we have `Module k[G] (restrictScalars k k[G] M)`.
-/


set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Representation.ofModule_asAlgebraHom_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Re
presentation`。
形式化陈述：ofModule_asAlgebraHom_apply_apply (r : k[G]) (m : RestrictScalars k k[G] M
) : ((ofModule M).asAlgebraHom r) m = (RestrictScalars.addEquiv _ _ _).symm (r •
 RestrictScalars.addEquiv _ _ _ m)
参数：r : k[G]；m : RestrictScalars k k[G] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.induction_on`：induction_on {motive : R[M] -> Prop} (x : R[
M]) (of : forall m, motive (.of R M m)) (add : forall x y : R[M], motive x -> mo
tive y -> motive…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用定理 `Representation.asAlgebraHom_single`：asAlgebraHom_single (g : G) (r : k) 
: asAlgebraHom ρ (MonoidAlgebra.single g r) = r • ρ g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `RestrictScalars.addEquiv_symm_map_smul_smul`：RestrictScalars.addEquiv_sy
mm_map_smul_smul (r : R) (s : S) (x : M) : (RestrictScalars.addEquiv R S M).symm
 ((r • s) • x) = r • (RestrictSca…

--- 原说明 ---
## `ofModule` and `asModule` are inverses.

This requires a little care in both directions:
this is a categorical equivalence, not an isomorphism.

See `Rep.equivalenceModuleMonoidAlgebra` for the full statement.

Starting with `ρ : Representation k G V`, converting to a module and back again
we have a `Representation k G (restrictScalars k k[G] ρ.asModule)`.
To compare these, we use the composition of `restrictScalarsAddEquiv` and `ρ.asM
oduleEquiv`.

Similarly, starting with `Module k[G] M`,
after we convert to a representation and back to a module,
we have `Module k[G] (restrictScalars k k[G] M)`.
-/
theorem ofModule_asAlgebraHom_apply_apply (r : k[G])
    (m : RestrictScalars k k[G] M) :
    ((ofModule M).asAlgebraHom r) m =
      (RestrictScalars.addEquiv _ _ _).symm (r • RestrictScalars.addEquiv _ _ _ m) := by
  apply MonoidAlgebra.induction_on r
  · intro g
    simp only [one_smul, MonoidAlgebra.lift_symm_apply, MonoidAlgebra.of_apply,
      Representation.asAlgebraHom_single, Representation.ofModule,
      RestrictScalars.lsmul_apply_apply]
  · intro f g fw gw
    simp only [fw, gw, map_add, add_smul, LinearMap.add_apply]
  · intro r f w
    simp only [w, map_smul, LinearMap.smul_apply, RestrictScalars.addEquiv_symm_map_smul_smul]

@[simp]
/-
**Representation.ofModule_asModule_act** 是 Mathlib 中的一个定理，位于命名空间 `Representation
`。
形式化陈述：ofModule_asModule_act (g : G) (x : RestrictScalars k k[G] ρ.asModule) : of
Module ρ.asModule g x = (RestrictScalars.addEquiv _ _ _).symm (ρ.asModuleEquiv.s
ymm (ρ g (ρ.asModuleEquiv (RestrictScalars.addEquiv _ _ _ x))))
参数：g : G；x : RestrictScalars k k[G] ρ.asModule。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Representation.asModuleEquiv_symm_map_rho`：asModuleEquiv_symm_map_rho (g
 : G) (x : V) : ρ.asModuleEquiv.symm (ρ g x) = MonoidAlgebra.of k G g • ρ.asModu
leEquiv.symm x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofModule_asModule_act (g : G) (x : RestrictScalars k k[G] ρ.asModule) :
    ofModule ρ.asModule g x =
      (RestrictScalars.addEquiv _ _ _).symm
        (ρ.asModuleEquiv.symm (ρ g (ρ.asModuleEquiv (RestrictScalars.addEquiv _ _ _ x)))) := by
  dsimp [ofModule, RestrictScalars.lsmul_apply_apply]
  simp
/-
**Representation.smul_ofModule_asModule** 是 Mathlib 中的一个定理，位于命名空间 `Representatio
n`。
形式化陈述：smul_ofModule_asModule (r : k[G]) (m : (ofModule M).asModule) : (RestrictS
calars.addEquiv k _ _) ((ofModule M).asModuleEquiv (r • m)) = r • (RestrictScala
rs.addEquiv k _ _) ((ofModule M).asModuleEquiv (G
参数：r : k[G]；m : (ofModule M).asModule。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Representation.ofModule_asAlgebraHom_apply_apply`：ofModule_asAlgebraHom_
apply_apply (r : k[G]) (m : RestrictScalars k k[G] M) : ((ofModule M).asAlgebraH
om r) m = (RestrictScalars.addEquiv _ …
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_ofModule_asModule (r : k[G]) (m : (ofModule M).asModule) :
    (RestrictScalars.addEquiv k _ _) ((ofModule M).asModuleEquiv (r • m)) =
      r • (RestrictScalars.addEquiv k _ _) ((ofModule M).asModuleEquiv (G := G) m) := by
  dsimp
  simp only [AddEquiv.apply_symm_apply, ofModule_asAlgebraHom_apply_apply]

end

@[simp]
/-
**Representation.single_smul** 是 Mathlib 中的一个引理，位于命名空间 `Representation`。
形式化陈述：single_smul (t : k) (g : G) (v : ρ.asModule) : MonoidAlgebra.single (g : G
) t • v = t • ρ g (ρ.asModuleEquiv v)
参数：t : k；g : G；v : ρ.asModule。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.smul_apply`：smul_apply (a : S) (f : M ->ₛₗ[σ₁₂] M₂) (x : M) : 
(a • f) x = a • f x
· 使用定理 `Representation.asAlgebraHom_single`：asAlgebraHom_single (g : G) (r : k) 
: asAlgebraHom ρ (MonoidAlgebra.single g r) = r • ρ g
· 使用定理 `Representation.asModuleEquiv_map_smul`：asModuleEquiv_map_smul (r : k[G])
 (x : ρ.asModule) : ρ.asModuleEquiv (r • x) = ρ.asAlgebraHom r (ρ.asModuleEquiv 
x)
-/
lemma single_smul (t : k) (g : G) (v : ρ.asModule) :
    MonoidAlgebra.single (g : G) t • v = t • ρ g (ρ.asModuleEquiv v) := by
  rw [← LinearMap.smul_apply, ← asAlgebraHom_single, ← asModuleEquiv_map_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Representation.** 是 Mathlib 中的一个实例，位于命名空间 `Representation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower k k[G] ρ.asModule where
  smul_assoc t x v := by
    revert t
    apply x.induction_on
    · simp
    · intro y z hy hz
      simp [add_smul, hy, hz]
    · intro s y hy t
      rw [← smul_assoc, smul_eq_mul, hy (t * s), ← smul_eq_mul, smul_assoc]
      aesop

end MonoidAlgebra

section Norm

variable {k G V : Type*} [Semiring k] [Group G] [Fintype G] [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V)

/-- Given a representation `(V, ρ)` of a finite group `G`, `norm ρ` is the linear map `V →ₗ[k] V`
defined by `x ↦ ∑ ρ g x` for `g` in `G`. -/
/-
**Representation.norm** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：norm : Module.End k V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a representation `(V, ρ)` of a finite group `G`, `norm ρ` is the linear ma
p `V →ₗ[k] V`
defined by `x ↦ ∑ ρ g x` for `g` in `G`.
-/
def norm : Module.End k V := ∑ g : G, ρ g

@[simp]
/-
**Representation.norm_comp_self** 是 Mathlib 中的一个引理，位于命名空间 `Representation`。
形式化陈述：norm_comp_self (g : G) : norm ρ ∘ₗ ρ g = norm ρ
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fintype.sum_bijective`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [i
nst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι → κ), 
Function.Bi…
· 使用定理 `Group.mulRight_bijective`：∀ {G : Type u_5} [inst : Group G] (a : G), Fun
ction.Bijective fun x => x * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma norm_comp_self (g : G) : norm ρ ∘ₗ ρ g = norm ρ := by
  ext
  simpa [norm] using Fintype.sum_bijective (· * g) (Group.mulRight_bijective g) _ _ <| by simp

@[simp]
/-
**Representation.norm_self_apply** 是 Mathlib 中的一个引理，位于命名空间 `Representation`。
形式化陈述：norm_self_apply (g : G) (x : V) : norm ρ (ρ g x) = norm ρ x
参数：g : G；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用引理 `Representation.norm_comp_self`：norm_comp_self (g : G) : norm ρ ∘ₗ ρ g = 
norm ρ
-/
lemma norm_self_apply (g : G) (x : V) : norm ρ (ρ g x) = norm ρ x :=
  LinearMap.ext_iff.1 (norm_comp_self _ _) x

@[simp]
/-
**Representation.self_comp_norm** 是 Mathlib 中的一个引理，位于命名空间 `Representation`。
形式化陈述：self_comp_norm (g : G) : ρ g ∘ₗ norm ρ = norm ρ
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fintype.sum_bijective`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [i
nst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι → κ), 
Function.Bi…
· 使用定理 `Group.mulLeft_bijective`：∀ {G : Type u_5} [inst : Group G] (a : G), Func
tion.Bijective fun x => a * x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma self_comp_norm (g : G) : ρ g ∘ₗ norm ρ = norm ρ := by
  ext
  simpa [norm] using Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ _ <| by simp

@[simp]
/-
**Representation.self_norm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Representation`。
形式化陈述：self_norm_apply (g : G) (x : V) : ρ g (norm ρ x) = norm ρ x
参数：g : G；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用引理 `Representation.self_comp_norm`：self_comp_norm (g : G) : ρ g ∘ₗ norm ρ = 
norm ρ
-/
lemma self_norm_apply (g : G) (x : V) : ρ g (norm ρ x) = norm ρ x :=
  LinearMap.ext_iff.1 (self_comp_norm _ _) x

end Norm

section Subrepresentation

variable {k G V : Type*} [Semiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)

set_option backward.isDefEq.respectTransparency false in
/-- Given a `k`-linear `G`-representation `(V, ρ)`, this is the representation defined by
restricting `ρ` to a `G`-invariant `k`-submodule of `V`. -/
@[simps]
/-
**Representation.subrepresentation** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：subrepresentation (W : Submodule k V) (le_comap : forall g, W <= W.comap (
ρ g)) : Representation k G W where toFun g
参数：W : Submodule k V；le_comap : forall g, W <= W.comap (ρ g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `k`-linear `G`-representation `(V, ρ)`, this is the representation defin
ed by
restricting `ρ` to a `G`-invariant `k`-submodule of `V`.
-/
def subrepresentation (W : Submodule k V) (le_comap : ∀ g, W ≤ W.comap (ρ g)) :
    Representation k G W where
  toFun g := (ρ g).restrict <| le_comap g
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

end Subrepresentation

section Quotient

variable {k G V : Type*} [Ring k] [Monoid G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- Given a `k`-linear `G`-representation `(V, ρ)` and a `G`-invariant `k`-submodule `W ≤ V`, this
is the representation induced on `V ⧸ W` by `ρ`. -/
@[simps]
/-
**Representation.quotient** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：quotient (W : Submodule k V) (le_comap : forall g, W <= W.comap (ρ g)) : R
epresentation k G (V ⧸ W) where toFun g
参数：W : Submodule k V；le_comap : forall g, W <= W.comap (ρ g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `k`-linear `G`-representation `(V, ρ)` and a `G`-invariant `k`-submodule
 `W ≤ V`, this
is the representation induced on `V ⧸ W` by `ρ`.
-/
def quotient (W : Submodule k V) (le_comap : ∀ g, W ≤ W.comap (ρ g)) :
    Representation k G (V ⧸ W) where
  toFun g := Submodule.mapQ _ _ (ρ g) <| le_comap g
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

end Quotient

section OfQuotient

variable {k G V : Type*} [Semiring k] [Group G] [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V) (S : Subgroup G)

/-
**Representation.apply_eq_of_coe_eq** 是 Mathlib 中的一个引理，位于命名空间 `Representation`。
形式化陈述：apply_eq_of_coe_eq [IsTrivial (ρ.comp S.subtype)] (g h : G) (hgh : (g : G 
⧸ S) = h) : ρ g = ρ h
参数：ρ.comp S.subtype；g h : G；hgh : (g : G ⧸ S) = h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Representation.apply_bijective`：apply_bijective (g : G) : Function.Bijec
tive (ρ g)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `QuotientGroup.eq`：∀ {α : Type u_1} [inst : Group α] {s : Subgroup α} {a 
b : α}, ↑a = ↑b ↔ a⁻¹ * b ∈ s
· 使用定理 `Representation.isTrivial_def`：isTrivial_def (ρ : Representation k G V) [
IsTrivial ρ] (g : G) : ρ g = LinearMap.id
-/
lemma apply_eq_of_coe_eq [IsTrivial (ρ.comp S.subtype)] (g h : G) (hgh : (g : G ⧸ S) = h) :
    ρ g = ρ h := by
  ext x
  apply (ρ.apply_bijective g⁻¹).1
  simpa [← Module.End.mul_apply, ← map_mul, -isTrivial_def] using
    (congr($(isTrivial_def (ρ.comp S.subtype) ⟨g⁻¹ * h, QuotientGroup.eq.1 hgh⟩) x)).symm

variable [S.Normal]

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` which is trivial on `S` factors
through `G ⧸ S`. -/
/-
**Representation.ofQuotient** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：ofQuotient [IsTrivial (ρ.comp S.subtype)] : Representation k (G ⧸ S) V
参数：ρ.comp S.subtype。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` which is trivial on `S
` factors
through `G ⧸ S`.
-/
def ofQuotient [IsTrivial (ρ.comp S.subtype)] :
    Representation k (G ⧸ S) V :=
  (QuotientGroup.con S).lift ρ <| by
    rintro x y ⟨⟨z, hz⟩, rfl⟩
    ext w
    change ρ (_ * z.unop) _ = _
    exact congr($(apply_eq_of_coe_eq ρ S _ _ (by simp_all)) w)

@[simp]
/-
**Representation.ofQuotient_coe_apply** 是 Mathlib 中的一个引理，位于命名空间 `Representation`
。
形式化陈述：ofQuotient_coe_apply [IsTrivial (ρ.comp S.subtype)] (g : G) (x : V) : ofQu
otient ρ S (g : G ⧸ S) x = ρ g x
参数：ρ.comp S.subtype；g : G；x : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofQuotient_coe_apply [IsTrivial (ρ.comp S.subtype)] (g : G) (x : V) :
    ofQuotient ρ S (g : G ⧸ S) x = ρ g x :=
  rfl

end OfQuotient

section AddCommGroup

variable {k G V : Type*} [Ring k] [Monoid G] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

/-
**Representation.** 是 Mathlib 中的一个实例，位于命名空间 `Representation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup ρ.asModule := inferInstanceAs <| AddCommGroup V

/- Given a representation `(V, ρ)` of a monoid `G`, this says
`(ρ(g) - Id)(x + ρ(g)(x) + ... + ρ(gⁿ)(x)) = ρ(gⁿ⁺¹)(x) - x` for all `n : ℕ, g : G` and `x : V`. -/
/-
**Representation.apply_sub_id_partialSum_eq** 是 Mathlib 中的一个引理，位于命名空间 `Represent
ation`。
形式化陈述：apply_sub_id_partialSum_eq (n : Nat) (g : G) (x : V) : (ρ g - LinearMap.id
 (R
参数：n : Nat；g : G；x : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `List.ofFn_congr`：ofFn_congr {m n : Nat} (h : m = n) (f : Fin m -> α) : o
fFn f = ofFn fun i : Fin n => f (Fin.cast h.symm i)
· 使用定理 `List.ofFn_succ`：∀ {α : Type u_1} {n : ℕ} {f : Fin (n + 1) → α}, List.ofF
n f = f 0 :: List.ofFn fun i => f i.succ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.ofFn_zero`：∀ {α : Type u_1} {f : Fin 0 → α}, List.ofFn f = []
· 使用定理 `List.take_nil`：∀ {α : Type u} {i : ℕ}, List.take i [] = []
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.succ_eq_last_succ`：∀ {n : ℕ} {i : Fin n.succ}, i.succ = Fin.last (n 
+ 1) ↔ i = Fin.last n
· 使用定理 `Fin.partialSum_succ`：∀ {M : Type u_2} [inst : AddMonoid M] {n : ℕ} (f : 
Fin n → M) (j : Fin n),   Fin.partialSum f j.succ = Fin.partialSum f j.castSucc 
+ f j
· 使用定理 `Fin.partialSum_init`：∀ {M : Type u_2} [inst : AddMonoid M] {n : ℕ} {f : 
Fin (n + 1) → M} (i : Fin (n + 1)),   Fin.partialSum (Fin.init f) i = Fin.partia
lSum f i.…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Given a representation `(V, ρ)` of a monoid `G`, this says
`(ρ(g) - Id)(x + ρ(g)(x) + ... + ρ(gⁿ)(x)) = ρ(gⁿ⁺¹)(x) - x` for all `n : ℕ, g :
 G` and `x : V`.
-/
lemma apply_sub_id_partialSum_eq (n : ℕ) (g : G) (x : V) :
    (ρ g - LinearMap.id (R := k) (M := V)) ((Fin.last _).partialSum
      (fun (j : Fin (n + 1)) => ρ (g ^ (j : ℕ)) x)) = ρ (g ^ (n + 1)) x - x := by
  induction n with
  | zero => simp [Fin.partialSum]
  | succ n h =>
    have : Fin.init (fun (j : Fin (n + 2)) => ρ (g ^ (j : ℕ)) x) =
      fun (j : Fin (n + 1)) => ρ (g ^ (j : ℕ)) x := by ext; simp [Fin.init]
    rw [← Fin.succ_eq_last_succ.2 rfl, Fin.partialSum_succ, ← Fin.partialSum_init, map_add,
      this, h]
    simp [pow_succ']

end AddCommGroup

section MulAction

variable (k : Type*) [Semiring k] (G : Type*) [Monoid G] (H : Type*) [MulAction G H]

/-- A `G`-action on `H` induces a representation `G →* End(k[H])` in the natural way. -/
/-
**Representation.ofMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：ofMulAction : Representation k G k[H] where toFun g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `G`-action on `H` induces a representation `G →* End(k[H])` in the natural way
.
-/
noncomputable def ofMulAction : Representation k G k[H] where
  toFun g := (coeffLinearEquiv k).symm.toLinearMap ∘ₗ Finsupp.lmapDomain k k (g • ·) ∘ₗ
    (coeffLinearEquiv k).toLinearMap
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_smul]

/-- The natural `k`-linear `G`-representation on `k[G]` induced by left multiplication in `G`. -/
/-
**Representation.leftRegular** 是 Mathlib 中的一个缩写定义，位于命名空间 `Representation`。
形式化陈述：leftRegular
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural `k`-linear `G`-representation on `k[G]` induced by left multiplicati
on in `G`.
-/
noncomputable abbrev leftRegular := ofMulAction k G G

/-- The natural `k`-linear `G`-representation on `k[Gⁿ]` induced by left multiplication in `G`. -/
/-
**Representation.diagonal** 是 Mathlib 中的一个缩写定义，位于命名空间 `Representation`。
形式化陈述：diagonal (n : Nat)
参数：n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural `k`-linear `G`-representation on `k[Gⁿ]` induced by left multiplicat
ion in `G`.
-/
noncomputable abbrev diagonal (n : ℕ) := ofMulAction k G (Fin n → G)

variable {k G H}
/-
**Representation.ofMulAction_def** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：ofMulAction_def (g : G) : ofMulAction k G H g = (coeffLinearEquiv k).symm.
toLinearMap ∘ₗ Finsupp.lmapDomain k k (g • ·) ∘ₗ (coeffLinearEquiv k).toLinearMa
p
参数：g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMulAction_def (g : G) :
    ofMulAction k G H g = (coeffLinearEquiv k).symm.toLinearMap ∘ₗ Finsupp.lmapDomain k k (g • ·) ∘ₗ
      (coeffLinearEquiv k).toLinearMap := rfl

@[simp]
/-
**Representation.ofMulAction_single** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：ofMulAction_single (g : G) (x : H) (r : k) : ofMulAction k G H g (single x
 r) = single (g • x) r
参数：g : G；x : H；r : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_symm_apply`：∀ (R : Type u_1) {S : Type u_
2} {M : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Mod
ule R S]   (a : M →₀ S), (Monoi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofMulAction_single (g : G) (x : H) (r : k) :
    ofMulAction k G H g (single x r) = single (g • x) r := by simp [ofMulAction_def]

end MulAction
section DistribMulAction

variable (k G A : Type*) [Semiring k] [Monoid G] [AddCommMonoid A] [Module k A]
  [DistribMulAction G A] [SMulCommClass G k A]

/-- Turns a `k`-module `A` with a compatible `DistribMulAction` of a monoid `G` into a
`k`-linear `G`-representation on `A`. -/
/-
**Representation.ofDistribMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：ofDistribMulAction : Representation k G A where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turns a `k`-module `A` with a compatible `DistribMulAction` of a monoid `G` into
 a
`k`-linear `G`-representation on `A`.
-/
def ofDistribMulAction : Representation k G A where
  toFun := fun m =>
    { DistribMulAction.toAddMonoidEnd G A m with
      map_smul' := smul_comm _ }
  map_one' := by ext; exact one_smul _ _
  map_mul' := by intros; ext; exact mul_smul _ _ _

variable {k G A}
/-
**Representation.ofDistribMulAction_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Repre
sentation`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} {A : Type u_3} [inst : Semiring k] [inst_1
 : Monoid G] [inst_2 : AddCommMonoid A]   [inst_3 : _root_.Module k A] [inst_4 :
 DistribMulAction G A] [inst_5 : SMulCommClass G k A] (g : G) (a : A),   ((Repre
sentation.ofDistribMulAction k G A) g) a = g • a
参数：g : G；a : A；(Representation.ofDistribMulAction k G A) g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofDistribMulAction_apply_apply (g : G) (a : A) :
    ofDistribMulAction k G A g a = g • a := rfl

@[simp]
/-
**Representation.norm_ofDistribMulAction_eq** 是 Mathlib 中的一个定理，位于命名空间 `Represent
ation`。
形式化陈述：norm_ofDistribMulAction_eq {G : Type*} [Group G] [Fintype G] [DistribMulAc
tion G A] [SMulCommClass G k A] (x : A) : (ofDistribMulAction k G A).norm x = ∑ 
g : G, g • x
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_ofDistribMulAction_eq {G : Type*} [Group G] [Fintype G]
    [DistribMulAction G A] [SMulCommClass G k A] (x : A) :
    (ofDistribMulAction k G A).norm x = ∑ g : G, g • x := by
  simp [norm]

end DistribMulAction
section MulDistribMulAction
variable (M G : Type*) [Monoid M] [CommGroup G] [MulDistribMulAction M G]

/-- Turns a `CommGroup` `G` with a `MulDistribMulAction` of a monoid `M` into a
`ℤ`-linear `M`-representation on `Additive G`. -/
/-
**Representation.ofMulDistribMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Representation
`。
形式化陈述：ofMulDistribMulAction : Representation Int M (Additive G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turns a `CommGroup` `G` with a `MulDistribMulAction` of a monoid `M` into a
`ℤ`-linear `M`-representation on `Additive G`.
-/
def ofMulDistribMulAction : Representation ℤ M (Additive G) :=
  (addMonoidEndRingEquivInt (Additive G) : AddMonoid.End (Additive G) →* _).comp
    ((monoidEndToAdditive G : _ →* _).comp (MulDistribMulAction.toMonoidEnd M G))
/-
**Representation.ofMulDistribMulAction_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Re
presentation`。
形式化陈述：∀ (M : Type u_1) (G : Type u_2) [inst : Monoid M] [inst_1 : CommGroup G] [
inst_2 : MulDistribMulAction M G] (g : M)   (a : Additive G), ((Representation.o
fMulDistribMulAction M G) g) a = Additive.ofMul (g • Additive.toMul a)
参数：M : Type u_1；G : Type u_2；g : M；a : Additive G；(Representation.ofMulDistribMu
lAction M G) g；g • Additive.toMul a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofMulDistribMulAction_apply_apply (g : M) (a : Additive G) :
    ofMulDistribMulAction M G g a = Additive.ofMul (g • a.toMul) := rfl

@[simp]
/-
**Representation.norm_ofMulDistribMulAction_eq** 是 Mathlib 中的一个定理，位于命名空间 `Repres
entation`。
形式化陈述：norm_ofMulDistribMulAction_eq {G M : Type} [Group G] [Fintype G] [CommGrou
p M] [MulDistribMulAction G M] (x : Additive M) : Additive.toMul ((ofMulDistribM
ulAction G M).norm x) = ∏ g : G, g • Additive.toMul x
参数：x : Additive M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_ofMulDistribMulAction_eq {G M : Type} [Group G] [Fintype G]
    [CommGroup M] [MulDistribMulAction G M] (x : Additive M) :
    Additive.toMul ((ofMulDistribMulAction G M).norm x) =
      ∏ g : G, g • Additive.toMul x := by
  simp [norm]

end MulDistribMulAction
section Group

section

variable {k G V : Type*} [Semiring k] [Group G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)
@[simp]
/-
**Representation.coeff_ofMulAction** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：coeff_ofMulAction {H : Type*} [MulAction G H] (g : G) (f : k[H]) (h : H) :
 (ofMulAction k G H g f).coeff h = f.coeff (g⁻¹ • h)
参数：g : G；f : k[H]；h : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_symm_apply`：∀ (R : Type u_1) {S : Type u_
2} {M : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Mod
ule R S]   (a : M →₀ S), (Monoi…
· 使用定理 `Finsupp.mapDomain_apply`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} 
[inst : AddCommMonoid M] {f : α → β},   Function.Injective f → ∀ (x : α →₀ M) (a
 : α), (Finsu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_ofMulAction {H : Type*} [MulAction G H] (g : G) (f : k[H]) (h : H) :
    (ofMulAction k G H g f).coeff h = f.coeff (g⁻¹ • h) := by
  conv_lhs => rw [← smul_inv_smul g h]
  set h' := g⁻¹ • h
  have hg : Function.Injective (g • · : H → H) := by
    intro h₁ h₂
    simp
  simp [ofMulAction_def, Finsupp.mapDomain_apply, hg]

@[deprecated (since := "2026-06-18")] alias ofMulAction_apply := coeff_ofMulAction

-- Noncomputable since `MonoidAlgebra.instMul` is now noncomputable
/-
**Representation.** 是 Mathlib 中的一个实例，位于命名空间 `Representation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : HMul k[G] (ofMulAction k G G).asModule k[G] where
  hMul x y := x * (ofMulAction k G G).asModuleEquiv y

end

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)

@[simp]
/-
**Representation.asAlgebraHom_ofMulAction_smul_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 
`Representation`。
形式化陈述：asAlgebraHom_ofMulAction_smul_eq_mul (x y : k[G]) : (ofMulAction k G G).as
AlgebraHom x y = x * y
参数：x y : k[G]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.induction_on`：induction_on {motive : R[M] -> Prop} (x : R[
M]) (of : forall m, motive (.of R M m)) (add : forall x y : R[M], motive x -> mo
tive y -> motive…
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用定理 `Representation.asAlgebraHom_single`：asAlgebraHom_single (g : G) (r : k) 
: asAlgebraHom ρ (MonoidAlgebra.single g r) = r • ρ g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Representation.coeff_ofMulAction`：coeff_ofMulAction {H : Type*} [MulActi
on G H] (g : G) (f : k[H]) (h : H) : (ofMulAction k G H g f).coeff h = f.coeff (
g⁻¹ • h)
· 使用引理 `MonoidAlgebra.coeff_single_mul_apply`：coeff_single_mul_apply (x : R[G]) 
(r : R) (g h : G) : (single g r * x).coeff h = r * x.coeff (g⁻¹ * h)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma asAlgebraHom_ofMulAction_smul_eq_mul (x y : k[G]) :
    (ofMulAction k G G).asAlgebraHom x y = x * y := by
  induction x using induction_on with
  | of g => ext; simp [MonoidAlgebra.coeff_single_mul_apply]
  | add x y hx hy => simp [hx, hy, add_mul]
  | smul r x hx => simp [← hx]

@[deprecated (since := "2026-06-18")]
alias ofMulAction_self_smul_eq_mul := asAlgebraHom_ofMulAction_smul_eq_mul

/-- If we equip `k[G]` with the `k`-linear `G`-representation induced by the left regular action of
`G` on itself, the resulting object is isomorphic as a `k[G]`-module to `k[G]` with its natural
`k[G]`-module structure. -/
@[simps]
/-
**Representation.ofMulActionSelfAsModuleEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Represe
ntation`。
形式化陈述：ofMulActionSelfAsModuleEquiv : (ofMulAction k G G).asModule ≃ₗ[k[G]] k[G] 
where toAddEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we equip `k[G]` with the `k`-linear `G`-representation induced by the left re
gular action of
`G` on itself, the resulting object is isomorphic as a `k[G]`-module to `k[G]` w
ith its natural
`k[G]`-module structure.
-/
noncomputable def ofMulActionSelfAsModuleEquiv : (ofMulAction k G G).asModule ≃ₗ[k[G]] k[G] where
  toAddEquiv := (asModuleEquiv _).toAddEquiv
  map_smul' := by simp

/-- When `G` is a group, a `k`-linear representation of `G` on `V` can be thought of as
a group homomorphism from `G` into the invertible `k`-linear endomorphisms of `V`.
-/
/-
**Representation.asGroupHom** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：asGroupHom : G ->* Units (V ->ₗ[k] V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `G` is a group, a `k`-linear representation of `G` on `V` can be thought of
 as
a group homomorphism from `G` into the invertible `k`-linear endomorphisms of `V
`.
-/
def asGroupHom : G →* Units (V →ₗ[k] V) :=
  MonoidHom.toHomUnits ρ
/-
**Representation.asGroupHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：asGroupHom_apply (g : G) : ↑(asGroupHom ρ g) = ρ g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem asGroupHom_apply (g : G) : ↑(asGroupHom ρ g) = ρ g := by
  simp only [asGroupHom, MonoidHom.coe_toHomUnits]

section Finite

variable [Fintype G]

open Finsupp

/-
**Representation.leftRegular_norm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Representatio
n`。
形式化陈述：leftRegular_norm_apply : (leftRegular k G).norm = (LinearMap.lsmul k _).fl
ip ((leftRegular k G).norm (single 1 1)) ∘ₗ linearCombination _ (fun _ => 1) ∘ₗ 
(coeffLinearEquiv _).toLinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.lhom_ext'`：lhom_ext' {N : Type*} [Semiring R] [AddCommMono
id N] [Module R N] [Module R S] ⦃f g : S[M] ->ₗ[R] N⦄ (H : forall (x : M), Linea
rMap.comp f (…
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Representation.ofMulAction_single`：ofMulAction_single (g : G) (x : H) (r
 : k) : ofMulAction k G H g (single x r) = single (g • x) r
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finset.sum_bijective`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [in
st : AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (e
 : ι → κ),…
· 使用定理 `Group.mulRight_bijective`：∀ {G : Type u_5} [inst : Group G] (a : G), Fun
ction.Bijective fun x => x * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftRegular_norm_apply :
    (leftRegular k G).norm =
      (LinearMap.lsmul k _).flip ((leftRegular k G).norm (single 1 1)) ∘ₗ
      linearCombination _ (fun _ => 1) ∘ₗ (coeffLinearEquiv _).toLinearMap := by
  ext i : 2
  simpa [Representation.norm] using Finset.sum_bijective _
    (Group.mulRight_bijective i) (by simp) (by simp)
/-
**Representation.leftRegular_norm_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Represe
ntation`。
形式化陈述：leftRegular_norm_eq_zero_iff (x : k[G]) : (leftRegular k G).norm x = 0 ↔ x
.coeff.linearCombination k (fun _ => (1 : k)) = 0
参数：x : k[G]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Representation.leftRegular_norm_apply`：leftRegular_norm_apply : (leftReg
ular k G).norm = (LinearMap.lsmul k _).flip ((leftRegular k G).norm (single 1 1)
) ∘ₗ linearCombination _ (f…
· 使用定理 `MonoidAlgebra.ext_iff`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring 
R] {x y : MonoidAlgebra R M}, x = y ↔ x.coeff = y.coeff
· 使用定理 `Finsupp.ext_iff`：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M] {f g : 
α →₀ M}, f = g ↔ ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Representation.ofMulAction_single`：ofMulAction_single (g : G) (x : H) (r
 : k) : ofMulAction k G H g (single x r) = single (g • x) r
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MonoidAlgebra.smul_single`：smul_single (a : A) (m : M) (r : R) : a • sin
gle m r = single m (a • r)
· 使用引理 `MonoidAlgebra.coeff_sum`：coeff_sum (s : Finset ι) (f : ι -> R[M]) : coef
f (∑ i in s, f i) = ∑ i in s, coeff (f i)
· 使用定理 `Finsupp.coe_finsetSum`：∀ {α : Type u_1} {ι : Type u_2} {N : Type u_10} [
inst : AddCommMonoid N] (S : Finset ι) (f : ι → α →₀ N),   ⇑(∑ i ∈ S, f i) = ∑ i
 ∈ S, ⇑(f i…
· 使用定理 `Finsupp.univ_sum_single_apply'`：univ_sum_single_apply' [AddCommMonoid M]
 [Fintype α] (i : α) (m : M) : ∑ j : α, single j m i = m
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftRegular_norm_eq_zero_iff (x : k[G]) :
    (leftRegular k G).norm x = 0 ↔ x.coeff.linearCombination k (fun _ => (1 : k)) = 0 := by
  rw [leftRegular_norm_apply]
  constructor
  · rw [MonoidAlgebra.ext_iff, Finsupp.ext_iff]
    intro h
    simpa [norm, Representation.norm] using h 1
  · intro h
    ext
    simp_all
/-
**Representation.ker_leftRegular_norm_eq** 是 Mathlib 中的一个引理，位于命名空间 `Representati
on`。
形式化陈述：ker_leftRegular_norm_eq : LinearMap.ker (leftRegular k G).norm = LinearMap
.ker (linearCombination k (fun _ => (1 : k)) ∘ₗ (coeffLinearEquiv _).toLinearMap
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用引理 `Representation.leftRegular_norm_eq_zero_iff`：leftRegular_norm_eq_zero_if
f (x : k[G]) : (leftRegular k G).norm x = 0 ↔ x.coeff.linearCombination k (fun _
 => (1 : k)) = 0
-/
lemma ker_leftRegular_norm_eq :
    LinearMap.ker (leftRegular k G).norm = LinearMap.ker
      (linearCombination k (fun _ => (1 : k)) ∘ₗ (coeffLinearEquiv _).toLinearMap) := by
  ext
  exact leftRegular_norm_eq_zero_iff _

end Finite
section Cyclic

/-
**Representation.coeff_of_leftRegular_of_generator** 是 Mathlib 中的一个引理，位于命名空间 `Re
presentation`。
形式化陈述：coeff_of_leftRegular_of_generator (g : G) (hg : forall x, x in Subgroup.zp
owers g) (x : k[G]) (hx : leftRegular k G g x = x) (γ : G) : x.coeff γ = x.coeff
 g
参数：g : G；hg : forall x, x in Subgroup.zpowers g；x : k[G]；hx : leftRegular k G g 
x = x；γ : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.induction_on`：∀ {motive : ℤ → Prop} (i : ℤ),   motive 0 → (∀ (i : ℕ)
, motive ↑i → motive (↑i + 1)) → (∀ (i : ℕ), motive (-↑i) → motive (-↑i - 1)) → 
motive…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Representation.coeff_ofMulAction`：coeff_ofMulAction {H : Type*} [MulActi
on G H] (g : G) (f : k[H]) (h : H) : (ofMulAction k G H g f).coeff h = f.coeff (
g⁻¹ • h)
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `Finsupp.ext_iff`：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M] {f g : 
α →₀ M}, f = g ↔ ∀ (a : α), f a = g a
· 使用定理 `MonoidAlgebra.ext_iff`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring 
R] {x y : MonoidAlgebra R M}, x = y ↔ x.coeff = y.coeff
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_add_one`：∀ {G : Type u_3} [inst : Group G] (a : G) (n : ℤ), a ^ (n 
+ 1) = a ^ n * a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `pow_mul_comm'`：pow_mul_comm' (a : M) (n : Nat) : a ^ n * a = a * a ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `zpow_sub`：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ (m - 
n) = a ^ m * (a ^ n)⁻¹
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
lemma coeff_of_leftRegular_of_generator (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (x : k[G]) (hx : leftRegular k G g x = x) (γ : G) :
    x.coeff γ = x.coeff g := by
  rw [MonoidAlgebra.ext_iff, Finsupp.ext_iff] at hx
  rcases hg γ with ⟨i, rfl⟩
  induction i with
  | zero => simpa using hx g
  | succ n h =>
    simpa [← h, zpow_natCast, zpow_add_one, pow_mul_comm', pow_succ'] using (hx (g ^ (n + 1))).symm
  | pred n h =>
    simpa [zpow_sub, ← h, ← mul_inv_rev, ← pow_mul_comm'] using hx (g ^ (-n : ℤ))

@[deprecated (since := "2026-06-18")]
alias apply_eq_of_leftRegular_eq_of_generator := coeff_of_leftRegular_of_generator

end Cyclic
end Group

section DirectSum

variable {k G : Type*} [Semiring k] [Monoid G]
variable {ι : Type*} {V : ι → Type*}
variable [(i : ι) → AddCommMonoid (V i)] [(i : ι) → Module k (V i)]
variable (ρ : (i : ι) → Representation k G (V i))

open DirectSum

/-- Given representations of `G` on a family `V i` indexed by `i`, there is a
natural representation of `G` on their direct sum `⨁ i, V i`.
-/
@[simps]
/-
**Representation.directSum** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：directSum : Representation k G (⨁ i, V i) where toFun g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given representations of `G` on a family `V i` indexed by `i`, there is a
natural representation of `G` on their direct sum `⨁ i, V i`.
-/
noncomputable def directSum : Representation k G (⨁ i, V i) where
  toFun g := DirectSum.lmap (fun _ => ρ _ g)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

end DirectSum

section Prod

variable {k G V W : Type*} [Semiring k] [Monoid G]
variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
variable (ρV : Representation k G V) (ρW : Representation k G W)

/-- Given representations of `G` on `V` and `W`, there is a natural representation of `G` on their
product `V × W`.
-/
@[simps!]
/-
**Representation.prod** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：prod : Representation k G (V × W) where toFun g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given representations of `G` on `V` and `W`, there is a natural representation o
f `G` on their
product `V × W`.
-/
noncomputable def prod : Representation k G (V × W) where
  toFun g := (ρV g).prodMap (ρW g)
  map_one' := by simp
  map_mul' g h := by simp [prodMap_mul]

end Prod

section TensorProduct

variable {k G V W : Type*} [CommSemiring k] [Monoid G]
variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
variable (ρV : Representation k G V) (ρW : Representation k G W)

open TensorProduct

/-- Given representations of `G` on `V` and `W`, there is a natural representation of `G` on their
tensor product `V ⊗[k] W`.
-/
/-
**Representation.tprod** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：tprod : Representation k G (V otimes[k] W) where toFun g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given representations of `G` on `V` and `W`, there is a natural representation o
f `G` on their
tensor product `V ⊗[k] W`.
-/
noncomputable def tprod : Representation k G (V ⊗[k] W) where
  toFun g := TensorProduct.map (ρV g) (ρW g)
  map_one' := by simp only [map_one, TensorProduct.map_one]
  map_mul' g h := by simp only [map_mul, TensorProduct.map_mul]

local notation ρV " ⊗ " ρW => tprod ρV ρW

@[simp]
/-
**Representation.tprod_apply** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：tprod_apply (g : G) : (ρV otimes ρW) g = TensorProduct.map (ρV g) (ρW g)
参数：g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tprod_apply (g : G) : (ρV ⊗ ρW) g = TensorProduct.map (ρV g) (ρW g) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Representation.smul_tprod_one_asModule** 是 Mathlib 中的一个定理，位于命名空间 `Representati
on`。
形式化陈述：smul_tprod_one_asModule (r : k[G]) (x : V) (y : W) : r • (show (ρV.tprod 1
).asModule from x otimesₜ y) = (r • show ρV.asModule from x) otimesₜ y
参数：r : k[G]；x : V；y : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidAlgebra.lift_apply`：lift_apply (F : M ->* A) (f : R[M]) : lift R A
 M F f = f.coeff.sum fun a b => b • F a
· 使用定理 `LinearMap.finsupp_sum_apply`：finsupp_sum_apply (t : ι ->₀ γ) (g : ι -> γ
 -> M ->ₛₗ[σ₁₂] M₂) (b : M) : (t.sum g) b = t.sum fun i d => g i d b
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `TensorProduct.sum_tmul`：sum_tmul {α : Type*} (s : Finset α) (m : α -> M)
 (n : N) : (∑ a in s, m a) otimesₜ[R] n = ∑ a in s, m a otimesₜ[R] n
-/
theorem smul_tprod_one_asModule (r : k[G]) (x : V) (y : W) :
    r • (show (ρV.tprod 1).asModule from x ⊗ₜ y) = (r • show ρV.asModule from x) ⊗ₜ y := by
  change asAlgebraHom (ρV ⊗ 1) _ _ = asAlgebraHom ρV _ _ ⊗ₜ _
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_apply, tprod_apply, MonoidHom.one_apply,
    LinearMap.finsupp_sum_apply, LinearMap.smul_apply, TensorProduct.map_tmul, Module.End.one_apply]
  simp only [Finsupp.sum, TensorProduct.sum_tmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Representation.smul_one_tprod_asModule** 是 Mathlib 中的一个定理，位于命名空间 `Representati
on`。
形式化陈述：smul_one_tprod_asModule (r : k[G]) (x : V) (y : W) : r • (show (1 otimes ρ
W).asModule from x otimesₜ y) = x otimesₜ (r • show ρW.asModule from y)
参数：r : k[G]；x : V；y : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidAlgebra.lift_apply`：lift_apply (F : M ->* A) (f : R[M]) : lift R A
 M F f = f.coeff.sum fun a b => b • F a
· 使用定理 `LinearMap.finsupp_sum_apply`：finsupp_sum_apply (t : ι ->₀ γ) (g : ι -> γ
 -> M ->ₛₗ[σ₁₂] M₂) (b : M) : (t.sum g) b = t.sum fun i d => g i d b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `TensorProduct.tmul_sum`：tmul_sum (m : M) {α : Type*} (s : Finset α) (n :
 α -> N) : (m otimesₜ[R] ∑ a in s, n a) = ∑ a in s, m otimesₜ[R] n a
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_one_tprod_asModule (r : k[G]) (x : V) (y : W) :
    r • (show (1 ⊗ ρW).asModule from x ⊗ₜ y) = x ⊗ₜ (r • show ρW.asModule from y) := by
  change asAlgebraHom (1 ⊗ ρW) _ _ = _ ⊗ₜ asAlgebraHom ρW _ _
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_apply, tprod_apply, MonoidHom.one_apply,
    LinearMap.finsupp_sum_apply, LinearMap.smul_apply, TensorProduct.map_tmul, Module.End.one_apply]
  simp only [Finsupp.sum, TensorProduct.tmul_sum, TensorProduct.tmul_smul]

end TensorProduct

section LinearHom

variable {k G V W : Type*} [CommSemiring k] [Group G]
variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
variable (ρV : Representation k G V) (ρW : Representation k G W)

/-- Given representations of `G` on `V` and `W`, there is a natural representation of `G` on the
module `V →ₗ[k] W`, where `G` acts by conjugation.
-/
/-
**Representation.linHom** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：linHom : Representation k G (V ->ₗ[k] W) where toFun g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given representations of `G` on `V` and `W`, there is a natural representation o
f `G` on the
module `V →ₗ[k] W`, where `G` acts by conjugation.
-/
def linHom : Representation k G (V →ₗ[k] W) where
  toFun g :=
    { toFun := fun f => ρW g ∘ₗ f ∘ₗ ρV g⁻¹
      map_add' := fun f₁ f₂ => by simp_rw [add_comp, comp_add]
      map_smul' := fun r f => by simp_rw [RingHom.id_apply, smul_comp, comp_smul] }
  map_one' := ext fun x => by simp [Module.End.one_eq_id]
  map_mul' g h := ext fun x => by simp [Module.End.mul_eq_comp, comp_assoc]

@[simp]
/-
**Representation.linHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：linHom_apply (g : G) (f : V ->ₗ[k] W) : (linHom ρV ρW) g f = ρW g ∘ₗ f ∘ₗ 
ρV g⁻¹
参数：g : G；f : V ->ₗ[k] W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linHom_apply (g : G) (f : V →ₗ[k] W) : (linHom ρV ρW) g f = ρW g ∘ₗ f ∘ₗ ρV g⁻¹ :=
  rfl

/-- The dual of a representation `ρ` of `G` on a module `V`, given by `(dual ρ) g f = f ∘ₗ (ρ g⁻¹)`,
where `f : Module.Dual k V`.
-/
/-
**Representation.dual** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：dual : Representation k G (Module.Dual k V) where toFun g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dual of a representation `ρ` of `G` on a module `V`, given by `(dual ρ) g f 
= f ∘ₗ (ρ g⁻¹)`,
where `f : Module.Dual k V`.
-/
def dual : Representation k G (Module.Dual k V) where
  toFun g :=
    { toFun := fun f => f ∘ₗ ρV g⁻¹
      map_add' := fun f₁ f₂ => by simp only [add_comp]
      map_smul' r f := by ext; simp }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[simp]
/-
**Representation.dual_apply** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：dual_apply (g : G) : (dual ρV) g = Module.Dual.transpose (R
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem dual_apply (g : G) : (dual ρV) g = Module.Dual.transpose (R := k) (ρV g⁻¹) :=
  rfl

/-- Given $k$-modules $V, W$, there is a homomorphism $φ : V^* ⊗ W → Hom_k(V, W)$
(implemented by `dualTensorHom` in `Mathlib/LinearAlgebra/Contraction.lean`).
Given representations of $G$ on $V$ and $W$,there are representations of $G$ on $V^* ⊗ W$ and on
$Hom_k(V, W)$.
This lemma says that $φ$ is $G$-linear.
-/
/-
**Representation.dualTensorHom_comm** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：dualTensorHom_comm (g : G) : dualTensorHom k V W ∘ₗ TensorProduct.map (ρV.
dual g) (ρW g) = (linHom ρV ρW) g ∘ₗ dualTensorHom k V W
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given $k$-modules $V, W$, there is a homomorphism $φ : V^* ⊗ W → Hom_k(V, W)$
(implemented by `dualTensorHom` in `Mathlib/LinearAlgebra/Contraction.lean`).
Given representations of $G$ on $V$ and $W$,there are representations of $G$ on 
$V^* ⊗ W$ and on
$Hom_k(V, W)$.
This lemma says that $φ$ is $G$-linear.
-/
theorem dualTensorHom_comm (g : G) :
    dualTensorHom k V W ∘ₗ TensorProduct.map (ρV.dual g) (ρW g) =
      (linHom ρV ρW) g ∘ₗ dualTensorHom k V W := by
  ext; simp [Module.Dual.transpose_apply]

end LinearHom

section

variable {k G : Type*} [CommSemiring k] [Monoid G] {α A B : Type*}
  [AddCommMonoid A] [Module k A] (ρ : Representation k G A)
  [AddCommMonoid B] [Module k B] (τ : Representation k G B)

open Finsupp

/-- The representation on `α →₀ A` defined pointwise by a representation on `A`. -/
@[simps -isSimp]
/-
**Representation.finsupp** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：finsupp (α : Type*) : Representation k G (α ->₀ A) where toFun g
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The representation on `α →₀ A` defined pointwise by a representation on `A`.
-/
noncomputable def finsupp (α : Type*) :
    Representation k G (α →₀ A) where
  toFun g := lsum k fun i => (Finsupp.lsingle i).comp (ρ g)
  map_one' := lhom_ext (fun _ _ => by simp)
  map_mul' _ _ := lhom_ext (fun _ _ => by simp)

@[simp]
/-
**Representation.finsupp_single** 是 Mathlib 中的一个引理，位于命名空间 `Representation`。
形式化陈述：finsupp_single (g : G) (x : α) (a : A) : ρ.finsupp α g (single x a) = sing
le x (ρ g a)
参数：g : G；x : α；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Representation.finsupp_apply`：∀ {k : Type u_1} {G : Type u_2} [inst : Co
mmSemiring k] [inst_1 : Monoid G] {A : Type u_4} [inst_2 : AddCommMonoid A]   [i
nst_3 : _root_.Mod…
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finsupp_single (g : G) (x : α) (a : A) :
    ρ.finsupp α g (single x a) = single x (ρ g a) := by
  simp [finsupp_apply]

/-- The representation on `α →₀ k[G]` defined pointwise by the left regular representation. -/
/-
**Representation.free** 是 Mathlib 中的一个缩写定义，位于命名空间 `Representation`。
形式化陈述：free (k G : Type*) [CommSemiring k] [Monoid G] (α : Type*) : Representatio
n k G (α ->₀ k[G])
参数：k G : Type*；α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The representation on `α →₀ k[G]` defined pointwise by the left regular represen
tation.
-/
noncomputable abbrev free (k G : Type*) [CommSemiring k] [Monoid G] (α : Type*) :
    Representation k G (α →₀ k[G]) :=
  finsupp (leftRegular k G) α
/-
**Representation.** 是 Mathlib 中的一个实例，位于命名空间 `Representation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (k G : Type*) [CommRing k] [Monoid G] (α : Type*) :
    AddCommGroup (free k G α).asModule :=
  inferInstanceAs <| AddCommGroup (α →₀ k[G])
/-
**Representation.free_single_single** 是 Mathlib 中的一个引理，位于命名空间 `Representation`。
形式化陈述：free_single_single (g h : G) (i : α) (r : k) : free k G α g (single i (sin
gle h r)) = .single i (single (g * h) r)
参数：g h : G；i : α；r : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Representation.finsupp_single`：finsupp_single (g : G) (x : α) (a : A) : 
ρ.finsupp α g (single x a) = single x (ρ g a)
· 使用定理 `Representation.ofMulAction_single`：ofMulAction_single (g : G) (x : H) (r
 : k) : ofMulAction k G H g (single x r) = single (g • x) r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma free_single_single (g h : G) (i : α) (r : k) :
    free k G α g (single i (single h r)) = .single i (single (g * h) r) := by
  simp

variable (k G) (α : Type*)

set_option backward.isDefEq.respectTransparency false in
/-- The free `k[G]`-module on a type `α` is isomorphic to the representation `free k G α`. -/
/-
**Representation.finsuppLEquivFreeAsModule** 是 Mathlib 中的一个定义，位于命名空间 `Representa
tion`。
形式化陈述：finsuppLEquivFreeAsModule : (α ->₀ k[G]) ≃ₗ[k[G]] (free k G α).asModule wh
ere toAddEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free `k[G]`-module on a type `α` is isomorphic to the representation `free k
 G α`.
-/
noncomputable def finsuppLEquivFreeAsModule : (α →₀ k[G]) ≃ₗ[k[G]] (free k G α).asModule where
  toAddEquiv := (asModuleEquiv _).symm.toAddEquiv
  map_smul' x y := by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom, LinearEquiv.coe_coe, RingHom.id_apply,
      (free k G α).asModuleEquiv.symm_apply_eq, asModuleEquiv_map_smul,
      LinearEquiv.apply_symm_apply]
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add => simp [*, add_smul]
    | single g a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add => simp [*]
    | single h y =>
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add => simp [*]
    | single i b => simp

/-- `α` gives a `k[G]`-basis of the representation `free k G α`. -/
/-
**Representation.freeAsModuleBasis** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：freeAsModuleBasis : Basis α k[G] (free k G α).asModule where repr
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`α` gives a `k[G]`-basis of the representation `free k G α`.
-/
noncomputable def freeAsModuleBasis : Basis α k[G] (free k G α).asModule where
  repr := (finsuppLEquivFreeAsModule k G α).symm
/-
**Representation.free_asModule_free** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：free_asModule_free : Module.Free k[G] (free k G α).asModule
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
-/
theorem free_asModule_free : Module.Free k[G] (free k G α).asModule :=
  Module.Free.of_basis (freeAsModuleBasis k G α)

end
end Representation

