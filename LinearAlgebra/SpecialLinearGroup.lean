/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# The special linear group of a module

If `R` is a commutative ring and `V` is an `R`-module,
we define `SpecialLinearGroup R V` as the subtype of
linear equivalences `V ≃ₗ[R] V` with determinant 1.
When `V` doesn't have a finite basis, the determinant is defined to be 1
and the definition gives `V ≃ₗ[R] V`.
The interest of this definition is that `SpecialLinearGroup R V`
has a group structure. (Starting from linear maps wouldn't have worked.)

The file is constructed parallel to the one defining `Matrix.SpecialLinearGroup`.

We provide `SpecialLinearGroup.toLinearEquiv`: the canonical map
from `SpecialLinearGroup R V` to `V ≃ₗ[R] V`, as a monoid hom.

When `V` is free and finite over `R`, we define
* `SpecialLinearGroup.dualMap`
* `SpecialLinearGroup.baseChange`

We define `Matrix.SpecialLinearGroup.toLin'_equiv`: the multiplicative equivalence
from `Matrix.SpecialLinearGroup n R` to `SpecialLinearGroup R (n → R)`
and its variant
`Matrix.SpecialLinearGroup.toLin_equiv`,
from `Matrix.SpecialLinearGroup n R` to `SpecialLinearGroup R V`,
associated with a finite basis of `V`.

-/

@[expose] public section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

variable (R V) in
/-- The special linear group of a module.

This is only meaningful when the module is finite and free,
for otherwise, it coincides with the group of linear equivalences. -/
/-
**SpecialLinearGroup** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：SpecialLinearGroup
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The special linear group of a module.

This is only meaningful when the module is finite and free,
for otherwise, it coincides with the group of linear equivalences.
-/
abbrev SpecialLinearGroup := { u : V ≃ₗ[R] V // u.det = 1 }

namespace SpecialLinearGroup

/-
**SpecialLinearGroup.det_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `SpecialLinearGroup`。
形式化陈述：det_eq_one (u : SpecialLinearGroup R V) : LinearMap.det (u : V ->ₗ[R] V) =
 1
参数：u : SpecialLinearGroup R V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_eq_one (u : SpecialLinearGroup R V) :
    LinearMap.det (u : V →ₗ[R] V) = 1 := by
  simp [← LinearEquiv.coe_det, u.prop]

/-- The coercion from `SpecialLinearGroup R V` to the function type `V → V` -/
/-
**SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `SpecialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion from `SpecialLinearGroup R V` to the function type `V → V`
-/
instance : CoeFun (SpecialLinearGroup R V) (fun _ ↦ V → V) where
  coe u x := u.val x
/-
**SpecialLinearGroup.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `SpecialLinearGroup`。
形式化陈述：ext_iff (u v : SpecialLinearGroup R V) : u = v ↔ forall x : V, u x = v x
参数：u v : SpecialLinearGroup R V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ext_iff (u v : SpecialLinearGroup R V) : u = v ↔ ∀ x : V, u x = v x := by
  simp only [← Subtype.coe_inj, LinearEquiv.ext_iff]

@[ext]
/-
**SpecialLinearGroup.ext** 是 Mathlib 中的一个定理，位于命名空间 `SpecialLinearGroup`。
形式化陈述：ext (u v : SpecialLinearGroup R V) : (forall x, u x = v x) -> u = v
参数：u v : SpecialLinearGroup R V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SpecialLinearGroup.ext_iff`：ext_iff (u v : SpecialLinearGroup R V) : u =
 v ↔ forall x : V, u x = v x
-/
theorem ext (u v : SpecialLinearGroup R V) : (∀ x, u x = v x) → u = v :=
  (SpecialLinearGroup.ext_iff u v).mpr

section rankOne

set_option backward.isDefEq.respectTransparency.types false in
/-- If a free module has `Module.finrank` equal to `1`, then its special linear group is trivial. -/
/-
**SpecialLinearGroup.subsingleton_of_finrank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `S
pecialLinearGroup`。
形式化陈述：subsingleton_of_finrank_eq_one [Module.Free R V] (d1 : Module.finrank R V 
= 1) : Subsingleton (SpecialLinearGroup R V) where allEq u v
参数：d1 : Module.finrank R V = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `SpecialLinearGroup.ext`：ext (u v : SpecialLinearGroup R V) : (forall x, 
u x = v x) -> u = v
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.eq_symm_apply`：eq_symm_apply {x y} : y = e.symm x ↔ e y = x
· 使用定理 `LinearMap.det_smul`：det_smul [Module.Free A M] (c : A) (f : M ->ₗ[A] M) 
: LinearMap.det (c • f) = c ^ Module.finrank A M * LinearMap.det f
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `LinearMap.det_id`：det_id : LinearMap.det (LinearMap.id : M ->ₗ[A] M) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one`：∀ {R : Type u_2} [i
nst : CommSemiring R] [StrongRankCondition R] {M : Type u_3} [inst_2 : AddCommMo
noid M]   [inst_3 : _root_.Module R M] [M…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
If a free module has `Module.finrank` equal to `1`, then its special linear grou
p is trivial.
-/
theorem subsingleton_of_finrank_eq_one [Module.Free R V] (d1 : Module.finrank R V = 1) :
    Subsingleton (SpecialLinearGroup R V) where
  allEq u v := by
    nontriviality R
    ext x
    by_cases hx : x = 0
    · simp [hx]
    suffices ∀ (u : SpecialLinearGroup R V), (u : V →ₗ[R] V) = LinearMap.id by
      simp only [LinearMap.ext_iff, LinearEquiv.coe_coe, LinearMap.id_coe, id_eq] at this
      simp [this u, this v]
    intro u
    ext x
    set c := (LinearEquiv.smul_id_of_finrank_eq_one d1).symm u with hc
    rw [LinearEquiv.eq_symm_apply] at hc
    suffices c = 1 by
      simp [← hc, LinearEquiv.smul_id_of_finrank_eq_one, this]
    have hu := u.prop
    simpa [← Units.val_inj, LinearEquiv.coe_det, ← hc,
      LinearEquiv.smul_id_of_finrank_eq_one, d1] using hu

end rankOne

/-
**SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `SpecialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (SpecialLinearGroup R V) :=
  ⟨fun A => ⟨A⁻¹, by simp [A.prop]⟩⟩
/-
**SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `SpecialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (SpecialLinearGroup R V) :=
  ⟨fun A B => ⟨A * B, by simp [A.prop, B.prop]⟩⟩
/-
**SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `SpecialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Div (SpecialLinearGroup R V) :=
  ⟨fun A B => ⟨A / B, by simp [A.prop, B.prop]⟩⟩
/-
**SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `SpecialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (SpecialLinearGroup R V) :=
  ⟨⟨1, by simp⟩⟩
/-
**SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `SpecialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (SpecialLinearGroup R V) ℕ where
  pow x n := ⟨x ^ n, by simp [x.prop]⟩
/-
**SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `SpecialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (SpecialLinearGroup R V) ℤ where
  pow x n := ⟨x ^ n, by simp [x.prop]⟩
/-
**SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `SpecialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (SpecialLinearGroup R V) :=
  ⟨1⟩

/-- The transpose of an element in `SpecialLinearGroup R V`. -/
/-
**SpecialLinearGroup.dualMap** 是 Mathlib 中的一个定义，位于命名空间 `SpecialLinearGroup`。
形式化陈述：dualMap [Module.Free R V] [Module.Finite R V] (A : SpecialLinearGroup R V)
 : SpecialLinearGroup R (Module.Dual R V)
参数：A : SpecialLinearGroup R V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transpose of an element in `SpecialLinearGroup R V`.
-/
def dualMap
    [Module.Free R V] [Module.Finite R V] (A : SpecialLinearGroup R V) :
    SpecialLinearGroup R (Module.Dual R V) :=
  ⟨LinearEquiv.dualMap (A : V ≃ₗ[R] V), by
    simp only [← Units.val_inj, LinearEquiv.coe_det, Units.val_one,
      LinearEquiv.dualMap, LinearMap.det_dualMap]
    simp [← LinearEquiv.coe_det, A.prop]⟩

@[inherit_doc]
scoped postfix:1024 "ᵀ" => SpecialLinearGroup.dualMap

section CoeLemmas

variable (A B : SpecialLinearGroup R V)

/-
**SpecialLinearGroup.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `SpecialLinearGroup`。
形式化陈述：coe_mk (A : V ≃ₗ[R] V) (h : A.det = 1) : ↑(⟨A, h⟩ : SpecialLinearGroup R V
) = A
参数：A : V ≃ₗ[R] V；h : A.det = 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (A : V ≃ₗ[R] V) (h : A.det = 1) : ↑(⟨A, h⟩ : SpecialLinearGroup R V) = A :=
  rfl

@[simp]
/-
**SpecialLinearGroup.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `SpecialLinearGroup`。
形式化陈述：coe_mul : (A * B : SpecialLinearGroup R V) = (A * B : V ≃ₗ[R] V)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul : (A * B : SpecialLinearGroup R V) = (A * B : V ≃ₗ[R] V) :=
  rfl

@[simp]
/-
**SpecialLinearGroup.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `SpecialLinearGroup`。
形式化陈述：coe_div : (A / B : SpecialLinearGroup R V) = (A / B : V ≃ₗ[R] V)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_div : (A / B : SpecialLinearGroup R V) = (A / B : V ≃ₗ[R] V) :=
  rfl

@[simp]
/-
**SpecialLinearGroup.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `SpecialLinearGroup`。
形式化陈述：coe_inv : (A : SpecialLinearGroup R V)⁻¹ = (A⁻¹ : V ≃ₗ[R] V)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv : (A : SpecialLinearGroup R V)⁻¹ = (A⁻¹ : V ≃ₗ[R] V) :=
  rfl

@[simp]
/-
**SpecialLinearGroup.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `SpecialLinearGroup`。
形式化陈述：coe_one : (1 : SpecialLinearGroup R V) = (1 : V ≃ₗ[R] V)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : (1 : SpecialLinearGroup R V) = (1 : V ≃ₗ[R] V) :=
  rfl

@[simp]
/-
**SpecialLinearGroup.det_coe** 是 Mathlib 中的一个定理，位于命名空间 `SpecialLinearGroup`。
形式化陈述：det_coe : LinearEquiv.det (A : V ≃ₗ[R] V) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem det_coe : LinearEquiv.det (A : V ≃ₗ[R] V) = 1 :=
  A.prop

@[simp]
/-
**SpecialLinearGroup.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `SpecialLinearGroup`。
形式化陈述：coe_pow (m : Nat) : (A ^ m : SpecialLinearGroup R V) = (A : V ≃ₗ[R] V) ^ m
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow (m : ℕ) : (A ^ m : SpecialLinearGroup R V) = (A : V ≃ₗ[R] V) ^ m :=
  rfl

@[simp]
/-
**SpecialLinearGroup.coe_zpow** 是 Mathlib 中的一个定理，位于命名空间 `SpecialLinearGroup`。
形式化陈述：coe_zpow (m : Int) : (A ^ m : SpecialLinearGroup R V) = (A : V ≃ₗ[R] V) ^ 
m
参数：m : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zpow (m : ℤ) : (A ^ m : SpecialLinearGroup R V) = (A : V ≃ₗ[R] V) ^ m :=
  rfl

@[simp]
/-
**SpecialLinearGroup.coe_dualMap** 是 Mathlib 中的一个定理，位于命名空间 `SpecialLinearGroup`。
形式化陈述：coe_dualMap [Module.Free R V] [Module.Finite R V] : Aᵀ = (A : V ≃ₗ[R] V).d
ualMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem coe_dualMap
    [Module.Free R V] [Module.Finite R V] :
    Aᵀ = (A : V ≃ₗ[R] V).dualMap :=
  rfl

end CoeLemmas

/-- The special linear group of a module is a group. -/
/-
**SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `SpecialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The special linear group of a module is a group.
-/
instance : Group (SpecialLinearGroup R V) := fast_instance%
  Function.Injective.group _ Subtype.coe_injective coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

/-- A version of `Matrix.toLin' A` that produces linear equivalences. -/
/-
**SpecialLinearGroup.toLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SpecialLinearGroup
`。
形式化陈述：toLinearEquiv : SpecialLinearGroup R V ->* V ≃ₗ[R] V where toFun A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SpecialLinearGroup.coe_one`：coe_one : (1 : SpecialLinearGroup R V) = (1 
: V ≃ₗ[R] V)
· 使用定理 `SpecialLinearGroup.coe_mul`：coe_mul : (A * B : SpecialLinearGroup R V) =
 (A * B : V ≃ₗ[R] V)

--- 原说明 ---
A version of `Matrix.toLin' A` that produces linear equivalences.
-/
def toLinearEquiv : SpecialLinearGroup R V →* V ≃ₗ[R] V where
  toFun A := A.val
  map_one' := coe_one
  map_mul' := coe_mul
/-
**SpecialLinearGroup.toLinearEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `SpecialLinea
rGroup`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 V] [inst_2 : _root_.Module R V]   (A : SpecialLinearGroup R V) (v : V), (Specia
lLinearGroup.toLinearEquiv A) v = (fun x => ↑A x) v
参数：A : SpecialLinearGroup R V；v : V；SpecialLinearGroup.toLinearEquiv A；fun x => 
↑A x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearEquiv_apply (A : SpecialLinearGroup R V) (v : V) :
    A.toLinearEquiv v = A v :=
  rfl

@[simp]
/-
**SpecialLinearGroup.toLinearEquiv_to_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `Speci
alLinearGroup`。
形式化陈述：toLinearEquiv_to_linearMap (A : SpecialLinearGroup R V) : (SpecialLinearGr
oup.toLinearEquiv A) = (A : V ->ₗ[R] V)
参数：A : SpecialLinearGroup R V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_to_linearMap (A : SpecialLinearGroup R V) :
    (SpecialLinearGroup.toLinearEquiv A) = (A : V →ₗ[R] V) :=
  rfl

@[simp]
/-
**SpecialLinearGroup.toLinearEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Special
LinearGroup`。
形式化陈述：toLinearEquiv_symm_apply (A : SpecialLinearGroup R V) (v : V) : A.toLinear
Equiv.symm v = A⁻¹ v
参数：A : SpecialLinearGroup R V；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_symm_apply (A : SpecialLinearGroup R V) (v : V) :
    A.toLinearEquiv.symm v = A⁻¹ v :=
  rfl

@[simp]
/-
**SpecialLinearGroup.toLinearEquiv_symm_to_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `
SpecialLinearGroup`。
形式化陈述：toLinearEquiv_symm_to_linearMap (A : SpecialLinearGroup R V) : A.toLinearE
quiv.symm = ((A⁻¹ : SpecialLinearGroup R V) : V ->ₗ[R] V)
参数：A : SpecialLinearGroup R V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_symm_to_linearMap (A : SpecialLinearGroup R V) :
    A.toLinearEquiv.symm = ((A⁻¹ : SpecialLinearGroup R V) : V →ₗ[R] V) :=
  rfl
/-
**SpecialLinearGroup.toLinearEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `SpecialL
inearGroup`。
形式化陈述：toLinearEquiv_injective : Function.Injective (toLinearEquiv : SpecialLinea
rGroup R V ->* V ≃ₗ[R] V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
theorem toLinearEquiv_injective :
    Function.Injective (toLinearEquiv : SpecialLinearGroup R V →* V ≃ₗ[R] V) :=
  Subtype.val_injective

/-- The canonical group morphism from the special linear group
to the general linear group. -/
/-
**SpecialLinearGroup.toGeneralLinearGroup** 是 Mathlib 中的一个定义，位于命名空间 `SpecialLine
arGroup`。
形式化陈述：toGeneralLinearGroup : SpecialLinearGroup R V ->* LinearMap.GeneralLinearG
roup R V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical group morphism from the special linear group
to the general linear group.
-/
def toGeneralLinearGroup : SpecialLinearGroup R V →* LinearMap.GeneralLinearGroup R V :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R V).symm.toMonoidHom.comp toLinearEquiv
/-
**SpecialLinearGroup.toGeneralLinearGroup_toLinearEquiv_apply** 是 Mathlib 中的一个引理
，位于命名空间 `SpecialLinearGroup`。
形式化陈述：toGeneralLinearGroup_toLinearEquiv_apply (u : SpecialLinearGroup R V) : u.
toGeneralLinearGroup.toLinearEquiv = u.toLinearEquiv
参数：u : SpecialLinearGroup R V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toGeneralLinearGroup_toLinearEquiv_apply (u : SpecialLinearGroup R V) :
    u.toGeneralLinearGroup.toLinearEquiv = u.toLinearEquiv := rfl
/-
**SpecialLinearGroup.coe_toGeneralLinearGroup_apply** 是 Mathlib 中的一个引理，位于命名空间 `S
pecialLinearGroup`。
形式化陈述：coe_toGeneralLinearGroup_apply (u : SpecialLinearGroup R V) : u.toGeneralL
inearGroup.val = u.toLinearEquiv
参数：u : SpecialLinearGroup R V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toGeneralLinearGroup_apply (u : SpecialLinearGroup R V) :
    u.toGeneralLinearGroup.val = u.toLinearEquiv := rfl
/-
**SpecialLinearGroup.toGeneralLinearGroup_injective** 是 Mathlib 中的一个引理，位于命名空间 `S
pecialLinearGroup`。
形式化陈述：toGeneralLinearGroup_injective : Function.Injective ⇑(toGeneralLinearGroup
 (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
-/
lemma toGeneralLinearGroup_injective :
    Function.Injective ⇑(toGeneralLinearGroup (R := R) (V := V)) := by
  simp [toGeneralLinearGroup, toLinearEquiv_injective]
/-
**SpecialLinearGroup.mem_range_toGeneralLinearGroup_iff** 是 Mathlib 中的一个引理，位于命名空
间 `SpecialLinearGroup`。
形式化陈述：mem_range_toGeneralLinearGroup_iff {u : LinearMap.GeneralLinearGroup R V} 
: u in Set.range ⇑(toGeneralLinearGroup (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SpecialLinearGroup.toGeneralLinearGroup_toLinearEquiv_apply`：toGeneralLi
nearGroup_toLinearEquiv_apply (u : SpecialLinearGroup R V) : u.toGeneralLinearGr
oup.toLinearEquiv = u.toLinearEquiv
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma mem_range_toGeneralLinearGroup_iff {u : LinearMap.GeneralLinearGroup R V} :
    u ∈ Set.range ⇑(toGeneralLinearGroup (R := R) (V := V)) ↔
      u.toLinearEquiv.det = 1 := by
  constructor
  · rintro ⟨v, hv⟩
    rw [← hv, toGeneralLinearGroup_toLinearEquiv_apply]
    exact v.prop
  · intro hu
    refine ⟨⟨u.toLinearEquiv, hu⟩, rfl⟩

/-- The natural action of `SpecialLinearGroup R V` on `V`. -/
/-
**SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `SpecialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural action of `SpecialLinearGroup R V` on `V`.
-/
instance : DistribMulAction (SpecialLinearGroup R V) V :=
  DistribMulAction.compHom  _ (SpecialLinearGroup.toLinearEquiv)
/-
**SpecialLinearGroup._root_.SpecialLinearGroup.smul_def** 是 Mathlib 中的一个定理，位于命名空
间 `SpecialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SpecialLinearGroup.smul_def (g : SpecialLinearGroup R V) (v : V) :
    g • v = g.toLinearEquiv • v := rfl
/-
**SpecialLinearGroup._root_.SpecialLinearGroup.toLinearEquiv_eq_coe** 是 Mathlib 
中的一个定理，位于命名空间 `SpecialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SpecialLinearGroup.toLinearEquiv_eq_coe (g : SpecialLinearGroup R V) :
    g.toLinearEquiv = (g : V ≃ₗ[R] V) := rfl
/-
**SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `SpecialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass (SpecialLinearGroup R V) R V where
  smul_comm g a v := by
    simp [SpecialLinearGroup.smul_def]

section baseChange

open TensorProduct

variable {S : Type*} [CommRing S] [Algebra R S]
  [Module.Free R V] [Module.Finite R V]

/-- By base change, an `R`-algebra `S` induces a group homomorphism from
`SpecialLinearGroup R V` to `SpecialLinearGroup S (S ⊗[R] V)`. -/
@[simps]
/-
**SpecialLinearGroup.baseChange** 是 Mathlib 中的一个定义，位于命名空间 `SpecialLinearGroup`。
形式化陈述：baseChange : SpecialLinearGroup R V ->* SpecialLinearGroup S (S otimes[R] 
V) where toFun g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
By base change, an `R`-algebra `S` induces a group homomorphism from
`SpecialLinearGroup R V` to `SpecialLinearGroup S (S ⊗[R] V)`.
-/
def baseChange : SpecialLinearGroup R V →* SpecialLinearGroup S (S ⊗[R] V) where
  toFun g := ⟨LinearEquiv.baseChange R S V V g, by
      rw [LinearEquiv.det_baseChange, g.prop, map_one]⟩
  map_one' := Subtype.ext <| by simp
  map_mul' x y := Subtype.ext <| by simp [LinearEquiv.baseChange_mul]

end baseChange

variable {W X : Type*} [AddCommGroup W] [Module R W] [AddCommGroup X] [Module R X]

/-- The isomorphism between special linear groups of isomorphic modules. -/
/-
**SpecialLinearGroup.congr_linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SpecialLinearG
roup`。
形式化陈述：congr_linearEquiv (e : V ≃ₗ[R] W) : SpecialLinearGroup R V ≃* SpecialLinea
rGroup R W where toFun f
参数：e : V ≃ₗ[R] W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between special linear groups of isomorphic modules.
-/
def congr_linearEquiv (e : V ≃ₗ[R] W) :
    SpecialLinearGroup R V ≃* SpecialLinearGroup R W where
  toFun f := ⟨e.symm ≪≫ₗ f ≪≫ₗ e, by simp [f.prop]⟩
  invFun g := ⟨e ≪≫ₗ g ≪≫ₗ e.symm, by
    nth_rewrite 1 [← LinearEquiv.symm_symm e]
    rw [LinearEquiv.det_conj g e.symm, g.prop]⟩
  left_inv f := Subtype.coe_injective <| by aesop
  right_inv g := Subtype.coe_injective <| by aesop
  map_mul' f g := Subtype.coe_injective <| by aesop

@[simp]
/-
**SpecialLinearGroup.congr_linearEquiv_coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `Spec
ialLinearGroup`。
形式化陈述：congr_linearEquiv_coe_apply (e : V ≃ₗ[R] W) (f : SpecialLinearGroup R V) :
 (congr_linearEquiv e f : W ≃ₗ[R] W) = e.symm ≪≫ₗ f ≪≫ₗ e
参数：e : V ≃ₗ[R] W；f : SpecialLinearGroup R V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_linearEquiv_coe_apply (e : V ≃ₗ[R] W) (f : SpecialLinearGroup R V) :
    (congr_linearEquiv e f : W ≃ₗ[R] W) = e.symm ≪≫ₗ f ≪≫ₗ e :=
  rfl

@[simp]
/-
**SpecialLinearGroup.congr_linearEquiv_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Sp
ecialLinearGroup`。
形式化陈述：congr_linearEquiv_apply_apply (e : V ≃ₗ[R] W) (f : SpecialLinearGroup R V)
 (x : W) : congr_linearEquiv e f x = e (f (e.symm x))
参数：e : V ≃ₗ[R] W；f : SpecialLinearGroup R V；x : W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_linearEquiv_apply_apply (e : V ≃ₗ[R] W) (f : SpecialLinearGroup R V) (x : W) :
    congr_linearEquiv e f x = e (f (e.symm x)) :=
  rfl
/-
**SpecialLinearGroup.congr_linearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `SpecialLi
nearGroup`。
形式化陈述：congr_linearEquiv_symm (e : V ≃ₗ[R] W) : (congr_linearEquiv e).symm = cong
r_linearEquiv e.symm
参数：e : V ≃ₗ[R] W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_linearEquiv_symm (e : V ≃ₗ[R] W) :
    (congr_linearEquiv e).symm = congr_linearEquiv e.symm :=
  rfl
/-
**SpecialLinearGroup.congr_linearEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `SpecialL
inearGroup`。
形式化陈述：congr_linearEquiv_trans (e : V ≃ₗ[R] W) (f : W ≃ₗ[R] X) : (congr_linearEqu
iv e).trans (congr_linearEquiv f) = congr_linearEquiv (e.trans f)
参数：e : V ≃ₗ[R] W；f : W ≃ₗ[R] X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_linearEquiv_trans (e : V ≃ₗ[R] W) (f : W ≃ₗ[R] X) :
    (congr_linearEquiv e).trans (congr_linearEquiv f) = congr_linearEquiv (e.trans f) := by
  rfl
/-
**SpecialLinearGroup.congr_linearEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `SpecialLi
nearGroup`。
形式化陈述：congr_linearEquiv_refl : congr_linearEquiv (LinearEquiv.refl R V) = MulEqu
iv.refl _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_linearEquiv_refl :
    congr_linearEquiv (LinearEquiv.refl R V) = MulEquiv.refl _ := by
  rfl

end SpecialLinearGroup

namespace Matrix.SpecialLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n R V)

/-- The canonical isomorphism from `SL(n, R)` to the special linear group of the module `n → R`. -/
/-
**Matrix.SpecialLinearGroup.toLin'_equiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.Speci
alLinearGroup`。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] →     {n : Type u_3} →       [inst_
1 : Fintype n] → [inst_2 : DecidableEq n] → Matrix.SpecialLinearGroup n R ≃* Spe
cialLinearGroup R (n → R)
参数：n → R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star

--- 原说明 ---
The canonical isomorphism from `SL(n, R)` to the special linear group of the mod
ule `n → R`.
-/
def toLin'_equiv : SpecialLinearGroup n R ≃* _root_.SpecialLinearGroup R (n → R) where
  toFun A := ⟨Matrix.SpecialLinearGroup.toLin' A,
    by
      simp [← Units.val_inj, LinearEquiv.coe_det, Units.val_one,
        Matrix.SpecialLinearGroup.toLin'_to_linearMap]⟩
  invFun u := ⟨LinearMap.toMatrix' u,
      by simp [← LinearEquiv.coe_det, u.prop]⟩
  left_inv A := Subtype.coe_injective <| by
    rw [← LinearEquiv.eq_symm_apply, LinearMap.toMatrix'_symm,
      Matrix.SpecialLinearGroup.toLin'_to_linearMap]
  right_inv u := Subtype.coe_injective <| by
    simp [← LinearEquiv.toLinearMap_inj, Matrix.SpecialLinearGroup.toLin']
  map_mul' A B := Subtype.coe_injective (by simp)

/-- The isomorphism from `Matrix.SpecialLinearGroup n R`
to the special linear group of a module associated with a basis of that module. -/
/-
**Matrix.SpecialLinearGroup.toLin_equiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.Specia
lLinearGroup`。
形式化陈述：toLin_equiv (b : Module.Basis n R V) : SpecialLinearGroup n R ≃* _root_.Sp
ecialLinearGroup R V
参数：b : Module.Basis n R V。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
The isomorphism from `Matrix.SpecialLinearGroup n R`
to the special linear group of a module associated with a basis of that module.
-/
noncomputable def toLin_equiv (b : Module.Basis n R V) :
    SpecialLinearGroup n R ≃* _root_.SpecialLinearGroup R V :=
  SpecialLinearGroup.toLin'_equiv.trans
    (SpecialLinearGroup.congr_linearEquiv b.equivFun.symm)
/-
**Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq** 是 Mathlib 中的一个定理，位于命名空间
 `Matrix.SpecialLinearGroup.toLin_equiv`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 V] [inst_2 : _root_.Module R V]   {n : Type u_3} [inst_3 : Fintype n] [inst_4 :
 DecidableEq n] (b : Module.Basis n R V)   (g : Matrix.SpecialLinearGroup n R), 
↑↑((Matrix.SpecialLinearGroup.toLin_equiv b) g) = (Matrix.toLin b b) ↑g
参数：b : Module.Basis n R V；g : Matrix.SpecialLinearGroup n R；(Matrix.SpecialLinea
rGroup.toLin_equiv b) g；Matrix.toLin b b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLin_equiv.toLinearMap_eq
    (b : Module.Basis n R V) (g : Matrix.SpecialLinearGroup n R) :
    (toLin_equiv b g : V →ₗ[R] V) = (Matrix.toLin b b g) :=
  rfl
/-
**Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq** 是 Mathlib 中的一个定理，位
于命名空间 `Matrix.SpecialLinearGroup.toLin_equiv`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 V] [inst_2 : _root_.Module R V]   {n : Type u_3} [inst_3 : Fintype n] [inst_4 :
 DecidableEq n] (b : Module.Basis n R V) (g : SpecialLinearGroup R V),   ↑((Matr
ix.SpecialLinearGroup.toLin_equiv b).symm g) = (LinearMap.toMatrix b b) ↑↑g
参数：b : Module.Basis n R V；g : SpecialLinearGroup R V；(Matrix.SpecialLinearGroup.
toLin_equiv b).symm g；LinearMap.toMatrix b b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLin_equiv.symm_toLinearMap_eq
    (b : Module.Basis n R V) (g : _root_.SpecialLinearGroup R V) :
    ((toLin_equiv b).symm g : Matrix n n R) = LinearMap.toMatrix b b g :=
  rfl

end Matrix.SpecialLinearGroup

namespace SpecialLinearGroup

section center

variable [Module.Free R V] [Module.Finite R V]

/-
**SpecialLinearGroup.center_eq_bot_of_finrank_le_one** 是 Mathlib 中的一个定理，位于命名空间 `
SpecialLinearGroup`。
形式化陈述：center_eq_bot_of_finrank_le_one (h : Module.finrank R V <= 1) : Subgroup.c
enter (SpecialLinearGroup R V) = ⊥
参数：h : Module.finrank R V <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finite.card_le_one_iff_subsingleton`：card_le_one_iff_subsingleton [Finit
e α] : Nat.card α <= 1 ↔ Subsingleton α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Subgroup.eq_bot_of_subsingleton`：eq_bot_of_subsingleton [Subsingleton H]
 : H = ⊥
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
-/
theorem center_eq_bot_of_finrank_le_one (h : Module.finrank R V ≤ 1) :
    Subgroup.center (SpecialLinearGroup R V) = ⊥ := by
  nontriviality R
  let b := Module.Free.chooseBasis R V
  have : Subsingleton (Module.Free.ChooseBasisIndex R V) := by
    rwa [← Finite.card_le_one_iff_subsingleton,
      Nat.card_eq_fintype_card, ← Module.finrank_eq_card_basis b]
  have : Subsingleton (Subgroup.center
    (Matrix.SpecialLinearGroup (Module.Free.ChooseBasisIndex R V) R)) := by
    infer_instance
  rw [Equiv.subsingleton_congr
    (Subgroup.centerCongr (Matrix.SpecialLinearGroup.toLin_equiv b)).toEquiv] at this
  exact Subgroup.eq_bot_of_subsingleton _
/-
**SpecialLinearGroup.mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 `SpecialLinearGrou
p`。
形式化陈述：mem_center_iff {g : SpecialLinearGroup R V} : g in Subgroup.center (Specia
lLinearGroup R V) ↔ exists (r : R), r ^ (Module.finrank R V) = 1 ∧ (g : V ->ₗ[R]
 V) = r • LinearMap.id
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.eq_one`：Subsingleton.eq_one [One α] [Subsingleton α] (a : α
) : a = 1
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.finrank_subsingleton`：∀ {R : Type u} {M : Type v} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Subsingleton R],
 Module.finrank R…
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulEquivClass.apply_mem_center_iff`：∀ {M : Type u_3} {N : Type u_1} {F :
 Type u_2} [inst : EquivLike F M N] [inst_1 : Mul M] [inst_2 : Mul N]   [MulEqui
vClass F M N] (e : F) {x…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Matrix.SpecialLinearGroup.mem_center_iff`：mem_center_iff {A : SpecialLin
earGroup n R} : A in center (SpecialLinearGroup n R) ↔ exists (r : R), r ^ (Fint
ype.card n) = 1 ∧ scalar n r =…
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
（共 46 条，此处仅展示前 30 条）
-/
theorem mem_center_iff {g : SpecialLinearGroup R V} :
    g ∈ Subgroup.center (SpecialLinearGroup R V) ↔
      ∃ (r : R), r ^ (Module.finrank R V) = 1 ∧
        (g : V →ₗ[R] V) = r • LinearMap.id := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : Subsingleton (SpecialLinearGroup R V) := inferInstance
    simp [Subsingleton.eq_one g]
  let b := Module.Free.chooseBasis R V
  let := Module.Free.ChooseBasisIndex.fintype R V
  rw [Module.finrank_eq_card_basis b]
  let e := (Matrix.SpecialLinearGroup.toLin_equiv b).symm
  rw [← show e g ∈ Subgroup.center _ ↔ g ∈ Subgroup.center _ from
    MulEquivClass.apply_mem_center_iff e]
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  apply exists_congr
  simp only [Matrix.scalar_apply, and_congr_right_iff, e]
  intro r hr
  suffices ((Matrix.SpecialLinearGroup.toLin_equiv b).symm g) =
    Matrix.of fun i j ↦ (b.repr (g (b j))) i by
    simp only [this]
    rw [← (LinearMap.toMatrix b b).injective.eq_iff]
    simp only [← Matrix.ext_iff, Matrix.of_apply]
    apply forall₂_congr
    intro i j
    simp [Matrix.diagonal, LinearMap.toMatrix_apply,
      Finsupp.single, Pi.single_apply, Iff.symm eq_comm]
  ext
  simp [Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq, LinearMap.toMatrix_apply]
/-
**SpecialLinearGroup.mem_center_iff_spec** 是 Mathlib 中的一个定理，位于命名空间 `SpecialLinea
rGroup`。
形式化陈述：mem_center_iff_spec {g : SpecialLinearGroup R V} (hg : g in Subgroup.cente
r (SpecialLinearGroup R V)) (x : V) : (g : V ->ₗ[R] V) x = (mem_center_iff.mp hg
).choose • x
参数：hg : g in Subgroup.center (SpecialLinearGroup R V)；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SpecialLinearGroup.mem_center_iff`：mem_center_iff {g : SpecialLinearGrou
p R V} : g in Subgroup.center (SpecialLinearGroup R V) ↔ exists (r : R), r ^ (Mo
dule.finrank R V) = 1 ∧…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mem_center_iff_spec {g : SpecialLinearGroup R V}
    (hg : g ∈ Subgroup.center (SpecialLinearGroup R V)) (x : V) :
    (g : V →ₗ[R] V) x = (mem_center_iff.mp hg).choose • x := by
  let H := (mem_center_iff.mp hg).choose_spec.2
  rw [LinearMap.ext_iff] at H
  simp [H]

/- TODO : delete this auxiliary definition
and put it in the definition of `centerEquivRootsOfUnity.
How can one access to the definition of one already defined term in a structure
while one is still defining it? -/
/-- The inverse map for the equivalence `SpecialLinearGroup.centerEquivRootsOfUnity`. -/
/-
**SpecialLinearGroup.centerEquivRootsOfUnity_invFun** 是 Mathlib 中的一个定义，位于命名空间 `S
pecialLinearGroup`。
形式化陈述：centerEquivRootsOfUnity_invFun (r : rootsOfUnity (max (Module.finrank R V)
 1) R) : Subgroup.center (SpecialLinearGroup R V)
参数：r : rootsOfUnity (max (Module.finrank R V) 1) R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse map for the equivalence `SpecialLinearGroup.centerEquivRootsOfUnity`
.
-/
noncomputable def centerEquivRootsOfUnity_invFun
    (r : rootsOfUnity (max (Module.finrank R V) 1) R) :
    Subgroup.center (SpecialLinearGroup R V) :=
  ⟨⟨LinearMap.equivOfIsUnitDet (M := V) (R := R) (f := ((r : Rˣ) : R) • LinearMap.id) (by
    simp [LinearMap.det_smul, IsUnit.pow]), by
    simp only [← Units.val_inj, LinearEquiv.coe_det, LinearMap.coe_equivOfIsUnitDet,
      LinearMap.det_smul, LinearMap.det_id, mul_one, Units.val_one]
    have := (mem_rootsOfUnity' _ _).mp r.prop
    rcases max_cases (Module.finrank R V) 1 with ⟨h, h'⟩ |  ⟨h, h'⟩
    · simp_rw [h] at this
      exact this
    · simp_rw [h, pow_one] at this
      simp [this]⟩, by
    simp only [mem_center_iff, LinearMap.coe_equivOfIsUnitDet]
    use r.val
    simp only [and_true]
    let ⟨r, hr⟩ := r
    by_cases hV : Module.finrank R V = 0
    · simp [hV]
    · rw [← ne_eq, ← Nat.one_le_iff_ne_zero] at hV
      rw [mem_rootsOfUnity', max_eq_left hV] at hr
      simpa [← Subtype.val_inj, ← Units.val_inj]⟩

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- The isomorphism between the roots of unity and the center of the special linear group. -/
/-
**SpecialLinearGroup.centerEquivRootsOfUnity** 是 Mathlib 中的一个定义，位于命名空间 `SpecialL
inearGroup`。
形式化陈述：centerEquivRootsOfUnity : (Subgroup.center (SpecialLinearGroup R V)) ≃* ↥(
rootsOfUnity (max (Module.finrank R V) 1) R) where toFun g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α

--- 原说明 ---
The isomorphism between the roots of unity and the center of the special linear 
group.
-/
noncomputable def centerEquivRootsOfUnity :
    (Subgroup.center (SpecialLinearGroup R V)) ≃*
      ↥(rootsOfUnity (max (Module.finrank R V) 1) R) where
  toFun g := (subsingleton_or_nontrivial R).by_cases
    (fun _ ↦ 1)
    (fun hR ↦ (subsingleton_or_nontrivial V).by_cases
      (fun _ ↦ 1)
      (fun hV ↦ by
        rw [← Module.finrank_pos_iff_of_free (R := R)] at hV
        replace hV : 1 ≤ Module.finrank R V := hV
        have hr := (mem_center_iff.mp g.prop).choose_spec.1
        set r := (mem_center_iff.mp g.prop).choose
        rw [← Nat.max_eq_left hV] at hr
        have : IsUnit r := by
          rw [← isUnit_pow_iff _, hr]
          · exact isUnit_one
          rw [Nat.max_eq_left hV]
          exact Nat.ne_zero_of_lt hV
        exact ⟨this.unit, by simp [mem_rootsOfUnity, ← Units.val_inj, hr]⟩))
  invFun := centerEquivRootsOfUnity_invFun
  left_inv g := by
    simp only [centerEquivRootsOfUnity_invFun, ← Subtype.val_inj,
      ← LinearEquiv.toLinearMap_inj, LinearMap.coe_equivOfIsUnitDet]
    simp only [Or.by_cases]
    split_ifs with hR hV
    · simp [Subsingleton.eq_one g]
    · simp [Subsingleton.eq_one g]
    · simp only [IsUnit.unit_spec, ← (mem_center_iff.mp g.prop).choose_spec.2]
  right_inv r := by
    rw [← Subtype.val_inj, SetLike.coe_eq_coe]
    simp only [Or.by_cases]
    split_ifs with hR hV
    · simp [Subsingleton.eq_one r]
    · replace hR := not_subsingleton_iff_nontrivial.mp hR
      symm
      rw [← Module.finrank_eq_zero_iff_of_free (R := R)] at hV
      simpa [hV] using (mem_rootsOfUnity _ _).mp r.prop
    · rw [not_subsingleton_iff_nontrivial] at hV
      have := Module.Free.instFaithfulSMulOfNontrivial R V
      simp only [← Subtype.val_inj, ← Units.val_inj, IsUnit.unit_spec]
      have H := mem_center_iff.mp (Subtype.prop (centerEquivRootsOfUnity_invFun r))
      suffices (H.choose • LinearMap.id : V →ₗ[R] V) = (r.val : R) • LinearMap.id by
        apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
        intro x
        rw [LinearMap.ext_iff] at this
        simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq] at this
        rw [this x]
      rw [← H.choose_spec.2]
      simp [centerEquivRootsOfUnity_invFun]
  map_mul' g h := by
    simp only [Or.by_cases, Subgroup.coe_mul, coe_mul, LinearEquiv.coe_toLinearMap_mul,
      mul_dite, mul_one, dite_mul, one_mul, MulMemClass.mk_mul_mk]
    split_ifs with hR hV
    · rfl
    · rfl
    rw [not_subsingleton_iff_nontrivial] at hV
    have := Module.Free.instFaithfulSMulOfNontrivial R V
    set Hg := (mem_center_iff.mp g.prop)
    set Hh := (mem_center_iff.mp h.prop)
    set Hgh := (mem_center_iff.mp (g * h).prop)
    simp only [← Subtype.val_inj, ← Units.val_inj, IsUnit.unit_spec, Units.val_mul]
    change Hgh.choose = Hg.choose * Hh.choose
    suffices (Hgh.choose • LinearMap.id : V →ₗ[R] V)
      = (Hg.choose • LinearMap.id) * (Hh.choose • LinearMap.id) by
      apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
      intro x
      simp [mul_smul,
        ← mem_center_iff_spec (g * h).prop, ← mem_center_iff_spec h.prop,
        ← mem_center_iff_spec g.prop]
    simp [← Hgh.choose_spec.2, ← Hh.choose_spec.2, ← Hg.choose_spec.2]
/-
**SpecialLinearGroup.centerEquivRootsOfUnity_apply** 是 Mathlib 中的一个定理，位于命名空间 `Sp
ecialLinearGroup`。
形式化陈述：centerEquivRootsOfUnity_apply (g : Subgroup.center (SpecialLinearGroup R V
)) : (g : V ->ₗ[R] V) = (centerEquivRootsOfUnity g) • LinearMap.id
参数：g : Subgroup.center (SpecialLinearGroup R V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `dite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) 
[inst_1 : Decidable p] (a : α) (b : p → β) (c : ¬p → β),   (if h : p then b h e…
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
· 使用定理 `Subsingleton.eq_one`：Subsingleton.eq_one [One α] [Subsingleton α] (a : α
) : a = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SpecialLinearGroup.mem_center_iff`：mem_center_iff {g : SpecialLinearGrou
p R V} : g in Subgroup.center (SpecialLinearGroup R V) ↔ exists (r : R), r ^ (Mo
dule.finrank R V) = 1 ∧…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem centerEquivRootsOfUnity_apply
    (g : Subgroup.center (SpecialLinearGroup R V)) :
    (g : V →ₗ[R] V) = (centerEquivRootsOfUnity g) • LinearMap.id := by
  simp only [centerEquivRootsOfUnity, Or.by_cases, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    dite_smul, one_smul, Subgroup.mk_smul, Units.smul_isUnit, dite_eq_ite]
  split_ifs with hR hV
  · have : Subsingleton V := Module.subsingleton R V
    apply Subsingleton.eq_one
  · apply Subsingleton.eq_one
  · rw [not_subsingleton_iff_nontrivial] at hV
    rw [← (mem_center_iff.mp g.prop).choose_spec.2]
/-
**SpecialLinearGroup.centerEquivRootsOfUnity_apply_apply** 是 Mathlib 中的一个定理，位于命名
空间 `SpecialLinearGroup`。
形式化陈述：centerEquivRootsOfUnity_apply_apply (g : Subgroup.center (SpecialLinearGro
up R V)) (x : V) : (centerEquivRootsOfUnity g) • x = (g : SpecialLinearGroup R V
) x
参数：g : Subgroup.center (SpecialLinearGroup R V)；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.coe_toLinearMap`：coe_toLinearMap : ⇑e.toLinearMap = e
· 使用定理 `SpecialLinearGroup.centerEquivRootsOfUnity_apply`：centerEquivRootsOfUnit
y_apply (g : Subgroup.center (SpecialLinearGroup R V)) : (g : V ->ₗ[R] V) = (cen
terEquivRootsOfUnity g) • LinearMap.id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem centerEquivRootsOfUnity_apply_apply
    (g : Subgroup.center (SpecialLinearGroup R V)) (x : V) :
    (centerEquivRootsOfUnity g) • x = (g : SpecialLinearGroup R V) x := by
  simp only
  rw [← LinearEquiv.coe_toLinearMap, centerEquivRootsOfUnity_apply]
  simp
/-
**SpecialLinearGroup._root_.rootsOfUnity.eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Speci
alLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.rootsOfUnity.eq_one {n : ℕ} {r : rootsOfUnity n R}
    (hn : n = 1) : r.val = 1 := by
  have h := r.prop
  simpa only [mem_rootsOfUnity, hn, pow_one] using h
/-
**SpecialLinearGroup.centerEquivRootsOfUnity_apply_of_finrank_le_one** 是 Mathlib
 中的一个定理，位于命名空间 `SpecialLinearGroup`。
形式化陈述：centerEquivRootsOfUnity_apply_of_finrank_le_one (d1 : Module.finrank R V <
= 1) (g : Subgroup.center (SpecialLinearGroup R V)) : centerEquivRootsOfUnity g 
= 1
参数：d1 : Module.finrank R V <= 1；g : Subgroup.center (SpecialLinearGroup R V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `OneMemClass.coe_one`：coe_one : ((1 : S') : M₁) = 1
· 使用定理 `rootsOfUnity.eq_one`：∀ {R : Type u_1} [inst : CommRing R] {n : ℕ} {r : ↥
(rootsOfUnity n R)}, n = 1 → ↑r = 1
· 使用定理 `Nat.max_eq_right`：∀ {a b : ℕ}, a ≤ b → max a b = b
-/
theorem centerEquivRootsOfUnity_apply_of_finrank_le_one
    (d1 : Module.finrank R V ≤ 1) (g : Subgroup.center (SpecialLinearGroup R V)) :
    centerEquivRootsOfUnity g = 1 := by
  rw [← Subtype.coe_inj, OneMemClass.coe_one]
  apply rootsOfUnity.eq_one
  rw [Nat.max_eq_right d1]

set_option backward.isDefEq.respectTransparency.types false in
/-
**SpecialLinearGroup.centerEquivRootsOfUnity_symm_apply** 是 Mathlib 中的一个定理，位于命名空
间 `SpecialLinearGroup`。
形式化陈述：centerEquivRootsOfUnity_symm_apply (r : rootsOfUnity (max (Module.finrank 
R V) 1) R) : (centerEquivRootsOfUnity.symm r : V ->ₗ[R] V) = r • LinearMap.id
参数：r : rootsOfUnity (max (Module.finrank R V) 1) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.coe_equivOfIsUnitDet`：LinearMap.coe_equivOfIsUnitDet [Module.F
ree R M] [Module.Finite R M] {f : M ->ₗ[R] M} (h : IsUnit f.det) : (LinearMap.eq
uivOfIsUnitDet h : M…
-/
theorem centerEquivRootsOfUnity_symm_apply
    (r : rootsOfUnity (max (Module.finrank R V) 1) R) :
    (centerEquivRootsOfUnity.symm r : V →ₗ[R] V) = r • LinearMap.id := by
  simp only [centerEquivRootsOfUnity, MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk,
    centerEquivRootsOfUnity_invFun, LinearMap.coe_equivOfIsUnitDet]
  congr

section

open Subgroup Matrix Matrix.SpecialLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

variable {V : Type*} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R V)

-- compare with `Matrix.SpecialLinearGroup.centerEquivRootsOfUnity`
-- TODO : golf!
/-
**SpecialLinearGroup.centerCongr_toLin_equiv_trans_centerEquivRootsOfUnity_eq** 
是 Mathlib 中的一个定理，位于命名空间 `SpecialLinearGroup`。
形式化陈述：centerCongr_toLin_equiv_trans_centerEquivRootsOfUnity_eq (g) : ((centerCon
gr (toLin_equiv b)).trans centerEquivRootsOfUnity g).val = Matrix.SpecialLinearG
roup.center_equiv_rootsOfUnity g
参数：g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `rootsOfUnity.eq_one`：∀ {R : Type u_1} [inst : CommRing R] {n : ℕ} {r : ↥
(rootsOfUnity n R)}, n = 1 → ↑r = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_eq_zero_iff_of_free`：finrank_eq_zero_iff_of_free [Module.
Free R M] [Module.Finite R M] : Module.finrank R M = 0 ↔ Subsingleton M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `Fintype.card_of_isEmpty`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α]
, Fintype.card α = 0
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
· 使用定理 `Subgroup.centerCongr_apply_coe`：∀ {G : Type u_1} [inst : Group G] {H : T
ype u_2} [inst_1 : Group H] (e : G ≃* H) (r : ↥(Subsemigroup.center G)),   ↑((Su
bgroup.centerCongr e…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `SpecialLinearGroup.centerEquivRootsOfUnity_apply_apply`：centerEquivRoots
OfUnity_apply_apply (g : Subgroup.center (SpecialLinearGroup R V)) (x : V) : (ce
nterEquivRootsOfUnity g) • x = (g : SpecialL…
· 使用定理 `LinearEquiv.coe_toLinearMap`：coe_toLinearMap : ⇑e.toLinearMap = e
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `LinearEquiv.toLinearMap_inj`：toLinearMap_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : (↑e
₁ : M ->ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq`：∀ {R : Type u_1} {
V : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Mod
ule R V]   {n : Type u_3} [inst_3 : Fintyp…
· 使用定理 `Matrix.SpecialLinearGroup.eq_scalar_center_equiv_rootsOfUnity`：eq_scalar
_center_equiv_rootsOfUnity (A : center (SpecialLinearGroup n R)) : A = scalar n 
((Matrix.SpecialLinearGroup.center_equiv_rootsOfUni…
· 使用定理 `Matrix.toLin_scalar`：Matrix.toLin_scalar (r : R) : Matrix.toLin v₁ v₁ (s
calar n r) = r • LinearMap.id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Units.val_inj`：val_inj {a b : αˣ} : (a : α) = b ↔ a = b
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `MulEquiv.trans_apply`：trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (m : M) : 
e₁.trans e₂ m = e₂ (e₁ m)
-/
theorem centerCongr_toLin_equiv_trans_centerEquivRootsOfUnity_eq (g) :
    ((centerCongr (toLin_equiv b)).trans centerEquivRootsOfUnity g).val =
      Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity g := by
  nontriviality R
  by_cases hV : Subsingleton V
  · convert! Eq.refl (1 : Rˣ) <;>
    · apply rootsOfUnity.eq_one
      rw [← Module.finrank_eq_zero_iff_of_free (R := R)] at hV
      simp only [hV, sup_eq_right, zero_le_one, ← Module.finrank_eq_card_basis b]
  · have hι : ¬ IsEmpty ι := fun hι ↦ hV (by
      rw [← Module.finrank_eq_zero_iff_of_free (R := R),
        Module.finrank_eq_card_basis b, Fintype.card_of_isEmpty])
    rw [not_subsingleton_iff_nontrivial] at hV
    have := Module.Free.instFaithfulSMulOfNontrivial R V
    suffices (((((Subgroup.centerCongr (Matrix.SpecialLinearGroup.toLin_equiv b)).trans
      centerEquivRootsOfUnity g).val : R) • LinearMap.id) : V →ₗ[R] V) =
        ((Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity g).val : R) • LinearMap.id by
      rw [← Units.val_inj]
      apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
      intro x
      simp only [MulEquiv.trans_apply, LinearMap.ext_iff, LinearMap.smul_apply, LinearMap.id_coe,
        id_eq] at this
      rw [MulEquiv.trans_apply, this]
    simp only [MulEquiv.trans_apply]
    have hgg' := Subgroup.centerCongr_apply_coe (Matrix.SpecialLinearGroup.toLin_equiv b) g
    rw [← Subtype.coe_inj, ← LinearEquiv.toLinearMap_inj, LinearMap.ext_iff] at hgg'
    set g' := ((Subgroup.centerCongr (Matrix.SpecialLinearGroup.toLin_equiv b)) g)
    ext x
    have := centerEquivRootsOfUnity_apply_apply g' x
    simp only [Subgroup.smul_def, Units.smul_def] at this
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    rw [this, ← LinearEquiv.coe_toLinearMap, hgg',
      Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq,
      Matrix.SpecialLinearGroup.eq_scalar_center_equiv_rootsOfUnity g,
      Matrix.toLin_scalar]
    simp

end

end center

end SpecialLinearGroup

