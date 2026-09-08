/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.RingTheory.Coalgebra.Hom

/-!
# Isomorphisms of `R`-coalgebras

This file defines bundled isomorphisms of `R`-coalgebras. We largely mirror the basic API of
`Mathlib/Algebra/Module/Equiv/Defs.lean`.

## Main definitions

* `CoalgEquiv R A B`: the type of `R`-coalgebra isomorphisms between `A` and `B`.

## Notation

* `A ≃ₗc[R] B` : `R`-coalgebra equivalence from `A` to `B`.
-/

@[expose] public section

universe u v w

variable {R A B C : Type*}

open Coalgebra

/-- An equivalence of coalgebras is an invertible coalgebra homomorphism. -/
/-
**CoalgEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_5) →   [inst : CommSemiring R] →     (A : Type u_6) →       (B
 : Type u_7) →         [inst_1 : AddCommMonoid A] →           [inst_2 : AddCommM
onoid B] →             [inst_3 : _root_.Module R A] →               [inst_4 : _r
oot_.Module R B] → [CoalgebraStruct R A] → [CoalgebraStruct R B] → Type (max u_6
 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of coalgebras is an invertible coalgebra homomorphism.
-/
structure CoalgEquiv (R : Type*) [CommSemiring R] (A B : Type*)
    [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] extends A →ₗc[R] B, A ≃ₗ[R] B where

attribute [nolint docBlame] CoalgEquiv.toCoalgHom
attribute [nolint docBlame] CoalgEquiv.toLinearEquiv

@[inherit_doc CoalgEquiv]
notation:50 A " ≃ₗc[" R "] " B => CoalgEquiv R A B

/-- `CoalgEquivClass F R A B` asserts `F` is a type of bundled coalgebra equivalences
from `A` to `B`. -/
/-
**CoalgEquivClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_5) →   (R : outParam (Type u_6)) →     (A : outParam (Type u_7
)) →       (B : outParam (Type u_8)) →         [inst : CommSemiring R] →        
   [inst_1 : AddCommMonoid A] →             [inst_2 : AddCommMonoid B] →        
       [inst_3 : _root_.Module R A] →                 [inst_4 : _root_.Module R 
B] → [CoalgebraStruct R A] → [CoalgebraStruct R B] → [EquivLike F A B] → Prop
参数：Type u_6；Type u_7；Type u_8。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CoalgEquivClass F R A B` asserts `F` is a type of bundled coalgebra equivalence
s
from `A` to `B`.
-/
class CoalgEquivClass (F : Type*) (R A B : outParam Type*) [CommSemiring R]
    [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] [EquivLike F A B] : Prop
    extends CoalgHomClass F R A B, SemilinearEquivClass F (RingHom.id R) A B

namespace CoalgEquivClass

variable {F R A B : Type*} [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B] [CoalgebraStruct R A] [CoalgebraStruct R B]

/-- Reinterpret an element of a type of coalgebra equivalences as a coalgebra equivalence. -/
@[coe]
/-
**CoalgEquivClass.toCoalgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CoalgEquivClass`。
形式化陈述：toCoalgEquiv [EquivLike F A B] [CoalgEquivClass F R A B] (f : F) : A ≃ₗc[R
] B
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgEquivClass.toCoalgHomClass`：∀ {F : Type u_5} {R : outParam (Type u_
6)} {A : outParam (Type u_7)} {B : outParam (Type u_8)} {inst : CommSemiring R} 
  {inst_1 : AddCommMo…
· 使用定理 `CoalgEquivClass.toSemilinearEquivClass`：∀ {F : Type u_5} {R : outParam (
Type u_6)} {A : outParam (Type u_7)} {B : outParam (Type u_8)} [inst : CommSemir
ing R]   [inst_1 : AddCommMo…

--- 原说明 ---
Reinterpret an element of a type of coalgebra equivalences as a coalgebra equiva
lence.
-/
def toCoalgEquiv [EquivLike F A B] [CoalgEquivClass F R A B] (f : F) : A ≃ₗc[R] B :=
  { (f : A →ₗc[R] B), (SemilinearEquivClass.semilinearEquiv f : A ≃ₗ[R] B) with }

/-- Reinterpret an element of a type of coalgebra equivalences as a coalgebra equivalence. -/
/-
**CoalgEquivClass.instCoeToCoalgEquiv** 是 Mathlib 中的一个实例，位于命名空间 `CoalgEquivClass
`。
形式化陈述：instCoeToCoalgEquiv [EquivLike F A B] [CoalgEquivClass F R A B] : CoeHead 
F (A ≃ₗc[R] B) where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an element of a type of coalgebra equivalences as a coalgebra equiva
lence.
-/
instance instCoeToCoalgEquiv
    [EquivLike F A B] [CoalgEquivClass F R A B] : CoeHead F (A ≃ₗc[R] B) where
  coe f := toCoalgEquiv f

end CoalgEquivClass

namespace CoalgEquiv

variable [CommSemiring R]

section

variable [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B]

/-- The equivalence of types underlying a coalgebra equivalence. -/
/-
**CoalgEquiv.toEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CoalgEquiv`。
形式化陈述：toEquiv : (A ≃ₗc[R] B) -> A ≃ B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of types underlying a coalgebra equivalence.
-/
def toEquiv : (A ≃ₗc[R] B) → A ≃ B := fun f => f.toLinearEquiv.toEquiv
/-
**CoalgEquiv.toEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：toEquiv_injective : Function.Injective (toEquiv : (A ≃ₗc[R] B) -> A ≃ B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgEquiv.mk.injEq`：∀ {R : Type u_5} [inst : CommSemiring R] {A : Type 
u_6} {B : Type u_7} [inst_1 : AddCommMonoid A]   [inst_2 : AddCommMonoid B] [ins
t_3 : _ro…
· 使用定理 `CoalgHom.ext`：ext {φ₁ φ₂ : A ->ₗc[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁
 = φ₂
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Equiv.mk.inj`：∀ {α : Sort u_1} {β : Sort u_2} {toFun : α → β} {invFun : 
β → α}   {left_inv : autoParam (Function.LeftInverse invFun toFun) Equiv.left_in
v.…
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem toEquiv_injective : Function.Injective (toEquiv : (A ≃ₗc[R] B) → A ≃ B) :=
  fun ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h =>
    (CoalgEquiv.mk.injEq _ _ _ _ _ _ _ _).mpr
      ⟨CoalgHom.ext (congr_fun (Equiv.mk.inj h).1), (Equiv.mk.inj h).2⟩

@[simp]
/-
**CoalgEquiv.toEquiv_inj** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：toEquiv_inj {e₁ e₂ : A ≃ₗc[R] B} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `CoalgEquiv.toEquiv_injective`：toEquiv_injective : Function.Injective (to
Equiv : (A ≃ₗc[R] B) -> A ≃ B)
-/
theorem toEquiv_inj {e₁ e₂ : A ≃ₗc[R] B} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff
/-
**CoalgEquiv.toCoalgHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：toCoalgHom_injective : Function.Injective (toCoalgHom : (A ≃ₗc[R] B) -> A 
->ₗc[R] B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgEquiv.toEquiv_injective`：toEquiv_injective : Function.Injective (to
Equiv : (A ≃ₗc[R] B) -> A ≃ B)
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `CoalgHom.congr_fun`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst
 : CommSemiring R] [inst_1 : AddCommMonoid A]   [inst_2 : _root_.Module R A] [in
st_3 : A…
-/
theorem toCoalgHom_injective : Function.Injective (toCoalgHom : (A ≃ₗc[R] B) → A →ₗc[R] B) :=
  fun _ _ H => toEquiv_injective <| Equiv.ext <| CoalgHom.congr_fun H
/-
**CoalgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `CoalgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (A ≃ₗc[R] B) A B where
  coe e := e.toFun
  inv := CoalgEquiv.invFun
  coe_injective' _ _ h _ := toCoalgHom_injective (DFunLike.coe_injective h)
  left_inv := CoalgEquiv.left_inv
  right_inv := CoalgEquiv.right_inv
/-
**CoalgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `CoalgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (A ≃ₗc[R] B) A B where
  coe := DFunLike.coe
  coe_injective := DFunLike.coe_injective
/-
**CoalgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `CoalgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoalgEquivClass (A ≃ₗc[R] B) R A B where
  map_add := (·.map_add')
  map_smulₛₗ := (·.map_smul')
  counit_comp := (·.counit_comp)
  map_comp_comul := (·.map_comp_comul)
/-
**CoalgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `CoalgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (A ≃ₗc[R] B) (A ≃ₗ[R] B) where coe := toLinearEquiv

@[simp, norm_cast]
/-
**CoalgEquiv.toCoalgHom_inj** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：toCoalgHom_inj {e₁ e₂ : A ≃ₗc[R] B} : (↑e₁ : A ->ₗc[R] B) = e₂ ↔ e₁ = e₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `CoalgEquiv.toCoalgHom_injective`：toCoalgHom_injective : Function.Injecti
ve (toCoalgHom : (A ≃ₗc[R] B) -> A ->ₗc[R] B)
-/
theorem toCoalgHom_inj {e₁ e₂ : A ≃ₗc[R] B} : (↑e₁ : A →ₗc[R] B) = e₂ ↔ e₁ = e₂ :=
  toCoalgHom_injective.eq_iff

@[simp]
/-
**CoalgEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：coe_mk {f h h₀ h₁ h₂ h₃ h₄ h₅} : (⟨⟨⟨⟨f, h⟩, h₀⟩, h₁, h₂⟩, h₃, h₄, h₅⟩ : A
 ≃ₗc[R] B) = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk {f h h₀ h₁ h₂ h₃ h₄ h₅} :
    (⟨⟨⟨⟨f, h⟩, h₀⟩, h₁, h₂⟩, h₃, h₄, h₅⟩ : A ≃ₗc[R] B) = f := rfl

end

section

variable [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [Module R A] [Module R B]
  [Module R C] [CoalgebraStruct R A] [CoalgebraStruct R B] [CoalgebraStruct R C]

variable (e e' : A ≃ₗc[R] B)

@[simp, norm_cast]
/-
**CoalgEquiv.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：coe_coe : ⇑(e : A ->ₗc[R] B) = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgEquivClass.toCoalgHomClass`：∀ {F : Type u_5} {R : outParam (Type u_
6)} {A : outParam (Type u_7)} {B : outParam (Type u_8)} {inst : CommSemiring R} 
  {inst_1 : AddCommMo…
· 使用定理 `CoalgEquiv.instCoalgEquivClass`：∀ {R : Type u_1} {A : Type u_2} {B : Typ
e u_3} [inst : CommSemiring R] [inst_1 : AddCommMonoid A]   [inst_2 : AddCommMon
oid B] [inst_3 : _ro…
-/
theorem coe_coe : ⇑(e : A →ₗc[R] B) = e :=
  rfl

@[nolint synTaut, deprecated "Now a syntactic tautology" (since := "2026-04-12")]
/-
**CoalgEquiv.toLinearEquiv_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：toLinearEquiv_eq_coe (f : A ≃ₗc[R] B) : f.toLinearEquiv = f
参数：f : A ≃ₗc[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_eq_coe (f : A ≃ₗc[R] B) : f.toLinearEquiv = f :=
  rfl

@[simp]
/-
**CoalgEquiv.toCoalgHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：toCoalgHom_eq_coe (f : A ≃ₗc[R] B) : f.toCoalgHom = f
参数：f : A ≃ₗc[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCoalgHom_eq_coe (f : A ≃ₗc[R] B) : f.toCoalgHom = f :=
  rfl

@[simp]
/-
**CoalgEquiv.coe_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：coe_toLinearEquiv : ⇑(e : A ≃ₗ[R] B) = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLinearEquiv : ⇑(e : A ≃ₗ[R] B) = e :=
  rfl

@[simp]
/-
**CoalgEquiv.coe_toCoalgHom** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：coe_toCoalgHom : ⇑(e : A ->ₗc[R] B) = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgEquivClass.toCoalgHomClass`：∀ {F : Type u_5} {R : outParam (Type u_
6)} {A : outParam (Type u_7)} {B : outParam (Type u_8)} {inst : CommSemiring R} 
  {inst_1 : AddCommMo…
· 使用定理 `CoalgEquiv.instCoalgEquivClass`：∀ {R : Type u_1} {A : Type u_2} {B : Typ
e u_3} [inst : CommSemiring R] [inst_1 : AddCommMonoid A]   [inst_2 : AddCommMon
oid B] [inst_3 : _ro…
-/
theorem coe_toCoalgHom : ⇑(e : A →ₗc[R] B) = e :=
  rfl
/-
**CoalgEquiv.toLinearEquiv_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：toLinearEquiv_toLinearMap : ((e : A ≃ₗ[R] B) : A ->ₗ[R] B) = (e : A ->ₗc[R
] B)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_toLinearMap : ((e : A ≃ₗ[R] B) : A →ₗ[R] B) = (e : A →ₗc[R] B) :=
  rfl

section

variable {e e'}

@[ext]
/-
**CoalgEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：ext (h : forall x, e x = e' x) : e = e'
参数：h : forall x, e x = e' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h
/-
**CoalgEquiv.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommSemiring R] [in
st_1 : AddCommMonoid A]   [inst_2 : AddCommMonoid B] [inst_3 : _root_.Module R A
] [inst_4 : _root_.Module R B] [inst_5 : CoalgebraStruct R A]   [inst_6 : Coalge
braStruct R B] {e : A ≃ₗc[R] B} {x x' : A}, x = x' → e x = e x'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
-/
protected theorem congr_arg {x x'} : x = x' → e x = e x' :=
  DFunLike.congr_arg e
/-
**CoalgEquiv.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommSemiring R] [in
st_1 : AddCommMonoid A]   [inst_2 : AddCommMonoid B] [inst_3 : _root_.Module R A
] [inst_4 : _root_.Module R B] [inst_5 : CoalgebraStruct R A]   [inst_6 : Coalge
braStruct R B] {e e' : A ≃ₗc[R] B}, e = e' → ∀ (x : A), e x = e' x
参数：x : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected theorem congr_fun (h : e = e') (x : A) : e x = e' x :=
  DFunLike.congr_fun h x

end

/-- Coalgebra equivalences are symmetric. -/
@[symm]
/-
**CoalgEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `CoalgEquiv`。
形式化陈述：symm (e : A ≃ₗc[R] B) : B ≃ₗc[R] A
参数：e : A ≃ₗc[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coalgebra equivalences are symmetric.
-/
def symm (e : A ≃ₗc[R] B) : B ≃ₗc[R] A :=
  { (e : A ≃ₗ[R] B).symm with
    counit_comp := (LinearEquiv.comp_toLinearMap_symm_eq _ _).2 e.counit_comp.symm
    map_comp_comul := by
      change (TensorProduct.congr (e : A ≃ₗ[R] B) (e : A ≃ₗ[R] B)).symm.toLinearMap ∘ₗ comul
        = comul ∘ₗ (e : A ≃ₗ[R] B).symm
      rw [LinearEquiv.toLinearMap_symm_comp_eq]
      simp only [TensorProduct.congr, toCoalgHom_eq_coe, CoalgHom.toLinearMap_eq_coe,
        LinearEquiv.toLinearMap_ofLinearMap, ← LinearMap.comp_assoc, CoalgHomClass.map_comp_comul]
      rw [← toLinearEquiv_toLinearMap, LinearEquiv.comp_symm_cancel_right] }

/-- See Note [custom simps projection] -/
/-
**CoalgEquiv.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `CoalgEquiv.Simps`。
形式化陈述：{R : Type u_5} →   [inst : CommSemiring R] →     {α : Type u_6} →       {β
 : Type u_7} →         [inst_1 : AddCommMonoid α] →           [inst_2 : AddCommM
onoid β] →             [inst_3 : _root_.Module R α] →               [inst_4 : _r
oot_.Module R β] →                 [inst_5 : CoalgebraStruct R α] → [inst_6 : Co
algebraStruct R β] → (α ≃ₗc[R] β) → α → β
参数：α ≃ₗc[R] β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.apply {R : Type*} [CommSemiring R] {α β : Type*}
    [AddCommMonoid α] [AddCommMonoid β] [Module R α]
    [Module R β] [CoalgebraStruct R α] [CoalgebraStruct R β]
    (f : α ≃ₗc[R] β) : α → β := f

/-- See Note [custom simps projection] -/
/-
**CoalgEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `CoalgEquiv.Simps`。
形式化陈述：{R : Type u_5} →   [inst : CommSemiring R] →     {A : Type u_6} →       {B
 : Type u_7} →         [inst_1 : AddCommMonoid A] →           [inst_2 : AddCommM
onoid B] →             [inst_3 : _root_.Module R A] →               [inst_4 : _r
oot_.Module R B] →                 [inst_5 : CoalgebraStruct R A] → [inst_6 : Co
algebraStruct R B] → (A ≃ₗc[R] B) → B → A
参数：A ≃ₗc[R] B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply {R : Type*} [CommSemiring R]
    {A : Type*} {B : Type*} [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B]
    (e : A ≃ₗc[R] B) : B → A :=
  e.symm

initialize_simps_projections CoalgEquiv (toFun → apply, invFun → symm_apply)

variable (A R) in
/-- The identity map is a coalgebra equivalence. -/
@[refl, simps!]
/-
**CoalgEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `CoalgEquiv`。
形式化陈述：refl : A ≃ₗc[R] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map is a coalgebra equivalence.
-/
def refl : A ≃ₗc[R] A :=
  { CoalgHom.id R A, LinearEquiv.refl R A with }

@[simp]
/-
**CoalgEquiv.refl_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：refl_toLinearEquiv : refl R A = LinearEquiv.refl R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_toLinearEquiv : refl R A = LinearEquiv.refl R A := rfl

@[simp]
/-
**CoalgEquiv.refl_toCoalgHom** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：refl_toCoalgHom : refl R A = CoalgHom.id R A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgEquivClass.toCoalgHomClass`：∀ {F : Type u_5} {R : outParam (Type u_
6)} {A : outParam (Type u_7)} {B : outParam (Type u_8)} {inst : CommSemiring R} 
  {inst_1 : AddCommMo…
· 使用定理 `CoalgEquiv.instCoalgEquivClass`：∀ {R : Type u_1} {A : Type u_2} {B : Typ
e u_3} [inst : CommSemiring R] [inst_1 : AddCommMonoid A]   [inst_2 : AddCommMon
oid B] [inst_3 : _ro…
-/
theorem refl_toCoalgHom : refl R A = CoalgHom.id R A :=
  rfl

@[simp]
/-
**CoalgEquiv.symm_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：symm_toLinearEquiv (e : A ≃ₗc[R] B) : e.symm = (e : A ≃ₗ[R] B).symm
参数：e : A ≃ₗc[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_toLinearEquiv (e : A ≃ₗc[R] B) :
    e.symm = (e : A ≃ₗ[R] B).symm := rfl
/-
**CoalgEquiv.coe_symm_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：coe_symm_toLinearEquiv (e : A ≃ₗc[R] B) : ⇑(e : A ≃ₗ[R] B).symm = e.symm
参数：e : A ≃ₗc[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_toLinearEquiv (e : A ≃ₗc[R] B) :
    ⇑(e : A ≃ₗ[R] B).symm = e.symm := rfl

@[simp]
/-
**CoalgEquiv.symm_toCoalgHom** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：symm_toCoalgHom (e : A ≃ₗc[R] B) : ((e.symm : B ->ₗc[R] A) : B ->ₗ[R] A) =
 (e : A ≃ₗ[R] B).symm
参数：e : A ≃ₗc[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgEquivClass.toCoalgHomClass`：∀ {F : Type u_5} {R : outParam (Type u_
6)} {A : outParam (Type u_7)} {B : outParam (Type u_8)} {inst : CommSemiring R} 
  {inst_1 : AddCommMo…
· 使用定理 `CoalgEquiv.instCoalgEquivClass`：∀ {R : Type u_1} {A : Type u_2} {B : Typ
e u_3} [inst : CommSemiring R] [inst_1 : AddCommMonoid A]   [inst_2 : AddCommMon
oid B] [inst_3 : _ro…
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
-/
theorem symm_toCoalgHom (e : A ≃ₗc[R] B) :
    ((e.symm : B →ₗc[R] A) : B →ₗ[R] A) = (e : A ≃ₗ[R] B).symm := rfl

@[simp]
/-
**CoalgEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：symm_apply_apply (e : A ≃ₗc[R] B) (x) : e.symm (e x) = x
参数：e : A ≃ₗc[R] B；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
theorem symm_apply_apply (e : A ≃ₗc[R] B) (x) :
    e.symm (e x) = x :=
  LinearEquiv.symm_apply_apply (e : A ≃ₗ[R] B) x

@[simp]
/-
**CoalgEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：apply_symm_apply (e : A ≃ₗc[R] B) (x) : e (e.symm x) = x
参数：e : A ≃ₗc[R] B；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem apply_symm_apply (e : A ≃ₗc[R] B) (x) :
    e (e.symm x) = x :=
  LinearEquiv.apply_symm_apply (e : A ≃ₗ[R] B) x

@[simp]
/-
**CoalgEquiv.invFun_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：invFun_eq_symm : e.invFun = e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invFun_eq_symm : e.invFun = e.symm :=
  rfl
/-
**CoalgEquiv.coe_toEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：coe_toEquiv_symm : e.toEquiv.symm = e.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_toEquiv_symm : e.toEquiv.symm = e.symm := rfl

@[simp]
/-
**CoalgEquiv.toEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：toEquiv_symm : e.symm.toEquiv = e.toEquiv.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_symm : e.symm.toEquiv = e.toEquiv.symm :=
  rfl

@[simp]
/-
**CoalgEquiv.coe_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：coe_toEquiv : ⇑e.toEquiv = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toEquiv : ⇑e.toEquiv = e :=
  rfl

@[simp]
/-
**CoalgEquiv.coe_symm_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：coe_symm_toEquiv : ⇑e.toEquiv.symm = e.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_symm_toEquiv : ⇑e.toEquiv.symm = e.symm :=
  rfl

variable {e₁₂ : A ≃ₗc[R] B} {e₂₃ : B ≃ₗc[R] C}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Coalgebra equivalences are transitive. -/
@[trans, simps!]
/-
**CoalgEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `CoalgEquiv`。
形式化陈述：trans (e₁₂ : A ≃ₗc[R] B) (e₂₃ : B ≃ₗc[R] C) : A ≃ₗc[R] C
参数：e₁₂ : A ≃ₗc[R] B；e₂₃ : B ≃ₗc[R] C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coalgebra equivalences are transitive.
-/
def trans (e₁₂ : A ≃ₗc[R] B) (e₂₃ : B ≃ₗc[R] C) : A ≃ₗc[R] C :=
  { (e₂₃ : B →ₗc[R] C).comp (e₁₂ : A →ₗc[R] B), e₁₂.toLinearEquiv ≪≫ₗ e₂₃.toLinearEquiv with }
/-
**CoalgEquiv.trans_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：trans_toLinearEquiv : (e₁₂.trans e₂₃ : A ≃ₗ[R] C) = (e₁₂ : A ≃ₗ[R] B) ≪≫ₗ 
e₂₃
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_toLinearEquiv :
    (e₁₂.trans e₂₃ : A ≃ₗ[R] C) = (e₁₂ : A ≃ₗ[R] B) ≪≫ₗ e₂₃ := rfl

@[simp]
/-
**CoalgEquiv.trans_toCoalgHom** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：trans_toCoalgHom : (e₁₂.trans e₂₃ : A ->ₗc[R] C) = e₂₃.comp e₁₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgEquivClass.toCoalgHomClass`：∀ {F : Type u_5} {R : outParam (Type u_
6)} {A : outParam (Type u_7)} {B : outParam (Type u_8)} {inst : CommSemiring R} 
  {inst_1 : AddCommMo…
· 使用定理 `CoalgEquiv.instCoalgEquivClass`：∀ {R : Type u_1} {A : Type u_2} {B : Typ
e u_3} [inst : CommSemiring R] [inst_1 : AddCommMonoid A]   [inst_2 : AddCommMon
oid B] [inst_3 : _ro…
-/
theorem trans_toCoalgHom :
    (e₁₂.trans e₂₃ : A →ₗc[R] C) = e₂₃.comp e₁₂ := rfl

@[simp]
/-
**CoalgEquiv.coe_toEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：coe_toEquiv_trans : (e₁₂ : A ≃ B).trans e₂₃ = (e₁₂.trans e₂₃ : A ≃ C)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem coe_toEquiv_trans : (e₁₂ : A ≃ B).trans e₂₃ = (e₁₂.trans e₂₃ : A ≃ C) :=
  rfl

/-- If a coalgebra morphism has an inverse, it is a coalgebra isomorphism. -/
/-
**CoalgEquiv.ofCoalgHom** 是 Mathlib 中的一个定义，位于命名空间 `CoalgEquiv`。
形式化陈述：ofCoalgHom (f : A ->ₗc[R] B) (g : B ->ₗc[R] A) (h₁ : f.comp g = CoalgHom.i
d R B) (h₂ : g.comp f = CoalgHom.id R A) : A ≃ₗc[R] B where __
参数：f : A ->ₗc[R] B；g : B ->ₗc[R] A；h₁ : f.comp g = CoalgHom.id R B；h₂ : g.comp f
 = CoalgHom.id R A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgHom.counit_comp`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [in
st : CommSemiring R] [inst_1 : AddCommMonoid A]   [inst_2 : _root_.Module R A] [
inst_3 : A…
· 使用定理 `CoalgHom.map_comp_comul`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : AddCommMonoid A]   [inst_2 : _root_.Module R A
] [inst_3 : A…

--- 原说明 ---
If a coalgebra morphism has an inverse, it is a coalgebra isomorphism.
-/
def ofCoalgHom (f : A →ₗc[R] B) (g : B →ₗc[R] A) (h₁ : f.comp g = CoalgHom.id R B)
    (h₂ : g.comp f = CoalgHom.id R A) : A ≃ₗc[R] B where
  __ := f
  toFun := f
  invFun := g
  left_inv := CoalgHom.ext_iff.1 h₂
  right_inv := CoalgHom.ext_iff.1 h₁

@[simp]
/-
**CoalgEquiv.coe_ofCoalgHom** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：coe_ofCoalgHom (f : A ->ₗc[R] B) (g : B ->ₗc[R] A) (h₁ h₂) : ofCoalgHom f 
g h₁ h₂ = f
参数：f : A ->ₗc[R] B；g : B ->ₗc[R] A；h₁ h₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgEquivClass.toCoalgHomClass`：∀ {F : Type u_5} {R : outParam (Type u_
6)} {A : outParam (Type u_7)} {B : outParam (Type u_8)} {inst : CommSemiring R} 
  {inst_1 : AddCommMo…
· 使用定理 `CoalgEquiv.instCoalgEquivClass`：∀ {R : Type u_1} {A : Type u_2} {B : Typ
e u_3} [inst : CommSemiring R] [inst_1 : AddCommMonoid A]   [inst_2 : AddCommMon
oid B] [inst_3 : _ro…
-/
theorem coe_ofCoalgHom (f : A →ₗc[R] B) (g : B →ₗc[R] A) (h₁ h₂) :
    ofCoalgHom f g h₁ h₂ = f :=
  rfl
/-
**CoalgEquiv.ofCoalgHom_symm** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：ofCoalgHom_symm (f : A ->ₗc[R] B) (g : B ->ₗc[R] A) (h₁ h₂) : (ofCoalgHom 
f g h₁ h₂).symm = ofCoalgHom g f h₂ h₁
参数：f : A ->ₗc[R] B；g : B ->ₗc[R] A；h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofCoalgHom_symm (f : A →ₗc[R] B) (g : B →ₗc[R] A) (h₁ h₂) :
    (ofCoalgHom f g h₁ h₂).symm = ofCoalgHom g f h₂ h₁ :=
  rfl

variable {f : A →ₗc[R] B} (hf : Function.Bijective f)

/-- Promotes a bijective coalgebra homomorphism to a coalgebra equivalence. -/
@[simps apply]
/-
**CoalgEquiv.ofBijective** 是 Mathlib 中的一个定义，位于命名空间 `CoalgEquiv`。
形式化陈述：ofBijective : A ≃ₗc[R] B where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgHom.counit_comp`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [in
st : CommSemiring R] [inst_1 : AddCommMonoid A]   [inst_2 : _root_.Module R A] [
inst_3 : A…
· 使用定理 `CoalgHom.map_comp_comul`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : AddCommMonoid A]   [inst_2 : _root_.Module R A
] [inst_3 : A…

--- 原说明 ---
Promotes a bijective coalgebra homomorphism to a coalgebra equivalence.
-/
noncomputable def ofBijective : A ≃ₗc[R] B where
  toFun := f
  __ := f
  __ := LinearEquiv.ofBijective (f : A →ₗ[R] B) hf

@[simp]
/-
**CoalgEquiv.coe_ofBijective** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：coe_ofBijective : (CoalgEquiv.ofBijective hf : A -> B) = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofBijective : (CoalgEquiv.ofBijective hf : A → B) = f :=
  rfl

end
variable
  [AddCommMonoid A] [Module R A] [Coalgebra R A]
  [AddCommMonoid B] [Module R B] [CoalgebraStruct R B]

/-- Let `A` be an `R`-coalgebra and let `B` be an `R`-module with a `CoalgebraStruct`.
A linear equivalence `A ≃ₗ[R] B` that respects the `CoalgebraStruct`s defines an `R`-coalgebra
/-
**CoalgEquiv.on** 是 Mathlib 中的一个结构，位于命名空间 `CoalgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure on `B`. -/
/-
**CoalgEquiv.toCoalgebra** 是 Mathlib 中的一个定义，位于命名空间 `CoalgEquiv`。
形式化陈述：{R : Type u_1} →   {A : Type u_2} →     {B : Type u_3} →       [inst : Com
mSemiring R] →         [inst_1 : AddCommMonoid A] →           [inst_2 : _root_.M
odule R A] →             [inst_3 : Coalgebra R A] →               [inst_4 : AddC
ommMonoid B] →                 [inst_5 : _root_.Module R B] → [inst_6 : Coalgebr
aStruct R B] → (A ≃ₗc[R] B) → Coalgebra R B
参数：A ≃ₗc[R] B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `A` be an `R`-coalgebra and let `B` be an `R`-module with a `CoalgebraStruct
`.
A linear equivalence `A ≃ₗ[R] B` that respects the `CoalgebraStruct`s defines an
 `R`-coalgebra
structure on `B`.
-/
@[reducible] def toCoalgebra (f : A ≃ₗc[R] B) :
    Coalgebra R B where
  coassoc := by
    simp only [← ((f : A ≃ₗ[R] B).comp_toLinearMap_symm_eq _ _).2 f.map_comp_comul,
      ← LinearMap.comp_assoc]
    congr 1
    ext x
    simpa only [toCoalgHom_eq_coe, CoalgHom.toLinearMap_eq_coe, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, ← (ℛ R _).eq, map_sum, TensorProduct.map_tmul,
      LinearMap.coe_coe, CoalgHom.coe_coe, LinearMap.rTensor_tmul, coe_symm_toLinearEquiv,
      symm_apply_apply, LinearMap.lTensor_comp_map, TensorProduct.sum_tmul,
      TensorProduct.assoc_tmul, TensorProduct.tmul_sum] using (sum_map_tmul_tmul_eq f f f x).symm
  rTensor_counit_comp_comul := by
    simp_rw [(f.toLinearEquiv.eq_comp_toLinearMap_symm _ _).2 f.counit_comp,
      ← (f.toLinearEquiv.comp_toLinearMap_symm_eq _ _).2 f.map_comp_comul, ← LinearMap.comp_assoc,
      f.toLinearEquiv.comp_toLinearMap_symm_eq]
    ext x
    simp [← (ℛ R _).eq]
  lTensor_counit_comp_comul := by
    simp_rw [(f.toLinearEquiv.eq_comp_toLinearMap_symm _ _).2 f.counit_comp,
      ← (f.toLinearEquiv.comp_toLinearMap_symm_eq _ _).2 f.map_comp_comul, ← LinearMap.comp_assoc,
      f.toLinearEquiv.comp_toLinearMap_symm_eq]
    ext x
    simp [← (ℛ R _).eq]

end CoalgEquiv

