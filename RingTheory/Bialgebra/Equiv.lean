/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.RingTheory.Coalgebra.Equiv
public import Mathlib.RingTheory.Bialgebra.Hom

/-!
# Isomorphisms of `R`-bialgebras

This file defines bundled isomorphisms of `R`-bialgebras. We simply mimic the early parts of
`Mathlib/Algebra/Algebra/Equiv.lean`.

## Main definitions

* `BialgEquiv R A B`: the type of `R`-bialgebra isomorphisms between `A` and `B`.

## Notation

* `A ≃ₐc[R] B` : `R`-bialgebra equivalence from `A` to `B`.
-/

@[expose] public section

universe u v w u₁

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁}

open TensorProduct Coalgebra Bialgebra Function

/-- An equivalence of bialgebras is an invertible bialgebra homomorphism. -/
/-
**BialgEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) →   [inst : CommSemiring R] →     (A : Type v) →       (B : T
ype w) →         [inst_1 : Semiring A] →           [inst_2 : Semiring B] →      
       [inst_3 : Algebra R A] →               [inst_4 : Algebra R B] → [Coalgebr
aStruct R A] → [CoalgebraStruct R B] → Type (max v w)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of bialgebras is an invertible bialgebra homomorphism.
-/
structure BialgEquiv (R : Type u) [CommSemiring R] (A : Type v) (B : Type w)
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] extends A ≃ₗc[R] B, A ≃* B where

attribute [nolint docBlame] BialgEquiv.toMulEquiv
attribute [nolint docBlame] BialgEquiv.toCoalgEquiv

@[inherit_doc BialgEquiv]
notation:50 A " ≃ₐc[" R "] " B => BialgEquiv R A B

/-- `BialgEquivClass F R A B` asserts `F` is a type of bundled bialgebra equivalences
from `A` to `B`. -/
/-
**BialgEquivClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   (R : outParam (Type u_2)) →     (A : outParam (Type u_3
)) →       (B : outParam (Type u_4)) →         [inst : CommSemiring R] →        
   [inst_1 : Semiring A] →             [inst_2 : Semiring B] →               [in
st_3 : Algebra R A] →                 [inst_4 : Algebra R B] → [CoalgebraStruct 
R A] → [CoalgebraStruct R B] → [EquivLike F A B] → Prop
参数：Type u_2；Type u_3；Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`BialgEquivClass F R A B` asserts `F` is a type of bundled bialgebra equivalence
s
from `A` to `B`.
-/
class BialgEquivClass (F : Type*) (R A B : outParam Type*) [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] [EquivLike F A B] : Prop
    extends CoalgEquivClass F R A B, MulEquivClass F A B

namespace BialgEquivClass

variable {F R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] [CoalgebraStruct R A] [CoalgebraStruct R B]
  [EquivLike F A B] [BialgEquivClass F R A B]

/-
**BialgEquivClass.** 是 Mathlib 中的一个实例，位于命名空间 `BialgEquivClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toBialgHomClass : BialgHomClass F R A B where
  map_add := map_add
  map_smulₛₗ := map_smul
  counit_comp := CoalgHomClass.counit_comp
  map_comp_comul := CoalgHomClass.map_comp_comul
  map_mul := map_mul
  map_one := map_one

/-- Reinterpret an element of a type of bialgebra equivalences as a bialgebra equivalence. -/
@[coe]
/-
**BialgEquivClass.toBialgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `BialgEquivClass`。
形式化陈述：toBialgEquiv (f : F) : A ≃ₐc[R] B
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BialgEquivClass.toCoalgEquivClass`：∀ {F : Type u_1} {R : outParam (Type 
u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R
}   {inst_1 : Semiring …
· 使用定理 `BialgEquivClass.toBialgHomClass`：∀ {F : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {B : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 :
 Semiring B] [inst_3 …
· 使用定理 `BialgHom.map_mul'`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst 
: CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semir
ing B] …

--- 原说明 ---
Reinterpret an element of a type of bialgebra equivalences as a bialgebra equiva
lence.
-/
def toBialgEquiv (f : F) : A ≃ₐc[R] B :=
  { (f : A ≃ₗc[R] B), (f : A →ₐc[R] B) with }

/-- Reinterpret an element of a type of bialgebra equivalences as a bialgebra equivalence. -/
/-
**BialgEquivClass.instCoeToBialgEquiv** 是 Mathlib 中的一个实例，位于命名空间 `BialgEquivClass
`。
形式化陈述：instCoeToBialgEquiv : CoeHead F (A ≃ₐc[R] B) where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an element of a type of bialgebra equivalences as a bialgebra equiva
lence.
-/
instance instCoeToBialgEquiv : CoeHead F (A ≃ₐc[R] B) where
  coe f := toBialgEquiv f
/-
**BialgEquivClass.** 是 Mathlib 中的一个实例，位于命名空间 `BialgEquivClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toAlgEquivClass : AlgEquivClass F R A B where
  map_mul := map_mul
  map_add := map_add
  commutes := AlgHomClass.commutes

end BialgEquivClass

namespace BialgEquiv

variable [CommSemiring R]

section

variable [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B]

/-- The bialgebra morphism underlying a bialgebra equivalence. -/
/-
**BialgEquiv.toBialgHom** 是 Mathlib 中的一个定义，位于命名空间 `BialgEquiv`。
形式化陈述：toBialgHom (f : A ≃ₐc[R] B) : A ->ₐc[R] B
参数：f : A ≃ₐc[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bialgebra morphism underlying a bialgebra equivalence.
-/
def toBialgHom (f : A ≃ₐc[R] B) : A →ₐc[R] B :=
  { f.toCoalgEquiv with
    map_one' := map_one f.toMulEquiv
    map_mul' := map_mul f.toMulEquiv }

/-- The algebra equivalence underlying a bialgebra equivalence. -/
/-
**BialgEquiv.toAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `BialgEquiv`。
形式化陈述：toAlgEquiv (f : A ≃ₐc[R] B) : A ≃ₐ[R] B
参数：f : A ≃ₐc[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra equivalence underlying a bialgebra equivalence.
-/
def toAlgEquiv (f : A ≃ₐc[R] B) : A ≃ₐ[R] B :=
  { f.toCoalgEquiv with
    map_mul' := map_mul f.toMulEquiv
    map_add' := map_add f.toCoalgEquiv
    commutes' := AlgHomClass.commutes f.toBialgHom }

/-- The equivalence of types underlying a bialgebra equivalence. -/
/-
**BialgEquiv.toEquiv** 是 Mathlib 中的一个定义，位于命名空间 `BialgEquiv`。
形式化陈述：toEquiv : (A ≃ₐc[R] B) -> A ≃ B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of types underlying a bialgebra equivalence.
-/
def toEquiv : (A ≃ₐc[R] B) → A ≃ B := fun f => f.toCoalgEquiv.toEquiv
/-
**BialgEquiv.toEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：toEquiv_injective : Function.Injective (toEquiv : (A ≃ₐc[R] B) -> A ≃ B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgEquiv.mk.injEq`：∀ {R : Type u} [inst : CommSemiring R] {A : Type v}
 {B : Type w} [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R 
A] [inst_…
· 使用定理 `CoalgEquiv.toEquiv_injective`：toEquiv_injective : Function.Injective (to
Equiv : (A ≃ₗc[R] B) -> A ≃ B)
-/
theorem toEquiv_injective : Function.Injective (toEquiv : (A ≃ₐc[R] B) → A ≃ B) :=
  fun ⟨_, _⟩ ⟨_, _⟩ h =>
    (BialgEquiv.mk.injEq _ _ _ _).mpr (CoalgEquiv.toEquiv_injective h)

@[simp]
/-
**BialgEquiv.toEquiv_inj** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：toEquiv_inj {e₁ e₂ : A ≃ₐc[R] B} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `BialgEquiv.toEquiv_injective`：toEquiv_injective : Function.Injective (to
Equiv : (A ≃ₐc[R] B) -> A ≃ B)
-/
theorem toEquiv_inj {e₁ e₂ : A ≃ₐc[R] B} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff
/-
**BialgEquiv.toBialgHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：toBialgHom_injective : Function.Injective (toBialgHom : (A ≃ₐc[R] B) -> A 
->ₐc[R] B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgEquiv.toEquiv_injective`：toEquiv_injective : Function.Injective (to
Equiv : (A ≃ₐc[R] B) -> A ≃ B)
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `BialgHom.congr_fun`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst
 : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algeb
ra R A] …
-/
theorem toBialgHom_injective : Function.Injective (toBialgHom : (A ≃ₐc[R] B) → A →ₐc[R] B) :=
  fun _ _ H => toEquiv_injective <| Equiv.ext <| BialgHom.congr_fun H
/-
**BialgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `BialgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (A ≃ₐc[R] B) A B where
  coe f := f.toFun
  inv := fun f => f.invFun
  coe_injective' _ _ h _ := toBialgHom_injective (DFunLike.coe_injective h)
  left_inv := fun f => f.left_inv
  right_inv := fun f => f.right_inv
/-
**BialgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `BialgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (A ≃ₐc[R] B) A B where
  coe := DFunLike.coe
  coe_injective := DFunLike.coe_injective
/-
**BialgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `BialgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BialgEquivClass (A ≃ₐc[R] B) R A B where
  map_add := (·.map_add')
  map_smulₛₗ := (·.map_smul')
  counit_comp := (·.counit_comp)
  map_comp_comul := (·.map_comp_comul)
  map_mul := (·.map_mul')
/-
**BialgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `BialgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (A ≃ₐc[R] B) (A ≃ₐ[R] B) where coe := toAlgEquiv

@[simp, norm_cast]
/-
**BialgEquiv.toBialgHom_inj** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：toBialgHom_inj {e₁ e₂ : A ≃ₐc[R] B} : (↑e₁ : A ->ₐc[R] B) = e₂ ↔ e₁ = e₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `BialgEquiv.toBialgHom_injective`：toBialgHom_injective : Function.Injecti
ve (toBialgHom : (A ≃ₐc[R] B) -> A ->ₐc[R] B)
-/
theorem toBialgHom_inj {e₁ e₂ : A ≃ₐc[R] B} : (↑e₁ : A →ₐc[R] B) = e₂ ↔ e₁ = e₂ :=
  toBialgHom_injective.eq_iff
/-
**BialgEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSemiring R] [inst_1 :
 Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Algebra R 
B] [inst_5 : CoalgebraStruct R A] [inst_6 : CoalgebraStruct R B]   (e : A ≃ₗc[R]
 B) (h : ∀ (x y : A), e.toFun (x * y) = e.toFun x * e.toFun y), ↑{ toCoalgEquiv 
:= e, map_mul' := h } = e
参数：e : A ≃ₗc[R] B；h : ∀ (x y : A), e.toFun (x * y) = e.toFun x * e.toFun y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgEquivClass.toCoalgEquivClass`：∀ {F : Type u_1} {R : outParam (Type 
u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R
}   {inst_1 : Semiring …
· 使用定理 `BialgEquiv.instBialgEquivClass`：∀ {R : Type u} {A : Type v} {B : Type w}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [inst_…
-/
@[simp] lemma coe_mk (e : A ≃ₗc[R] B) (h) : mk e h = e := rfl

end

section

variable [Semiring A] [Semiring B] [Semiring C] [Algebra R A] [Algebra R B]
  [Algebra R C] [CoalgebraStruct R A] [CoalgebraStruct R B] [CoalgebraStruct R C]

variable (e e' : A ≃ₐc[R] B)

@[simp, norm_cast]
/-
**BialgEquiv.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：coe_coe : ⇑(e : A ->ₐc[R] B) = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgEquivClass.toBialgHomClass`：∀ {F : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {B : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 :
 Semiring B] [inst_3 …
· 使用定理 `BialgEquiv.instBialgEquivClass`：∀ {R : Type u} {A : Type v} {B : Type w}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [inst_…
-/
theorem coe_coe : ⇑(e : A →ₐc[R] B) = e :=
  rfl

@[simp]
/-
**BialgEquiv.toCoalgEquiv_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：toCoalgEquiv_eq_coe (f : A ≃ₐc[R] B) : f.toCoalgEquiv = f
参数：f : A ≃ₐc[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCoalgEquiv_eq_coe (f : A ≃ₐc[R] B) : f.toCoalgEquiv = f :=
  rfl

@[simp]
/-
**BialgEquiv.toBialgHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：toBialgHom_eq_coe (f : A ≃ₐc[R] B) : f.toBialgHom = f
参数：f : A ≃ₐc[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBialgHom_eq_coe (f : A ≃ₐc[R] B) : f.toBialgHom = f :=
  rfl

@[deprecated "Now a syntactic tautology" (since := "2026-04-09"), nolint synTaut]
/-
**BialgEquiv.toAlgEquiv_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：toAlgEquiv_eq_coe (f : A ≃ₐc[R] B) : f.toAlgEquiv = f
参数：f : A ≃ₐc[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAlgEquiv_eq_coe (f : A ≃ₐc[R] B) : f.toAlgEquiv = f :=
  rfl

@[simp]
/-
**BialgEquiv.coe_toCoalgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：coe_toCoalgEquiv : ⇑(e : A ≃ₐ[R] B) = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toCoalgEquiv : ⇑(e : A ≃ₐ[R] B) = e :=
  rfl

@[simp]
/-
**BialgEquiv.coe_toBialgHom** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：coe_toBialgHom : ⇑(e : A ->ₐc[R] B) = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgEquivClass.toBialgHomClass`：∀ {F : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {B : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 :
 Semiring B] [inst_3 …
· 使用定理 `BialgEquiv.instBialgEquivClass`：∀ {R : Type u} {A : Type v} {B : Type w}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [inst_…
-/
theorem coe_toBialgHom : ⇑(e : A →ₐc[R] B) = e :=
  rfl

@[simp]
/-
**BialgEquiv.coe_toAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：coe_toAlgEquiv : ⇑(e : A ≃ₐ[R] B) = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAlgEquiv : ⇑(e : A ≃ₐ[R] B) = e :=
  rfl
/-
**BialgEquiv.toCoalgEquiv_toCoalgHom** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：toCoalgEquiv_toCoalgHom : ((e : A ≃ₐc[R] B) : A ->ₗc[R] B) = (e : A ->ₐc[R
] B)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgEquivClass.toCoalgHomClass`：∀ {F : Type u_5} {R : outParam (Type u_
6)} {A : outParam (Type u_7)} {B : outParam (Type u_8)} {inst : CommSemiring R} 
  {inst_1 : AddCommMo…
· 使用定理 `BialgEquivClass.toCoalgEquivClass`：∀ {F : Type u_1} {R : outParam (Type 
u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R
}   {inst_1 : Semiring …
· 使用定理 `BialgEquiv.instBialgEquivClass`：∀ {R : Type u} {A : Type v} {B : Type w}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [inst_…
-/
theorem toCoalgEquiv_toCoalgHom : ((e : A ≃ₐc[R] B) : A →ₗc[R] B) = (e : A →ₐc[R] B) :=
  rfl

@[deprecated "Now a syntactic equality" (since := "2026-04-30"), nolint synTaut]
/-
**BialgEquiv.toBialgHom_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：toBialgHom_toAlgHom : ((e : A ->ₐc[R] B) : A ->ₐ[R] B) = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgEquivClass.toBialgHomClass`：∀ {F : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {B : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 :
 Semiring B] [inst_3 …
· 使用定理 `BialgEquiv.instBialgEquivClass`：∀ {R : Type u} {A : Type v} {B : Type w}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [inst_…
-/
theorem toBialgHom_toAlgHom : ((e : A →ₐc[R] B) : A →ₐ[R] B) = e := rfl

section

variable {e e'}

@[ext]
/-
**BialgEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：ext (h : forall x, e x = e' x) : e = e'
参数：h : forall x, e x = e' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h
/-
**BialgEquiv.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSemiring R] [inst_1 :
 Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Algebra R 
B] [inst_5 : CoalgebraStruct R A] [inst_6 : CoalgebraStruct R B]   {e : A ≃ₐc[R]
 B} {x x' : A}, x = x' → e x = e x'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
-/
protected theorem congr_arg {x x'} : x = x' → e x = e x' :=
  DFunLike.congr_arg e
/-
**BialgEquiv.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSemiring R] [inst_1 :
 Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Algebra R 
B] [inst_5 : CoalgebraStruct R A] [inst_6 : CoalgebraStruct R B]   {e e' : A ≃ₐc
[R] B}, e = e' → ∀ (x : A), e x = e' x
参数：x : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected theorem congr_fun (h : e = e') (x : A) : e x = e' x :=
  DFunLike.congr_fun h x

end

/-- See Note [custom simps projection] -/
/-
**BialgEquiv.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `BialgEquiv.Simps`。
形式化陈述：{R : Type u} →   [inst : CommSemiring R] →     {α : Type v} →       {β : T
ype w} →         [inst_1 : Semiring α] →           [inst_2 : Semiring β] →      
       [inst_3 : Algebra R α] →               [inst_4 : Algebra R β] →          
       [inst_5 : CoalgebraStruct R α] → [inst_6 : CoalgebraStruct R β] → (α ≃ₐc[
R] β) → α → β
参数：α ≃ₐc[R] β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.apply {R : Type u} [CommSemiring R] {α : Type v} {β : Type w}
    [Semiring α] [Semiring β] [Algebra R α]
    [Algebra R β] [CoalgebraStruct R α] [CoalgebraStruct R β]
    (f : α ≃ₐc[R] β) : α → β := f

/-- See Note [custom simps projection] -/
/-
**BialgEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `BialgEquiv.Simps`。
形式化陈述：{R : Type u_1} →   [inst : CommSemiring R] →     {A : Type u_2} →       {B
 : Type u_3} →         [inst_1 : Semiring A] →           [inst_2 : Semiring B] →
             [inst_3 : Algebra R A] →               [inst_4 : Algebra R B] →    
             [inst_5 : CoalgebraStruct R A] → [inst_6 : CoalgebraStruct R B] → (
A ≃ₐc[R] B) → B → A
参数：A ≃ₐc[R] B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply {R : Type*} [CommSemiring R]
    {A : Type*} {B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B]
    (e : A ≃ₐc[R] B) : B → A :=
  e.symm

initialize_simps_projections BialgEquiv (toFun → apply, invFun → symm_apply)

variable (A R) in
/-- The identity map is a bialgebra equivalence. -/
@[refl, simps! apply]
/-
**BialgEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `BialgEquiv`。
形式化陈述：refl : A ≃ₐc[R] A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHom.map_mul'`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst 
: CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semir
ing B] …

--- 原说明 ---
The identity map is a bialgebra equivalence.
-/
def refl : A ≃ₐc[R] A :=
  { CoalgEquiv.refl R A, BialgHom.id R A with }

@[simp]
/-
**BialgEquiv.refl_toCoalgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：refl_toCoalgEquiv : refl R A = CoalgEquiv.refl R A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgEquivClass.toCoalgEquivClass`：∀ {F : Type u_1} {R : outParam (Type 
u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R
}   {inst_1 : Semiring …
· 使用定理 `BialgEquiv.instBialgEquivClass`：∀ {R : Type u} {A : Type v} {B : Type w}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [inst_…
-/
theorem refl_toCoalgEquiv : refl R A = CoalgEquiv.refl R A := rfl

@[simp]
/-
**BialgEquiv.refl_toBialgHom** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：refl_toBialgHom : refl R A = BialgHom.id R A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgEquivClass.toBialgHomClass`：∀ {F : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {B : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 :
 Semiring B] [inst_3 …
· 使用定理 `BialgEquiv.instBialgEquivClass`：∀ {R : Type u} {A : Type v} {B : Type w}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [inst_…
-/
theorem refl_toBialgHom : refl R A = BialgHom.id R A :=
  rfl

/-- Bialgebra equivalences are symmetric. -/
@[symm]
/-
**BialgEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `BialgEquiv`。
形式化陈述：symm (e : A ≃ₐc[R] B) : B ≃ₐc[R] A
参数：e : A ≃ₐc[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bialgebra equivalences are symmetric.
-/
def symm (e : A ≃ₐc[R] B) : B ≃ₐc[R] A :=
  { (e : A ≃ₗc[R] B).symm, (e : A ≃* B).symm with }

@[simp]
/-
**BialgEquiv.symm_toCoalgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：symm_toCoalgEquiv (e : A ≃ₐc[R] B) : e.symm = (e : A ≃ₗc[R] B).symm
参数：e : A ≃ₐc[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgEquivClass.toCoalgEquivClass`：∀ {F : Type u_1} {R : outParam (Type 
u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R
}   {inst_1 : Semiring …
· 使用定理 `BialgEquiv.instBialgEquivClass`：∀ {R : Type u} {A : Type v} {B : Type w}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [inst_…
-/
theorem symm_toCoalgEquiv (e : A ≃ₐc[R] B) :
    e.symm = (e : A ≃ₗc[R] B).symm := rfl
/-
**BialgEquiv.invFun_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：invFun_eq_symm : e.invFun = e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invFun_eq_symm : e.invFun = e.symm :=
  rfl
/-
**BialgEquiv.coe_toEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：coe_toEquiv_symm : e.toEquiv.symm = e.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_toEquiv_symm : e.toEquiv.symm = e.symm := rfl

@[simp]
/-
**BialgEquiv.toEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：toEquiv_symm : e.symm.toEquiv = e.toEquiv.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_symm : e.symm.toEquiv = e.toEquiv.symm :=
  rfl

@[simp]
/-
**BialgEquiv.coe_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：coe_toEquiv : ⇑e.toEquiv = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toEquiv : ⇑e.toEquiv = e :=
  rfl

@[simp]
/-
**BialgEquiv.coe_symm_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：coe_symm_toEquiv : ⇑e.toEquiv.symm = e.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_symm_toEquiv : ⇑e.toEquiv.symm = e.symm :=
  rfl

variable {e₁₂ : A ≃ₐc[R] B} {e₂₃ : B ≃ₐc[R] C}

/-- Bialgebra equivalences are transitive. -/
@[trans, simps! apply]
/-
**BialgEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `BialgEquiv`。
形式化陈述：trans (e₁₂ : A ≃ₐc[R] B) (e₂₃ : B ≃ₐc[R] C) : A ≃ₐc[R] C
参数：e₁₂ : A ≃ₐc[R] B；e₂₃ : B ≃ₐc[R] C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bialgebra equivalences are transitive.
-/
def trans (e₁₂ : A ≃ₐc[R] B) (e₂₃ : B ≃ₐc[R] C) : A ≃ₐc[R] C :=
  { (e₁₂ : A ≃ₗc[R] B).trans (e₂₃ : B ≃ₗc[R] C), (e₁₂ : A ≃* B).trans (e₂₃ : B ≃* C) with }

@[simp]
/-
**BialgEquiv.trans_toCoalgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：trans_toCoalgEquiv : (e₁₂.trans e₂₃ : A ≃ₗc[R] C) = (e₁₂ : A ≃ₗc[R] B).tra
ns (e₂₃ : B ≃ₗc[R] C)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgEquivClass.toCoalgEquivClass`：∀ {F : Type u_1} {R : outParam (Type 
u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R
}   {inst_1 : Semiring …
· 使用定理 `BialgEquiv.instBialgEquivClass`：∀ {R : Type u} {A : Type v} {B : Type w}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [inst_…
-/
theorem trans_toCoalgEquiv :
    (e₁₂.trans e₂₃ : A ≃ₗc[R] C) = (e₁₂ : A ≃ₗc[R] B).trans (e₂₃ : B ≃ₗc[R] C) := rfl

@[simp]
/-
**BialgEquiv.trans_toBialgHom** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：trans_toBialgHom : (e₁₂.trans e₂₃ : A ->ₐc[R] C) = (e₂₃ : B ->ₐc[R] C).com
p e₁₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgEquivClass.toBialgHomClass`：∀ {F : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {B : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 :
 Semiring B] [inst_3 …
· 使用定理 `BialgEquiv.instBialgEquivClass`：∀ {R : Type u} {A : Type v} {B : Type w}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [inst_…
-/
theorem trans_toBialgHom :
    (e₁₂.trans e₂₃ : A →ₐc[R] C) = (e₂₃ : B →ₐc[R] C).comp e₁₂ := rfl

@[simp]
/-
**BialgEquiv.coe_toEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：coe_toEquiv_trans : (e₁₂ : A ≃ B).trans e₂₃ = (e₁₂.trans e₂₃ : A ≃ C)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem coe_toEquiv_trans : (e₁₂ : A ≃ B).trans e₂₃ = (e₁₂.trans e₂₃ : A ≃ C) :=
  rfl

@[simp]
/-
**BialgEquiv.apply_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `BialgEquiv`。
形式化陈述：apply_symm_apply (e : A ≃ₐc[R] B) : forall x, e (e.symm x) = x
参数：e : A ≃ₐc[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma apply_symm_apply (e : A ≃ₐc[R] B) : ∀ x, e (e.symm x) = x := e.toEquiv.apply_symm_apply

@[simp]
/-
**BialgEquiv.symm_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `BialgEquiv`。
形式化陈述：symm_apply_apply (e : A ≃ₐc[R] B) : forall x, e.symm (e x) = x
参数：e : A ≃ₐc[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma symm_apply_apply (e : A ≃ₐc[R] B) : ∀ x, e.symm (e x) = x := e.toEquiv.symm_apply_apply
/-
**BialgEquiv.comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSemiring R] [inst_1 :
 Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Algebra R 
B] [inst_5 : CoalgebraStruct R A] [inst_6 : CoalgebraStruct R B]   (e : A ≃ₐc[R]
 B), (↑e).comp ↑e.symm = BialgHom.id R B
参数：e : A ≃ₐc[R] B；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHom.coe_toAlgHom_injective`：coe_toAlgHom_injective : Function.Injec
tive ((↑) : (A ->ₐc[R] B) -> A ->ₐ[R] B)
· 使用定理 `BialgEquivClass.toBialgHomClass`：∀ {F : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {B : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 :
 Semiring B] [inst_3 …
· 使用定理 `BialgEquiv.instBialgEquivClass`：∀ {R : Type u} {A : Type v} {B : Type w}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [inst_…
· 使用定理 `AlgEquiv.comp_symm`：comp_symm (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp (e : A₁ ->
ₐ[R] A₂) ↑e.symm = AlgHom.id R A₂
-/
@[simp] lemma comp_symm (e : A ≃ₐc[R] B) : (e : A →ₐc[R] B).comp e.symm = .id R B :=
  BialgHom.coe_toAlgHom_injective e.toAlgEquiv.comp_symm
/-
**BialgEquiv.symm_comp** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSemiring R] [inst_1 :
 Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Algebra R 
B] [inst_5 : CoalgebraStruct R A] [inst_6 : CoalgebraStruct R B]   (e : A ≃ₐc[R]
 B), (↑e.symm).comp ↑e = BialgHom.id R A
参数：e : A ≃ₐc[R] B；↑e.symm。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHom.coe_toAlgHom_injective`：coe_toAlgHom_injective : Function.Injec
tive ((↑) : (A ->ₐc[R] B) -> A ->ₐ[R] B)
· 使用定理 `BialgEquivClass.toBialgHomClass`：∀ {F : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {B : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 :
 Semiring B] [inst_3 …
· 使用定理 `BialgEquiv.instBialgEquivClass`：∀ {R : Type u} {A : Type v} {B : Type w}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [inst_…
· 使用定理 `AlgEquiv.symm_comp`：symm_comp (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp ↑e.symm (e
 : A₁ ->ₐ[R] A₂) = AlgHom.id R A₁
-/
@[simp] lemma symm_comp (e : A ≃ₐc[R] B) : (e.symm : B →ₐc[R] A).comp e = .id R A :=
  BialgHom.coe_toAlgHom_injective e.toAlgEquiv.symm_comp
/-
**BialgEquiv.toRingEquiv_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSemiring R] [inst_1 :
 Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Algebra R 
B] [inst_5 : CoalgebraStruct R A] [inst_6 : CoalgebraStruct R B]   (e : A ≃ₐc[R]
 B), ↑e.toAlgEquiv.toRingEquiv = ↑e
参数：e : A ≃ₐc[R] B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
@[simp] lemma toRingEquiv_toRingHom (e : A ≃ₐc[R] B) : ((e : A ≃+* B) : A →+* B) = e := rfl
/-
**BialgEquiv.toAlgEquiv_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSemiring R] [inst_1 :
 Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Algebra R 
B] [inst_5 : CoalgebraStruct R A] [inst_6 : CoalgebraStruct R B]   (e : A ≃ₐc[R]
 B), ↑e.toAlgEquiv = ↑e
参数：e : A ≃ₐc[R] B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
@[simp] lemma toAlgEquiv_toRingHom (e : A ≃ₐc[R] B) : ((e : A ≃ₐ[R] B) : A →+* B) = e := rfl

/-- If a coalgebra morphism has an inverse, it is a coalgebra isomorphism. -/
/-
**BialgEquiv.ofBialgHom** 是 Mathlib 中的一个定义，位于命名空间 `BialgEquiv`。
形式化陈述：ofBialgHom (f : A ->ₐc[R] B) (g : B ->ₐc[R] A) (h₁ : f.comp g = BialgHom.i
d R B) (h₂ : g.comp f = BialgHom.id R A) : A ≃ₐc[R] B where __
参数：f : A ->ₐc[R] B；g : B ->ₐc[R] A；h₁ : f.comp g = BialgHom.id R B；h₂ : g.comp f
 = BialgHom.id R A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHom.map_mul'`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst 
: CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semir
ing B] …

--- 原说明 ---
If a coalgebra morphism has an inverse, it is a coalgebra isomorphism.
-/
def ofBialgHom (f : A →ₐc[R] B) (g : B →ₐc[R] A) (h₁ : f.comp g = BialgHom.id R B)
    (h₂ : g.comp f = BialgHom.id R A) : A ≃ₐc[R] B where
  __ := f
  toFun := f
  invFun := g
  left_inv := BialgHom.ext_iff.1 h₂
  right_inv := BialgHom.ext_iff.1 h₁

@[simp]
/-
**BialgEquiv.coe_ofBialgHom** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：coe_ofBialgHom (f : A ->ₐc[R] B) (g : B ->ₐc[R] A) (h₁ h₂) : ofBialgHom f 
g h₁ h₂ = f
参数：f : A ->ₐc[R] B；g : B ->ₐc[R] A；h₁ h₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgEquivClass.toBialgHomClass`：∀ {F : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {B : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 :
 Semiring B] [inst_3 …
· 使用定理 `BialgEquiv.instBialgEquivClass`：∀ {R : Type u} {A : Type v} {B : Type w}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [inst_…
-/
theorem coe_ofBialgHom (f : A →ₐc[R] B) (g : B →ₐc[R] A) (h₁ h₂) :
    ofBialgHom f g h₁ h₂ = f :=
  rfl
/-
**BialgEquiv.ofBialgHom_symm** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：ofBialgHom_symm (f : A ->ₐc[R] B) (g : B ->ₐc[R] A) (h₁ h₂) : (ofBialgHom 
f g h₁ h₂).symm = ofBialgHom g f h₂ h₁
参数：f : A ->ₐc[R] B；g : B ->ₐc[R] A；h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBialgHom_symm (f : A →ₐc[R] B) (g : B →ₐc[R] A) (h₁ h₂) :
    (ofBialgHom f g h₁ h₂).symm = ofBialgHom g f h₂ h₁ :=
  rfl

end

variable [Semiring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]

/-- Construct a bialgebra equiv from an algebra equiv respecting counit and comultiplication. -/
/-
**BialgEquiv.ofAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `BialgEquiv`。
形式化陈述：{R : Type u} →   {A : Type v} →     {B : Type w} →       [inst : CommSemir
ing R] →         [inst_1 : Semiring A] →           [inst_2 : Semiring B] →      
       [inst_3 : Bialgebra R A] →               [inst_4 : Bialgebra R B] →      
           (f : A ≃ₐ[R] B) →                   (Bialgebra.counitAlgHom R B).comp
 ↑f = Bialgebra.counitAlgHom R A →                     (Algebra.TensorProduct.ma
p ↑f ↑f).comp (Bialgebra.comulAlgHom R A) =                         (Bialgebra.c
omulAlgHom R B).comp ↑f →                       A ≃ₐc[R] B
参数：f : A ≃ₐ[R] B；Bialgebra.counitAlgHom R B；Algebra.TensorProduct.map ↑f ↑f；Bial
gebra.comulAlgHom R A；Bialgebra.comulAlgHom R B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bialgebra equiv from an algebra equiv respecting counit and comultip
lication.
-/
@[simps apply] def ofAlgEquiv (f : A ≃ₐ[R] B)
    (counit_comp : (Bialgebra.counitAlgHom R B).comp f = Bialgebra.counitAlgHom R A)
    (map_comp_comul : (Algebra.TensorProduct.map f f).comp (Bialgebra.comulAlgHom R A) =
        (Bialgebra.comulAlgHom R B).comp f) : A ≃ₐc[R] B where
  __ := f
  map_smul' := map_smul f
  counit_comp := congr($(counit_comp).toLinearMap)
  map_comp_comul := congr($(map_comp_comul).toLinearMap)

@[simp]
/-
**BialgEquiv.toLinearMap_ofAlgEquiv** 是 Mathlib 中的一个引理，位于命名空间 `BialgEquiv`。
形式化陈述：toLinearMap_ofAlgEquiv (f : A ≃ₐ[R] B) (counit_comp map_comp_comul) : (ofA
lgEquiv f counit_comp map_comp_comul : A ->ₗ[R] B) = f
参数：f : A ≃ₐ[R] B；counit_comp map_comp_comul。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma toLinearMap_ofAlgEquiv (f : A ≃ₐ[R] B) (counit_comp map_comp_comul) :
    (ofAlgEquiv f counit_comp map_comp_comul : A →ₗ[R] B) = f := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Promotes a bijective bialgebra homomorphism to a bialgebra equivalence. -/
@[simps! apply]
/-
**BialgEquiv.ofBijective** 是 Mathlib 中的一个定义，位于命名空间 `BialgEquiv`。
形式化陈述：ofBijective (f : A ->ₐc[R] B) (hf : Bijective f) : A ≃ₐc[R] B
参数：f : A ->ₐc[R] B；hf : Bijective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Promotes a bijective bialgebra homomorphism to a bialgebra equivalence.
-/
noncomputable def ofBijective (f : A →ₐc[R] B) (hf : Bijective f) : A ≃ₐc[R] B :=
  .ofAlgEquiv (.ofBijective (f : A →ₐ[R] B) hf) (by ext; simp) (by ext; simp)

@[simp]
/-
**BialgEquiv.coe_ofBijective** 是 Mathlib 中的一个引理，位于命名空间 `BialgEquiv`。
形式化陈述：coe_ofBijective (f : A ->ₐc[R] B) (hf : Bijective f) : (ofBijective f hf :
 A -> B) = f
参数：f : A ->ₐc[R] B；hf : Bijective f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_ofBijective (f : A →ₐc[R] B) (hf : Bijective f) : (ofBijective f hf : A → B) = f := rfl

end BialgEquiv

