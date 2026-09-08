/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Ring.Action.Group

/-!
# Isomorphisms of `R`-algebras

This file defines bundled isomorphisms of `R`-algebras.

## Main definitions

* `AlgEquiv R A B`: the type of `R`-algebra isomorphisms between `A` and `B`.

## Notation

* `A ≃ₐ[R] B` : `R`-algebra equivalence from `A` to `B`.
-/

@[expose] public section

universe u v w u₁ v₁ u₂ u₃

/-- An equivalence of algebras (denoted as `A ≃ₐ[R] B`)
is an equivalence of rings commuting with the actions of scalars. -/
/-
**AlgEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) →   (A : Type v) →     (B : Type w) →       [inst : CommSemir
ing R] →         [inst_1 : Semiring A] → [inst_2 : Semiring B] → [Algebra R A] →
 [Algebra R B] → Type (max v w)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of algebras (denoted as `A ≃ₐ[R] B`)
is an equivalence of rings commuting with the actions of scalars.
-/
structure AlgEquiv (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] extends A ≃ B, A ≃* B, A ≃+ B, A ≃+* B where
  /-- An equivalence of algebras commutes with the action of scalars. -/
  protected commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r

attribute [nolint docBlame] AlgEquiv.toRingEquiv
attribute [nolint docBlame] AlgEquiv.toEquiv
attribute [nolint docBlame] AlgEquiv.toAddEquiv
attribute [nolint docBlame] AlgEquiv.toMulEquiv

@[inherit_doc]
notation:50 A " ≃ₐ[" R "] " A' => AlgEquiv R A A'

/-- `AlgEquivClass F R A B` states that `F` is a type of algebra structure preserving
  equivalences. You should extend this class when you extend `AlgEquiv`. -/
/-
**AlgEquivClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   (R : outParam (Type u_2)) →     (A : outParam (Type u_3
)) →       (B : outParam (Type u_4)) →         [inst : CommSemiring R] →        
   [inst_1 : Semiring A] → [inst_2 : Semiring B] → [Algebra R A] → [Algebra R B]
 → [EquivLike F A B] → Prop
参数：Type u_2；Type u_3；Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AlgEquivClass F R A B` states that `F` is a type of algebra structure preservin
g
  equivalences. You should extend this class when you extend `AlgEquiv`.
-/
class AlgEquivClass (F : Type*) (R A B : outParam Type*) [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [EquivLike F A B] : Prop
    extends RingEquivClass F A B where
  /-- An equivalence of algebras commutes with the action of scalars. -/
  commutes : ∀ (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r

namespace AlgEquivClass

-- See note [lower instance priority]
/-
**AlgEquivClass.** 是 Mathlib 中的一个实例，位于命名空间 `AlgEquivClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toAlgHomClass (F R A B : Type*) [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [EquivLike F A B] [h : AlgEquivClass F R A B] :
    AlgHomClass F R A B :=
  { h with }
/-
**AlgEquivClass.** 是 Mathlib 中的一个实例，位于命名空间 `AlgEquivClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toLinearEquivClass (F R A B : Type*) [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [EquivLike F A B] [h : AlgEquivClass F R A B] : LinearEquivClass F R A B :=
  { h with map_smulₛₗ := fun f => map_smulₛₗ f }

/-- Turn an element of a type `F` satisfying `AlgEquivClass F R A B` into an actual `AlgEquiv`.
This is declared as the default coercion from `F` to `A ≃ₐ[R] B`. -/
@[coe]
/-
**AlgEquivClass.toAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquivClass`。
形式化陈述：toAlgEquiv {F R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [A
lgebra R A] [Algebra R B] [EquivLike F A B] [AlgEquivClass F R A B] (f : F) : A 
≃ₐ[R] B
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `AlgEquivClass.commutes`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A : 
outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {inst_1
 : Semiring …

--- 原说明 ---
Turn an element of a type `F` satisfying `AlgEquivClass F R A B` into an actual 
`AlgEquiv`.
This is declared as the default coercion from `F` to `A ≃ₐ[R] B`.
-/
def toAlgEquiv {F R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
    [Algebra R B] [EquivLike F A B] [AlgEquivClass F R A B] (f : F) : A ≃ₐ[R] B :=
  { (f : A ≃ B), (RingEquivClass.toRingEquiv f : A ≃+* B) with commutes' := commutes f }

end AlgEquivClass

namespace AlgEquiv

universe uR uA₁ uA₂ uA₃ uA₁' uA₂' uA₃'
variable {R : Type uR}
variable {A₁ : Type uA₁} {A₂ : Type uA₂} {A₃ : Type uA₃}
variable {A₁' : Type uA₁'} {A₂' : Type uA₂'} {A₃' : Type uA₃'}

section Semiring

variable [CommSemiring R] [Semiring A₁] [Semiring A₂] [Semiring A₃]
variable [Semiring A₁'] [Semiring A₂'] [Semiring A₃']
variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]
variable [Algebra R A₁'] [Algebra R A₂'] [Algebra R A₃']
variable (e : A₁ ≃ₐ[R] A₂)

section coe

/-
**AlgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `AlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (A₁ ≃ₐ[R] A₂) A₁ A₂ where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨f, _⟩, _⟩ := f
    obtain ⟨⟨g, _⟩, _⟩ := g
    congr

/-- Helper instance since the coercion is not always found. -/
/-
**AlgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `AlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper instance since the coercion is not always found.
-/
instance : FunLike (A₁ ≃ₐ[R] A₂) A₁ A₂ where
  coe := DFunLike.coe
  coe_injective := DFunLike.coe_injective
/-
**AlgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `AlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AlgEquivClass (A₁ ≃ₐ[R] A₂) R A₁ A₂ where
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  commutes f := f.commutes'

@[ext]
/-
**AlgEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : A₁ ≃ₐ[R] A₂} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
/-
**AlgEquiv.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst : CommSemiring R] [i
nst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algebra R A₁] [inst_4 : 
Algebra R A₂] {f : A₁ ≃ₐ[R] A₂} {x x' : A₁}, x = x' → f x = f x'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
-/
protected theorem congr_arg {f : A₁ ≃ₐ[R] A₂} {x x' : A₁} : x = x' → f x = f x' :=
  DFunLike.congr_arg f
/-
**AlgEquiv.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst : CommSemiring R] [i
nst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algebra R A₁] [inst_4 : 
Algebra R A₂] {f g : A₁ ≃ₐ[R] A₂}, f = g → ∀ (x : A₁), f x = g x
参数：x : A₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected theorem congr_fun {f g : A₁ ≃ₐ[R] A₂} (h : f = g) (x : A₁) : f x = g x :=
  DFunLike.congr_fun h x

@[simp]
/-
**AlgEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：coe_mk {toEquiv map_mul map_add commutes} : ⇑(⟨toEquiv, map_mul, map_add, 
commutes⟩ : A₁ ≃ₐ[R] A₂) = toEquiv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk {toEquiv map_mul map_add commutes} :
    ⇑(⟨toEquiv, map_mul, map_add, commutes⟩ : A₁ ≃ₐ[R] A₂) = toEquiv :=
  rfl

@[simp]
/-
**AlgEquiv.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：mk_coe (e : A₁ ≃ₐ[R] A₂) (e' h₁ h₂ h₃ h₄ h₅) : (⟨⟨e, e', h₁, h₂⟩, h₃, h₄, 
h₅⟩ : A₁ ≃ₐ[R] A₂) = e
参数：e : A₁ ≃ₐ[R] A₂；e' h₁ h₂ h₃ h₄ h₅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
-/
theorem mk_coe (e : A₁ ≃ₐ[R] A₂) (e' h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨e, e', h₁, h₂⟩, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂) = e :=
  ext fun _ => rfl

@[simp]
/-
**AlgEquiv.toEquiv_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toEquiv_eq_coe : e.toEquiv = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_eq_coe : e.toEquiv = e :=
  rfl

@[simp]
/-
**AlgEquiv.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst : CommSemiring R] [i
nst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algebra R A₁] [inst_4 : 
Algebra R A₂] {F : Type u_1} [inst_5 : EquivLike F A₁ A₂]   [inst_6 : AlgEquivCl
ass F R A₁ A₂] (f : F), ⇑↑f = ⇑f
参数：f : F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_coe {F : Type*} [EquivLike F A₁ A₂] [AlgEquivClass F R A₁ A₂] (f : F) :
    ⇑(AlgEquivClass.toAlgEquiv f) = f :=
  rfl
/-
**AlgEquiv.coe_fun_injective** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：coe_fun_injective : @Function.Injective (A₁ ≃ₐ[R] A₂) (A₁ -> A₂) fun e => 
(e : A₁ -> A₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_fun_injective : @Function.Injective (A₁ ≃ₐ[R] A₂) (A₁ → A₂) fun e => (e : A₁ → A₂) :=
  DFunLike.coe_injective

/-- Forgetting the multiplicative structures, an equivalence of algebras is a linear equivalence. -/
/-
**AlgEquiv.toLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：{R : Type uR} →   {A₁ : Type uA₁} →     {A₂ : Type uA₂} →       [inst : Co
mmSemiring R] →         [inst_1 : Semiring A₁] →           [inst_2 : Semiring A₂
] → [inst_3 : Algebra R A₁] → [inst_4 : Algebra R A₂] → (A₁ ≃ₐ[R] A₂) → A₁ ≃ₗ[R]
 A₂
参数：A₁ ≃ₐ[R] A₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Forgetting the multiplicative structures, an equivalence of algebras is a linear
 equivalence.
-/
@[coe, simps! apply] def toLinearEquiv (e : A₁ ≃ₐ[R] A₂) : A₁ ≃ₗ[R] A₂ where
  toAddEquiv := e.toAddEquiv
  map_smul' := map_smulₛₗ e
/-
**AlgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `AlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (A₁ ≃ₐ[R] A₂) (A₁ ≃ₗ[R] A₂) where coe := toLinearEquiv
/-
**AlgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `AlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (A₁ ≃ₐ[R] A₂) (A₁ ≃+* A₂) where coe := toRingEquiv

@[simp]
/-
**AlgEquiv.coe_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：coe_toEquiv : ((e : A₁ ≃ A₂) : A₁ -> A₂) = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toEquiv : ((e : A₁ ≃ A₂) : A₁ → A₂) = e :=
  rfl

@[deprecated "Now a syntactic equality" (since := "2026-04-09"), nolint synTaut]
/-
**AlgEquiv.toRingEquiv_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toRingEquiv_eq_coe : e.toRingEquiv = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRingEquiv_eq_coe : e.toRingEquiv = e :=
  rfl

@[simp]
/-
**AlgEquiv.toRingEquiv_toRingHom** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：toRingEquiv_toRingHom : ((e : A₁ ≃+* A₂) : A₁ ->+* A₂) = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
lemma toRingEquiv_toRingHom : ((e : A₁ ≃+* A₂) : A₁ →+* A₂) = e :=
  rfl
/-
**AlgEquiv.coe_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：coe_ringEquiv : ((e : A₁ ≃+* A₂) : A₁ -> A₂) = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ringEquiv : ((e : A₁ ≃+* A₂) : A₁ → A₂) = e := rfl

@[deprecated (since := "2026-06-21")] alias coe_ringEquiv' := coe_ringEquiv
/-
**AlgEquiv.coe_ringEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：coe_ringEquiv_injective : Function.Injective ((↑) : (A₁ ≃ₐ[R] A₂) -> A₁ ≃+
* A₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `RingEquiv.congr_fun`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] {f g : R ≃+* S},   f = g → ∀ (x :
 R), f x …
-/
theorem coe_ringEquiv_injective : Function.Injective ((↑) : (A₁ ≃ₐ[R] A₂) → A₁ ≃+* A₂) :=
  fun _ _ h => ext <| RingEquiv.congr_fun h

/-- Interpret an algebra equivalence as an algebra homomorphism.

This definition is included for symmetry with the other `to*Hom` projections.
The `simp` normal form is to use the coercion of the `AlgHomClass.coeTC` instance. -/
@[coe]
/-
**AlgEquiv.toAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：toAlgHom : A₁ ->ₐ[R] A₂
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.map_mul'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A]
 [inst_…
· 使用定理 `AlgEquiv.map_add'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A]
 [inst_…
· 使用定理 `AlgEquiv.commutes'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A
] [inst_…

--- 原说明 ---
Interpret an algebra equivalence as an algebra homomorphism.

This definition is included for symmetry with the other `to*Hom` projections.
The `simp` normal form is to use the coercion of the `AlgHomClass.coeTC` instanc
e.
-/
def toAlgHom : A₁ →ₐ[R] A₂ :=
  { e with
    map_one' := map_one e
    map_zero' := map_zero e }
/-
**AlgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `AlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (A₁ ≃ₐ[R] A₂) (A₁ →ₐ[R] A₂) where coe := AlgEquiv.toAlgHom

@[deprecated "Now a syntactic equality" (since := "2026-04-29"), nolint synTaut]
/-
**AlgEquiv.toAlgHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toAlgHom_eq_coe : e.toAlgHom = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAlgHom_eq_coe : e.toAlgHom = e :=
  rfl
/-
**AlgEquiv.toAlgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toAlgHom_apply (x : A₁) : e.toAlgHom x = e x
参数：x : A₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAlgHom_apply (x : A₁) : e.toAlgHom x = e x :=
  rfl

@[simp, norm_cast]
/-
**AlgEquiv.coe_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：coe_toAlgHom : DFunLike.coe e.toAlgHom = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAlgHom :  DFunLike.coe e.toAlgHom = e := rfl
/-
**AlgEquiv.coe_toAlgHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：coe_toAlgHom_injective : Function.Injective ((↑) : (A₁ ≃ₐ[R] A₂) -> A₁ ->ₐ
[R] A₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
-/
theorem coe_toAlgHom_injective : Function.Injective ((↑) : (A₁ ≃ₐ[R] A₂) → A₁ →ₐ[R] A₂) :=
  fun _ _ h => ext <| AlgHom.congr_fun h

@[deprecated (since := "2026-05-05")] alias coe_algHom := coe_toAlgHom
@[deprecated (since := "2026-05-05")] alias coe_algHom_injective := coe_toAlgHom_injective

@[simp, norm_cast]
/-
**AlgEquiv.toAlgHom_toRingHom** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：toAlgHom_toRingHom : ((e : A₁ ->ₐ[R] A₂) : A₁ ->+* A₂) = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
lemma toAlgHom_toRingHom : ((e : A₁ →ₐ[R] A₂) : A₁ →+* A₂) = e :=
  rfl

/-- The two paths coercion can take to a `RingHom` are equivalent -/
/-
**AlgEquiv.coe_ringHom_commutes** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：coe_ringHom_commutes : ((e : A₁ ->ₐ[R] A₂) : A₁ ->+* A₂) = ((e : A₁ ≃+* A₂
) : A₁ ->+* A₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …

--- 原说明 ---
The two paths coercion can take to a `RingHom` are equivalent
-/
theorem coe_ringHom_commutes : ((e : A₁ →ₐ[R] A₂) : A₁ →+* A₂) = ((e : A₁ ≃+* A₂) : A₁ →+* A₂) :=
  rfl

@[simp]
/-
**AlgEquiv.commutes** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：commutes : forall r : R, e (algebraMap R A₁ r) = algebraMap R A₂ r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.commutes'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A
] [inst_…
-/
theorem commutes : ∀ r : R, e (algebraMap R A₁ r) = algebraMap R A₂ r :=
  e.commutes'

end coe

section bijective

/-
**AlgEquiv.bijective** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst : CommSemiring R] [i
nst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algebra R A₁] [inst_4 : 
Algebra R A₂] (e : A₁ ≃ₐ[R] A₂), Function.Bijective ⇑e
参数：e : A₁ ≃ₐ[R] A₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.bijective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Bijective ⇑e
-/
protected theorem bijective : Function.Bijective e :=
  EquivLike.bijective e
/-
**AlgEquiv.injective** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst : CommSemiring R] [i
nst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algebra R A₁] [inst_4 : 
Algebra R A₂] (e : A₁ ≃ₐ[R] A₂), Function.Injective ⇑e
参数：e : A₁ ≃ₐ[R] A₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
-/
protected theorem injective : Function.Injective e :=
  EquivLike.injective e
/-
**AlgEquiv.surjective** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst : CommSemiring R] [i
nst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algebra R A₁] [inst_4 : 
Algebra R A₂] (e : A₁ ≃ₐ[R] A₂), Function.Surjective ⇑e
参数：e : A₁ ≃ₐ[R] A₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
-/
protected theorem surjective : Function.Surjective e :=
  EquivLike.surjective e

end bijective

section refl

/-- Algebra equivalences are reflexive. -/
@[refl]
/-
**AlgEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：refl : A₁ ≃ₐ[R] A₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Algebra equivalences are reflexive.
-/
def refl : A₁ ≃ₐ[R] A₁ :=
  { (.refl _ : A₁ ≃+* A₁) with commutes' := fun _ => rfl }
/-
**AlgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `AlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (A₁ ≃ₐ[R] A₁) :=
  ⟨refl⟩
/-
**AlgEquiv.refl_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ {R : Type uR} {A₁ : Type uA₁} [inst : CommSemiring R] [inst_1 : Semiring
 A₁] [inst_2 : Algebra R A₁],   ↑AlgEquiv.refl = AlgHom.id R A₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma refl_toAlgHom : (refl : A₁ ≃ₐ[R] A₁) = AlgHom.id R A₁ := rfl
/-
**AlgEquiv.refl_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ {R : Type uR} {A₁ : Type uA₁} [inst : CommSemiring R] [inst_1 : Semiring
 A₁] [inst_2 : Algebra R A₁],   ↑AlgEquiv.refl = RingHom.id A₁
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
@[simp, norm_cast] lemma refl_toRingHom : (refl : A₁ ≃ₐ[R] A₁) = RingHom.id A₁ := rfl

@[simp]
/-
**AlgEquiv.coe_refl** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：coe_refl : ⇑(refl : A₁ ≃ₐ[R] A₁) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_refl : ⇑(refl : A₁ ≃ₐ[R] A₁) = id :=
  rfl

end refl

section symm

/-- Algebra equivalences are symmetric. -/
@[symm]
/-
**AlgEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：symm (e : A₁ ≃ₐ[R] A₂) : A₂ ≃ₐ[R] A₁
参数：e : A₁ ≃ₐ[R] A₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Algebra equivalences are symmetric.
-/
def symm (e : A₁ ≃ₐ[R] A₂) : A₂ ≃ₐ[R] A₁ :=
  { e.toRingEquiv.symm with
    commutes' := fun r => by
      rw [← e.toRingEquiv.symm_apply_apply (algebraMap R A₁ r)]
      congr
      simp }
/-
**AlgEquiv.invFun_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：invFun_eq_symm {e : A₁ ≃ₐ[R] A₂} : e.invFun = e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invFun_eq_symm {e : A₁ ≃ₐ[R] A₂} : e.invFun = e.symm :=
  rfl

@[simp]
/-
**AlgEquiv.coe_apply_coe_coe_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：coe_apply_coe_coe_symm_apply {F : Type*} [EquivLike F A₁ A₂] [AlgEquivClas
s F R A₁ A₂] (f : F) (x : A₂) : f ((AlgEquivClass.toAlgEquiv f).symm x) = x
参数：f : F；x : A₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.right_inv`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β : out
Param (Sort u_3)} [self : EquivLike E α β] (e : E),   Function.RightInverse (Equ
ivLike.in…
-/
theorem coe_apply_coe_coe_symm_apply {F : Type*} [EquivLike F A₁ A₂] [AlgEquivClass F R A₁ A₂]
    (f : F) (x : A₂) :
    f ((AlgEquivClass.toAlgEquiv f).symm x) = x :=
  EquivLike.right_inv f x

@[simp]
/-
**AlgEquiv.coe_coe_symm_apply_coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：coe_coe_symm_apply_coe_apply {F : Type*} [EquivLike F A₁ A₂] [AlgEquivClas
s F R A₁ A₂] (f : F) (x : A₁) : (AlgEquivClass.toAlgEquiv f).symm (f x) = x
参数：f : F；x : A₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.left_inv`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β : outP
aram (Sort u_3)} [self : EquivLike E α β] (e : E),   Function.LeftInverse (Equiv
Like.inv…
-/
theorem coe_coe_symm_apply_coe_apply {F : Type*} [EquivLike F A₁ A₂] [AlgEquivClass F R A₁ A₂]
    (f : F) (x : A₁) :
    (AlgEquivClass.toAlgEquiv f).symm (f x) = x :=
  EquivLike.left_inv f x

/-- `simp` normal form of `invFun_eq_symm` -/
@[simp]
/-
**AlgEquiv.symm_toEquiv_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：symm_toEquiv_eq_symm {e : A₁ ≃ₐ[R] A₂} : (e : A₁ ≃ A₂).symm = e.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`simp` normal form of `invFun_eq_symm`
-/
theorem symm_toEquiv_eq_symm {e : A₁ ≃ₐ[R] A₂} : (e : A₁ ≃ A₂).symm = e.symm :=
  rfl

@[simp]
/-
**AlgEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：symm_symm (e : A₁ ≃ₐ[R] A₂) : e.symm.symm = e
参数：e : A₁ ≃ₐ[R] A₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (e : A₁ ≃ₐ[R] A₂) : e.symm.symm = e := rfl
/-
**AlgEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：symm_bijective : Function.Bijective (symm : (A₁ ≃ₐ[R] A₂) -> A₂ ≃ₐ[R] A₁)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `AlgEquiv.symm_symm`：symm_symm (e : A₁ ≃ₐ[R] A₂) : e.symm.symm = e
-/
theorem symm_bijective : Function.Bijective (symm : (A₁ ≃ₐ[R] A₂) → A₂ ≃ₐ[R] A₁) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/-
**AlgEquiv.mk_coe'** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：mk_coe' (e : A₁ ≃ₐ[R] A₂) (f h₁ h₂ h₃ h₄ h₅) : (⟨⟨f, e, h₁, h₂⟩, h₃, h₄, h
₅⟩ : A₂ ≃ₐ[R] A₁) = e.symm
参数：e : A₁ ≃ₐ[R] A₂；f h₁ h₂ h₃ h₄ h₅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `AlgEquiv.symm_bijective`：symm_bijective : Function.Bijective (symm : (A₁
 ≃ₐ[R] A₂) -> A₂ ≃ₐ[R] A₁)
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
-/
theorem mk_coe' (e : A₁ ≃ₐ[R] A₂) (f h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨f, e, h₁, h₂⟩, h₃, h₄, h₅⟩ : A₂ ≃ₐ[R] A₁) = e.symm :=
  symm_bijective.injective <| ext fun _ => rfl

@[simp]
/-
**AlgEquiv.symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：symm_mk (e : A₁ ≃ A₂) (h₁ h₂ h₃) : dsimp% (mk e h₁ h₂ h₃ : A₁ ≃ₐ[R] A₂).sy
mm = { (mk e h₁ h₂ h₃ : A₁ ≃ₐ[R] A₂).symm with toEquiv
参数：e : A₁ ≃ A₂；h₁ h₂ h₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_mk (e : A₁ ≃ A₂) (h₁ h₂ h₃) : dsimp%
    (mk e h₁ h₂ h₃ : A₁ ≃ₐ[R] A₂).symm =
      { (mk e h₁ h₂ h₃ : A₁ ≃ₐ[R] A₂).symm with
        toEquiv := e.symm } :=
  rfl

@[simp]
/-
**AlgEquiv.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：refl_symm : (AlgEquiv.refl : A₁ ≃ₐ[R] A₁).symm = AlgEquiv.refl
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_symm : (AlgEquiv.refl : A₁ ≃ₐ[R] A₁).symm = AlgEquiv.refl :=
  rfl
/-
**AlgEquiv.toRingEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toRingEquiv_symm : (e : A₁ ≃+* A₂).symm = e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRingEquiv_symm : (e : A₁ ≃+* A₂).symm = e.symm :=
  rfl

@[simp]
/-
**AlgEquiv.symm_toRingEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：symm_toRingEquiv : (e.symm : A₂ ≃+* A₁) = (e : A₁ ≃+* A₂).symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_toRingEquiv : (e.symm : A₂ ≃+* A₁) = (e : A₁ ≃+* A₂).symm :=
  rfl

@[simp]
/-
**AlgEquiv.symm_toAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：symm_toAddEquiv : (e.symm : A₂ ≃+ A₁) = (e : A₁ ≃+ A₂).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearEquivClass.toAddEquivClass`：∀ {F : Type u_14} {R : outParam (T
ype u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S} 
  {σ : outParam (R →+* S)}…
· 使用定理 `AlgEquivClass.toLinearEquivClass`：∀ (F : Type u_1) (R : Type u_2) (A : T
ype u_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 
: Semiring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
theorem symm_toAddEquiv : (e.symm : A₂ ≃+ A₁) = (e : A₁ ≃+ A₂).symm :=
  rfl

@[simp]
/-
**AlgEquiv.symm_toMulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：symm_toMulEquiv : (e.symm : A₂ ≃* A₁) = (e : A₁ ≃* A₂).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
theorem symm_toMulEquiv : (e.symm : A₂ ≃* A₁) = (e : A₁ ≃* A₂).symm :=
  rfl

@[simp]
/-
**AlgEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x, e (e.symm x) = x
参数：e : A₁ ≃ₐ[R] A₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply

@[simp]
/-
**AlgEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x, e.symm (e x) = x
参数：e : A₁ ≃ₐ[R] A₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply
/-
**AlgEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：symm_apply_eq (e : A₁ ≃ₐ[R] A₂) {x y} : e.symm x = y ↔ x = e y
参数：e : A₁ ≃ₐ[R] A₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem symm_apply_eq (e : A₁ ≃ₐ[R] A₂) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq
/-
**AlgEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：eq_symm_apply (e : A₁ ≃ₐ[R] A₂) {x y} : y = e.symm x ↔ e y = x
参数：e : A₁ ≃ₐ[R] A₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem eq_symm_apply (e : A₁ ≃ₐ[R] A₂) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

@[simp]
/-
**AlgEquiv.comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：comp_symm (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp (e : A₁ ->ₐ[R] A₂) ↑e.symm = Alg
Hom.id R A₂
参数：e : A₁ ≃ₐ[R] A₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_symm (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp (e : A₁ →ₐ[R] A₂) ↑e.symm = AlgHom.id R A₂ := by
  ext
  simp

@[simp]
/-
**AlgEquiv.symm_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：symm_comp (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp ↑e.symm (e : A₁ ->ₐ[R] A₂) = Alg
Hom.id R A₁
参数：e : A₁ ≃ₐ[R] A₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symm_comp (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp ↑e.symm (e : A₁ →ₐ[R] A₂) = AlgHom.id R A₁ := by
  ext
  simp
/-
**AlgEquiv.leftInverse_symm** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：leftInverse_symm (e : A₁ ≃ₐ[R] A₂) : Function.LeftInverse e.symm e
参数：e : A₁ ≃ₐ[R] A₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
theorem leftInverse_symm (e : A₁ ≃ₐ[R] A₂) : Function.LeftInverse e.symm e :=
  e.left_inv
/-
**AlgEquiv.rightInverse_symm** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：rightInverse_symm (e : A₁ ≃ₐ[R] A₂) : Function.RightInverse e.symm e
参数：e : A₁ ≃ₐ[R] A₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem rightInverse_symm (e : A₁ ≃ₐ[R] A₂) : Function.RightInverse e.symm e :=
  e.right_inv
/-
**AlgEquiv.image_symm_eq_preimage** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：image_symm_eq_preimage (e : A₁ ≃ₐ[R] A₂) (s : Set A₂) : e.symm '' s = e ⁻¹
' s
参数：e : A₁ ≃ₐ[R] A₂；s : Set A₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.image_symm_eq_preimage`：∀ {R : Type u_1} {S : Type u_6} {M :
 Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 :
 AddCommMonoid M] [inst_…
-/
lemma image_symm_eq_preimage (e : A₁ ≃ₐ[R] A₂) (s : Set A₂) : e.symm '' s = e ⁻¹' s :=
  e.toLinearEquiv.image_symm_eq_preimage _

end symm

section simps

/-- See Note [custom simps projection] -/
/-
**AlgEquiv.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv.Simps`。
形式化陈述：{R : Type uR} →   {A₁ : Type uA₁} →     {A₂ : Type uA₂} →       [inst : Co
mmSemiring R] →         [inst_1 : Semiring A₁] →           [inst_2 : Semiring A₂
] → [inst_3 : Algebra R A₁] → [inst_4 : Algebra R A₂] → (A₁ ≃ₐ[R] A₂) → A₁ → A₂
参数：A₁ ≃ₐ[R] A₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.apply (e : A₁ ≃ₐ[R] A₂) : A₁ → A₂ :=
  e

/-- See Note [custom simps projection] -/
/-
**AlgEquiv.Simps.toEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv.Simps`。
形式化陈述：{R : Type uR} →   {A₁ : Type uA₁} →     {A₂ : Type uA₂} →       [inst : Co
mmSemiring R] →         [inst_1 : Semiring A₁] →           [inst_2 : Semiring A₂
] → [inst_3 : Algebra R A₁] → [inst_4 : Algebra R A₂] → (A₁ ≃ₐ[R] A₂) → A₁ ≃ A₂
参数：A₁ ≃ₐ[R] A₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.toEquiv (e : A₁ ≃ₐ[R] A₂) : A₁ ≃ A₂ :=
  e

/-- See Note [custom simps projection] -/
/-
**AlgEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv.Simps`。
形式化陈述：{R : Type uR} →   {A₁ : Type uA₁} →     {A₂ : Type uA₂} →       [inst : Co
mmSemiring R] →         [inst_1 : Semiring A₁] →           [inst_2 : Semiring A₂
] → [inst_3 : Algebra R A₁] → [inst_4 : Algebra R A₂] → (A₁ ≃ₐ[R] A₂) → A₂ → A₁
参数：A₁ ≃ₐ[R] A₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (e : A₁ ≃ₐ[R] A₂) : A₂ → A₁ :=
  e.symm

initialize_simps_projections AlgEquiv (toFun → apply, invFun → symm_apply)

end simps

section trans

/-- Algebra equivalences are transitive. -/
@[trans]
/-
**AlgEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : A₁ ≃ₐ[R] A₃
参数：e₁ : A₁ ≃ₐ[R] A₂；e₂ : A₂ ≃ₐ[R] A₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Algebra equivalences are transitive.
-/
def trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : A₁ ≃ₐ[R] A₃ :=
  { e₁.toRingEquiv.trans e₂.toRingEquiv with
    commutes' := fun r => show e₂.toFun (e₁.toFun _) = _ by rw [e₁.commutes', e₂.commutes'] }

@[simp]
/-
**AlgEquiv.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：coe_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁
参数：e₁ : A₁ ≃ₐ[R] A₂；e₂ : A₂ ≃ₐ[R] A₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
/-
**AlgEquiv.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₁) : (e₁.trans e₂)
 x = e₂ (e₁ x)
参数：e₁ : A₁ ≃ₐ[R] A₂；e₂ : A₂ ≃ₐ[R] A₃；x : A₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₁) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl

@[simp]
/-
**AlgEquiv.symm_trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：symm_trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₃) : (e₁.tran
s e₂).symm x = e₁.symm (e₂.symm x)
参数：e₁ : A₁ ≃ₐ[R] A₂；e₂ : A₂ ≃ₐ[R] A₃；x : A₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₃) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl
/-
**AlgEquiv.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst : CommSemiring R] [i
nst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algebra R A₁] [inst_4 : 
Algebra R A₂] (e : A₁ ≃ₐ[R] A₂), e.trans e.symm = AlgEquiv.refl
参数：e : A₁ ≃ₐ[R] A₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma self_trans_symm (e : A₁ ≃ₐ[R] A₂) : e.trans e.symm = refl := by ext; simp
/-
**AlgEquiv.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst : CommSemiring R] [i
nst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algebra R A₁] [inst_4 : 
Algebra R A₂] (e : A₁ ≃ₐ[R] A₂), e.symm.trans e = AlgEquiv.refl
参数：e : A₁ ≃ₐ[R] A₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma symm_trans_self (e : A₁ ≃ₐ[R] A₂) : e.symm.trans e = refl := by ext; simp

@[simp, norm_cast]
/-
**AlgEquiv.toRingHom_trans** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：toRingHom_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : (e₁.trans e₂ : A₁ 
->+* A₃) = .comp e₂ (e₁ : A₁ ->+* A₂)
参数：e₁ : A₁ ≃ₐ[R] A₂；e₂ : A₂ ≃ₐ[R] A₃。
该定理/引理给出了一组等式。
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
lemma toRingHom_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
    (e₁.trans e₂ : A₁ →+* A₃) = .comp e₂ (e₁ : A₁ →+* A₂) := rfl

end trans

/-- `Equiv.cast (congrArg _ h)` as an algebra equiv.

Note that unlike `Equiv.cast`, this takes an equality of indices rather than an equality of types,
to avoid having to deal with an equality of the algebraic structure itself. -/
@[simps!]
/-
**AlgEquiv.cast** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：{R : Type uR} →   [inst : CommSemiring R] →     {ι : Type u_1} →       {A 
: ι → Type u_2} →         [inst_1 : (i : ι) → Semiring (A i)] → [inst_2 : (i : ι
) → Algebra R (A i)] → {i j : ι} → i = j → A i ≃ₐ[R] A j
参数：i : ι；A i；i : ι；A i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.cast (congrArg _ h)` as an algebra equiv.

Note that unlike `Equiv.cast`, this takes an equality of indices rather than an 
equality of types,
to avoid having to deal with an equality of the algebraic structure itself.
-/
protected def cast
    {ι : Type*} {A : ι → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] {i j : ι} (h : i = j) :
    A i ≃ₐ[R] A j where
  __ := RingEquiv.cast h
  commutes' _ := by cases h; rfl

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'`, then the type of maps
`A₁ →ₐ[R] A₂` is equivalent to the type of maps `A₁' →ₐ[R] A₂'`. -/
@[simps apply]
/-
**AlgEquiv.arrowCongr** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：arrowCongr (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') : (A₁ ->ₐ[R] A₂) ≃ (A₁'
 ->ₐ[R] A₂') where toFun f
参数：e₁ : A₁ ≃ₐ[R] A₁'；e₂ : A₂ ≃ₐ[R] A₂'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'`, then the type of
 maps
`A₁ →ₐ[R] A₂` is equivalent to the type of maps `A₁' →ₐ[R] A₂'`.
-/
def arrowCongr (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') : (A₁ →ₐ[R] A₂) ≃ (A₁' →ₐ[R] A₂') where
  toFun f := (e₂.toAlgHom.comp f).comp e₁.symm.toAlgHom
  invFun f := (e₂.symm.toAlgHom.comp f).comp e₁.toAlgHom
  left_inv f := by
    simp only [AlgHom.comp_assoc, symm_comp]
    simp only [← AlgHom.comp_assoc, symm_comp, AlgHom.id_comp, AlgHom.comp_id]
  right_inv f := by
    simp only [AlgHom.comp_assoc, comp_symm]
    simp only [← AlgHom.comp_assoc, comp_symm, AlgHom.id_comp, AlgHom.comp_id]
/-
**AlgEquiv.arrowCongr_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：arrowCongr_comp (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') (e₃ : A₃ ≃ₐ[R] A₃'
) (f : A₁ ->ₐ[R] A₂) (g : A₂ ->ₐ[R] A₃) : arrowCongr e₁ e₃ (g.comp f) = (arrowCo
ngr e₂ e₃ g).comp (arrowCongr e₁ e₂ f)
参数：e₁ : A₁ ≃ₐ[R] A₁'；e₂ : A₂ ≃ₐ[R] A₂'；e₃ : A₃ ≃ₐ[R] A₃'；f : A₁ ->ₐ[R] A₂；g : A₂
 ->ₐ[R] A₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgEquiv.arrowCongr_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA
₂} {A₁' : Type uA₁'} {A₂' : Type uA₂'} [inst : CommSemiring R]   [inst_1 : Semir
ing A₁] [inst_2…
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arrowCongr_comp (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂')
    (e₃ : A₃ ≃ₐ[R] A₃') (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₃) :
    arrowCongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f) := by
  ext
  simp

@[simp]
/-
**AlgEquiv.arrowCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：arrowCongr_refl : arrowCongr AlgEquiv.refl AlgEquiv.refl = Equiv.refl (A₁ 
->ₐ[R] A₂)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arrowCongr_refl : arrowCongr AlgEquiv.refl AlgEquiv.refl = Equiv.refl (A₁ →ₐ[R] A₂) :=
  rfl

@[simp]
/-
**AlgEquiv.arrowCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：arrowCongr_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₁' : A₁' ≃ₐ[R] A₂') (e₂ : A₂ ≃ₐ[R] A
₃) (e₂' : A₂' ≃ₐ[R] A₃') : arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCong
r e₁ e₁').trans (arrowCongr e₂ e₂')
参数：e₁ : A₁ ≃ₐ[R] A₂；e₁' : A₁' ≃ₐ[R] A₂'；e₂ : A₂ ≃ₐ[R] A₃；e₂' : A₂' ≃ₐ[R] A₃'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arrowCongr_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₁' : A₁' ≃ₐ[R] A₂')
    (e₂ : A₂ ≃ₐ[R] A₃) (e₂' : A₂' ≃ₐ[R] A₃') :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') :=
  rfl

@[simp]
/-
**AlgEquiv.arrowCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：arrowCongr_symm (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') : (arrowCongr e₁ e
₂).symm = arrowCongr e₁.symm e₂.symm
参数：e₁ : A₁ ≃ₐ[R] A₁'；e₂ : A₂ ≃ₐ[R] A₂'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem arrowCongr_symm (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') :
    (arrowCongr e₁ e₂).symm = arrowCongr e₁.symm e₂.symm :=
  rfl

/-- If `A₁` is equivalent to `A₂` and `A₁'` is equivalent to `A₂'`, then the type of maps
`A₁ ≃ₐ[R] A₁'` is equivalent to the type of maps `A₂ ≃ₐ[R] A₂'`.

This is the `AlgEquiv` version of `AlgEquiv.arrowCongr`. -/
@[simps apply]
/-
**AlgEquiv.equivCongr** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：equivCongr (e : A₁ ≃ₐ[R] A₂) (e' : A₁' ≃ₐ[R] A₂') : (A₁ ≃ₐ[R] A₁') ≃ A₂ ≃ₐ
[R] A₂' where toFun ψ
参数：e : A₁ ≃ₐ[R] A₂；e' : A₁' ≃ₐ[R] A₂'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A₁` is equivalent to `A₂` and `A₁'` is equivalent to `A₂'`, then the type of
 maps
`A₁ ≃ₐ[R] A₁'` is equivalent to the type of maps `A₂ ≃ₐ[R] A₂'`.

This is the `AlgEquiv` version of `AlgEquiv.arrowCongr`.
-/
def equivCongr (e : A₁ ≃ₐ[R] A₂) (e' : A₁' ≃ₐ[R] A₂') : (A₁ ≃ₐ[R] A₁') ≃ A₂ ≃ₐ[R] A₂' where
  toFun ψ := e.symm.trans (ψ.trans e')
  invFun ψ := e.trans (ψ.trans e'.symm)
  left_inv ψ := by
    ext
    simp_rw [trans_apply, symm_apply_apply]
  right_inv ψ := by
    ext
    simp_rw [trans_apply, apply_symm_apply]

@[simp]
/-
**AlgEquiv.equivCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：equivCongr_refl : equivCongr AlgEquiv.refl AlgEquiv.refl = Equiv.refl (A₁ 
≃ₐ[R] A₁')
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivCongr_refl : equivCongr AlgEquiv.refl AlgEquiv.refl = Equiv.refl (A₁ ≃ₐ[R] A₁') :=
  rfl

@[simp]
/-
**AlgEquiv.equivCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：equivCongr_symm (e : A₁ ≃ₐ[R] A₂) (e' : A₁' ≃ₐ[R] A₂') : (equivCongr e e')
.symm = equivCongr e.symm e'.symm
参数：e : A₁ ≃ₐ[R] A₂；e' : A₁' ≃ₐ[R] A₂'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem equivCongr_symm (e : A₁ ≃ₐ[R] A₂) (e' : A₁' ≃ₐ[R] A₂') :
    (equivCongr e e').symm = equivCongr e.symm e'.symm :=
  rfl

@[simp]
/-
**AlgEquiv.equivCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：equivCongr_trans (e₁₂ : A₁ ≃ₐ[R] A₂) (e₁₂' : A₁' ≃ₐ[R] A₂') (e₂₃ : A₂ ≃ₐ[R
] A₃) (e₂₃' : A₂' ≃ₐ[R] A₃') : (equivCongr e₁₂ e₁₂').trans (equivCongr e₂₃ e₂₃')
 = equivCongr (e₁₂.trans e₂₃) (e₁₂'.trans e₂₃')
参数：e₁₂ : A₁ ≃ₐ[R] A₂；e₁₂' : A₁' ≃ₐ[R] A₂'；e₂₃ : A₂ ≃ₐ[R] A₃；e₂₃' : A₂' ≃ₐ[R] A₃'
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem equivCongr_trans (e₁₂ : A₁ ≃ₐ[R] A₂) (e₁₂' : A₁' ≃ₐ[R] A₂')
    (e₂₃ : A₂ ≃ₐ[R] A₃) (e₂₃' : A₂' ≃ₐ[R] A₃') :
    (equivCongr e₁₂ e₁₂').trans (equivCongr e₂₃ e₂₃') =
      equivCongr (e₁₂.trans e₂₃) (e₁₂'.trans e₂₃') :=
  rfl

/-- If an algebra morphism has an inverse, it is an algebra isomorphism. -/
@[simps]
/-
**AlgEquiv.ofAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：ofAlgHom (f : A₁ ->ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ : f.comp g = AlgHom.id 
R A₂) (h₂ : g.comp f = AlgHom.id R A₁) : A₁ ≃ₐ[R] A₂
参数：f : A₁ ->ₐ[R] A₂；g : A₂ ->ₐ[R] A₁；h₁ : f.comp g = AlgHom.id R A₂；h₂ : g.comp 
f = AlgHom.id R A₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.commutes'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…

--- 原说明 ---
If an algebra morphism has an inverse, it is an algebra isomorphism.
-/
def ofAlgHom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ : f.comp g = AlgHom.id R A₂)
    (h₂ : g.comp f = AlgHom.id R A₁) : A₁ ≃ₐ[R] A₂ :=
  { f with
    toFun := f
    invFun := g
    left_inv := AlgHom.ext_iff.1 h₂
    right_inv := AlgHom.ext_iff.1 h₁ }
/-
**AlgEquiv.toAlgHom_ofAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toAlgHom_ofAlgHom (f : A₁ ->ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ h₂) : ↑(ofAlgH
om f g h₁ h₂) = f
参数：f : A₁ ->ₐ[R] A₂；g : A₂ ->ₐ[R] A₁；h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAlgHom_ofAlgHom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
    ↑(ofAlgHom f g h₁ h₂) = f :=
  rfl

@[simp]
/-
**AlgEquiv.ofAlgHom_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：ofAlgHom_toAlgHom (f : A₁ ≃ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ h₂) : ofAlgHom 
(↑f) g h₁ h₂ = f
参数：f : A₁ ≃ₐ[R] A₂；g : A₂ ->ₐ[R] A₁；h₁ h₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
-/
theorem ofAlgHom_toAlgHom (f : A₁ ≃ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
    ofAlgHom (↑f) g h₁ h₂ = f :=
  ext fun _ => rfl

@[deprecated (since := "2026-05-05")] alias coe_algHom_ofAlgHom := toAlgHom_ofAlgHom
@[deprecated (since := "2026-05-05")] alias ofAlgHom_coe_algHom := ofAlgHom_toAlgHom
/-
**AlgEquiv.ofAlgHom_symm** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：ofAlgHom_symm (f : A₁ ->ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ h₂) : (ofAlgHom f 
g h₁ h₂).symm = ofAlgHom g f h₂ h₁
参数：f : A₁ ->ₐ[R] A₂；g : A₂ ->ₐ[R] A₁；h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofAlgHom_symm (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
    (ofAlgHom f g h₁ h₂).symm = ofAlgHom g f h₂ h₁ :=
  rfl

@[simp]
/-
**AlgEquiv.toLinearEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toLinearEquiv_refl : (AlgEquiv.refl : A₁ ≃ₐ[R] A₁).toLinearEquiv = LinearE
quiv.refl R A₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_refl : (AlgEquiv.refl : A₁ ≃ₐ[R] A₁).toLinearEquiv = LinearEquiv.refl R A₁ :=
  rfl

@[simp]
/-
**AlgEquiv.toLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toLinearEquiv_symm (e : A₁ ≃ₐ[R] A₂) : e.symm.toLinearEquiv = e.toLinearEq
uiv.symm
参数：e : A₁ ≃ₐ[R] A₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_symm (e : A₁ ≃ₐ[R] A₂) : e.symm.toLinearEquiv = e.toLinearEquiv.symm :=
  rfl

@[simp]
/-
**AlgEquiv.coe_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：coe_toLinearEquiv (e : A₁ ≃ₐ[R] A₂) : ⇑e.toLinearEquiv = e
参数：e : A₁ ≃ₐ[R] A₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLinearEquiv (e : A₁ ≃ₐ[R] A₂) : ⇑e.toLinearEquiv = e := rfl

@[simp]
/-
**AlgEquiv.coe_symm_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：coe_symm_toLinearEquiv (e : A₁ ≃ₐ[R] A₂) : ⇑e.toLinearEquiv.symm = e.symm
参数：e : A₁ ≃ₐ[R] A₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_toLinearEquiv (e : A₁ ≃ₐ[R] A₂) : ⇑e.toLinearEquiv.symm = e.symm := rfl

@[simp]
/-
**AlgEquiv.toLinearEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toLinearEquiv_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : (e₁.trans e₂).
toLinearEquiv = e₁.toLinearEquiv.trans e₂.toLinearEquiv
参数：e₁ : A₁ ≃ₐ[R] A₂；e₂ : A₂ ≃ₐ[R] A₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
    (e₁.trans e₂).toLinearEquiv = e₁.toLinearEquiv.trans e₂.toLinearEquiv :=
  rfl
/-
**AlgEquiv.toLinearEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toLinearEquiv_injective : Function.Injective (toLinearEquiv : _ -> A₁ ≃ₗ[R
] A₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `LinearEquiv.congr_fun`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem toLinearEquiv_injective : Function.Injective (toLinearEquiv : _ → A₁ ≃ₗ[R] A₂) :=
  fun _ _ h => ext <| LinearEquiv.congr_fun h

/-- Interpret an algebra equivalence as a linear map. -/
/-
**AlgEquiv.toLinearMap** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgEquiv`。
形式化陈述：toLinearMap : A₁ ->ₗ[R] A₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret an algebra equivalence as a linear map.
-/
abbrev toLinearMap : A₁ →ₗ[R] A₂ :=
  e.toLinearEquiv

@[simp]
/-
**AlgEquiv.toAlgHom_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：toAlgHom_toLinearMap : e.toAlgHom.toLinearMap = e.toLinearEquiv.toLinearMa
p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAlgHom_toLinearMap : e.toAlgHom.toLinearMap = e.toLinearEquiv.toLinearMap := rfl
/-
**AlgEquiv.toLinearMap_ofAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toLinearMap_ofAlgHom (f : A₁ ->ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ h₂) : (ofAl
gHom f g h₁ h₂).toLinearMap = f.toLinearMap
参数：f : A₁ ->ₐ[R] A₂；g : A₂ ->ₐ[R] A₁；h₁ h₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem toLinearMap_ofAlgHom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
    (ofAlgHom f g h₁ h₂).toLinearMap = f.toLinearMap :=
  LinearMap.ext fun _ => rfl
/-
**AlgEquiv.toLinearEquiv_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toLinearEquiv_toLinearMap : e.toLinearEquiv.toLinearMap = e.toLinearMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_toLinearMap : e.toLinearEquiv.toLinearMap = e.toLinearMap :=
  rfl

@[simp]
/-
**AlgEquiv.toLinearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toLinearMap_apply (x : A₁) : e.toLinearMap x = e x
参数：x : A₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_apply (x : A₁) : e.toLinearMap x = e x :=
  rfl
/-
**AlgEquiv.toLinearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toLinearMap_injective : Function.Injective (toLinearMap : _ -> A₁ ->ₗ[R] A
₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem toLinearMap_injective : Function.Injective (toLinearMap : _ → A₁ →ₗ[R] A₂) := fun _ _ h =>
  ext <| LinearMap.congr_fun h

@[simp]
/-
**AlgEquiv.trans_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：trans_toLinearMap (f : A₁ ≃ₐ[R] A₂) (g : A₂ ≃ₐ[R] A₃) : (f.trans g).toLine
arMap = g.toLinearMap.comp f.toLinearMap
参数：f : A₁ ≃ₐ[R] A₂；g : A₂ ≃ₐ[R] A₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_toLinearMap (f : A₁ ≃ₐ[R] A₂) (g : A₂ ≃ₐ[R] A₃) :
    (f.trans g).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl
/-
**AlgEquiv.linearEquivConj_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst : CommSemiring R] [i
nst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algebra R A₁] [inst_4 : 
Algebra R A₂] (f : A₁ ≃ₐ[R] A₂) (x : A₁),   (↑f).conj (LinearMap.mulLeft R x) = 
LinearMap.mulLeft R (f x)
参数：f : A₁ ≃ₐ[R] A₂；x : A₁；↑f；LinearMap.mulLeft R x；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.toLinearEquiv_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem linearEquivConj_mulLeft (f : A₁ ≃ₐ[R] A₂) (x : A₁) :
    f.toLinearEquiv.conj (.mulLeft R x) = .mulLeft R (f x) := by
  ext; simp
/-
**AlgEquiv.linearEquivConj_mulRight** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst : CommSemiring R] [i
nst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algebra R A₁] [inst_4 : 
Algebra R A₂] (f : A₁ ≃ₐ[R] A₂) (x : A₁),   (↑f).conj (LinearMap.mulRight R x) =
 LinearMap.mulRight R (f x)
参数：f : A₁ ≃ₐ[R] A₂；x : A₁；↑f；LinearMap.mulRight R x；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.toLinearEquiv_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem linearEquivConj_mulRight (f : A₁ ≃ₐ[R] A₂) (x : A₁) :
    f.toLinearEquiv.conj (.mulRight R x) = .mulRight R (f x) := by
  ext; simp
/-
**AlgEquiv.linearEquivConj_mulLeftRight** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst : CommSemiring R] [i
nst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algebra R A₁] [inst_4 : 
Algebra R A₂] (f : A₁ ≃ₐ[R] A₂) (x : A₁ × A₁),   (↑f).conj (LinearMap.mulLeftRig
ht R x) = LinearMap.mulLeftRight R (Prod.map (⇑f) (⇑f) x)
参数：f : A₁ ≃ₐ[R] A₂；x : A₁ × A₁；↑f；LinearMap.mulLeftRight R x；Prod.map (⇑f) (⇑f) 
x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.toLinearEquiv_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] theorem linearEquivConj_mulLeftRight (f : A₁ ≃ₐ[R] A₂) (x : A₁ × A₁) :
    f.toLinearEquiv.conj (.mulLeftRight R x) = .mulLeftRight R (Prod.map f f x) := by
  cases x; ext; simp

/-- Promotes a bijective algebra homomorphism to an algebra equivalence. -/
/-
**AlgEquiv.ofBijective** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：ofBijective (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f) : A₁ ≃ₐ[R] A₂
参数：f : A₁ ->ₐ[R] A₂；hf : Function.Bijective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.commutes'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…

--- 原说明 ---
Promotes a bijective algebra homomorphism to an algebra equivalence.
-/
noncomputable def ofBijective (f : A₁ →ₐ[R] A₂) (hf : Function.Bijective f) : A₁ ≃ₐ[R] A₂ :=
  { RingEquiv.ofBijective (f : A₁ →+* A₂) hf, f with }

@[simp]
/-
**AlgEquiv.coe_ofBijective** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：coe_ofBijective (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f) : (ofBiject
ive f hf : A₁ -> A₂) = f
参数：f : A₁ ->ₐ[R] A₂；hf : Function.Bijective f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_ofBijective (f : A₁ →ₐ[R] A₂) (hf : Function.Bijective f) :
    (ofBijective f hf : A₁ → A₂) = f := rfl
/-
**AlgEquiv.ofBijective_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：ofBijective_apply (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f) (a : A₁) 
: (ofBijective f hf) a = f a
参数：f : A₁ ->ₐ[R] A₂；hf : Function.Bijective f；a : A₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofBijective_apply (f : A₁ →ₐ[R] A₂) (hf : Function.Bijective f) (a : A₁) :
    (ofBijective f hf) a = f a := rfl

@[simp]
/-
**AlgEquiv.toLinearMap_ofBijective** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：toLinearMap_ofBijective (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f) : (
ofBijective f hf).toLinearMap = f
参数：f : A₁ ->ₐ[R] A₂；hf : Function.Bijective f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_ofBijective (f : A₁ →ₐ[R] A₂) (hf : Function.Bijective f) :
    (ofBijective f hf).toLinearMap = f := rfl

@[simp]
/-
**AlgEquiv.toAlgHom_ofBijective** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：toAlgHom_ofBijective (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f) : (ofB
ijective f hf).toAlgHom = f
参数：f : A₁ ->ₐ[R] A₂；hf : Function.Bijective f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAlgHom_ofBijective (f : A₁ →ₐ[R] A₂) (hf : Function.Bijective f) :
    (ofBijective f hf).toAlgHom = f := rfl
/-
**AlgEquiv.ofBijective_apply_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：ofBijective_apply_symm_apply (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f
) (x : A₂) : f ((ofBijective f hf).symm x) = x
参数：f : A₁ ->ₐ[R] A₂；hf : Function.Bijective f；x : A₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
-/
lemma ofBijective_apply_symm_apply (f : A₁ →ₐ[R] A₂) (hf : Function.Bijective f) (x : A₂) :
    f ((ofBijective f hf).symm x) = x :=
  (ofBijective f hf).apply_symm_apply x

@[simp]
/-
**AlgEquiv.ofBijective_symm_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：ofBijective_symm_apply_apply (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f
) (x : A₁) : (ofBijective f hf).symm (f x) = x
参数：f : A₁ ->ₐ[R] A₂；hf : Function.Bijective f；x : A₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
-/
lemma ofBijective_symm_apply_apply (f : A₁ →ₐ[R] A₂) (hf : Function.Bijective f) (x : A₁) :
    (ofBijective f hf).symm (f x) = x :=
  (ofBijective f hf).symm_apply_apply x

section OfLinearEquiv

variable (l : A₁ ≃ₗ[R] A₂) (map_one : l 1 = 1) (map_mul : ∀ x y : A₁, l (x * y) = l x * l y)

/--
Upgrade a linear equivalence to an algebra equivalence,
given that it distributes over multiplication and the identity
-/
@[simps apply]
/-
**AlgEquiv.ofLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：ofLinearEquiv : A₁ ≃ₐ[R] A₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Upgrade a linear equivalence to an algebra equivalence,
given that it distributes over multiplication and the identity
-/
def ofLinearEquiv : A₁ ≃ₐ[R] A₂ :=
  { l with
    toFun := l
    invFun := l.symm
    map_mul' := map_mul
    commutes' := (AlgHom.ofLinearMap l map_one map_mul : A₁ →ₐ[R] A₂).commutes }

/-- Auxiliary definition to avoid looping in `dsimp` with `AlgEquiv.ofLinearEquiv_symm`. -/
/-
**AlgEquiv.ofLinearEquiv_symm.aux** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv.ofLinearEq
uiv_symm`。
形式化陈述：{R : Type uR} →   {A₁ : Type uA₁} →     {A₂ : Type uA₂} →       [inst : Co
mmSemiring R] →         [inst_1 : Semiring A₁] →           [inst_2 : Semiring A₂
] →             [inst_3 : Algebra R A₁] →               [inst_4 : Algebra R A₂] 
→                 (l : A₁ ≃ₗ[R] A₂) → l 1 = 1 → (∀ (x y : A₁), l (x * y) = l x *
 l y) → A₂ ≃ₐ[R] A₁
参数：l : A₁ ≃ₗ[R] A₂；∀ (x y : A₁), l (x * y) = l x * l y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition to avoid looping in `dsimp` with `AlgEquiv.ofLinearEquiv_sy
mm`.
-/
protected def ofLinearEquiv_symm.aux := (ofLinearEquiv l map_one map_mul).symm

@[simp]
/-
**AlgEquiv.ofLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：ofLinearEquiv_symm : (ofLinearEquiv l map_one map_mul).symm = ofLinearEqui
v l.symm (_root_.map_one <| ofLinearEquiv_symm.aux l map_one map_mul) (_root_.ma
p_mul <| ofLinearEquiv_symm.aux l map_one map_mul)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLinearEquiv_symm :
    (ofLinearEquiv l map_one map_mul).symm =
      ofLinearEquiv l.symm
        (_root_.map_one <| ofLinearEquiv_symm.aux l map_one map_mul)
        (_root_.map_mul <| ofLinearEquiv_symm.aux l map_one map_mul) :=
  rfl

@[simp]
/-
**AlgEquiv.ofLinearEquiv_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：ofLinearEquiv_toLinearEquiv (map_mul) (map_one) : ofLinearEquiv e.toLinear
Equiv map_mul map_one = e
参数：map_mul；map_one。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLinearEquiv_toLinearEquiv (map_mul) (map_one) :
    ofLinearEquiv e.toLinearEquiv map_mul map_one = e :=
  rfl

@[simp]
/-
**AlgEquiv.toLinearEquiv_ofLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toLinearEquiv_ofLinearEquiv : toLinearEquiv (ofLinearEquiv l map_one map_m
ul) = l
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_ofLinearEquiv : toLinearEquiv (ofLinearEquiv l map_one map_mul) = l :=
  rfl

end OfLinearEquiv

section OfRingEquiv

/-- Promotes a linear `RingEquiv` to an `AlgEquiv`. -/
@[simps apply symm_apply toEquiv]
/-
**AlgEquiv.ofRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：ofRingEquiv {f : A₁ ≃+* A₂} (hf : forall x, f (algebraMap R A₁ x) = algebr
aMap R A₂ x) : A₁ ≃ₐ[R] A₂
参数：hf : forall x, f (algebraMap R A₁ x) = algebraMap R A₂ x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Promotes a linear `RingEquiv` to an `AlgEquiv`.
-/
def ofRingEquiv {f : A₁ ≃+* A₂} (hf : ∀ x, f (algebraMap R A₁ x) = algebraMap R A₂ x) :
    A₁ ≃ₐ[R] A₂ :=
  { f with
    toFun := f
    invFun := f.symm
    commutes' := hf }

end OfRingEquiv

@[simps -isSimp one mul, stacks 09HR]
/-
**AlgEquiv.aut** 是 Mathlib 中的一个实例，位于命名空间 `AlgEquiv`。
形式化陈述：aut : Group (A₁ ≃ₐ[R] A₁) where mul ϕ ψ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance aut : Group (A₁ ≃ₐ[R] A₁) where
  mul ϕ ψ := ψ.trans ϕ
  mul_assoc _ _ _ := rfl
  one := refl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv := symm
  inv_mul_cancel ϕ := ext <| symm_apply_apply ϕ

@[simp]
/-
**AlgEquiv.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：one_apply (x : A₁) : (1 : A₁ ≃ₐ[R] A₁) x = x
参数：x : A₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (x : A₁) : (1 : A₁ ≃ₐ[R] A₁) x = x :=
  rfl

@[simp]
/-
**AlgEquiv.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：mul_apply (e₁ e₂ : A₁ ≃ₐ[R] A₁) (x : A₁) : (e₁ * e₂) x = e₁ (e₂ x)
参数：e₁ e₂ : A₁ ≃ₐ[R] A₁；x : A₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (e₁ e₂ : A₁ ≃ₐ[R] A₁) (x : A₁) : (e₁ * e₂) x = e₁ (e₂ x) :=
  rfl
/-
**AlgEquiv.aut_inv** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：aut_inv (ϕ : A₁ ≃ₐ[R] A₁) : ϕ⁻¹ = ϕ.symm
参数：ϕ : A₁ ≃ₐ[R] A₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma aut_inv (ϕ : A₁ ≃ₐ[R] A₁) : ϕ⁻¹ = ϕ.symm := rfl
/-
**AlgEquiv.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ {R : Type uR} {A₁ : Type uA₁} [inst : CommSemiring R] [inst_1 : Semiring
 A₁] [inst_2 : Algebra R A₁]   (ϕ : A₁ ≃ₐ[R] A₁), ⇑ϕ⁻¹ = ⇑ϕ.symm
参数：ϕ : A₁ ≃ₐ[R] A₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_inv (ϕ : A₁ ≃ₐ[R] A₁) : ⇑ϕ⁻¹ = ⇑ϕ.symm := rfl
/-
**AlgEquiv.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ {R : Type uR} {A₁ : Type uA₁} [inst : CommSemiring R] [inst_1 : Semiring
 A₁] [inst_2 : Algebra R A₁] (e : A₁ ≃ₐ[R] A₁)   (n : ℕ), ⇑(e ^ n) = (⇑e)^[n]
参数：e : A₁ ≃ₐ[R] A₁；n : ℕ；e ^ n；⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
@[simp] theorem coe_pow (e : A₁ ≃ₐ[R] A₁) (n : ℕ) : ⇑(e ^ n) = e^[n] :=
  n.rec (by ext; simp) fun _ ih ↦ by ext; simp [pow_succ, ih]

/-- An algebra isomorphism induces a group isomorphism between automorphism groups.

This is a more bundled version of `AlgEquiv.equivCongr`. -/
@[simps apply]
/-
**AlgEquiv.autCongr** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：autCongr (ϕ : A₁ ≃ₐ[R] A₂) : (A₁ ≃ₐ[R] A₁) ≃* A₂ ≃ₐ[R] A₂ where __
参数：ϕ : A₁ ≃ₐ[R] A₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An algebra isomorphism induces a group isomorphism between automorphism groups.

This is a more bundled version of `AlgEquiv.equivCongr`.
-/
def autCongr (ϕ : A₁ ≃ₐ[R] A₂) : (A₁ ≃ₐ[R] A₁) ≃* A₂ ≃ₐ[R] A₂ where
  __ := equivCongr ϕ ϕ
  toFun ψ := ϕ.symm.trans (ψ.trans ϕ)
  invFun ψ := ϕ.trans (ψ.trans ϕ.symm)
  map_mul' ψ χ := by
    ext
    simp only [mul_apply, trans_apply, symm_apply_apply]

@[simp]
/-
**AlgEquiv.autCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：autCongr_refl : autCongr AlgEquiv.refl = MulEquiv.refl (A₁ ≃ₐ[R] A₁)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem autCongr_refl : autCongr AlgEquiv.refl = MulEquiv.refl (A₁ ≃ₐ[R] A₁) := rfl

@[simp]
/-
**AlgEquiv.autCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：autCongr_symm (ϕ : A₁ ≃ₐ[R] A₂) : (autCongr ϕ).symm = autCongr ϕ.symm
参数：ϕ : A₁ ≃ₐ[R] A₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem autCongr_symm (ϕ : A₁ ≃ₐ[R] A₂) : (autCongr ϕ).symm = autCongr ϕ.symm :=
  rfl

@[simp]
/-
**AlgEquiv.autCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：autCongr_trans (ϕ : A₁ ≃ₐ[R] A₂) (ψ : A₂ ≃ₐ[R] A₃) : (autCongr ϕ).trans (a
utCongr ψ) = autCongr (ϕ.trans ψ)
参数：ϕ : A₁ ≃ₐ[R] A₂；ψ : A₂ ≃ₐ[R] A₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem autCongr_trans (ϕ : A₁ ≃ₐ[R] A₂) (ψ : A₂ ≃ₐ[R] A₃) :
    (autCongr ϕ).trans (autCongr ψ) = autCongr (ϕ.trans ψ) :=
  rfl

/-- The tautological action by `A₁ ≃ₐ[R] A₁` on `A₁`.

This generalizes `Function.End.applyMulAction`. -/
/-
**AlgEquiv.applyMulSemiringAction** 是 Mathlib 中的一个实例，位于命名空间 `AlgEquiv`。
形式化陈述：applyMulSemiringAction : MulSemiringAction (A₁ ≃ₐ[R] A₁) A₁ where smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological action by `A₁ ≃ₐ[R] A₁` on `A₁`.

This generalizes `Function.End.applyMulAction`.
-/
instance applyMulSemiringAction : MulSemiringAction (A₁ ≃ₐ[R] A₁) A₁ where
  smul := (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  smul_one := map_one
  smul_mul := map_mul
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
/-
**AlgEquiv.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ {R : Type uR} {A₁ : Type uA₁} [inst : CommSemiring R] [inst_1 : Semiring
 A₁] [inst_2 : Algebra R A₁] (f : A₁ ≃ₐ[R] A₁)   (a : A₁), f • a = f a
参数：f : A₁ ≃ₐ[R] A₁；a : A₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem smul_def (f : A₁ ≃ₐ[R] A₁) (a : A₁) : f • a = f a :=
  rfl
/-
**AlgEquiv.apply_faithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 `AlgEquiv`。
形式化陈述：apply_faithfulSMul : FaithfulSMul (A₁ ≃ₐ[R] A₁) A₁
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
-/
instance apply_faithfulSMul : FaithfulSMul (A₁ ≃ₐ[R] A₁) A₁ :=
  ⟨AlgEquiv.ext⟩
/-
**AlgEquiv.apply_smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `AlgEquiv`。
形式化陈述：apply_smulCommClass {S} [SMul S R] [SMul S A₁] [IsScalarTower S R A₁] : SM
ulCommClass S (A₁ ≃ₐ[R] A₁) A₁ where smul_comm r e a
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
-/
instance apply_smulCommClass {S} [SMul S R] [SMul S A₁] [IsScalarTower S R A₁] :
    SMulCommClass S (A₁ ≃ₐ[R] A₁) A₁ where
  smul_comm r e a := (e.toLinearEquiv.map_smul_of_tower r a).symm
/-
**AlgEquiv.apply_smulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 `AlgEquiv`。
形式化陈述：apply_smulCommClass' {S} [SMul S R] [SMul S A₁] [IsScalarTower S R A₁] : S
MulCommClass (A₁ ≃ₐ[R] A₁) S A₁
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance apply_smulCommClass' {S} [SMul S R] [SMul S A₁] [IsScalarTower S R A₁] :
    SMulCommClass (A₁ ≃ₐ[R] A₁) S A₁ :=
  SMulCommClass.symm _ _ _
/-
**AlgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `AlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulDistribMulAction (A₁ ≃ₐ[R] A₁) A₁ˣ where
  smul := fun f => Units.map f
  one_smul := fun x => by ext; rfl
  mul_smul := fun x y z => by ext; rfl
  smul_mul := fun x y z => by ext; exact map_mul x _ _
  smul_one := fun x => by ext; exact map_one x

@[simp]
/-
**AlgEquiv.smul_units_def** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：smul_units_def (f : A₁ ≃ₐ[R] A₁) (x : A₁ˣ) : f • x = Units.map f x
参数：f : A₁ ≃ₐ[R] A₁；x : A₁ˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_units_def (f : A₁ ≃ₐ[R] A₁) (x : A₁ˣ) :
    f • x = Units.map f x := rfl

@[simp]
/-
**AlgEquiv._root_.MulSemiringAction.toRingEquiv_algEquiv** 是 Mathlib 中的一个引理，位于命名
空间 `AlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MulSemiringAction.toRingEquiv_algEquiv (σ : A₁ ≃ₐ[R] A₁) :
    MulSemiringAction.toRingEquiv _ A₁ σ = σ := rfl

@[simp]
/-
**AlgEquiv.algebraMap_eq_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：algebraMap_eq_apply (e : A₁ ≃ₐ[R] A₂) {y : R} {x : A₁} : algebraMap R A₂ y
 = e x ↔ algebraMap R A₁ y = x
参数：e : A₁ ≃ₐ[R] A₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用定理 `AlgHom.algebraMap_eq_apply`：algebraMap_eq_apply (f : A ->ₐ[R] B) {y : R}
 {x : A} (h : algebraMap R A y = x) : algebraMap R B y = f x
-/
theorem algebraMap_eq_apply (e : A₁ ≃ₐ[R] A₂) {y : R} {x : A₁} :
    algebraMap R A₂ y = e x ↔ algebraMap R A₁ y = x :=
  ⟨fun h => by simpa using e.symm.toAlgHom.algebraMap_eq_apply h, fun h =>
    e.toAlgHom.algebraMap_eq_apply h⟩

/-- `AlgEquiv.toAlgHom` as a `MonoidHom`. -/
/-
**AlgEquiv.toAlgHomHom** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：(R : Type u_1) →   (A : Type u_2) → [inst : CommSemiring R] → [inst_1 : Se
miring A] → [inst_2 : Algebra R A] → (A ≃ₐ[R] A) →* A →ₐ[R] A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AlgEquiv.toAlgHom` as a `MonoidHom`.
-/
@[simps] def toAlgHomHom (R A) [CommSemiring R] [Semiring A] [Algebra R A] :
    (A ≃ₐ[R] A) →* A →ₐ[R] A where
  toFun := AlgEquiv.toAlgHom
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `AlgEquiv.toLinearMap` as a `MonoidHom`. -/
@[simps!]
/-
**AlgEquiv.toLinearMapHom** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：toLinearMapHom (R A) [CommSemiring R] [Semiring A] [Algebra R A] : (A ≃ₐ[R
] A) ->* Module.End R A
参数：R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AlgEquiv.toLinearMap` as a `MonoidHom`.
-/
def toLinearMapHom (R A) [CommSemiring R] [Semiring A] [Algebra R A] :
    (A ≃ₐ[R] A) →* Module.End R A :=
  AlgHom.toEnd.comp (toAlgHomHom R A)
/-
**AlgEquiv.pow_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：pow_toLinearMap (σ : A₁ ≃ₐ[R] A₁) (n : Nat) : (σ ^ n).toLinearMap = σ.toLi
nearMap ^ n
参数：σ : A₁ ≃ₐ[R] A₁；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
-/
lemma pow_toLinearMap (σ : A₁ ≃ₐ[R] A₁) (n : ℕ) :
    (σ ^ n).toLinearMap = σ.toLinearMap ^ n :=
  (AlgEquiv.toLinearMapHom R A₁).map_pow σ n

@[simp]
/-
**AlgEquiv.one_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：one_toLinearMap : (1 : A₁ ≃ₐ[R] A₁).toLinearMap = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_toLinearMap :
    (1 : A₁ ≃ₐ[R] A₁).toLinearMap = 1 := rfl

/-- The units group of `S →ₐ[R] S` is `S ≃ₐ[R] S`.
See `LinearMap.GeneralLinearGroup.generalLinearEquiv` for the linear map version. -/
@[simps]
/-
**AlgEquiv.algHomUnitsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：algHomUnitsEquiv (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S]
 : (S ->ₐ[R] S)ˣ ≃* (S ≃ₐ[R] S) where toFun
参数：R S : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.commutes'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `AlgEquiv.comp_symm`：comp_symm (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp (e : A₁ ->
ₐ[R] A₂) ↑e.symm = AlgHom.id R A₂
· 使用定理 `AlgEquiv.symm_comp`：symm_comp (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp ↑e.symm (e
 : A₁ ->ₐ[R] A₂) = AlgHom.id R A₁

--- 原说明 ---
The units group of `S →ₐ[R] S` is `S ≃ₐ[R] S`.
See `LinearMap.GeneralLinearGroup.generalLinearEquiv` for the linear map version
.
-/
def algHomUnitsEquiv (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S] :
    (S →ₐ[R] S)ˣ ≃* (S ≃ₐ[R] S) where
  toFun := fun f ↦
    { (f : S →ₐ[R] S) with
      invFun := ↑(f⁻¹)
      left_inv := (fun x ↦ show (↑(f⁻¹ * f) : S →ₐ[R] S) x = x by rw [inv_mul_cancel]; rfl)
      right_inv := (fun x ↦ show (↑(f * f⁻¹) : S →ₐ[R] S) x = x by rw [mul_inv_cancel]; rfl) }
  invFun := fun f ↦ ⟨f, f.symm, f.comp_symm, f.symm_comp⟩
  map_mul' := fun _ _ ↦ rfl

/-- See also `Finite.algHom` -/
/-
**AlgEquiv._root_.Finite.algEquiv** 是 Mathlib 中的一个实例，位于命名空间 `AlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See also `Finite.algHom`
-/
instance _root_.Finite.algEquiv [Finite (A₁ →ₐ[R] A₂)] : Finite (A₁ ≃ₐ[R] A₂) :=
  Finite.of_injective _ AlgEquiv.coe_toAlgHom_injective

-- TODO Morally this is just `isLocalHom_equiv`: can we obviate the need for this instance?
/-
**AlgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `AlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalHom e.toAlgHom := by
  have : IsLocalHom e.toRingEquiv := inferInstance
  exact ⟨this.map_nonunit⟩

end Semiring

end AlgEquiv

namespace RingEquiv

variable {R S : Type*}

/-- Reinterpret a `RingEquiv` as an `ℕ`-algebra isomorphism. -/
@[simps! -isSimp apply]
/-
**RingEquiv.toNatAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：toNatAlgEquiv [Semiring R] [Semiring S] (f : R ≃+* S) : R ≃ₐ[Nat] S where 
toEquiv
参数：f : R ≃+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a `RingEquiv` as an `ℕ`-algebra isomorphism.
-/
def toNatAlgEquiv [Semiring R] [Semiring S] (f : R ≃+* S) : R ≃ₐ[ℕ] S where
  toEquiv := f
  __ := f.toRingHom.toNatAlgHom

@[simp]
/-
**RingEquiv.coe_toNatAlgEquiv** 是 Mathlib 中的一个引理，位于命名空间 `RingEquiv`。
形式化陈述：coe_toNatAlgEquiv [Semiring R] [Semiring S] (f : R ≃+* S) : ⇑f.toNatAlgEqu
iv = ⇑f
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toNatAlgEquiv [Semiring R] [Semiring S] (f : R ≃+* S) :
    ⇑f.toNatAlgEquiv = ⇑f := rfl
/-
**RingEquiv.toAlgHom_toNatAlgEquiv** 是 Mathlib 中的一个引理，位于命名空间 `RingEquiv`。
形式化陈述：toAlgHom_toNatAlgEquiv [Semiring R] [Semiring S] (f : R ≃+* S) : f.toNatAl
gEquiv.toAlgHom = (f : R ->+* S).toNatAlgHom
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAlgHom_toNatAlgEquiv [Semiring R] [Semiring S] (f : R ≃+* S) :
    f.toNatAlgEquiv.toAlgHom = (f : R →+* S).toNatAlgHom := rfl

@[simp]
/-
**RingEquiv.symm_toNatAlgEquiv** 是 Mathlib 中的一个引理，位于命名空间 `RingEquiv`。
形式化陈述：symm_toNatAlgEquiv [Semiring R] [Semiring S] (f : R ≃+* S) : f.toNatAlgEqu
iv.symm = f.symm.toNatAlgEquiv
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_toNatAlgEquiv [Semiring R] [Semiring S] (f : R ≃+* S) :
    f.toNatAlgEquiv.symm = f.symm.toNatAlgEquiv := rfl

variable (R) (S) in
/-- The equivalence between `RingEquiv` and `ℕ`-algebra isomorphisms. -/
@[simps apply symm_apply]
/-
**RingEquiv.equivNatAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：equivNatAlgEquiv [Semiring R] [Semiring S] : (R ≃+* S) ≃ (R ≃ₐ[Nat] S) whe
re toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `RingEquiv` and `ℕ`-algebra isomorphisms.
-/
def equivNatAlgEquiv [Semiring R] [Semiring S] : (R ≃+* S) ≃ (R ≃ₐ[ℕ] S) where
  toFun := toNatAlgEquiv
  invFun := AlgEquiv.toRingEquiv
/-
**RingEquiv.toNatAlgEquiv_injective** 是 Mathlib 中的一个引理，位于命名空间 `RingEquiv`。
形式化陈述：toNatAlgEquiv_injective [Semiring R] [Semiring S] : Function.Injective (Ri
ngEquiv.toNatAlgEquiv : (R ≃+* S) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma toNatAlgEquiv_injective [Semiring R] [Semiring S] :
    Function.Injective (RingEquiv.toNatAlgEquiv : (R ≃+* S) → _) :=
  (equivNatAlgEquiv R S).injective

/-- Reinterpret a `RingEquiv` as a `ℤ`-algebra isomorphism. -/
@[simps! -isSimp apply]
/-
**RingEquiv.toIntAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：toIntAlgEquiv [Ring R] [Ring S] (f : R ≃+* S) : R ≃ₐ[Int] S where toEquiv
参数：f : R ≃+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a `RingEquiv` as a `ℤ`-algebra isomorphism.
-/
def toIntAlgEquiv [Ring R] [Ring S] (f : R ≃+* S) : R ≃ₐ[ℤ] S where
  toEquiv := f
  __ := f.toRingHom.toIntAlgHom

@[simp]
/-
**RingEquiv.coe_toIntAlgEquiv** 是 Mathlib 中的一个引理，位于命名空间 `RingEquiv`。
形式化陈述：coe_toIntAlgEquiv [Ring R] [Ring S] (f : R ≃+* S) : ⇑f.toIntAlgEquiv = ⇑f
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toIntAlgEquiv [Ring R] [Ring S] (f : R ≃+* S) :
    ⇑f.toIntAlgEquiv = ⇑f := rfl
/-
**RingEquiv.toAlgHom_toIntAlgEquiv** 是 Mathlib 中的一个引理，位于命名空间 `RingEquiv`。
形式化陈述：toAlgHom_toIntAlgEquiv [Ring R] [Ring S] (f : R ≃+* S) : f.toIntAlgEquiv.t
oAlgHom = (f : R ->+* S).toIntAlgHom
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAlgHom_toIntAlgEquiv [Ring R] [Ring S] (f : R ≃+* S) :
    f.toIntAlgEquiv.toAlgHom = (f : R →+* S).toIntAlgHom := rfl

@[simp]
/-
**RingEquiv.symm_toIntAlgEquiv** 是 Mathlib 中的一个引理，位于命名空间 `RingEquiv`。
形式化陈述：symm_toIntAlgEquiv [Ring R] [Ring S] (f : R ≃+* S) : f.toIntAlgEquiv.symm 
= f.symm.toIntAlgEquiv
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_toIntAlgEquiv [Ring R] [Ring S] (f : R ≃+* S) :
    f.toIntAlgEquiv.symm = f.symm.toIntAlgEquiv := rfl

variable (R) (S) in
/-- The equivalence between `RingEquiv` and `ℤ`-algebra isomorphisms. -/
@[simps apply symm_apply]
/-
**RingEquiv.equivIntAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：equivIntAlgEquiv [Ring R] [Ring S] : (R ≃+* S) ≃ (R ≃ₐ[Int] S) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `RingEquiv` and `ℤ`-algebra isomorphisms.
-/
def equivIntAlgEquiv [Ring R] [Ring S] : (R ≃+* S) ≃ (R ≃ₐ[ℤ] S) where
  toFun := toIntAlgEquiv
  invFun := AlgEquiv.toRingEquiv
/-
**RingEquiv.toIntAlgEquiv_injective** 是 Mathlib 中的一个引理，位于命名空间 `RingEquiv`。
形式化陈述：toIntAlgEquiv_injective [Ring R] [Ring S] : Function.Injective (RingEquiv.
toIntAlgEquiv : (R ≃+* S) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma toIntAlgEquiv_injective [Ring R] [Ring S] :
    Function.Injective (RingEquiv.toIntAlgEquiv : (R ≃+* S) → _) :=
  (equivIntAlgEquiv R S).injective

end RingEquiv

namespace MulSemiringAction

variable {M G : Type*} (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

section

variable [Group G] [MulSemiringAction G A] [SMulCommClass G R A]

/-- Each element of the group defines an algebra equivalence.

This is a stronger version of `MulSemiringAction.toRingEquiv` and
`DistribMulAction.toLinearEquiv`. -/
@[simps! apply symm_apply toEquiv]
/-
**MulSemiringAction.toAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MulSemiringAction`。
形式化陈述：toAlgEquiv (g : G) : A ≃ₐ[R] A
参数：g : G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.commutes'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…

--- 原说明 ---
Each element of the group defines an algebra equivalence.

This is a stronger version of `MulSemiringAction.toRingEquiv` and
`DistribMulAction.toLinearEquiv`.
-/
def toAlgEquiv (g : G) : A ≃ₐ[R] A :=
  { MulSemiringAction.toRingEquiv _ _ g, MulSemiringAction.toAlgHom R A g with }
/-
**MulSemiringAction.toAlgEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringA
ction`。
形式化陈述：toAlgEquiv_injective [FaithfulSMul G A] : Function.Injective (MulSemiringA
ction.toAlgEquiv R A : G -> A ≃ₐ[R] A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgEquiv.ext_iff`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst 
: CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Alge
bra R …
-/
theorem toAlgEquiv_injective [FaithfulSMul G A] :
    Function.Injective (MulSemiringAction.toAlgEquiv R A : G → A ≃ₐ[R] A) := fun _ _ h =>
  eq_of_smul_eq_smul fun r => AlgEquiv.ext_iff.1 h r

variable (G)

/-- Each element of the group defines an algebra equivalence.

This is a stronger version of `MulSemiringAction.toRingAut` and
`DistribMulAction.toModuleEnd`. -/
@[simps]
/-
**MulSemiringAction.toAlgAut** 是 Mathlib 中的一个定义，位于命名空间 `MulSemiringAction`。
形式化陈述：toAlgAut : G ->* A ≃ₐ[R] A where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each element of the group defines an algebra equivalence.

This is a stronger version of `MulSemiringAction.toRingAut` and
`DistribMulAction.toModuleEnd`.
-/
def toAlgAut : G →* A ≃ₐ[R] A where
  toFun := toAlgEquiv R A
  map_one' := AlgEquiv.ext <| one_smul _
  map_mul' g h := AlgEquiv.ext <| mul_smul g h

end

end MulSemiringAction

section

variable {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton S] [Subsingleton T] : Unique (S ≃ₐ[R] T) where
  default := AlgEquiv.ofAlgHom default default
    (AlgHom.ext fun _ ↦ Subsingleton.elim _ _)
    (AlgHom.ext fun _ ↦ Subsingleton.elim _ _)
  uniq _ := AlgEquiv.ext fun _ ↦ Subsingleton.elim _ _

@[simp]
/-
**AlgEquiv.default_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AlgEquiv.default_apply [Subsingleton S] [Subsingleton T] (x : S) : (defaul
t : S ≃ₐ[R] T) x = 0
参数：x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma AlgEquiv.default_apply [Subsingleton S] [Subsingleton T] (x : S) :
    (default : S ≃ₐ[R] T) x = 0 :=
  rfl

end

/-- The algebra equivalence between `ULift A` and `A`. -/
@[simps! apply, simps! -isSimp symm_apply, pp_with_univ]
/-
**ULift.algEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ULift.algEquiv {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Al
gebra R A] : ULift.{w} A ≃ₐ[R] A where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra equivalence between `ULift A` and `A`.
-/
def ULift.algEquiv {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A] :
    ULift.{w} A ≃ₐ[R] A where
  __ := ULift.ringEquiv
  commutes' _ := rfl

@[simp]
/-
**ULift.down_algEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ULift.down_algEquiv_symm_apply {R A : Type*} [CommSemiring R] [Semiring A]
 [Algebra R A] (a : A) : (ULift.algEquiv (R
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ULift.down_algEquiv_symm_apply {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (a : A) :
    (ULift.algEquiv (R := R).symm a).down = a :=
  rfl

section

variable {R S T : Type*} [CommSemiring R] [Semiring S]
  [Semiring T] [Algebra R S] [Algebra R T]

attribute [local instance] ULift.algebra' in
/-- `ULift` is functorial for algebra homomorphisms. -/
@[pp_with_univ]
/-
**AlgHom.ulift** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgHom.ulift (f : S ->ₐ[R] T) : ULift.{u₁} S ->ₐ[ULift.{u₂} R] ULift.{u₃} 
T where __
参数：f : S ->ₐ[R] T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ULift` is functorial for algebra homomorphisms.
-/
def AlgHom.ulift (f : S →ₐ[R] T) :
    ULift.{u₁} S →ₐ[ULift.{u₂} R] ULift.{u₃} T where
  __ := AlgHom.comp ULift.algEquiv.symm.toAlgHom (f.comp ULift.algEquiv.toAlgHom)
  commutes' _ := by simp

@[simp]
/-
**AlgHom.down_ulift_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AlgHom.down_ulift_apply (f : S ->ₐ[R] T) (x : ULift S) : (f.ulift x).down 
= f x.down
参数：f : S ->ₐ[R] T；x : ULift S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma AlgHom.down_ulift_apply (f : S →ₐ[R] T) (x : ULift S) :
    (f.ulift x).down = f x.down :=
  rfl
/-
**AlgHom.ulift_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AlgHom.ulift_apply (f : S ->ₐ[R] T) (x : ULift S) : f.ulift x = ⟨f x.down⟩
参数：f : S ->ₐ[R] T；x : ULift S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma AlgHom.ulift_apply (f : S →ₐ[R] T) (x : ULift S) :
    f.ulift x = ⟨f x.down⟩ :=
  rfl

end

/-- If an `R`-algebra `A` is isomorphic to `R` as `R`-module, then the canonical map `R → A` is an
equivalence of `R`-algebras.

Note that if `e : R ≃ₗ[R] A` is the linear equivalence, then this is not the same as the equivalence
of algebras provided here unless `e 1 = 1`. -/
/-
**LinearEquiv.algEquivOfRing** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：{R : Type u_1} →   {A : Type u_2} →     [inst : CommSemiring R] → [inst_1 
: CommSemiring A] → [inst_2 : Algebra R A] → (R ≃ₗ[R] A) → R ≃ₐ[R] A
参数：R ≃ₗ[R] A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an `R`-algebra `A` is isomorphic to `R` as `R`-module, then the canonical map
 `R → A` is an
equivalence of `R`-algebras.

Note that if `e : R ≃ₗ[R] A` is the linear equivalence, then this is not the sam
e as the equivalence
of algebras provided here unless `e 1 = 1`.
-/
@[simps] def LinearEquiv.algEquivOfRing
    {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (e : R ≃ₗ[R] A) : R ≃ₐ[R] A where
  __ := Algebra.ofId R A
  invFun x := e.symm (e 1 * x)
  left_inv x := calc
    e.symm (e 1 * (algebraMap R A) x)
      = e.symm (x • e 1) := by rw [Algebra.smul_def, mul_comm]
    _ = x := by rw [map_smul, e.symm_apply_apply, smul_eq_mul, mul_one]
  right_inv x := calc
    (algebraMap R A) (e.symm (e 1 * x))
      = (algebraMap R A) (e.symm (e 1 * x)) * e (e.symm 1 • 1) := by
          rw [smul_eq_mul, mul_one, e.apply_symm_apply, mul_one]
    _ = x := by rw [map_smul, Algebra.smul_def, mul_left_comm, ← Algebra.smul_def _ (e 1),
          ← map_smul, smul_eq_mul, mul_one, e.apply_symm_apply, ← mul_assoc, ← Algebra.smul_def,
          ← map_smul, smul_eq_mul, mul_one, e.apply_symm_apply, one_mul]

namespace LinearEquiv
variable {R S M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁] [Module R M₁]
  [AddCommMonoid M₂] [Module R M₂] [Semiring S] [Module S M₁] [Module S M₂]
  [SMulCommClass S R M₁] [SMulCommClass S R M₂] [SMul R S] [IsScalarTower R S M₁]
  [IsScalarTower R S M₂]

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-- A linear equivalence of two modules induces an equivalence of algebras of their
endomorphisms. -/
/-
**LinearEquiv.conjAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：(R : Type u_1) →   {S : Type u_2} →     {M₁ : Type u_3} →       {M₂ : Type
 u_4} →         [inst : CommSemiring R] →           [inst_1 : AddCommMonoid M₁] 
→             [inst_2 : _root_.Module R M₁] →               [inst_3 : AddCommMon
oid M₂] →                 [inst_4 : _root_.Module R M₂] →                   [ins
t_5 : Semiring S] →                     [inst_6 : _root_.Module S M₁] →         
              [inst_7 : _root_.Module S M₂] →                         [inst_8 : 
SMulCommClass S R M₁] →                           [inst_9 : SMulCommClass S R M₂
] →                             [inst_10 : SMul R S] →                          
     [inst_11 : IsScalarTower R S M₁] →                                 [inst_12
 : IsScalarTower R S M₂] → (M₁ ≃ₗ[S] M₂) → Module.End S M₁ ≃ₐ[R] Module.End S M₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear equivalence of two modules induces an equivalence of algebras of their
endomorphisms.
-/
@[simps!] def conjAlgEquiv (e : M₁ ≃ₗ[S] M₂) : Module.End S M₁ ≃ₐ[R] Module.End S M₂ where
  __ := e.conjRingEquiv
  commutes' _ := by ext; change e.restrictScalars R _ = _; simp
/-
**LinearEquiv.conjAlgEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：conjAlgEquiv_apply (e : M₁ ≃ₗ[S] M₂) (f : Module.End S M₁) : e.conjAlgEqui
v R f = e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap
参数：e : M₁ ≃ₗ[S] M₂；f : Module.End S M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjAlgEquiv_apply (e : M₁ ≃ₗ[S] M₂) (f : Module.End S M₁) :
    e.conjAlgEquiv R f = e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap := rfl
/-
**LinearEquiv.symm_conjAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_conjAlgEquiv (e : M₁ ≃ₗ[S] M₂) : (e.conjAlgEquiv R).symm = e.symm.con
jAlgEquiv R
参数：e : M₁ ≃ₗ[S] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_conjAlgEquiv (e : M₁ ≃ₗ[S] M₂) : (e.conjAlgEquiv R).symm = e.symm.conjAlgEquiv R := rfl

end LinearEquiv

