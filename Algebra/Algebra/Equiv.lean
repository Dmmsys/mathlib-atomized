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

/--
Definition of `AlgEquiv` / `AlgEquiv` 的定义

English:
structure AlgEquiv
  parameters: (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]
  extends: A ≃ B, A ≃* B, A ≃+ B, A ≃+* B
  axioms and operations (1):
    - commutes' : forall r : R, toFun (algebraMap R A r) = algebraMap R B r

中文:
结构 代数等价
  参数: (R : 类型u) (A : 类型v) (B : 类型 w) [交换半环 R] [半环 A] [半环 B]
  继承: A ≃ B, A ≃* B, A ≃+ B, A ≃+* B
  公理与运算 (1 个):
    - commutes' : 对任意 r : R, toFun (algebraMap R A r) = algebraMap R B r
-/
structure AlgEquiv (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] extends A ≃ B, A ≃* B, A ≃+ B, A ≃+* B where
  /-- An equivalence of algebras commutes with the action of scalars. -/
  protected commutes' : forall r : R, toFun (algebraMap R A r) = algebraMap R B r

attribute [nolint docBlame] AlgEquiv.toRingEquiv
attribute [nolint docBlame] AlgEquiv.toEquiv
attribute [nolint docBlame] AlgEquiv.toAddEquiv
attribute [nolint docBlame] AlgEquiv.toMulEquiv

@[inherit_doc]
notation:50 A " ≃ₐ[" R "] " A' => AlgEquiv R A A'

/--
Definition of `AlgEquivClass` / `AlgEquivClass` 的定义

English:
class AlgEquivClass
  parameters: (F : Type*) (R A B : outParam Type*) [CommSemiring R] [Semiring A]
  extends: RingEquivClass F A B
  axioms and operations (1):
    - commutes : forall (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r

中文:
类 代数等价类
  参数: (F : 类型) (R A B : outParam 类型) [交换半环 R] [半环 A]
  继承: 环等价类 F A B
  公理与运算 (1 个):
    - commutes : 对任意 (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r
-/
class AlgEquivClass (F : Type*) (R A B : outParam Type*) [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [EquivLike F A B] : Prop
    extends RingEquivClass F A B where
  /-- An equivalence of algebras commutes with the action of scalars. -/
  commutes : forall (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r

namespace AlgEquivClass

-- See note [lower instance priority]
instance (priority := 100) toAlgHomClass (F R A B : Type*) [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [EquivLike F A B] [h : AlgEquivClass F R A B] :
    AlgHomClass F R A B :=
  { h with }

instance (priority := 100) toLinearEquivClass (F R A B : Type*) [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [EquivLike F A B] [h : AlgEquivClass F R A B] : LinearEquivClass F R A B :=
  { h with map_smulₛₗ := fun f => map_smulₛₗ f }

/-- Turn an element of a type `F` satisfying `AlgEquivClass F R A B` into an actual `AlgEquiv`.
This is declared as the default coercion from `F` to `A ≃ₐ[R] B`. -/
@[coe]
/--
Definition of `toAlgEquiv` / `toAlgEquiv` 的定义

English:
definition toAlgEquiv
  signature: {F R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
  body: { (f : A ≃ B), (RingEquivClass.toRingEquiv f : A ≃+* B) with commutes' := commutes f }

中文:
定义 toAlgEquiv
  签名: {F R A B : 类型} [交换半环 R] [半环 A] [半环 B] [代数 R A]
  定义体: { (f : A ≃ B), (RingEquivClass.toRingEquiv f : A ≃+* B) with commutes' := commutes f }

Depends on / 依赖: RingEquivClass, RingEquivClass.toRingEquiv, commutes, toRingEquiv
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (A₁ ≃ₐ[R] A₂) A₁ A₂
  body: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨f, _⟩, _⟩ := f
    obtain ⟨⟨g, _⟩, _⟩ := g
    congr

中文:
实例 :
  签名: 等价状 (A₁ ≃ₐ[R] A₂) A₁ A₂
  定义体: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨f, _⟩, _⟩ := f
    obtain ⟨⟨g, _⟩, _⟩ := g
    congr

Depends on / 依赖: f.toFun
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (A₁ ≃ₐ[R] A₂) A₁ A₂
  body: DFunLike.coe
  coe_injective := DFunLike.coe_injective

中文:
实例 :
  签名: 函数状 (A₁ ≃ₐ[R] A₂) A₁ A₂
  定义体: DFunLike.coe
  coe_injective := DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe
-/
instance : FunLike (A₁ ≃ₐ[R] A₂) A₁ A₂ where
  coe := DFunLike.coe
  coe_injective := DFunLike.coe_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AlgEquivClass (A₁ ≃ₐ[R] A₂) R A₁ A₂
  body: f.map_add'
  map_mul f := f.map_mul'
  commutes f := f.commutes'

@[ext]

中文:
实例 :
  签名: 代数等价类 (A₁ ≃ₐ[R] A₂) R A₁ A₂
  定义体: f.map_add'
  map_mul f := f.map_mul'
  commutes f := f.commutes'

@[ext]

Depends on / 依赖: f.map_add, map_add
-/
instance : AlgEquivClass (A₁ ≃ₐ[R] A₂) R A₁ A₂ where
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  commutes f := f.commutes'

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : A₁ ≃ₐ[R] A₂} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: {f : A₁ ≃ₐ[R] A₂} {x x' : A₁}
  statement: x = x' -> f x = f x'
  proof: DFunLike.congr_arg f

中文:
定理 congr_arg
  条件: {f : A₁ ≃ₐ[R] A₂} {x x' : A₁}
  结论: x = x' -> f x = f x'
  证明: DFunLike.congr_arg f
-/
protected theorem congr_arg {f : A₁ ≃ₐ[R] A₂} {x x' : A₁} : x = x' -> f x = f x' :=
  DFunLike.congr_arg f

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : A₁ ≃ₐ[R] A₂} (h : f = g) (x : A₁)
  statement: f x = g x
  proof: DFunLike.congr_fun h x

@[simp]

中文:
定理 congr_fun
  条件: {f g : A₁ ≃ₐ[R] A₂} (h : f = g) (x : A₁)
  结论: f x = g x
  证明: DFunLike.congr_fun h x

@[simp]
-/
protected theorem congr_fun {f g : A₁ ≃ₐ[R] A₂} (h : f = g) (x : A₁) : f x = g x :=
  DFunLike.congr_fun h x

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: {toEquiv map_mul map_add commutes}
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: {toEquiv map_mul map_add commutes}
  证明: rfl

@[simp]
-/
theorem coe_mk {toEquiv map_mul map_add commutes} :
    ⇑(⟨toEquiv, map_mul, map_add, commutes⟩ : A₁ ≃ₐ[R] A₂) = toEquiv :=
  rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (e : A₁ ≃ₐ[R] A₂) (e' h₁ h₂ h₃ h₄ h₅)
  proof: ext fun _ => rfl

@[simp]

中文:
定理 mk_coe
  条件: (e : A₁ ≃ₐ[R] A₂) (e' h₁ h₂ h₃ h₄ h₅)
  证明: ext fun _ => rfl

@[simp]
-/
theorem mk_coe (e : A₁ ≃ₐ[R] A₂) (e' h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨e, e', h₁, h₂⟩, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂) = e :=
  ext fun _ => rfl

@[simp]
/--
theorem `toEquiv_eq_coe` / 定理 `toEquiv_eq_coe`

English:
theorem toEquiv_eq_coe
  statement: e.toEquiv = e
  proof: rfl

@[simp]

中文:
定理 toEquiv_eq_coe
  结论: e.toEquiv = e
  证明: rfl

@[simp]
-/
theorem toEquiv_eq_coe : e.toEquiv = e :=
  rfl

@[simp]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: {F : Type*} [EquivLike F A₁ A₂] [AlgEquivClass F R A₁ A₂] (f : F)
  proof: rfl

中文:
定理 coe_coe
  条件: {F : 类型} [等价状 F A₁ A₂] [代数等价类 F R A₁ A₂] (f : F)
  证明: rfl
-/
protected theorem coe_coe {F : Type*} [EquivLike F A₁ A₂] [AlgEquivClass F R A₁ A₂] (f : F) :
    ⇑(AlgEquivClass.toAlgEquiv f) = f :=
  rfl

/--
theorem `coe_fun_injective` / 定理 `coe_fun_injective`

English:
theorem coe_fun_injective
  statement: @Function.Injective (A₁ ≃ₐ[R] A₂) (A₁ -> A₂) fun e => (e : A₁ -> A₂)
  proof: DFunLike.coe_injective

中文:
定理 coe_fun_injective
  结论: @函数.单射 (A₁ ≃ₐ[R] A₂) (A₁ -> A₂) fun e => (e : A₁ -> A₂)
  证明: DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_fun_injective : @Function.Injective (A₁ ≃ₐ[R] A₂) (A₁ -> A₂) fun e => (e : A₁ -> A₂) :=
  DFunLike.coe_injective

/--
Definition of `toLinearEquiv` / `toLinearEquiv` 的定义

English:
definition toLinearEquiv
  signature: (e : A₁ ≃ₐ[R] A₂)
  body: e.toAddEquiv
  map_smul' := map_smulₛₗ e

中文:
定义 toLinearEquiv
  签名: (e : A₁ ≃ₐ[R] A₂)
  定义体: e.toAddEquiv
  map_smul' := map_smulₛₗ e
-/
@[coe, simps! apply] def toLinearEquiv (e : A₁ ≃ₐ[R] A₂) : A₁ ≃ₗ[R] A₂ where
  toAddEquiv := e.toAddEquiv
  map_smul' := map_smulₛₗ e

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (A₁ ≃ₐ[R] A₂) (A₁ ≃ₗ[R] A₂)
  body: toLinearEquiv

中文:
实例 :
  签名: CoeOut (A₁ ≃ₐ[R] A₂) (A₁ ≃ₗ[R] A₂)
  定义体: toLinearEquiv

Depends on / 依赖: toLinearEquiv
-/
instance : CoeOut (A₁ ≃ₐ[R] A₂) (A₁ ≃ₗ[R] A₂) where coe := toLinearEquiv
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (A₁ ≃ₐ[R] A₂) (A₁ ≃+* A₂)
  body: toRingEquiv

@[simp]

中文:
实例 :
  签名: CoeOut (A₁ ≃ₐ[R] A₂) (A₁ ≃+* A₂)
  定义体: toRingEquiv

@[simp]

Depends on / 依赖: toRingEquiv
-/
instance : CoeOut (A₁ ≃ₐ[R] A₂) (A₁ ≃+* A₂) where coe := toRingEquiv

@[simp]
/--
theorem `coe_toEquiv` / 定理 `coe_toEquiv`

English:
theorem coe_toEquiv
  statement: ((e : A₁ ≃ A₂) : A₁ -> A₂) = e
  proof: rfl

@[deprecated "Now a syntactic equality" (since := "2026-04-09"), nolint synTaut]

中文:
定理 coe_toEquiv
  结论: ((e : A₁ ≃ A₂) : A₁ -> A₂) = e
  证明: rfl

@[deprecated "Now a syntactic equality" (since := "2026-04-09"), nolint synTaut]
-/
theorem coe_toEquiv : ((e : A₁ ≃ A₂) : A₁ -> A₂) = e :=
  rfl

@[deprecated "Now a syntactic equality" (since := "2026-04-09"), nolint synTaut]
/--
theorem `toRingEquiv_eq_coe` / 定理 `toRingEquiv_eq_coe`

English:
theorem toRingEquiv_eq_coe
  statement: e.toRingEquiv = e
  proof: rfl

@[simp]

中文:
定理 toRingEquiv_eq_coe
  结论: e.toRingEquiv = e
  证明: rfl

@[simp]
-/
theorem toRingEquiv_eq_coe : e.toRingEquiv = e :=
  rfl

@[simp]
/--
lemma `toRingEquiv_toRingHom` / 引理 `toRingEquiv_toRingHom`

English:
lemma toRingEquiv_toRingHom
  statement: ((e : A₁ ≃+* A₂) : A₁ ->+* A₂) = e
  proof: rfl

中文:
引理 toRingEquiv_toRingHom
  结论: ((e : A₁ ≃+* A₂) : A₁ ->+* A₂) = e
  证明: rfl
-/
lemma toRingEquiv_toRingHom : ((e : A₁ ≃+* A₂) : A₁ ->+* A₂) = e :=
  rfl

/--
theorem `coe_ringEquiv` / 定理 `coe_ringEquiv`

English:
theorem coe_ringEquiv
  statement: ((e : A₁ ≃+* A₂) : A₁ -> A₂) = e
  proof: rfl

@[deprecated (since := "2026-06-21")] alias coe_ringEquiv' := coe_ringEquiv

中文:
定理 coe_ringEquiv
  结论: ((e : A₁ ≃+* A₂) : A₁ -> A₂) = e
  证明: rfl

@[deprecated (since := "2026-06-21")] alias coe_ringEquiv' := coe_ringEquiv
-/
theorem coe_ringEquiv : ((e : A₁ ≃+* A₂) : A₁ -> A₂) = e := rfl

@[deprecated (since := "2026-06-21")] alias coe_ringEquiv' := coe_ringEquiv

/--
theorem `coe_ringEquiv_injective` / 定理 `coe_ringEquiv_injective`

English:
theorem coe_ringEquiv_injective
  statement: Function.Injective ((↑) : (A₁ ≃ₐ[R] A₂) -> A₁ ≃+* A₂)
  proof: fun _ _ h => ext RingEquiv.congr_fun h

中文:
定理 coe_ringEquiv_injective
  结论: 函数.单射 ((↑) : (A₁ ≃ₐ[R] A₂) -> A₁ ≃+* A₂)
  证明: fun _ _ h => ext RingEquiv.congr_fun h

Depends on / 依赖: RingEquiv, RingEquiv.congr_fun, congr_fun
-/
theorem coe_ringEquiv_injective : Function.Injective ((↑) : (A₁ ≃ₐ[R] A₂) -> A₁ ≃+* A₂) :=
fun _ _ h => ext RingEquiv.congr_fun h

/-- Interpret an algebra equivalence as an algebra homomorphism.

This definition is included for symmetry with the other `to*Hom` projections.
The `simp` normal form is to use the coercion of the `AlgHomClass.coeTC` instance. -/
@[coe]
/--
Definition of `toAlgHom` / `toAlgHom` 的定义

English:
definition toAlgHom
  signature: : A₁ ->ₐ[R] A₂
  body: { e with
    map_one' := map_one e
    map_zero' := map_zero e }

中文:
定义 toAlgHom
  签名: : A₁ ->ₐ[R] A₂
  定义体: { e with
    map_one' := map_one e
    map_zero' := map_zero e }

Depends on / 依赖: map_one, map_zero
-/
def toAlgHom : A₁ ->ₐ[R] A₂ :=
  { e with
    map_one' := map_one e
    map_zero' := map_zero e }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (A₁ ≃ₐ[R] A₂) (A₁ ->ₐ[R] A₂)
  body: AlgEquiv.toAlgHom

@[deprecated "Now a syntactic equality" (since := "2026-04-29"), nolint synTaut]

中文:
实例 :
  签名: CoeOut (A₁ ≃ₐ[R] A₂) (A₁ ->ₐ[R] A₂)
  定义体: AlgEquiv.toAlgHom

@[deprecated "Now a syntactic equality" (since := "2026-04-29"), nolint synTaut]

Depends on / 依赖: AlgEquiv, AlgEquiv.toAlgHom, toAlgHom
-/
instance : CoeOut (A₁ ≃ₐ[R] A₂) (A₁ ->ₐ[R] A₂) where coe := AlgEquiv.toAlgHom

@[deprecated "Now a syntactic equality" (since := "2026-04-29"), nolint synTaut]
/--
theorem `toAlgHom_eq_coe` / 定理 `toAlgHom_eq_coe`

English:
theorem toAlgHom_eq_coe
  statement: e.toAlgHom = e
  proof: rfl

中文:
定理 toAlgHom_eq_coe
  结论: e.toAlgHom = e
  证明: rfl
-/
theorem toAlgHom_eq_coe : e.toAlgHom = e :=
  rfl

/--
theorem `toAlgHom_apply` / 定理 `toAlgHom_apply`

English:
theorem toAlgHom_apply
  given: (x : A₁)
  statement: e.toAlgHom x = e x
  proof: rfl

@[simp, norm_cast]

中文:
定理 toAlgHom_apply
  条件: (x : A₁)
  结论: e.toAlgHom x = e x
  证明: rfl

@[simp, norm_cast]
-/
theorem toAlgHom_apply (x : A₁) : e.toAlgHom x = e x :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_toAlgHom` / 定理 `coe_toAlgHom`

English:
theorem coe_toAlgHom
  statement: DFunLike.coe e.toAlgHom = e
  proof: rfl

中文:
定理 coe_toAlgHom
  结论: 依赖函数状.coe e.toAlgHom = e
  证明: rfl
-/
theorem coe_toAlgHom : DFunLike.coe e.toAlgHom = e := rfl

/--
theorem `coe_toAlgHom_injective` / 定理 `coe_toAlgHom_injective`

English:
theorem coe_toAlgHom_injective
  statement: Function.Injective ((↑) : (A₁ ≃ₐ[R] A₂) -> A₁ ->ₐ[R] A₂)
  proof: fun _ _ h => ext AlgHom.congr_fun h

@[deprecated (since := "2026-05-05")] alias coe_algHom := coe_toAlgHom
@[deprecated (since := "2026-05-05")] alias coe_algHom_injective := coe_toAlgHom_injective

@[simp, norm_cast]

中文:
定理 coe_toAlgHom_injective
  结论: 函数.单射 ((↑) : (A₁ ≃ₐ[R] A₂) -> A₁ ->ₐ[R] A₂)
  证明: fun _ _ h => ext AlgHom.congr_fun h

@[deprecated (since := "2026-05-05")] alias coe_algHom := coe_toAlgHom
@[deprecated (since := "2026-05-05")] alias coe_algHom_injective := coe_toAlgHom_injective

@[simp, norm_cast]

Depends on / 依赖: AlgHom, AlgHom.congr_fun, congr_fun
-/
theorem coe_toAlgHom_injective : Function.Injective ((↑) : (A₁ ≃ₐ[R] A₂) -> A₁ ->ₐ[R] A₂) :=
fun _ _ h => ext AlgHom.congr_fun h

@[deprecated (since := "2026-05-05")] alias coe_algHom := coe_toAlgHom
@[deprecated (since := "2026-05-05")] alias coe_algHom_injective := coe_toAlgHom_injective

@[simp, norm_cast]
/--
lemma `toAlgHom_toRingHom` / 引理 `toAlgHom_toRingHom`

English:
lemma toAlgHom_toRingHom
  statement: ((e : A₁ ->ₐ[R] A₂) : A₁ ->+* A₂) = e
  proof: rfl

中文:
引理 toAlgHom_toRingHom
  结论: ((e : A₁ ->ₐ[R] A₂) : A₁ ->+* A₂) = e
  证明: rfl
-/
lemma toAlgHom_toRingHom : ((e : A₁ ->ₐ[R] A₂) : A₁ ->+* A₂) = e :=
  rfl

/--
theorem `coe_ringHom_commutes` / 定理 `coe_ringHom_commutes`

English:
theorem coe_ringHom_commutes
  statement: ((e : A₁ ->ₐ[R] A₂) : A₁ ->+* A₂) = ((e : A₁ ≃+* A₂) : A₁ ->+* A₂)
  proof: rfl

@[simp]

中文:
定理 coe_ringHom_commutes
  结论: ((e : A₁ ->ₐ[R] A₂) : A₁ ->+* A₂) = ((e : A₁ ≃+* A₂) : A₁ ->+* A₂)
  证明: rfl

@[simp]
-/
theorem coe_ringHom_commutes : ((e : A₁ ->ₐ[R] A₂) : A₁ ->+* A₂) = ((e : A₁ ≃+* A₂) : A₁ ->+* A₂) :=
  rfl

@[simp]
/--
theorem `commutes` / 定理 `commutes`

English:
theorem commutes
  statement: forall r : R, e (algebraMap R A₁ r) = algebraMap R A₂ r
  proof: e.commutes'

中文:
定理 commutes
  结论: 对任意 r : R, e (algebraMap R A₁ r) = algebraMap R A₂ r
  证明: e.commutes'

Depends on / 依赖: commutes, e.commutes
-/
theorem commutes : forall r : R, e (algebraMap R A₁ r) = algebraMap R A₂ r :=
  e.commutes'

end coe

section bijective

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  statement: Function.Bijective e
  proof: EquivLike.bijective e

中文:
定理 bijective
  结论: 函数.双射 e
  证明: EquivLike.bijective e
-/
protected theorem bijective : Function.Bijective e :=
  EquivLike.bijective e

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  statement: Function.Injective e
  proof: EquivLike.injective e

中文:
定理 injective
  结论: 函数.单射 e
  证明: EquivLike.injective e
-/
protected theorem injective : Function.Injective e :=
  EquivLike.injective e

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  statement: Function.Surjective e
  proof: EquivLike.surjective e

中文:
定理 surjective
  结论: 函数.满射 e
  证明: EquivLike.surjective e
-/
protected theorem surjective : Function.Surjective e :=
  EquivLike.surjective e

end bijective

section refl

/-- Algebra equivalences are reflexive. -/
@[refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : A₁ ≃ₐ[R] A₁
  body: { (.refl _ : A₁ ≃+* A₁) with commutes' := fun _ => rfl }

中文:
定义 refl
  签名: : A₁ ≃ₐ[R] A₁
  定义体: { (.refl _ : A₁ ≃+* A₁) with commutes' := fun _ => rfl }

Depends on / 依赖: commutes
-/
def refl : A₁ ≃ₐ[R] A₁ :=
  { (.refl _ : A₁ ≃+* A₁) with commutes' := fun _ => rfl }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (A₁ ≃ₐ[R] A₁)
  body: ⟨refl⟩

中文:
实例 :
  签名: 可居 (A₁ ≃ₐ[R] A₁)
  定义体: ⟨refl⟩
-/
instance : Inhabited (A₁ ≃ₐ[R] A₁) :=
  ⟨refl⟩

/--
lemma `refl_toAlgHom` / 引理 `refl_toAlgHom`

English:
lemma refl_toAlgHom
  statement: (refl : A₁ ≃ₐ[R] A₁) = AlgHom.id R A₁
  proof: rfl

中文:
引理 refl_toAlgHom
  结论: (refl : A₁ ≃ₐ[R] A₁) = 代数态射.id R A₁
  证明: rfl
-/
@[simp, norm_cast] lemma refl_toAlgHom : (refl : A₁ ≃ₐ[R] A₁) = AlgHom.id R A₁ := rfl
/--
lemma `refl_toRingHom` / 引理 `refl_toRingHom`

English:
lemma refl_toRingHom
  statement: (refl : A₁ ≃ₐ[R] A₁) = RingHom.id A₁
  proof: rfl

@[simp]

中文:
引理 refl_toRingHom
  结论: (refl : A₁ ≃ₐ[R] A₁) = 环态射.id A₁
  证明: rfl

@[simp]

Depends on / 依赖: Inhabited
-/
@[simp, norm_cast] lemma refl_toRingHom : (refl : A₁ ≃ₐ[R] A₁) = RingHom.id A₁ := rfl

@[simp]
/--
theorem `coe_refl` / 定理 `coe_refl`

English:
theorem coe_refl
  statement: ⇑(refl : A₁ ≃ₐ[R] A₁) = id
  proof: rfl

中文:
定理 coe_refl
  结论: ⇑(refl : A₁ ≃ₐ[R] A₁) = id
  证明: rfl
-/
theorem coe_refl : ⇑(refl : A₁ ≃ₐ[R] A₁) = id :=
  rfl

end refl

section symm

/-- Algebra equivalences are symmetric. -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (e : A₁ ≃ₐ[R] A₂)
  body: { e.toRingEquiv.symm with
    commutes' := fun r => by
      rw [← e.toRingEquiv.symm_apply_apply (algebraMap R A₁ r)]
      congr
      simp }

中文:
定义 symm
  签名: (e : A₁ ≃ₐ[R] A₂)
  定义体: { e.toRingEquiv.symm with
    commutes' := fun r => by
      rw [← e.toRingEquiv.symm_apply_apply (algebraMap R A₁ r)]
      congr
      simp }

Depends on / 依赖: algebraMap, commutes, e.toRingEquiv.symm, e.toRingEquiv.symm_apply_apply, symm_apply_apply, toRingEquiv
-/
def symm (e : A₁ ≃ₐ[R] A₂) : A₂ ≃ₐ[R] A₁ :=
  { e.toRingEquiv.symm with
    commutes' := fun r => by
      rw [← e.toRingEquiv.symm_apply_apply (algebraMap R A₁ r)]
      congr
      simp }

/--
theorem `invFun_eq_symm` / 定理 `invFun_eq_symm`

English:
theorem invFun_eq_symm
  given: {e : A₁ ≃ₐ[R] A₂}
  statement: e.invFun = e.symm
  proof: rfl

@[simp]

中文:
定理 invFun_eq_symm
  条件: {e : A₁ ≃ₐ[R] A₂}
  结论: e.invFun = e.symm
  证明: rfl

@[simp]
-/
theorem invFun_eq_symm {e : A₁ ≃ₐ[R] A₂} : e.invFun = e.symm :=
  rfl

@[simp]
/--
theorem `coe_apply_coe_coe_symm_apply` / 定理 `coe_apply_coe_coe_symm_apply`

English:
theorem coe_apply_coe_coe_symm_apply
  statement: {F : Type*} [EquivLike F A₁ A₂] [AlgEquivClass F R A₁ A₂]
  proof: EquivLike.right_inv f x

@[simp]

中文:
定理 coe_apply_coe_coe_symm_apply
  结论: {F : 类型} [等价状 F A₁ A₂] [代数等价类 F R A₁ A₂]
  证明: EquivLike.right_inv f x

@[simp]

Depends on / 依赖: EquivLike, EquivLike.right_inv, right_inv
-/
theorem coe_apply_coe_coe_symm_apply {F : Type*} [EquivLike F A₁ A₂] [AlgEquivClass F R A₁ A₂]
    (f : F) (x : A₂) :
    f ((AlgEquivClass.toAlgEquiv f).symm x) = x :=
  EquivLike.right_inv f x

@[simp]
/--
theorem `coe_coe_symm_apply_coe_apply` / 定理 `coe_coe_symm_apply_coe_apply`

English:
theorem coe_coe_symm_apply_coe_apply
  statement: {F : Type*} [EquivLike F A₁ A₂] [AlgEquivClass F R A₁ A₂]
  proof: EquivLike.left_inv f x

中文:
定理 coe_coe_symm_apply_coe_apply
  结论: {F : 类型} [等价状 F A₁ A₂] [代数等价类 F R A₁ A₂]
  证明: EquivLike.left_inv f x

Depends on / 依赖: EquivLike, EquivLike.left_inv, left_inv
-/
theorem coe_coe_symm_apply_coe_apply {F : Type*} [EquivLike F A₁ A₂] [AlgEquivClass F R A₁ A₂]
    (f : F) (x : A₁) :
    (AlgEquivClass.toAlgEquiv f).symm (f x) = x :=
  EquivLike.left_inv f x

/-- `simp` normal form of `invFun_eq_symm` -/
@[simp]
/--
theorem `symm_toEquiv_eq_symm` / 定理 `symm_toEquiv_eq_symm`

English:
theorem symm_toEquiv_eq_symm
  given: {e : A₁ ≃ₐ[R] A₂}
  statement: (e : A₁ ≃ A₂).symm = e.symm
  proof: rfl

@[simp]

中文:
定理 symm_toEquiv_eq_symm
  条件: {e : A₁ ≃ₐ[R] A₂}
  结论: (e : A₁ ≃ A₂).symm = e.symm
  证明: rfl

@[simp]
-/
theorem symm_toEquiv_eq_symm {e : A₁ ≃ₐ[R] A₂} : (e : A₁ ≃ A₂).symm = e.symm :=
  rfl

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (e : A₁ ≃ₐ[R] A₂)
  statement: e.symm.symm = e
  proof: rfl

中文:
定理 symm_symm
  条件: (e : A₁ ≃ₐ[R] A₂)
  结论: e.symm.symm = e
  证明: rfl
-/
theorem symm_symm (e : A₁ ≃ₐ[R] A₂) : e.symm.symm = e := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (symm : (A₁ ≃ₐ[R] A₂) -> A₂ ≃ₐ[R] A₁)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

中文:
定理 symm_bijective
  结论: 函数.双射 (symm : (A₁ ≃ₐ[R] A₂) -> A₂ ≃ₐ[R] A₁)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (symm : (A₁ ≃ₐ[R] A₂) -> A₂ ≃ₐ[R] A₁) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/--
theorem `mk_coe'` / 定理 `mk_coe'`

English:
theorem mk_coe'
  given: (e : A₁ ≃ₐ[R] A₂) (f h₁ h₂ h₃ h₄ h₅)
  proof: symm_bijective.injective ext fun _ => rfl

@[simp]

中文:
定理 mk_coe'
  条件: (e : A₁ ≃ₐ[R] A₂) (f h₁ h₂ h₃ h₄ h₅)
  证明: symm_bijective.injective ext fun _ => rfl

@[simp]

Depends on / 依赖: injective, symm_bijective, symm_bijective.injective
-/
theorem mk_coe' (e : A₁ ≃ₐ[R] A₂) (f h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨f, e, h₁, h₂⟩, h₃, h₄, h₅⟩ : A₂ ≃ₐ[R] A₁) = e.symm :=
symm_bijective.injective ext fun _ => rfl

@[simp]
/--
theorem `symm_mk` / 定理 `symm_mk`

English:
theorem symm_mk
  given: (e : A₁ ≃ A₂) (h₁ h₂ h₃)
  statement: dsimp%
  proof: rfl

@[simp]

中文:
定理 symm_mk
  条件: (e : A₁ ≃ A₂) (h₁ h₂ h₃)
  结论: dsimp%
  证明: rfl

@[simp]

Depends on / 依赖: e.symm
-/
theorem symm_mk (e : A₁ ≃ A₂) (h₁ h₂ h₃) : dsimp%
    (mk e h₁ h₂ h₃ : A₁ ≃ₐ[R] A₂).symm =
      { (mk e h₁ h₂ h₃ : A₁ ≃ₐ[R] A₂).symm with
        toEquiv := e.symm } :=
  rfl

@[simp]
/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  statement: (AlgEquiv.refl : A₁ ≃ₐ[R] A₁).symm = AlgEquiv.refl
  proof: rfl

中文:
定理 refl_symm
  结论: (代数等价.refl : A₁ ≃ₐ[R] A₁).symm = 代数等价.refl
  证明: rfl
-/
theorem refl_symm : (AlgEquiv.refl : A₁ ≃ₐ[R] A₁).symm = AlgEquiv.refl :=
  rfl

/--
theorem `toRingEquiv_symm` / 定理 `toRingEquiv_symm`

English:
theorem toRingEquiv_symm
  statement: (e : A₁ ≃+* A₂).symm = e.symm
  proof: rfl

@[simp]

中文:
定理 toRingEquiv_symm
  结论: (e : A₁ ≃+* A₂).symm = e.symm
  证明: rfl

@[simp]
-/
theorem toRingEquiv_symm : (e : A₁ ≃+* A₂).symm = e.symm :=
  rfl

@[simp]
/--
theorem `symm_toRingEquiv` / 定理 `symm_toRingEquiv`

English:
theorem symm_toRingEquiv
  statement: (e.symm : A₂ ≃+* A₁) = (e : A₁ ≃+* A₂).symm
  proof: rfl

@[simp]

中文:
定理 symm_toRingEquiv
  结论: (e.symm : A₂ ≃+* A₁) = (e : A₁ ≃+* A₂).symm
  证明: rfl

@[simp]
-/
theorem symm_toRingEquiv : (e.symm : A₂ ≃+* A₁) = (e : A₁ ≃+* A₂).symm :=
  rfl

@[simp]
/--
theorem `symm_toAddEquiv` / 定理 `symm_toAddEquiv`

English:
theorem symm_toAddEquiv
  statement: (e.symm : A₂ ≃+ A₁) = (e : A₁ ≃+ A₂).symm
  proof: rfl

@[simp]

中文:
定理 symm_toAddEquiv
  结论: (e.symm : A₂ ≃+ A₁) = (e : A₁ ≃+ A₂).symm
  证明: rfl

@[simp]
-/
theorem symm_toAddEquiv : (e.symm : A₂ ≃+ A₁) = (e : A₁ ≃+ A₂).symm :=
  rfl

@[simp]
/--
theorem `symm_toMulEquiv` / 定理 `symm_toMulEquiv`

English:
theorem symm_toMulEquiv
  statement: (e.symm : A₂ ≃* A₁) = (e : A₁ ≃* A₂).symm
  proof: rfl

@[simp]

中文:
定理 symm_toMulEquiv
  结论: (e.symm : A₂ ≃* A₁) = (e : A₁ ≃* A₂).symm
  证明: rfl

@[simp]
-/
theorem symm_toMulEquiv : (e.symm : A₂ ≃* A₁) = (e : A₁ ≃* A₂).symm :=
  rfl

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : A₁ ≃ₐ[R] A₂)
  statement: forall x, e (e.symm x) = x
  proof: e.toEquiv.apply_symm_apply

@[simp]

中文:
定理 apply_symm_apply
  条件: (e : A₁ ≃ₐ[R] A₂)
  结论: 对任意 x, e (e.symm x) = x
  证明: e.toEquiv.apply_symm_apply

@[simp]

Depends on / 依赖: GradeZero, GradeZero.one, apply_symm_apply, e.toEquiv.apply_symm_apply, toEquiv
-/
theorem apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x, e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : A₁ ≃ₐ[R] A₂)
  statement: forall x, e.symm (e x) = x
  proof: e.toEquiv.symm_apply_apply

中文:
定理 symm_apply_apply
  条件: (e : A₁ ≃ₐ[R] A₂)
  结论: 对任意 x, e.symm (e x) = x
  证明: e.toEquiv.symm_apply_apply

Depends on / 依赖: e.toEquiv.symm_apply_apply, symm_apply_apply, toEquiv
-/
theorem symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x, e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: (e : A₁ ≃ₐ[R] A₂) {x y}
  statement: e.symm x = y ↔ x = e y
  proof: e.toEquiv.symm_apply_eq

中文:
定理 symm_apply_eq
  条件: (e : A₁ ≃ₐ[R] A₂) {x y}
  结论: e.symm x = y ↔ x = e y
  证明: e.toEquiv.symm_apply_eq

Depends on / 依赖: GradeZero, GradeZero.mul, e.toEquiv.symm_apply_eq, symm_apply_eq, toEquiv
-/
theorem symm_apply_eq (e : A₁ ≃ₐ[R] A₂) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: (e : A₁ ≃ₐ[R] A₂) {x y}
  statement: y = e.symm x ↔ e y = x
  proof: e.toEquiv.eq_symm_apply

@[simp]

中文:
定理 eq_symm_apply
  条件: (e : A₁ ≃ₐ[R] A₂) {x y}
  结论: y = e.symm x ↔ e y = x
  证明: e.toEquiv.eq_symm_apply

@[simp]

Depends on / 依赖: e.toEquiv.eq_symm_apply, eq_symm_apply, toEquiv
-/
theorem eq_symm_apply (e : A₁ ≃ₐ[R] A₂) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

@[simp]
/--
theorem `comp_symm` / 定理 `comp_symm`

English:
theorem comp_symm
  given: (e : A₁ ≃ₐ[R] A₂)
  statement: AlgHom.comp (e : A₁ ->ₐ[R] A₂) ↑e.symm = AlgHom.id R A₂
  proof: by
  ext
  simp

@[simp]

中文:
定理 comp_symm
  条件: (e : A₁ ≃ₐ[R] A₂)
  结论: 代数态射.comp (e : A₁ ->ₐ[R] A₂) ↑e.symm = 代数态射.id R A₂
  证明: by
  ext
  simp

@[simp]
-/
theorem comp_symm (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp (e : A₁ ->ₐ[R] A₂) ↑e.symm = AlgHom.id R A₂ := by
  ext
  simp

@[simp]
/--
theorem `symm_comp` / 定理 `symm_comp`

English:
theorem symm_comp
  given: (e : A₁ ≃ₐ[R] A₂)
  statement: AlgHom.comp ↑e.symm (e : A₁ ->ₐ[R] A₂) = AlgHom.id R A₁
  proof: by
  ext
  simp

中文:
定理 symm_comp
  条件: (e : A₁ ≃ₐ[R] A₂)
  结论: 代数态射.comp ↑e.symm (e : A₁ ->ₐ[R] A₂) = 代数态射.id R A₁
  证明: by
  ext
  simp
-/
theorem symm_comp (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp ↑e.symm (e : A₁ ->ₐ[R] A₂) = AlgHom.id R A₁ := by
  ext
  simp

/--
theorem `leftInverse_symm` / 定理 `leftInverse_symm`

English:
theorem leftInverse_symm
  given: (e : A₁ ≃ₐ[R] A₂)
  statement: Function.LeftInverse e.symm e
  proof: e.left_inv

中文:
定理 leftInverse_symm
  条件: (e : A₁ ≃ₐ[R] A₂)
  结论: 函数.左逆 e.symm e
  证明: e.left_inv

Depends on / 依赖: e.left_inv, left_inv
-/
theorem leftInverse_symm (e : A₁ ≃ₐ[R] A₂) : Function.LeftInverse e.symm e :=
  e.left_inv

/--
theorem `rightInverse_symm` / 定理 `rightInverse_symm`

English:
theorem rightInverse_symm
  given: (e : A₁ ≃ₐ[R] A₂)
  statement: Function.RightInverse e.symm e
  proof: e.right_inv

中文:
定理 rightInverse_symm
  条件: (e : A₁ ≃ₐ[R] A₂)
  结论: 函数.右逆 e.symm e
  证明: e.right_inv

Depends on / 依赖: GradeZero, GradeZero.monoid, Monoid, e.right_inv, monoid, right_inv
-/
theorem rightInverse_symm (e : A₁ ≃ₐ[R] A₂) : Function.RightInverse e.symm e :=
  e.right_inv

/--
lemma `image_symm_eq_preimage` / 引理 `image_symm_eq_preimage`

English:
lemma image_symm_eq_preimage
  given: (e : A₁ ≃ₐ[R] A₂) (s : Set A₂)
  statement: e.symm '' s = e ⁻¹' s
  proof: e.toLinearEquiv.image_symm_eq_preimage _

中文:
引理 image_symm_eq_preimage
  条件: (e : A₁ ≃ₐ[R] A₂) (s : 集合 A₂)
  结论: e.symm '' s = e ⁻¹' s
  证明: e.toLinearEquiv.image_symm_eq_preimage _

Depends on / 依赖: CommMonoid, GradeZero, GradeZero.commMonoid, commMonoid, e.toLinearEquiv.image_symm_eq_preimage, image_symm_eq_preimage, toLinearEquiv
-/
lemma image_symm_eq_preimage (e : A₁ ≃ₐ[R] A₂) (s : Set A₂) : e.symm '' s = e ⁻¹' s :=
  e.toLinearEquiv.image_symm_eq_preimage _

end symm

section simps

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (e : A₁ ≃ₐ[R] A₂)
  body: e

中文:
定义 Simps.apply
  签名: (e : A₁ ≃ₐ[R] A₂)
  定义体: e
-/
def Simps.apply (e : A₁ ≃ₐ[R] A₂) : A₁ -> A₂ :=
  e

/--
Definition of `Simps.toEquiv` / `Simps.toEquiv` 的定义

English:
definition Simps.toEquiv
  signature: (e : A₁ ≃ₐ[R] A₂)
  body: e

中文:
定义 Simps.toEquiv
  签名: (e : A₁ ≃ₐ[R] A₂)
  定义体: e
-/
def Simps.toEquiv (e : A₁ ≃ₐ[R] A₂) : A₁ ≃ A₂ :=
  e

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (e : A₁ ≃ₐ[R] A₂)
  body: e.symm

initialize_simps_projections AlgEquiv (toFun -> apply, invFun -> symm_apply)

中文:
定义 Simps.symm_apply
  签名: (e : A₁ ≃ₐ[R] A₂)
  定义体: e.symm

initialize_simps_projections AlgEquiv (toFun -> apply, invFun -> symm_apply)
-/
def Simps.symm_apply (e : A₁ ≃ₐ[R] A₂) : A₂ -> A₁ :=
  e.symm

initialize_simps_projections AlgEquiv (toFun -> apply, invFun -> symm_apply)

end simps

section trans

/-- Algebra equivalences are transitive. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃)
  body: { e₁.toRingEquiv.trans e₂.toRingEquiv with
    commutes' := fun r => show e₂.toFun (e₁.toFun _) = _ by rw [e₁.commutes', e₂.commutes'] }

@[simp]

中文:
定义 trans
  签名: (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃)
  定义体: { e₁.toRingEquiv.trans e₂.toRingEquiv with
    commutes' := fun r => show e₂.toFun (e₁.toFun _) = _ by rw [e₁.commutes', e₂.commutes'] }

@[simp]

Depends on / 依赖: commutes, toRingEquiv, toRingEquiv.trans
-/
def trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : A₁ ≃ₐ[R] A₃ :=
  { e₁.toRingEquiv.trans e₂.toRingEquiv with
    commutes' := fun r => show e₂.toFun (e₁.toFun _) = _ by rw [e₁.commutes', e₂.commutes'] }

@[simp]
/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  given: (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃)
  statement: ⇑(e₁.trans e₂) = e₂ ∘ e₁
  proof: rfl

@[simp]

中文:
定理 coe_trans
  条件: (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃)
  结论: ⇑(e₁.trans e₂) = e₂ ∘ e₁
  证明: rfl

@[simp]
-/
theorem coe_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₁)
  statement: (e₁.trans e₂) x = e₂ (e₁ x)
  proof: rfl

@[simp]

中文:
定理 trans_apply
  条件: (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₁)
  结论: (e₁.trans e₂) x = e₂ (e₁ x)
  证明: rfl

@[simp]
-/
theorem trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₁) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl

@[simp]
/--
theorem `symm_trans_apply` / 定理 `symm_trans_apply`

English:
theorem symm_trans_apply
  given: (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₃)
  proof: rfl

中文:
定理 symm_trans_apply
  条件: (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₃)
  证明: rfl
-/
theorem symm_trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₃) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl

/--
lemma `self_trans_symm` / 引理 `self_trans_symm`

English:
lemma self_trans_symm
  given: (e : A₁ ≃ₐ[R] A₂)
  statement: e.trans e.symm = refl
  proof: by ext; simp

中文:
引理 self_trans_symm
  条件: (e : A₁ ≃ₐ[R] A₂)
  结论: e.trans e.symm = refl
  证明: by ext; simp
-/
@[simp] lemma self_trans_symm (e : A₁ ≃ₐ[R] A₂) : e.trans e.symm = refl := by ext; simp
/--
lemma `symm_trans_self` / 引理 `symm_trans_self`

English:
lemma symm_trans_self
  given: (e : A₁ ≃ₐ[R] A₂)
  statement: e.symm.trans e = refl
  proof: by ext; simp

@[simp, norm_cast]

中文:
引理 symm_trans_self
  条件: (e : A₁ ≃ₐ[R] A₂)
  结论: e.symm.trans e = refl
  证明: by ext; simp

@[simp, norm_cast]
-/
@[simp] lemma symm_trans_self (e : A₁ ≃ₐ[R] A₂) : e.symm.trans e = refl := by ext; simp

@[simp, norm_cast]
/--
lemma `toRingHom_trans` / 引理 `toRingHom_trans`

English:
lemma toRingHom_trans
  given: (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃)
  proof: rfl

中文:
引理 toRingHom_trans
  条件: (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃)
  证明: rfl
-/
lemma toRingHom_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
    (e₁.trans e₂ : A₁ ->+* A₃) = .comp e₂ (e₁ : A₁ ->+* A₂) := rfl

end trans

/-- `Equiv.cast (congrArg _ h)` as an algebra equiv.

Note that unlike `Equiv.cast`, this takes an equality of indices rather than an equality of types,
to avoid having to deal with an equality of the algebraic structure itself. -/
@[simps!]
/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  body: RingEquiv.cast h
  commutes' _ := by cases h; rfl

中文:
定义 cast
  定义体: RingEquiv.cast h
  commutes' _ := by cases h; rfl
-/
protected def cast
    {ι : Type*} {A : ι -> Type*} [forall i, Semiring (A i)] [forall i, Algebra R (A i)] {i j : ι} (h : i = j) :
    A i ≃ₐ[R] A j where
  __ := RingEquiv.cast h
  commutes' _ := by cases h; rfl

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'`, then the type of maps
`A₁ →ₐ[R] A₂` is equivalent to the type of maps `A₁' →ₐ[R] A₂'`. -/
@[simps apply]
/--
Definition of `arrowCongr` / `arrowCongr` 的定义

English:
definition arrowCongr
  signature: (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂')
  body: (e₂.toAlgHom.comp f).comp e₁.symm.toAlgHom
  invFun f := (e₂.symm.toAlgHom.comp f).comp e₁.toAlgHom
  left_inv f := by
    simp only [AlgHom.comp_assoc, symm_comp]
    simp only [← AlgHom.comp_assoc, symm_comp, AlgHom.id_comp, AlgHom.comp_id]
  right_inv f := by
    simp only [AlgHom.comp_assoc, comp_symm]
    simp only [← AlgHom.comp_assoc, comp_symm, AlgHom.id_comp, AlgHom.comp_id]

中文:
定义 arrowCongr
  签名: (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂')
  定义体: (e₂.toAlgHom.comp f).comp e₁.symm.toAlgHom
  invFun f := (e₂.symm.toAlgHom.comp f).comp e₁.toAlgHom
  left_inv f := by
    simp only [AlgHom.comp_assoc, symm_comp]
    simp only [← AlgHom.comp_assoc, symm_comp, AlgHom.id_comp, AlgHom.comp_id]
  right_inv f := by
    simp only [AlgHom.comp_assoc, comp_symm]
    simp only [← AlgHom.comp_assoc, comp_symm, AlgHom.id_comp, AlgHom.comp_id]

Depends on / 依赖: symm.toAlgHom, toAlgHom, toAlgHom.comp
-/
def arrowCongr (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') : (A₁ ->ₐ[R] A₂) ≃ (A₁' ->ₐ[R] A₂') where
  toFun f := (e₂.toAlgHom.comp f).comp e₁.symm.toAlgHom
  invFun f := (e₂.symm.toAlgHom.comp f).comp e₁.toAlgHom
  left_inv f := by
    simp only [AlgHom.comp_assoc, symm_comp]
    simp only [← AlgHom.comp_assoc, symm_comp, AlgHom.id_comp, AlgHom.comp_id]
  right_inv f := by
    simp only [AlgHom.comp_assoc, comp_symm]
    simp only [← AlgHom.comp_assoc, comp_symm, AlgHom.id_comp, AlgHom.comp_id]

/--
theorem `arrowCongr_comp` / 定理 `arrowCongr_comp`

English:
theorem arrowCongr_comp
  statement: (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂')
  proof: by
  ext
  simp

@[simp]

中文:
定理 arrowCongr_comp
  结论: (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂')
  证明: by
  ext
  simp

@[simp]
-/
theorem arrowCongr_comp (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂')
    (e₃ : A₃ ≃ₐ[R] A₃') (f : A₁ ->ₐ[R] A₂) (g : A₂ ->ₐ[R] A₃) :
    arrowCongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f) := by
  ext
  simp

@[simp]
/--
theorem `arrowCongr_refl` / 定理 `arrowCongr_refl`

English:
theorem arrowCongr_refl
  statement: arrowCongr AlgEquiv.refl AlgEquiv.refl = Equiv.refl (A₁ ->ₐ[R] A₂)
  proof: rfl

@[simp]

中文:
定理 arrowCongr_refl
  结论: arrowCongr 代数等价.refl 代数等价.refl = 等价.refl (A₁ ->ₐ[R] A₂)
  证明: rfl

@[simp]
-/
theorem arrowCongr_refl : arrowCongr AlgEquiv.refl AlgEquiv.refl = Equiv.refl (A₁ ->ₐ[R] A₂) :=
  rfl

@[simp]
/--
theorem `arrowCongr_trans` / 定理 `arrowCongr_trans`

English:
theorem arrowCongr_trans
  statement: (e₁ : A₁ ≃ₐ[R] A₂) (e₁' : A₁' ≃ₐ[R] A₂')
  proof: rfl

@[simp]

中文:
定理 arrowCongr_trans
  结论: (e₁ : A₁ ≃ₐ[R] A₂) (e₁' : A₁' ≃ₐ[R] A₂')
  证明: rfl

@[simp]
-/
theorem arrowCongr_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₁' : A₁' ≃ₐ[R] A₂')
    (e₂ : A₂ ≃ₐ[R] A₃) (e₂' : A₂' ≃ₐ[R] A₃') :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') :=
  rfl

@[simp]
/--
theorem `arrowCongr_symm` / 定理 `arrowCongr_symm`

English:
theorem arrowCongr_symm
  given: (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂')
  proof: rfl

中文:
定理 arrowCongr_symm
  条件: (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂')
  证明: rfl
-/
theorem arrowCongr_symm (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') :
    (arrowCongr e₁ e₂).symm = arrowCongr e₁.symm e₂.symm :=
  rfl

/-- If `A₁` is equivalent to `A₂` and `A₁'` is equivalent to `A₂'`, then the type of maps
`A₁ ≃ₐ[R] A₁'` is equivalent to the type of maps `A₂ ≃ₐ[R] A₂'`.

This is the `AlgEquiv` version of `AlgEquiv.arrowCongr`. -/
@[simps apply]
/--
Definition of `equivCongr` / `equivCongr` 的定义

English:
definition equivCongr
  signature: (e : A₁ ≃ₐ[R] A₂) (e' : A₁' ≃ₐ[R] A₂')
  body: e.symm.trans (ψ.trans e')
  invFun ψ := e.trans (ψ.trans e'.symm)
  left_inv ψ := by
    ext
    simp_rw [trans_apply, symm_apply_apply]
  right_inv ψ := by
    ext
    simp_rw [trans_apply, apply_symm_apply]

@[simp]

中文:
定义 equivCongr
  签名: (e : A₁ ≃ₐ[R] A₂) (e' : A₁' ≃ₐ[R] A₂')
  定义体: e.symm.trans (ψ.trans e')
  invFun ψ := e.trans (ψ.trans e'.symm)
  left_inv ψ := by
    ext
    simp_rw [trans_apply, symm_apply_apply]
  right_inv ψ := by
    ext
    simp_rw [trans_apply, apply_symm_apply]

@[simp]

Depends on / 依赖: e.symm.trans
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
/--
theorem `equivCongr_refl` / 定理 `equivCongr_refl`

English:
theorem equivCongr_refl
  statement: equivCongr AlgEquiv.refl AlgEquiv.refl = Equiv.refl (A₁ ≃ₐ[R] A₁')
  proof: rfl

@[simp]

中文:
定理 equivCongr_refl
  结论: equivCongr 代数等价.refl 代数等价.refl = 等价.refl (A₁ ≃ₐ[R] A₁')
  证明: rfl

@[simp]
-/
theorem equivCongr_refl : equivCongr AlgEquiv.refl AlgEquiv.refl = Equiv.refl (A₁ ≃ₐ[R] A₁') :=
  rfl

@[simp]
/--
theorem `equivCongr_symm` / 定理 `equivCongr_symm`

English:
theorem equivCongr_symm
  given: (e : A₁ ≃ₐ[R] A₂) (e' : A₁' ≃ₐ[R] A₂')
  proof: rfl

@[simp]

中文:
定理 equivCongr_symm
  条件: (e : A₁ ≃ₐ[R] A₂) (e' : A₁' ≃ₐ[R] A₂')
  证明: rfl

@[simp]
-/
theorem equivCongr_symm (e : A₁ ≃ₐ[R] A₂) (e' : A₁' ≃ₐ[R] A₂') :
    (equivCongr e e').symm = equivCongr e.symm e'.symm :=
  rfl

@[simp]
/--
theorem `equivCongr_trans` / 定理 `equivCongr_trans`

English:
theorem equivCongr_trans
  statement: (e₁₂ : A₁ ≃ₐ[R] A₂) (e₁₂' : A₁' ≃ₐ[R] A₂')
  proof: rfl

中文:
定理 equivCongr_trans
  结论: (e₁₂ : A₁ ≃ₐ[R] A₂) (e₁₂' : A₁' ≃ₐ[R] A₂')
  证明: rfl
-/
theorem equivCongr_trans (e₁₂ : A₁ ≃ₐ[R] A₂) (e₁₂' : A₁' ≃ₐ[R] A₂')
    (e₂₃ : A₂ ≃ₐ[R] A₃) (e₂₃' : A₂' ≃ₐ[R] A₃') :
    (equivCongr e₁₂ e₁₂').trans (equivCongr e₂₃ e₂₃') =
      equivCongr (e₁₂.trans e₂₃) (e₁₂'.trans e₂₃') :=
  rfl

/-- If an algebra morphism has an inverse, it is an algebra isomorphism. -/
@[simps]
/--
Definition of `ofAlgHom` / `ofAlgHom` 的定义

English:
definition ofAlgHom
  signature: (f : A₁ ->ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ : f.comp g = AlgHom.id R A₂)
  body: { f with
    toFun := f
    invFun := g
    left_inv := AlgHom.ext_iff.1 h₂
    right_inv := AlgHom.ext_iff.1 h₁ }

中文:
定义 ofAlgHom
  签名: (f : A₁ ->ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ : f.comp g = 代数态射.id R A₂)
  定义体: { f with
    toFun := f
    invFun := g
    left_inv := AlgHom.ext_iff.1 h₂
    right_inv := AlgHom.ext_iff.1 h₁ }

Depends on / 依赖: AlgHom, AlgHom.ext_iff, ext_iff, invFun, left_inv, right_inv
-/
def ofAlgHom (f : A₁ ->ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ : f.comp g = AlgHom.id R A₂)
    (h₂ : g.comp f = AlgHom.id R A₁) : A₁ ≃ₐ[R] A₂ :=
  { f with
    toFun := f
    invFun := g
    left_inv := AlgHom.ext_iff.1 h₂
    right_inv := AlgHom.ext_iff.1 h₁ }

/--
theorem `toAlgHom_ofAlgHom` / 定理 `toAlgHom_ofAlgHom`

English:
theorem toAlgHom_ofAlgHom
  given: (f : A₁ ->ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ h₂)
  proof: rfl

@[simp]

中文:
定理 toAlgHom_ofAlgHom
  条件: (f : A₁ ->ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ h₂)
  证明: rfl

@[simp]
-/
theorem toAlgHom_ofAlgHom (f : A₁ ->ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ h₂) :
    ↑(ofAlgHom f g h₁ h₂) = f :=
  rfl

@[simp]
/--
theorem `ofAlgHom_toAlgHom` / 定理 `ofAlgHom_toAlgHom`

English:
theorem ofAlgHom_toAlgHom
  given: (f : A₁ ≃ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ h₂)
  proof: ext fun _ => rfl

@[deprecated (since := "2026-05-05")] alias coe_algHom_ofAlgHom := toAlgHom_ofAlgHom
@[deprecated (since := "2026-05-05")] alias ofAlgHom_coe_algHom := ofAlgHom_toAlgHom

中文:
定理 ofAlgHom_toAlgHom
  条件: (f : A₁ ≃ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ h₂)
  证明: ext fun _ => rfl

@[deprecated (since := "2026-05-05")] alias coe_algHom_ofAlgHom := toAlgHom_ofAlgHom
@[deprecated (since := "2026-05-05")] alias ofAlgHom_coe_algHom := ofAlgHom_toAlgHom
-/
theorem ofAlgHom_toAlgHom (f : A₁ ≃ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ h₂) :
    ofAlgHom (↑f) g h₁ h₂ = f :=
  ext fun _ => rfl

@[deprecated (since := "2026-05-05")] alias coe_algHom_ofAlgHom := toAlgHom_ofAlgHom
@[deprecated (since := "2026-05-05")] alias ofAlgHom_coe_algHom := ofAlgHom_toAlgHom

/--
theorem `ofAlgHom_symm` / 定理 `ofAlgHom_symm`

English:
theorem ofAlgHom_symm
  given: (f : A₁ ->ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ h₂)
  proof: rfl

@[simp]

中文:
定理 ofAlgHom_symm
  条件: (f : A₁ ->ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ h₂)
  证明: rfl

@[simp]
-/
theorem ofAlgHom_symm (f : A₁ ->ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ h₂) :
    (ofAlgHom f g h₁ h₂).symm = ofAlgHom g f h₂ h₁ :=
  rfl

@[simp]
/--
theorem `toLinearEquiv_refl` / 定理 `toLinearEquiv_refl`

English:
theorem toLinearEquiv_refl
  statement: (AlgEquiv.refl : A₁ ≃ₐ[R] A₁).toLinearEquiv = LinearEquiv.refl R A₁
  proof: rfl

@[simp]

中文:
定理 toLinearEquiv_refl
  结论: (代数等价.refl : A₁ ≃ₐ[R] A₁).toLinearEquiv = 线性等价.refl R A₁
  证明: rfl

@[simp]
-/
theorem toLinearEquiv_refl : (AlgEquiv.refl : A₁ ≃ₐ[R] A₁).toLinearEquiv = LinearEquiv.refl R A₁ :=
  rfl

@[simp]
/--
theorem `toLinearEquiv_symm` / 定理 `toLinearEquiv_symm`

English:
theorem toLinearEquiv_symm
  given: (e : A₁ ≃ₐ[R] A₂)
  statement: e.symm.toLinearEquiv = e.toLinearEquiv.symm
  proof: rfl

@[simp]

中文:
定理 toLinearEquiv_symm
  条件: (e : A₁ ≃ₐ[R] A₂)
  结论: e.symm.toLinearEquiv = e.toLinearEquiv.symm
  证明: rfl

@[simp]
-/
theorem toLinearEquiv_symm (e : A₁ ≃ₐ[R] A₂) : e.symm.toLinearEquiv = e.toLinearEquiv.symm :=
  rfl

@[simp]
/--
theorem `coe_toLinearEquiv` / 定理 `coe_toLinearEquiv`

English:
theorem coe_toLinearEquiv
  given: (e : A₁ ≃ₐ[R] A₂)
  statement: ⇑e.toLinearEquiv = e
  proof: rfl

@[simp]

中文:
定理 coe_toLinearEquiv
  条件: (e : A₁ ≃ₐ[R] A₂)
  结论: ⇑e.toLinearEquiv = e
  证明: rfl

@[simp]
-/
theorem coe_toLinearEquiv (e : A₁ ≃ₐ[R] A₂) : ⇑e.toLinearEquiv = e := rfl

@[simp]
/--
theorem `coe_symm_toLinearEquiv` / 定理 `coe_symm_toLinearEquiv`

English:
theorem coe_symm_toLinearEquiv
  given: (e : A₁ ≃ₐ[R] A₂)
  statement: ⇑e.toLinearEquiv.symm = e.symm
  proof: rfl

@[simp]

中文:
定理 coe_symm_toLinearEquiv
  条件: (e : A₁ ≃ₐ[R] A₂)
  结论: ⇑e.toLinearEquiv.symm = e.symm
  证明: rfl

@[simp]
-/
theorem coe_symm_toLinearEquiv (e : A₁ ≃ₐ[R] A₂) : ⇑e.toLinearEquiv.symm = e.symm := rfl

@[simp]
/--
theorem `toLinearEquiv_trans` / 定理 `toLinearEquiv_trans`

English:
theorem toLinearEquiv_trans
  given: (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃)
  proof: rfl

中文:
定理 toLinearEquiv_trans
  条件: (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃)
  证明: rfl
-/
theorem toLinearEquiv_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
    (e₁.trans e₂).toLinearEquiv = e₁.toLinearEquiv.trans e₂.toLinearEquiv :=
  rfl

/--
theorem `toLinearEquiv_injective` / 定理 `toLinearEquiv_injective`

English:
theorem toLinearEquiv_injective
  statement: Function.Injective (toLinearEquiv : _ -> A₁ ≃ₗ[R] A₂)
  proof: fun _ _ h => ext LinearEquiv.congr_fun h

中文:
定理 toLinearEquiv_injective
  结论: 函数.单射 (toLinearEquiv : _ -> A₁ ≃ₗ[R] A₂)
  证明: fun _ _ h => ext LinearEquiv.congr_fun h

Depends on / 依赖: LinearEquiv, LinearEquiv.congr_fun, congr_fun
-/
theorem toLinearEquiv_injective : Function.Injective (toLinearEquiv : _ -> A₁ ≃ₗ[R] A₂) :=
fun _ _ h => ext LinearEquiv.congr_fun h

/--
Definition of `toLinearMap` / `toLinearMap` 的定义

English:
abbreviation toLinearMap
  signature: : A₁ ->ₗ[R] A₂
  body: e.toLinearEquiv

@[simp]

中文:
缩写 toLinearMap
  签名: : A₁ ->ₗ[R] A₂
  定义体: e.toLinearEquiv

@[simp]

Depends on / 依赖: e.toLinearEquiv, toLinearEquiv
-/
abbrev toLinearMap : A₁ ->ₗ[R] A₂ :=
  e.toLinearEquiv

@[simp]
/--
lemma `toAlgHom_toLinearMap` / 引理 `toAlgHom_toLinearMap`

English:
lemma toAlgHom_toLinearMap
  statement: e.toAlgHom.toLinearMap = e.toLinearEquiv.toLinearMap
  proof: rfl

中文:
引理 toAlgHom_toLinearMap
  结论: e.toAlgHom.toLinearMap = e.toLinearEquiv.toLinearMap
  证明: rfl
-/
lemma toAlgHom_toLinearMap : e.toAlgHom.toLinearMap = e.toLinearEquiv.toLinearMap := rfl

/--
theorem `toLinearMap_ofAlgHom` / 定理 `toLinearMap_ofAlgHom`

English:
theorem toLinearMap_ofAlgHom
  given: (f : A₁ ->ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ h₂)
  proof: LinearMap.ext fun _ => rfl

中文:
定理 toLinearMap_ofAlgHom
  条件: (f : A₁ ->ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ h₂)
  证明: LinearMap.ext fun _ => rfl

Depends on / 依赖: LinearMap, LinearMap.ext
-/
theorem toLinearMap_ofAlgHom (f : A₁ ->ₐ[R] A₂) (g : A₂ ->ₐ[R] A₁) (h₁ h₂) :
    (ofAlgHom f g h₁ h₂).toLinearMap = f.toLinearMap :=
  LinearMap.ext fun _ => rfl

/--
theorem `toLinearEquiv_toLinearMap` / 定理 `toLinearEquiv_toLinearMap`

English:
theorem toLinearEquiv_toLinearMap
  statement: e.toLinearEquiv.toLinearMap = e.toLinearMap
  proof: rfl

@[simp]

中文:
定理 toLinearEquiv_toLinearMap
  结论: e.toLinearEquiv.toLinearMap = e.toLinearMap
  证明: rfl

@[simp]
-/
theorem toLinearEquiv_toLinearMap : e.toLinearEquiv.toLinearMap = e.toLinearMap :=
  rfl

@[simp]
/--
theorem `toLinearMap_apply` / 定理 `toLinearMap_apply`

English:
theorem toLinearMap_apply
  given: (x : A₁)
  statement: e.toLinearMap x = e x
  proof: rfl

中文:
定理 toLinearMap_apply
  条件: (x : A₁)
  结论: e.toLinearMap x = e x
  证明: rfl
-/
theorem toLinearMap_apply (x : A₁) : e.toLinearMap x = e x :=
  rfl

/--
theorem `toLinearMap_injective` / 定理 `toLinearMap_injective`

English:
theorem toLinearMap_injective
  statement: Function.Injective (toLinearMap : _ -> A₁ ->ₗ[R] A₂)
  proof: fun _ _ h =>
ext LinearMap.congr_fun h

@[simp]

中文:
定理 toLinearMap_injective
  结论: 函数.单射 (toLinearMap : _ -> A₁ ->ₗ[R] A₂)
  证明: fun _ _ h =>
ext LinearMap.congr_fun h

@[simp]
-/
theorem toLinearMap_injective : Function.Injective (toLinearMap : _ -> A₁ ->ₗ[R] A₂) := fun _ _ h =>
ext LinearMap.congr_fun h

@[simp]
/--
theorem `trans_toLinearMap` / 定理 `trans_toLinearMap`

English:
theorem trans_toLinearMap
  given: (f : A₁ ≃ₐ[R] A₂) (g : A₂ ≃ₐ[R] A₃)
  proof: rfl

中文:
定理 trans_toLinearMap
  条件: (f : A₁ ≃ₐ[R] A₂) (g : A₂ ≃ₐ[R] A₃)
  证明: rfl
-/
theorem trans_toLinearMap (f : A₁ ≃ₐ[R] A₂) (g : A₂ ≃ₐ[R] A₃) :
    (f.trans g).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl

/--
theorem `linearEquivConj_mulLeft` / 定理 `linearEquivConj_mulLeft`

English:
theorem linearEquivConj_mulLeft
  given: (f : A₁ ≃ₐ[R] A₂) (x : A₁)
  proof: by
  ext; simp

中文:
定理 linearEquivConj_mulLeft
  条件: (f : A₁ ≃ₐ[R] A₂) (x : A₁)
  证明: by
  ext; simp
-/
@[simp] theorem linearEquivConj_mulLeft (f : A₁ ≃ₐ[R] A₂) (x : A₁) :
    f.toLinearEquiv.conj (.mulLeft R x) = .mulLeft R (f x) := by
  ext; simp

/--
theorem `linearEquivConj_mulRight` / 定理 `linearEquivConj_mulRight`

English:
theorem linearEquivConj_mulRight
  given: (f : A₁ ≃ₐ[R] A₂) (x : A₁)
  proof: by
  ext; simp

中文:
定理 linearEquivConj_mulRight
  条件: (f : A₁ ≃ₐ[R] A₂) (x : A₁)
  证明: by
  ext; simp
-/
@[simp] theorem linearEquivConj_mulRight (f : A₁ ≃ₐ[R] A₂) (x : A₁) :
    f.toLinearEquiv.conj (.mulRight R x) = .mulRight R (f x) := by
  ext; simp

/--
theorem `linearEquivConj_mulLeftRight` / 定理 `linearEquivConj_mulLeftRight`

English:
theorem linearEquivConj_mulLeftRight
  given: (f : A₁ ≃ₐ[R] A₂) (x : A₁ × A₁)
  proof: by
  cases x; ext; simp

中文:
定理 linearEquivConj_mulLeftRight
  条件: (f : A₁ ≃ₐ[R] A₂) (x : A₁ × A₁)
  证明: by
  cases x; ext; simp
-/
@[simp] theorem linearEquivConj_mulLeftRight (f : A₁ ≃ₐ[R] A₂) (x : A₁ × A₁) :
    f.toLinearEquiv.conj (.mulLeftRight R x) = .mulLeftRight R (Prod.map f f x) := by
  cases x; ext; simp

/--
Definition of `ofBijective` / `ofBijective` 的定义

English:
definition ofBijective
  signature: (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f)
  body: { RingEquiv.ofBijective (f : A₁ ->+* A₂) hf, f with }

@[simp]

中文:
定义 ofBijective
  签名: (f : A₁ ->ₐ[R] A₂) (hf : 函数.双射 f)
  定义体: { RingEquiv.ofBijective (f : A₁ ->+* A₂) hf, f with }

@[simp]

Depends on / 依赖: RingEquiv, RingEquiv.ofBijective, ofBijective
-/
noncomputable def ofBijective (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f) : A₁ ≃ₐ[R] A₂ :=
  { RingEquiv.ofBijective (f : A₁ ->+* A₂) hf, f with }

@[simp]
/--
lemma `coe_ofBijective` / 引理 `coe_ofBijective`

English:
lemma coe_ofBijective
  given: (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f)
  proof: rfl

中文:
引理 coe_ofBijective
  条件: (f : A₁ ->ₐ[R] A₂) (hf : 函数.双射 f)
  证明: rfl
-/
lemma coe_ofBijective (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f) :
    (ofBijective f hf : A₁ -> A₂) = f := rfl

/--
lemma `ofBijective_apply` / 引理 `ofBijective_apply`

English:
lemma ofBijective_apply
  given: (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f) (a : A₁)
  proof: rfl

@[simp]

中文:
引理 ofBijective_apply
  条件: (f : A₁ ->ₐ[R] A₂) (hf : 函数.双射 f) (a : A₁)
  证明: rfl

@[simp]
-/
lemma ofBijective_apply (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f) (a : A₁) :
    (ofBijective f hf) a = f a := rfl

@[simp]
/--
lemma `toLinearMap_ofBijective` / 引理 `toLinearMap_ofBijective`

English:
lemma toLinearMap_ofBijective
  given: (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f)
  proof: rfl

@[simp]

中文:
引理 toLinearMap_ofBijective
  条件: (f : A₁ ->ₐ[R] A₂) (hf : 函数.双射 f)
  证明: rfl

@[simp]
-/
lemma toLinearMap_ofBijective (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f) :
    (ofBijective f hf).toLinearMap = f := rfl

@[simp]
/--
lemma `toAlgHom_ofBijective` / 引理 `toAlgHom_ofBijective`

English:
lemma toAlgHom_ofBijective
  given: (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f)
  proof: rfl

中文:
引理 toAlgHom_ofBijective
  条件: (f : A₁ ->ₐ[R] A₂) (hf : 函数.双射 f)
  证明: rfl
-/
lemma toAlgHom_ofBijective (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f) :
    (ofBijective f hf).toAlgHom = f := rfl

/--
lemma `ofBijective_apply_symm_apply` / 引理 `ofBijective_apply_symm_apply`

English:
lemma ofBijective_apply_symm_apply
  given: (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f) (x : A₂)
  proof: (ofBijective f hf).apply_symm_apply x

@[simp]

中文:
引理 ofBijective_apply_symm_apply
  条件: (f : A₁ ->ₐ[R] A₂) (hf : 函数.双射 f) (x : A₂)
  证明: (ofBijective f hf).apply_symm_apply x

@[simp]

Depends on / 依赖: apply_symm_apply, ofBijective
-/
lemma ofBijective_apply_symm_apply (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f) (x : A₂) :
    f ((ofBijective f hf).symm x) = x :=
  (ofBijective f hf).apply_symm_apply x

@[simp]
/--
lemma `ofBijective_symm_apply_apply` / 引理 `ofBijective_symm_apply_apply`

English:
lemma ofBijective_symm_apply_apply
  given: (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f) (x : A₁)
  proof: (ofBijective f hf).symm_apply_apply x

中文:
引理 ofBijective_symm_apply_apply
  条件: (f : A₁ ->ₐ[R] A₂) (hf : 函数.双射 f) (x : A₁)
  证明: (ofBijective f hf).symm_apply_apply x

Depends on / 依赖: ofBijective, symm_apply_apply
-/
lemma ofBijective_symm_apply_apply (f : A₁ ->ₐ[R] A₂) (hf : Function.Bijective f) (x : A₁) :
    (ofBijective f hf).symm (f x) = x :=
  (ofBijective f hf).symm_apply_apply x

section OfLinearEquiv

variable (l : A₁ ≃ₗ[R] A₂) (map_one : l 1 = 1) (map_mul : forall x y : A₁, l (x * y) = l x * l y)

/--
Upgrade a linear equivalence to an algebra equivalence,
given that it distributes over multiplication and the identity
-/
@[simps apply]
/--
Definition of `ofLinearEquiv` / `ofLinearEquiv` 的定义

English:
definition ofLinearEquiv
  signature: : A₁ ≃ₐ[R] A₂
  body: { l with
    toFun := l
    invFun := l.symm
    map_mul' := map_mul
    commutes' := (AlgHom.ofLinearMap l map_one map_mul : A₁ ->ₐ[R] A₂).commutes }

中文:
定义 ofLinearEquiv
  签名: : A₁ ≃ₐ[R] A₂
  定义体: { l with
    toFun := l
    invFun := l.symm
    map_mul' := map_mul
    commutes' := (AlgHom.ofLinearMap l map_one map_mul : A₁ ->ₐ[R] A₂).commutes }

Depends on / 依赖: AlgHom, AlgHom.ofLinearMap, commutes, invFun, l.symm, map_mul, map_one, ofLinearMap
-/
def ofLinearEquiv : A₁ ≃ₐ[R] A₂ :=
  { l with
    toFun := l
    invFun := l.symm
    map_mul' := map_mul
    commutes' := (AlgHom.ofLinearMap l map_one map_mul : A₁ ->ₐ[R] A₂).commutes }

/--
Definition of `ofLinearEquiv_symm.aux` / `ofLinearEquiv_symm.aux` 的定义

English:
definition ofLinearEquiv_symm.aux
  body: (ofLinearEquiv l map_one map_mul).symm

@[simp]

中文:
定义 ofLinearEquiv_symm.aux
  定义体: (ofLinearEquiv l map_one map_mul).symm

@[simp]
-/
protected def ofLinearEquiv_symm.aux := (ofLinearEquiv l map_one map_mul).symm

@[simp]
/--
theorem `ofLinearEquiv_symm` / 定理 `ofLinearEquiv_symm`

English:
theorem ofLinearEquiv_symm
  proof: rfl

@[simp]

中文:
定理 ofLinearEquiv_symm
  证明: rfl

@[simp]
-/
theorem ofLinearEquiv_symm :
    (ofLinearEquiv l map_one map_mul).symm =
      ofLinearEquiv l.symm
        (_root_.map_one <| ofLinearEquiv_symm.aux l map_one map_mul)
        (_root_.map_mul <| ofLinearEquiv_symm.aux l map_one map_mul) :=
  rfl

@[simp]
/--
theorem `ofLinearEquiv_toLinearEquiv` / 定理 `ofLinearEquiv_toLinearEquiv`

English:
theorem ofLinearEquiv_toLinearEquiv
  given: (map_mul) (map_one)
  proof: rfl

@[simp]

中文:
定理 ofLinearEquiv_toLinearEquiv
  条件: (map_mul) (map_one)
  证明: rfl

@[simp]
-/
theorem ofLinearEquiv_toLinearEquiv (map_mul) (map_one) :
    ofLinearEquiv e.toLinearEquiv map_mul map_one = e :=
  rfl

@[simp]
/--
theorem `toLinearEquiv_ofLinearEquiv` / 定理 `toLinearEquiv_ofLinearEquiv`

English:
theorem toLinearEquiv_ofLinearEquiv
  statement: toLinearEquiv (ofLinearEquiv l map_one map_mul) = l
  proof: rfl

中文:
定理 toLinearEquiv_ofLinearEquiv
  结论: toLinearEquiv (ofLinearEquiv l map_one map_mul) = l
  证明: rfl
-/
theorem toLinearEquiv_ofLinearEquiv : toLinearEquiv (ofLinearEquiv l map_one map_mul) = l :=
  rfl

end OfLinearEquiv

section OfRingEquiv

/-- Promotes a linear `RingEquiv` to an `AlgEquiv`. -/
@[simps apply symm_apply toEquiv]
/--
Definition of `ofRingEquiv` / `ofRingEquiv` 的定义

English:
definition ofRingEquiv
  signature: {f : A₁ ≃+* A₂} (hf : forall x, f (algebraMap R A₁ x) = algebraMap R A₂ x)
  body: { f with
    toFun := f
    invFun := f.symm
    commutes' := hf }

中文:
定义 ofRingEquiv
  签名: {f : A₁ ≃+* A₂} (hf : 对任意 x, f (algebraMap R A₁ x) = algebraMap R A₂ x)
  定义体: { f with
    toFun := f
    invFun := f.symm
    commutes' := hf }

Depends on / 依赖: commutes, f.symm, invFun
-/
def ofRingEquiv {f : A₁ ≃+* A₂} (hf : forall x, f (algebraMap R A₁ x) = algebraMap R A₂ x) :
    A₁ ≃ₐ[R] A₂ :=
  { f with
    toFun := f
    invFun := f.symm
    commutes' := hf }

end OfRingEquiv

@[simps -isSimp one mul, stacks 09HR]
/--
Instance `aut` / 实例 `aut`

English:
instance aut
  signature: : Group (A₁ ≃ₐ[R] A₁) where
  body: ψ.trans ϕ
  mul_assoc _ _ _ := rfl
  one := refl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv := symm
inv_mul_cancel ϕ := ext symm_apply_apply ϕ

@[simp]

中文:
实例 aut
  签名: : 群 (A₁ ≃ₐ[R] A₁) where
  定义体: ψ.trans ϕ
  mul_assoc _ _ _ := rfl
  one := refl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv := symm
inv_mul_cancel ϕ := ext symm_apply_apply ϕ

@[simp]
-/
instance aut : Group (A₁ ≃ₐ[R] A₁) where
  mul ϕ ψ := ψ.trans ϕ
  mul_assoc _ _ _ := rfl
  one := refl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv := symm
inv_mul_cancel ϕ := ext symm_apply_apply ϕ

@[simp]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (x : A₁)
  statement: (1 : A₁ ≃ₐ[R] A₁) x = x
  proof: rfl

@[simp]

中文:
定理 one_apply
  条件: (x : A₁)
  结论: (1 : A₁ ≃ₐ[R] A₁) x = x
  证明: rfl

@[simp]
-/
theorem one_apply (x : A₁) : (1 : A₁ ≃ₐ[R] A₁) x = x :=
  rfl

@[simp]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (e₁ e₂ : A₁ ≃ₐ[R] A₁) (x : A₁)
  statement: (e₁ * e₂) x = e₁ (e₂ x)
  proof: rfl

中文:
定理 mul_apply
  条件: (e₁ e₂ : A₁ ≃ₐ[R] A₁) (x : A₁)
  结论: (e₁ * e₂) x = e₁ (e₂ x)
  证明: rfl
-/
theorem mul_apply (e₁ e₂ : A₁ ≃ₐ[R] A₁) (x : A₁) : (e₁ * e₂) x = e₁ (e₂ x) :=
  rfl

/--
lemma `aut_inv` / 引理 `aut_inv`

English:
lemma aut_inv
  given: (ϕ : A₁ ≃ₐ[R] A₁)
  statement: ϕ⁻¹ = ϕ.symm
  proof: rfl

中文:
引理 aut_inv
  条件: (ϕ : A₁ ≃ₐ[R] A₁)
  结论: ϕ⁻¹ = ϕ.symm
  证明: rfl
-/
lemma aut_inv (ϕ : A₁ ≃ₐ[R] A₁) : ϕ⁻¹ = ϕ.symm := rfl

/--
lemma `coe_inv` / 引理 `coe_inv`

English:
lemma coe_inv
  given: (ϕ : A₁ ≃ₐ[R] A₁)
  statement: ⇑ϕ⁻¹ = ⇑ϕ.symm
  proof: rfl

中文:
引理 coe_inv
  条件: (ϕ : A₁ ≃ₐ[R] A₁)
  结论: ⇑ϕ⁻¹ = ⇑ϕ.symm
  证明: rfl
-/
@[simp] lemma coe_inv (ϕ : A₁ ≃ₐ[R] A₁) : ⇑ϕ⁻¹ = ⇑ϕ.symm := rfl

/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (e : A₁ ≃ₐ[R] A₁) (n : Nat)
  statement: ⇑(e ^ n) = e^[n]
  proof: n.rec (by ext; simp) fun _ ih => by ext; simp [pow_succ, ih]

中文:
定理 coe_pow
  条件: (e : A₁ ≃ₐ[R] A₁) (n : 自然数)
  结论: ⇑(e ^ n) = e^[n]
  证明: n.rec (by ext; simp) fun _ ih => by ext; simp [pow_succ, ih]
-/
@[simp] theorem coe_pow (e : A₁ ≃ₐ[R] A₁) (n : Nat) : ⇑(e ^ n) = e^[n] :=
  n.rec (by ext; simp) fun _ ih => by ext; simp [pow_succ, ih]

/-- An algebra isomorphism induces a group isomorphism between automorphism groups.

This is a more bundled version of `AlgEquiv.equivCongr`. -/
@[simps apply]
/--
Definition of `autCongr` / `autCongr` 的定义

English:
definition autCongr
  signature: (ϕ : A₁ ≃ₐ[R] A₂)
  body: equivCongr ϕ ϕ
  toFun ψ := ϕ.symm.trans (ψ.trans ϕ)
  invFun ψ := ϕ.trans (ψ.trans ϕ.symm)
  map_mul' ψ χ := by
    ext
    simp only [mul_apply, trans_apply, symm_apply_apply]

@[simp]

中文:
定义 autCongr
  签名: (ϕ : A₁ ≃ₐ[R] A₂)
  定义体: equivCongr ϕ ϕ
  toFun ψ := ϕ.symm.trans (ψ.trans ϕ)
  invFun ψ := ϕ.trans (ψ.trans ϕ.symm)
  map_mul' ψ χ := by
    ext
    simp only [mul_apply, trans_apply, symm_apply_apply]

@[simp]

Depends on / 依赖: equivCongr
-/
def autCongr (ϕ : A₁ ≃ₐ[R] A₂) : (A₁ ≃ₐ[R] A₁) ≃* A₂ ≃ₐ[R] A₂ where
  __ := equivCongr ϕ ϕ
  toFun ψ := ϕ.symm.trans (ψ.trans ϕ)
  invFun ψ := ϕ.trans (ψ.trans ϕ.symm)
  map_mul' ψ χ := by
    ext
    simp only [mul_apply, trans_apply, symm_apply_apply]

@[simp]
/--
theorem `autCongr_refl` / 定理 `autCongr_refl`

English:
theorem autCongr_refl
  statement: autCongr AlgEquiv.refl = MulEquiv.refl (A₁ ≃ₐ[R] A₁)
  proof: rfl

@[simp]

中文:
定理 autCongr_refl
  结论: autCongr 代数等价.refl = 乘法等价.refl (A₁ ≃ₐ[R] A₁)
  证明: rfl

@[simp]
-/
theorem autCongr_refl : autCongr AlgEquiv.refl = MulEquiv.refl (A₁ ≃ₐ[R] A₁) := rfl

@[simp]
/--
theorem `autCongr_symm` / 定理 `autCongr_symm`

English:
theorem autCongr_symm
  given: (ϕ : A₁ ≃ₐ[R] A₂)
  statement: (autCongr ϕ).symm = autCongr ϕ.symm
  proof: rfl

@[simp]

中文:
定理 autCongr_symm
  条件: (ϕ : A₁ ≃ₐ[R] A₂)
  结论: (autCongr ϕ).symm = autCongr ϕ.symm
  证明: rfl

@[simp]
-/
theorem autCongr_symm (ϕ : A₁ ≃ₐ[R] A₂) : (autCongr ϕ).symm = autCongr ϕ.symm :=
  rfl

@[simp]
/--
theorem `autCongr_trans` / 定理 `autCongr_trans`

English:
theorem autCongr_trans
  given: (ϕ : A₁ ≃ₐ[R] A₂) (ψ : A₂ ≃ₐ[R] A₃)
  proof: rfl

中文:
定理 autCongr_trans
  条件: (ϕ : A₁ ≃ₐ[R] A₂) (ψ : A₂ ≃ₐ[R] A₃)
  证明: rfl
-/
theorem autCongr_trans (ϕ : A₁ ≃ₐ[R] A₂) (ψ : A₂ ≃ₐ[R] A₃) :
    (autCongr ϕ).trans (autCongr ψ) = autCongr (ϕ.trans ψ) :=
  rfl

/--
Instance `applyMulSemiringAction` / 实例 `applyMulSemiringAction`

English:
instance applyMulSemiringAction
  signature: : MulSemiringAction (A₁ ≃ₐ[R] A₁) A₁ where
  body: (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  smul_one := map_one
  smul_mul := map_mul
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]

中文:
实例 applyMulSemiringAction
  签名: : MulSemiring作用 (A₁ ≃ₐ[R] A₁) A₁ where
  定义体: (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  smul_one := map_one
  smul_mul := map_mul
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
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
/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: (f : A₁ ≃ₐ[R] A₁) (a : A₁)
  statement: f • a = f a
  proof: rfl

中文:
定理 smul_def
  条件: (f : A₁ ≃ₐ[R] A₁) (a : A₁)
  结论: f • a = f a
  证明: rfl
-/
protected theorem smul_def (f : A₁ ≃ₐ[R] A₁) (a : A₁) : f • a = f a :=
  rfl

/--
Instance `apply_faithfulSMul` / 实例 `apply_faithfulSMul`

English:
instance apply_faithfulSMul
  signature: : FaithfulSMul (A₁ ≃ₐ[R] A₁) A₁
  body: ⟨AlgEquiv.ext⟩

中文:
实例 apply_faithfulSMul
  签名: : 忠实标量乘法 (A₁ ≃ₐ[R] A₁) A₁
  定义体: ⟨AlgEquiv.ext⟩

Depends on / 依赖: AlgEquiv, AlgEquiv.ext
-/
instance apply_faithfulSMul : FaithfulSMul (A₁ ≃ₐ[R] A₁) A₁ :=
  ⟨AlgEquiv.ext⟩

/--
Instance `apply_smulCommClass` / 实例 `apply_smulCommClass`

English:
instance apply_smulCommClass
  signature: {S} [SMul S R] [SMul S A₁] [IsScalarTower S R A₁]
  body: (e.toLinearEquiv.map_smul_of_tower r a).symm

中文:
实例 apply_smulCommClass
  签名: {S} [标量乘法 S R] [标量乘法 S A₁] [标量塔 S R A₁]
  定义体: (e.toLinearEquiv.map_smul_of_tower r a).symm

Depends on / 依赖: e.toLinearEquiv.map_smul_of_tower, map_smul_of_tower, toLinearEquiv
-/
instance apply_smulCommClass {S} [SMul S R] [SMul S A₁] [IsScalarTower S R A₁] :
    SMulCommClass S (A₁ ≃ₐ[R] A₁) A₁ where
  smul_comm r e a := (e.toLinearEquiv.map_smul_of_tower r a).symm

/--
Instance `apply_smulCommClass'` / 实例 `apply_smulCommClass'`

English:
instance apply_smulCommClass'
  signature: {S} [SMul S R] [SMul S A₁] [IsScalarTower S R A₁]
  body: SMulCommClass.symm _ _ _

中文:
实例 apply_smulCommClass'
  签名: {S} [标量乘法 S R] [标量乘法 S A₁] [标量塔 S R A₁]
  定义体: SMulCommClass.symm _ _ _

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance apply_smulCommClass' {S} [SMul S R] [SMul S A₁] [IsScalarTower S R A₁] :
    SMulCommClass (A₁ ≃ₐ[R] A₁) S A₁ :=
  SMulCommClass.symm _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulDistribMulAction (A₁ ≃ₐ[R] A₁) A₁ˣ
  body: fun f => Units.map f
  one_smul := fun x => by ext; rfl
  mul_smul := fun x y z => by ext; rfl
  smul_mul := fun x y z => by ext; exact map_mul x _ _
  smul_one := fun x => by ext; exact map_one x

@[simp]

中文:
实例 :
  签名: MulDistribMul作用 (A₁ ≃ₐ[R] A₁) A₁ˣ
  定义体: fun f => Units.map f
  one_smul := fun x => by ext; rfl
  mul_smul := fun x y z => by ext; rfl
  smul_mul := fun x y z => by ext; exact map_mul x _ _
  smul_one := fun x => by ext; exact map_one x

@[simp]

Depends on / 依赖: Units.map
-/
instance : MulDistribMulAction (A₁ ≃ₐ[R] A₁) A₁ˣ where
  smul := fun f => Units.map f
  one_smul := fun x => by ext; rfl
  mul_smul := fun x y z => by ext; rfl
  smul_mul := fun x y z => by ext; exact map_mul x _ _
  smul_one := fun x => by ext; exact map_one x

@[simp]
/--
theorem `smul_units_def` / 定理 `smul_units_def`

English:
theorem smul_units_def
  given: (f : A₁ ≃ₐ[R] A₁) (x : A₁ˣ)
  proof: rfl

@[simp]

中文:
定理 smul_units_def
  条件: (f : A₁ ≃ₐ[R] A₁) (x : A₁ˣ)
  证明: rfl

@[simp]
-/
theorem smul_units_def (f : A₁ ≃ₐ[R] A₁) (x : A₁ˣ) :
    f • x = Units.map f x := rfl

@[simp]
/--
lemma `_root_.MulSemiringAction.toRingEquiv_algEquiv` / 引理 `_root_.MulSemiringAction.toRingEquiv_algEquiv`

English:
lemma _root_.MulSemiringAction.toRingEquiv_algEquiv
  given: (σ : A₁ ≃ₐ[R] A₁)
  proof: rfl

@[simp]

中文:
引理 _root_.MulSemiring作用.toRingEquiv_algEquiv
  条件: (σ : A₁ ≃ₐ[R] A₁)
  证明: rfl

@[simp]
-/
lemma _root_.MulSemiringAction.toRingEquiv_algEquiv (σ : A₁ ≃ₐ[R] A₁) :
    MulSemiringAction.toRingEquiv _ A₁ σ = σ := rfl

@[simp]
/--
theorem `algebraMap_eq_apply` / 定理 `algebraMap_eq_apply`

English:
theorem algebraMap_eq_apply
  given: (e : A₁ ≃ₐ[R] A₂) {y : R} {x : A₁}
  proof: ⟨fun h => by simpa using e.symm.toAlgHom.algebraMap_eq_apply h, fun h =>
    e.toAlgHom.algebraMap_eq_apply h⟩

中文:
定理 algebraMap_eq_apply
  条件: (e : A₁ ≃ₐ[R] A₂) {y : R} {x : A₁}
  证明: ⟨fun h => by simpa using e.symm.toAlgHom.algebraMap_eq_apply h, fun h =>
    e.toAlgHom.algebraMap_eq_apply h⟩

Depends on / 依赖: algebraMap_eq_apply, e.symm.toAlgHom.algebraMap_eq_apply, e.toAlgHom.algebraMap_eq_apply, toAlgHom
-/
theorem algebraMap_eq_apply (e : A₁ ≃ₐ[R] A₂) {y : R} {x : A₁} :
    algebraMap R A₂ y = e x ↔ algebraMap R A₁ y = x :=
  ⟨fun h => by simpa using e.symm.toAlgHom.algebraMap_eq_apply h, fun h =>
    e.toAlgHom.algebraMap_eq_apply h⟩

/--
Definition of `toAlgHomHom` / `toAlgHomHom` 的定义

English:
definition toAlgHomHom
  signature: (R A) [CommSemiring R] [Semiring A] [Algebra R A]
  body: AlgEquiv.toAlgHom
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 toAlgHomHom
  签名: (R A) [交换半环 R] [半环 A] [代数 R A]
  定义体: AlgEquiv.toAlgHom
  map_one' := rfl
  map_mul' _ _ := rfl
-/
@[simps] def toAlgHomHom (R A) [CommSemiring R] [Semiring A] [Algebra R A] :
    (A ≃ₐ[R] A) ->* A ->ₐ[R] A where
  toFun := AlgEquiv.toAlgHom
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `AlgEquiv.toLinearMap` as a `MonoidHom`. -/
@[simps!]
/--
Definition of `toLinearMapHom` / `toLinearMapHom` 的定义

English:
definition toLinearMapHom
  signature: (R A) [CommSemiring R] [Semiring A] [Algebra R A]
  body: AlgHom.toEnd.comp (toAlgHomHom R A)

中文:
定义 toLinearMapHom
  签名: (R A) [交换半环 R] [半环 A] [代数 R A]
  定义体: AlgHom.toEnd.comp (toAlgHomHom R A)

Depends on / 依赖: AlgHom, AlgHom.toEnd.comp, toAlgHomHom
-/
def toLinearMapHom (R A) [CommSemiring R] [Semiring A] [Algebra R A] :
    (A ≃ₐ[R] A) ->* Module.End R A :=
  AlgHom.toEnd.comp (toAlgHomHom R A)

/--
lemma `pow_toLinearMap` / 引理 `pow_toLinearMap`

English:
lemma pow_toLinearMap
  given: (σ : A₁ ≃ₐ[R] A₁) (n : Nat)
  proof: (AlgEquiv.toLinearMapHom R A₁).map_pow σ n

@[simp]

中文:
引理 pow_toLinearMap
  条件: (σ : A₁ ≃ₐ[R] A₁) (n : 自然数)
  证明: (AlgEquiv.toLinearMapHom R A₁).map_pow σ n

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.toLinearMapHom, map_pow, toLinearMapHom
-/
lemma pow_toLinearMap (σ : A₁ ≃ₐ[R] A₁) (n : Nat) :
    (σ ^ n).toLinearMap = σ.toLinearMap ^ n :=
  (AlgEquiv.toLinearMapHom R A₁).map_pow σ n

@[simp]
/--
lemma `one_toLinearMap` / 引理 `one_toLinearMap`

English:
lemma one_toLinearMap
  proof: rfl

中文:
引理 one_toLinearMap
  证明: rfl

Depends on / 依赖: decidable_of_iff, isPrimePow_nat_iff_bounded_log_minFac
-/
lemma one_toLinearMap :
    (1 : A₁ ≃ₐ[R] A₁).toLinearMap = 1 := rfl

/-- The units group of `S →ₐ[R] S` is `S ≃ₐ[R] S`.
See `LinearMap.GeneralLinearGroup.generalLinearEquiv` for the linear map version. -/
@[simps]
/--
Definition of `algHomUnitsEquiv` / `algHomUnitsEquiv` 的定义

English:
definition algHomUnitsEquiv
  signature: (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S]
  body: fun f =>
    { (f : S ->ₐ[R] S) with
      invFun := ↑(f⁻¹)
      left_inv := (fun x => show (↑(f⁻¹ * f) : S ->ₐ[R] S) x = x by rw [inv_mul_cancel]; rfl)
      right_inv := (fun x => show (↑(f * f⁻¹) : S ->ₐ[R] S) x = x by rw [mul_inv_cancel]; rfl) }
  invFun := fun f => ⟨f, f.symm, f.comp_symm, f.symm_comp⟩
  map_mul' := fun _ _ => rfl

中文:
定义 algHomUnitsEquiv
  签名: (R S : 类型) [交换半环 R] [半环 S] [代数 R S]
  定义体: fun f =>
    { (f : S ->ₐ[R] S) with
      invFun := ↑(f⁻¹)
      left_inv := (fun x => show (↑(f⁻¹ * f) : S ->ₐ[R] S) x = x by rw [inv_mul_cancel]; rfl)
      right_inv := (fun x => show (↑(f * f⁻¹) : S ->ₐ[R] S) x = x by rw [mul_inv_cancel]; rfl) }
  invFun := fun f => ⟨f, f.symm, f.comp_symm, f.symm_comp⟩
  map_mul' := fun _ _ => rfl
-/
def algHomUnitsEquiv (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S] :
    (S ->ₐ[R] S)ˣ ≃* (S ≃ₐ[R] S) where
  toFun := fun f =>
    { (f : S ->ₐ[R] S) with
      invFun := ↑(f⁻¹)
      left_inv := (fun x => show (↑(f⁻¹ * f) : S ->ₐ[R] S) x = x by rw [inv_mul_cancel]; rfl)
      right_inv := (fun x => show (↑(f * f⁻¹) : S ->ₐ[R] S) x = x by rw [mul_inv_cancel]; rfl) }
  invFun := fun f => ⟨f, f.symm, f.comp_symm, f.symm_comp⟩
  map_mul' := fun _ _ => rfl

/--
Instance `_root_.Finite.algEquiv` / 实例 `_root_.Finite.algEquiv`

English:
instance _root_.Finite.algEquiv
  signature: [Finite (A₁ ->ₐ[R] A₂)]
  body: Finite.of_injective _ AlgEquiv.coe_toAlgHom_injective

中文:
实例 _root_.有限.algEquiv
  签名: [有限 (A₁ ->ₐ[R] A₂)]
  定义体: Finite.of_injective _ AlgEquiv.coe_toAlgHom_injective

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_toAlgHom_injective, Finite, Finite.of_injective, coe_toAlgHom_injective, of_injective
-/
instance _root_.Finite.algEquiv [Finite (A₁ ->ₐ[R] A₂)] : Finite (A₁ ≃ₐ[R] A₂) :=
  Finite.of_injective _ AlgEquiv.coe_toAlgHom_injective

-- TODO Morally this is just `isLocalHom_equiv`: can we obviate the need for this instance?
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalHom e.toAlgHom
  body: by
  have : IsLocalHom e.toRingEquiv := inferInstance
  exact ⟨this.map_nonunit⟩

中文:
实例 :
  签名: 是Local态射 e.toAlgHom
  定义体: by
  have : IsLocalHom e.toRingEquiv := inferInstance
  exact ⟨this.map_nonunit⟩

Depends on / 依赖: IsLocalHom, e.toRingEquiv, map_nonunit, this.map_nonunit, toRingEquiv
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
/--
Definition of `toNatAlgEquiv` / `toNatAlgEquiv` 的定义

English:
definition toNatAlgEquiv
  signature: [Semiring R] [Semiring S] (f : R ≃+* S)
  body: f
  __ := f.toRingHom.toNatAlgHom

@[simp]

中文:
定义 to自然数AlgEquiv
  签名: [半环 R] [半环 S] (f : R ≃+* S)
  定义体: f
  __ := f.toRingHom.toNatAlgHom

@[simp]
-/
def toNatAlgEquiv [Semiring R] [Semiring S] (f : R ≃+* S) : R ≃ₐ[Nat] S where
  toEquiv := f
  __ := f.toRingHom.toNatAlgHom

@[simp]
/--
lemma `coe_toNatAlgEquiv` / 引理 `coe_toNatAlgEquiv`

English:
lemma coe_toNatAlgEquiv
  given: [Semiring R] [Semiring S] (f : R ≃+* S)
  proof: rfl

中文:
引理 coe_to自然数AlgEquiv
  条件: [半环 R] [半环 S] (f : R ≃+* S)
  证明: rfl
-/
lemma coe_toNatAlgEquiv [Semiring R] [Semiring S] (f : R ≃+* S) :
    ⇑f.toNatAlgEquiv = ⇑f := rfl

/--
lemma `toAlgHom_toNatAlgEquiv` / 引理 `toAlgHom_toNatAlgEquiv`

English:
lemma toAlgHom_toNatAlgEquiv
  given: [Semiring R] [Semiring S] (f : R ≃+* S)
  proof: rfl

@[simp]

中文:
引理 toAlgHom_to自然数AlgEquiv
  条件: [半环 R] [半环 S] (f : R ≃+* S)
  证明: rfl

@[simp]
-/
lemma toAlgHom_toNatAlgEquiv [Semiring R] [Semiring S] (f : R ≃+* S) :
    f.toNatAlgEquiv.toAlgHom = (f : R ->+* S).toNatAlgHom := rfl

@[simp]
/--
lemma `symm_toNatAlgEquiv` / 引理 `symm_toNatAlgEquiv`

English:
lemma symm_toNatAlgEquiv
  given: [Semiring R] [Semiring S] (f : R ≃+* S)
  proof: rfl

中文:
引理 symm_to自然数AlgEquiv
  条件: [半环 R] [半环 S] (f : R ≃+* S)
  证明: rfl
-/
lemma symm_toNatAlgEquiv [Semiring R] [Semiring S] (f : R ≃+* S) :
    f.toNatAlgEquiv.symm = f.symm.toNatAlgEquiv := rfl

variable (R) (S) in
/-- The equivalence between `RingEquiv` and `ℕ`-algebra isomorphisms. -/
@[simps apply symm_apply]
/--
Definition of `equivNatAlgEquiv` / `equivNatAlgEquiv` 的定义

English:
definition equivNatAlgEquiv
  signature: [Semiring R] [Semiring S]
  body: toNatAlgEquiv
  invFun := AlgEquiv.toRingEquiv

中文:
定义 equiv自然数AlgEquiv
  签名: [半环 R] [半环 S]
  定义体: toNatAlgEquiv
  invFun := AlgEquiv.toRingEquiv

Depends on / 依赖: toNatAlgEquiv
-/
def equivNatAlgEquiv [Semiring R] [Semiring S] : (R ≃+* S) ≃ (R ≃ₐ[Nat] S) where
  toFun := toNatAlgEquiv
  invFun := AlgEquiv.toRingEquiv

/--
lemma `toNatAlgEquiv_injective` / 引理 `toNatAlgEquiv_injective`

English:
lemma toNatAlgEquiv_injective
  given: [Semiring R] [Semiring S]
  proof: (equivNatAlgEquiv R S).injective

中文:
引理 to自然数AlgEquiv_injective
  条件: [半环 R] [半环 S]
  证明: (equivNatAlgEquiv R S).injective

Depends on / 依赖: equivNatAlgEquiv, injective
-/
lemma toNatAlgEquiv_injective [Semiring R] [Semiring S] :
    Function.Injective (RingEquiv.toNatAlgEquiv : (R ≃+* S) -> _) :=
  (equivNatAlgEquiv R S).injective

/-- Reinterpret a `RingEquiv` as a `ℤ`-algebra isomorphism. -/
@[simps! -isSimp apply]
/--
Definition of `toIntAlgEquiv` / `toIntAlgEquiv` 的定义

English:
definition toIntAlgEquiv
  signature: [Ring R] [Ring S] (f : R ≃+* S)
  body: f
  __ := f.toRingHom.toIntAlgHom

@[simp]

中文:
定义 to整数AlgEquiv
  签名: [环 R] [环 S] (f : R ≃+* S)
  定义体: f
  __ := f.toRingHom.toIntAlgHom

@[simp]
-/
def toIntAlgEquiv [Ring R] [Ring S] (f : R ≃+* S) : R ≃ₐ[Int] S where
  toEquiv := f
  __ := f.toRingHom.toIntAlgHom

@[simp]
/--
lemma `coe_toIntAlgEquiv` / 引理 `coe_toIntAlgEquiv`

English:
lemma coe_toIntAlgEquiv
  given: [Ring R] [Ring S] (f : R ≃+* S)
  proof: rfl

中文:
引理 coe_to整数AlgEquiv
  条件: [环 R] [环 S] (f : R ≃+* S)
  证明: rfl
-/
lemma coe_toIntAlgEquiv [Ring R] [Ring S] (f : R ≃+* S) :
    ⇑f.toIntAlgEquiv = ⇑f := rfl

/--
lemma `toAlgHom_toIntAlgEquiv` / 引理 `toAlgHom_toIntAlgEquiv`

English:
lemma toAlgHom_toIntAlgEquiv
  given: [Ring R] [Ring S] (f : R ≃+* S)
  proof: rfl

@[simp]

中文:
引理 toAlgHom_to整数AlgEquiv
  条件: [环 R] [环 S] (f : R ≃+* S)
  证明: rfl

@[simp]
-/
lemma toAlgHom_toIntAlgEquiv [Ring R] [Ring S] (f : R ≃+* S) :
    f.toIntAlgEquiv.toAlgHom = (f : R ->+* S).toIntAlgHom := rfl

@[simp]
/--
lemma `symm_toIntAlgEquiv` / 引理 `symm_toIntAlgEquiv`

English:
lemma symm_toIntAlgEquiv
  given: [Ring R] [Ring S] (f : R ≃+* S)
  proof: rfl

中文:
引理 symm_to整数AlgEquiv
  条件: [环 R] [环 S] (f : R ≃+* S)
  证明: rfl
-/
lemma symm_toIntAlgEquiv [Ring R] [Ring S] (f : R ≃+* S) :
    f.toIntAlgEquiv.symm = f.symm.toIntAlgEquiv := rfl

variable (R) (S) in
/-- The equivalence between `RingEquiv` and `ℤ`-algebra isomorphisms. -/
@[simps apply symm_apply]
/--
Definition of `equivIntAlgEquiv` / `equivIntAlgEquiv` 的定义

English:
definition equivIntAlgEquiv
  signature: [Ring R] [Ring S]
  body: toIntAlgEquiv
  invFun := AlgEquiv.toRingEquiv

中文:
定义 equiv整数AlgEquiv
  签名: [环 R] [环 S]
  定义体: toIntAlgEquiv
  invFun := AlgEquiv.toRingEquiv

Depends on / 依赖: toIntAlgEquiv
-/
def equivIntAlgEquiv [Ring R] [Ring S] : (R ≃+* S) ≃ (R ≃ₐ[Int] S) where
  toFun := toIntAlgEquiv
  invFun := AlgEquiv.toRingEquiv

/--
lemma `toIntAlgEquiv_injective` / 引理 `toIntAlgEquiv_injective`

English:
lemma toIntAlgEquiv_injective
  given: [Ring R] [Ring S]
  proof: (equivIntAlgEquiv R S).injective

中文:
引理 to整数AlgEquiv_injective
  条件: [环 R] [环 S]
  证明: (equivIntAlgEquiv R S).injective

Depends on / 依赖: equivIntAlgEquiv, injective
-/
lemma toIntAlgEquiv_injective [Ring R] [Ring S] :
    Function.Injective (RingEquiv.toIntAlgEquiv : (R ≃+* S) -> _) :=
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
/--
Definition of `toAlgEquiv` / `toAlgEquiv` 的定义

English:
definition toAlgEquiv
  signature: (g : G)
  body: { MulSemiringAction.toRingEquiv _ _ g, MulSemiringAction.toAlgHom R A g with }

中文:
定义 toAlgEquiv
  签名: (g : G)
  定义体: { MulSemiringAction.toRingEquiv _ _ g, MulSemiringAction.toAlgHom R A g with }

Depends on / 依赖: MulSemiringAction, MulSemiringAction.toAlgHom, MulSemiringAction.toRingEquiv, toAlgHom, toRingEquiv
-/
def toAlgEquiv (g : G) : A ≃ₐ[R] A :=
  { MulSemiringAction.toRingEquiv _ _ g, MulSemiringAction.toAlgHom R A g with }

/--
theorem `toAlgEquiv_injective` / 定理 `toAlgEquiv_injective`

English:
theorem toAlgEquiv_injective
  given: [FaithfulSMul G A]
  proof: fun _ _ h =>
  eq_of_smul_eq_smul fun r => AlgEquiv.ext_iff.1 h r

中文:
定理 toAlgEquiv_injective
  条件: [忠实标量乘法 G A]
  证明: fun _ _ h =>
  eq_of_smul_eq_smul fun r => AlgEquiv.ext_iff.1 h r
-/
theorem toAlgEquiv_injective [FaithfulSMul G A] :
    Function.Injective (MulSemiringAction.toAlgEquiv R A : G -> A ≃ₐ[R] A) := fun _ _ h =>
  eq_of_smul_eq_smul fun r => AlgEquiv.ext_iff.1 h r

variable (G)

/-- Each element of the group defines an algebra equivalence.

This is a stronger version of `MulSemiringAction.toRingAut` and
`DistribMulAction.toModuleEnd`. -/
@[simps]
/--
Definition of `toAlgAut` / `toAlgAut` 的定义

English:
definition toAlgAut
  signature: : G ->* A ≃ₐ[R] A where
  body: toAlgEquiv R A
map_one' := AlgEquiv.ext one_smul _
map_mul' g h := AlgEquiv.ext mul_smul g h

中文:
定义 toAlgAut
  签名: : G ->* A ≃ₐ[R] A where
  定义体: toAlgEquiv R A
map_one' := AlgEquiv.ext one_smul _
map_mul' g h := AlgEquiv.ext mul_smul g h

Depends on / 依赖: toAlgEquiv
-/
def toAlgAut : G ->* A ≃ₐ[R] A where
  toFun := toAlgEquiv R A
map_one' := AlgEquiv.ext one_smul _
map_mul' g h := AlgEquiv.ext mul_smul g h

end

end MulSemiringAction

section

variable {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: S] [Subsingleton T] : Unique (S ≃ₐ[R] T) where
  body: AlgEquiv.ofAlgHom default default
    (AlgHom.ext fun _ => Subsingleton.elim _ _)
    (AlgHom.ext fun _ => Subsingleton.elim _ _)
  uniq _ := AlgEquiv.ext fun _ => Subsingleton.elim _ _

@[simp]

中文:
实例 [子单例
  签名: S] [子单例 T] : 唯一 (S ≃ₐ[R] T) where
  定义体: AlgEquiv.ofAlgHom default default
    (AlgHom.ext fun _ => Subsingleton.elim _ _)
    (AlgHom.ext fun _ => Subsingleton.elim _ _)
  uniq _ := AlgEquiv.ext fun _ => Subsingleton.elim _ _

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, ofAlgHom
-/
instance [Subsingleton S] [Subsingleton T] : Unique (S ≃ₐ[R] T) where
  default := AlgEquiv.ofAlgHom default default
    (AlgHom.ext fun _ => Subsingleton.elim _ _)
    (AlgHom.ext fun _ => Subsingleton.elim _ _)
  uniq _ := AlgEquiv.ext fun _ => Subsingleton.elim _ _

@[simp]
/--
lemma `AlgEquiv.default_apply` / 引理 `AlgEquiv.default_apply`

English:
lemma AlgEquiv.default_apply
  given: [Subsingleton S] [Subsingleton T] (x : S)
  proof: rfl

中文:
引理 代数等价.default_apply
  条件: [子单例 S] [子单例 T] (x : S)
  证明: rfl
-/
lemma AlgEquiv.default_apply [Subsingleton S] [Subsingleton T] (x : S) :
    (default : S ≃ₐ[R] T) x = 0 :=
  rfl

end

/-- The algebra equivalence between `ULift A` and `A`. -/
@[simps! apply, simps! -isSimp symm_apply, pp_with_univ]
/--
Definition of `ULift.algEquiv` / `ULift.algEquiv` 的定义

English:
definition ULift.algEquiv
  signature: {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]
  body: ULift.ringEquiv
  commutes' _ := rfl

@[simp]

中文:
定义 类型层提升.algEquiv
  签名: {R : 类型u} {A : 类型v} [交换半环 R] [半环 A] [代数 R A]
  定义体: ULift.ringEquiv
  commutes' _ := rfl

@[simp]

Depends on / 依赖: ULift.ringEquiv, ringEquiv
-/
def ULift.algEquiv {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A] :
    ULift.{w} A ≃ₐ[R] A where
  __ := ULift.ringEquiv
  commutes' _ := rfl

@[simp]
/--
lemma `ULift.down_algEquiv_symm_apply` / 引理 `ULift.down_algEquiv_symm_apply`

English:
lemma ULift.down_algEquiv_symm_apply
  statement: {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  proof: rfl

中文:
引理 类型层提升.down_algEquiv_symm_apply
  结论: {R A : 类型} [交换半环 R] [半环 A] [代数 R A]
  证明: rfl
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
/--
Definition of `AlgHom.ulift` / `AlgHom.ulift` 的定义

English:
definition AlgHom.ulift
  signature: (f : S ->ₐ[R] T)
  body: AlgHom.comp ULift.algEquiv.symm.toAlgHom (f.comp ULift.algEquiv.toAlgHom)
  commutes' _ := by simp

@[simp]

中文:
定义 代数态射.ulift
  签名: (f : S ->ₐ[R] T)
  定义体: AlgHom.comp ULift.algEquiv.symm.toAlgHom (f.comp ULift.algEquiv.toAlgHom)
  commutes' _ := by simp

@[simp]

Depends on / 依赖: AlgHom, AlgHom.comp, ULift.algEquiv.symm.toAlgHom, ULift.algEquiv.toAlgHom, algEquiv, f.comp, toAlgHom
-/
def AlgHom.ulift (f : S ->ₐ[R] T) :
    ULift.{u₁} S ->ₐ[ULift.{u₂} R] ULift.{u₃} T where
  __ := AlgHom.comp ULift.algEquiv.symm.toAlgHom (f.comp ULift.algEquiv.toAlgHom)
  commutes' _ := by simp

@[simp]
/--
lemma `AlgHom.down_ulift_apply` / 引理 `AlgHom.down_ulift_apply`

English:
lemma AlgHom.down_ulift_apply
  given: (f : S ->ₐ[R] T) (x : ULift S)
  proof: rfl

中文:
引理 代数态射.down_ulift_apply
  条件: (f : S ->ₐ[R] T) (x : 类型层提升 S)
  证明: rfl
-/
lemma AlgHom.down_ulift_apply (f : S ->ₐ[R] T) (x : ULift S) :
    (f.ulift x).down = f x.down :=
  rfl

/--
lemma `AlgHom.ulift_apply` / 引理 `AlgHom.ulift_apply`

English:
lemma AlgHom.ulift_apply
  given: (f : S ->ₐ[R] T) (x : ULift S)
  proof: rfl

中文:
引理 代数态射.ulift_apply
  条件: (f : S ->ₐ[R] T) (x : 类型层提升 S)
  证明: rfl
-/
lemma AlgHom.ulift_apply (f : S ->ₐ[R] T) (x : ULift S) :
    f.ulift x = ⟨f x.down⟩ :=
  rfl

end

/--
Definition of `LinearEquiv.algEquivOfRing` / `LinearEquiv.algEquivOfRing` 的定义

English:
definition LinearEquiv.algEquivOfRing
  body: Algebra.ofId R A
  invFun x := e.symm (e 1 * x)
  left_inv x := calc
    e.symm (e 1 * (algebraMap R A) x)
      = e.symm (x • e 1) := by rw [Algebra.smul_def, mul_comm]
    _ = x := by rw [map_smul, e.symm_apply_apply, smul_eq_mul, mul_one]
  right_inv x := calc
    (algebraMap R A) (e.symm (e 1 * x))
      = (algebraMap R A) (e.symm (e 1 * x)) * e (e.symm 1 • 1) := by
          rw [smul_eq_mul]; rw [mul_one]; rw [e.apply_symm_apply]; rw [mul_one]
    _ = x := by rw [map_smul, Algebra.smul_def, mul_left_comm, ← Algebra.smul_def _ (e 1),
          ← map_smul, smul_eq_mul, mul_one, e.apply_symm_apply, ← mul_assoc, ← Algebra.smul_def,
          ← map_smul, smul_eq_mul, mul_one, e.apply_symm_apply, one_mul]

中文:
定义 线性等价.algEquivOfRing
  定义体: Algebra.ofId R A
  invFun x := e.symm (e 1 * x)
  left_inv x := calc
    e.symm (e 1 * (algebraMap R A) x)
      = e.symm (x • e 1) := by rw [Algebra.smul_def, mul_comm]
    _ = x := by rw [map_smul, e.symm_apply_apply, smul_eq_mul, mul_one]
  right_inv x := calc
    (algebraMap R A) (e.symm (e 1 * x))
      = (algebraMap R A) (e.symm (e 1 * x)) * e (e.symm 1 • 1) := by
          rw [smul_eq_mul]; rw [mul_one]; rw [e.apply_symm_apply]; rw [mul_one]
    _ = x := by rw [map_smul, Algebra.smul_def, mul_left_comm, ← Algebra.smul_def _ (e 1),
          ← map_smul, smul_eq_mul, mul_one, e.apply_symm_apply, ← mul_assoc, ← Algebra.smul_def,
          ← map_smul, smul_eq_mul, mul_one, e.apply_symm_apply, one_mul]
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
          rw [smul_eq_mul]; rw [mul_one]; rw [e.apply_symm_apply]; rw [mul_one]
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
/--
Definition of `conjAlgEquiv` / `conjAlgEquiv` 的定义

English:
definition conjAlgEquiv
  signature: (e : M₁ ≃ₗ[S] M₂)
  body: e.conjRingEquiv
  commutes' _ := by ext; change e.restrictScalars R _ = _; simp

中文:
定义 conjAlgEquiv
  签名: (e : M₁ ≃ₗ[S] M₂)
  定义体: e.conjRingEquiv
  commutes' _ := by ext; change e.restrictScalars R _ = _; simp
-/
@[simps!] def conjAlgEquiv (e : M₁ ≃ₗ[S] M₂) : Module.End S M₁ ≃ₐ[R] Module.End S M₂ where
  __ := e.conjRingEquiv
  commutes' _ := by ext; change e.restrictScalars R _ = _; simp

/--
theorem `conjAlgEquiv_apply` / 定理 `conjAlgEquiv_apply`

English:
theorem conjAlgEquiv_apply
  given: (e : M₁ ≃ₗ[S] M₂) (f : Module.End S M₁)
  proof: rfl

中文:
定理 conjAlgEquiv_apply
  条件: (e : M₁ ≃ₗ[S] M₂) (f : 模.End S M₁)
  证明: rfl
-/
theorem conjAlgEquiv_apply (e : M₁ ≃ₗ[S] M₂) (f : Module.End S M₁) :
    e.conjAlgEquiv R f = e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap := rfl

/--
theorem `symm_conjAlgEquiv` / 定理 `symm_conjAlgEquiv`

English:
theorem symm_conjAlgEquiv
  given: (e : M₁ ≃ₗ[S] M₂)
  statement: (e.conjAlgEquiv R).symm = e.symm.conjAlgEquiv R
  proof: rfl

中文:
定理 symm_conjAlgEquiv
  条件: (e : M₁ ≃ₗ[S] M₂)
  结论: (e.conjAlgEquiv R).symm = e.symm.conjAlgEquiv R
  证明: rfl
-/
theorem symm_conjAlgEquiv (e : M₁ ≃ₗ[S] M₂) : (e.conjAlgEquiv R).symm = e.symm.conjAlgEquiv R := rfl

end LinearEquiv
