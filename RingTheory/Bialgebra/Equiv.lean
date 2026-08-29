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

/--
Definition of `BialgEquiv` / `BialgEquiv` 的定义

English:
structure BialgEquiv
  parameters: (R : Type u) [CommSemiring R] (A : Type v) (B : Type w)
  extends: A ≃ₗc[R] B, A ≃* B
  (no additional axioms)

中文:
结构 Bialg等价
  参数: (R : 类型u) [交换半环 R] (A : 类型v) (B : 类型 w)
  继承: A ≃ₗc[R] B, A ≃* B
  (无附加公理)
-/
structure BialgEquiv (R : Type u) [CommSemiring R] (A : Type v) (B : Type w)
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] extends A ≃ₗc[R] B, A ≃* B where

attribute [nolint docBlame] BialgEquiv.toMulEquiv
attribute [nolint docBlame] BialgEquiv.toCoalgEquiv

@[inherit_doc BialgEquiv]
notation:50 A " ≃ₐc[" R "] " B => BialgEquiv R A B

/--
Definition of `BialgEquivClass` / `BialgEquivClass` 的定义

English:
class BialgEquivClass
  parameters: (F : Type*) (R A B : outParam Type*) [CommSemiring R]
  extends: CoalgEquivClass F R A B, MulEquivClass F A B
  (no additional axioms)

中文:
类 Bialg等价类
  参数: (F : 类型) (R A B : outParam 类型) [交换半环 R]
  继承: 余alg等价类 F R A B, 乘法等价类 F A B
  (无附加公理)
-/
class BialgEquivClass (F : Type*) (R A B : outParam Type*) [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] [EquivLike F A B] : Prop
    extends CoalgEquivClass F R A B, MulEquivClass F A B

namespace BialgEquivClass

variable {F R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] [CoalgebraStruct R A] [CoalgebraStruct R B]
  [EquivLike F A B] [BialgEquivClass F R A B]

instance (priority := 100) toBialgHomClass : BialgHomClass F R A B where
  map_add := map_add
  map_smulₛₗ := map_smul
  counit_comp := CoalgHomClass.counit_comp
  map_comp_comul := CoalgHomClass.map_comp_comul
  map_mul := map_mul
  map_one := map_one

/-- Reinterpret an element of a type of bialgebra equivalences as a bialgebra equivalence. -/
@[coe]
/--
Definition of `toBialgEquiv` / `toBialgEquiv` 的定义

English:
definition toBialgEquiv
  signature: (f : F)
  body: { (f : A ≃ₗc[R] B), (f : A ->ₐc[R] B) with }

中文:
定义 toBialgEquiv
  签名: (f : F)
  定义体: { (f : A ≃ₗc[R] B), (f : A ->ₐc[R] B) with }
-/
def toBialgEquiv (f : F) : A ≃ₐc[R] B :=
  { (f : A ≃ₗc[R] B), (f : A ->ₐc[R] B) with }

/--
Instance `instCoeToBialgEquiv` / 实例 `instCoeToBialgEquiv`

English:
instance instCoeToBialgEquiv
  signature: : CoeHead F (A ≃ₐc[R] B) where
  body: toBialgEquiv f

中文:
实例 instCoeToBialgEquiv
  签名: : CoeHead F (A ≃ₐc[R] B) where
  定义体: toBialgEquiv f

Depends on / 依赖: toBialgEquiv
-/
instance instCoeToBialgEquiv : CoeHead F (A ≃ₐc[R] B) where
  coe f := toBialgEquiv f

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

/--
Definition of `toBialgHom` / `toBialgHom` 的定义

English:
definition toBialgHom
  signature: (f : A ≃ₐc[R] B)
  body: { f.toCoalgEquiv with
    map_one' := map_one f.toMulEquiv
    map_mul' := map_mul f.toMulEquiv }

中文:
定义 toBialgHom
  签名: (f : A ≃ₐc[R] B)
  定义体: { f.toCoalgEquiv with
    map_one' := map_one f.toMulEquiv
    map_mul' := map_mul f.toMulEquiv }

Depends on / 依赖: f.toCoalgEquiv, f.toMulEquiv, map_mul, map_one, toCoalgEquiv, toMulEquiv
-/
def toBialgHom (f : A ≃ₐc[R] B) : A ->ₐc[R] B :=
  { f.toCoalgEquiv with
    map_one' := map_one f.toMulEquiv
    map_mul' := map_mul f.toMulEquiv }

/--
Definition of `toAlgEquiv` / `toAlgEquiv` 的定义

English:
definition toAlgEquiv
  signature: (f : A ≃ₐc[R] B)
  body: { f.toCoalgEquiv with
    map_mul' := map_mul f.toMulEquiv
    map_add' := map_add f.toCoalgEquiv
    commutes' := AlgHomClass.commutes f.toBialgHom }

中文:
定义 toAlgEquiv
  签名: (f : A ≃ₐc[R] B)
  定义体: { f.toCoalgEquiv with
    map_mul' := map_mul f.toMulEquiv
    map_add' := map_add f.toCoalgEquiv
    commutes' := AlgHomClass.commutes f.toBialgHom }

Depends on / 依赖: AlgHomClass, AlgHomClass.commutes, commutes, f.toBialgHom, f.toCoalgEquiv, f.toMulEquiv, map_add, map_mul, toBialgHom, toCoalgEquiv, toMulEquiv
-/
def toAlgEquiv (f : A ≃ₐc[R] B) : A ≃ₐ[R] B :=
  { f.toCoalgEquiv with
    map_mul' := map_mul f.toMulEquiv
    map_add' := map_add f.toCoalgEquiv
    commutes' := AlgHomClass.commutes f.toBialgHom }

/--
Definition of `toEquiv` / `toEquiv` 的定义

English:
definition toEquiv
  signature: : (A ≃ₐc[R] B) -> A ≃ B
  body: fun f => f.toCoalgEquiv.toEquiv

中文:
定义 toEquiv
  签名: : (A ≃ₐc[R] B) -> A ≃ B
  定义体: fun f => f.toCoalgEquiv.toEquiv

Depends on / 依赖: f.toCoalgEquiv.toEquiv, toCoalgEquiv, toEquiv
-/
def toEquiv : (A ≃ₐc[R] B) -> A ≃ B := fun f => f.toCoalgEquiv.toEquiv

/--
theorem `toEquiv_injective` / 定理 `toEquiv_injective`

English:
theorem toEquiv_injective
  statement: Function.Injective (toEquiv : (A ≃ₐc[R] B) -> A ≃ B)
  proof: fun ⟨_, _⟩ ⟨_, _⟩ h =>
    (BialgEquiv.mk.injEq _ _ _ _).mpr (CoalgEquiv.toEquiv_injective h)

@[simp]

中文:
定理 toEquiv_injective
  结论: 函数.单射 (toEquiv : (A ≃ₐc[R] B) -> A ≃ B)
  证明: fun ⟨_, _⟩ ⟨_, _⟩ h =>
    (BialgEquiv.mk.injEq _ _ _ _).mpr (CoalgEquiv.toEquiv_injective h)

@[simp]

Depends on / 依赖: BialgEquiv, BialgEquiv.mk.injEq, CoalgEquiv, CoalgEquiv.toEquiv_injective, toEquiv_injective
-/
theorem toEquiv_injective : Function.Injective (toEquiv : (A ≃ₐc[R] B) -> A ≃ B) :=
  fun ⟨_, _⟩ ⟨_, _⟩ h =>
    (BialgEquiv.mk.injEq _ _ _ _).mpr (CoalgEquiv.toEquiv_injective h)

@[simp]
/--
theorem `toEquiv_inj` / 定理 `toEquiv_inj`

English:
theorem toEquiv_inj
  given: {e₁ e₂ : A ≃ₐc[R] B}
  statement: e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂
  proof: toEquiv_injective.eq_iff

中文:
定理 toEquiv_inj
  条件: {e₁ e₂ : A ≃ₐc[R] B}
  结论: e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂
  证明: toEquiv_injective.eq_iff

Depends on / 依赖: eq_iff, toEquiv_injective, toEquiv_injective.eq_iff
-/
theorem toEquiv_inj {e₁ e₂ : A ≃ₐc[R] B} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff

/--
theorem `toBialgHom_injective` / 定理 `toBialgHom_injective`

English:
theorem toBialgHom_injective
  statement: Function.Injective (toBialgHom : (A ≃ₐc[R] B) -> A ->ₐc[R] B)
  proof: fun _ _ H => toEquiv_injective Equiv.ext BialgHom.congr_fun H

中文:
定理 toBialgHom_injective
  结论: 函数.单射 (toBialgHom : (A ≃ₐc[R] B) -> A ->ₐc[R] B)
  证明: fun _ _ H => toEquiv_injective Equiv.ext BialgHom.congr_fun H

Depends on / 依赖: BialgHom, BialgHom.congr_fun, Equiv.ext, congr_fun, toEquiv_injective
-/
theorem toBialgHom_injective : Function.Injective (toBialgHom : (A ≃ₐc[R] B) -> A ->ₐc[R] B) :=
fun _ _ H => toEquiv_injective Equiv.ext BialgHom.congr_fun H

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (A ≃ₐc[R] B) A B
  body: f.toFun
  inv := fun f => f.invFun
  coe_injective' _ _ h _ := toBialgHom_injective (DFunLike.coe_injective h)
  left_inv := fun f => f.left_inv
  right_inv := fun f => f.right_inv

中文:
实例 :
  签名: 等价状 (A ≃ₐc[R] B) A B
  定义体: f.toFun
  inv := fun f => f.invFun
  coe_injective' _ _ h _ := toBialgHom_injective (DFunLike.coe_injective h)
  left_inv := fun f => f.left_inv
  right_inv := fun f => f.right_inv

Depends on / 依赖: f.toFun
-/
instance : EquivLike (A ≃ₐc[R] B) A B where
  coe f := f.toFun
  inv := fun f => f.invFun
  coe_injective' _ _ h _ := toBialgHom_injective (DFunLike.coe_injective h)
  left_inv := fun f => f.left_inv
  right_inv := fun f => f.right_inv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (A ≃ₐc[R] B) A B
  body: DFunLike.coe
  coe_injective := DFunLike.coe_injective

中文:
实例 :
  签名: 函数状 (A ≃ₐc[R] B) A B
  定义体: DFunLike.coe
  coe_injective := DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe
-/
instance : FunLike (A ≃ₐc[R] B) A B where
  coe := DFunLike.coe
  coe_injective := DFunLike.coe_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BialgEquivClass (A ≃ₐc[R] B) R A B
  body: (·.map_add')
  map_smulₛₗ := (·.map_smul')
  counit_comp := (·.counit_comp)
  map_comp_comul := (·.map_comp_comul)
  map_mul := (·.map_mul')

中文:
实例 :
  签名: Bialg等价类 (A ≃ₐc[R] B) R A B
  定义体: (·.map_add')
  map_smulₛₗ := (·.map_smul')
  counit_comp := (·.counit_comp)
  map_comp_comul := (·.map_comp_comul)
  map_mul := (·.map_mul')

Depends on / 依赖: map_add
-/
instance : BialgEquivClass (A ≃ₐc[R] B) R A B where
  map_add := (·.map_add')
  map_smulₛₗ := (·.map_smul')
  counit_comp := (·.counit_comp)
  map_comp_comul := (·.map_comp_comul)
  map_mul := (·.map_mul')

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (A ≃ₐc[R] B) (A ≃ₐ[R] B)
  body: toAlgEquiv

@[simp, norm_cast]

中文:
实例 :
  签名: CoeOut (A ≃ₐc[R] B) (A ≃ₐ[R] B)
  定义体: toAlgEquiv

@[simp, norm_cast]

Depends on / 依赖: toAlgEquiv
-/
instance : CoeOut (A ≃ₐc[R] B) (A ≃ₐ[R] B) where coe := toAlgEquiv

@[simp, norm_cast]
/--
theorem `toBialgHom_inj` / 定理 `toBialgHom_inj`

English:
theorem toBialgHom_inj
  given: {e₁ e₂ : A ≃ₐc[R] B}
  statement: (↑e₁ : A ->ₐc[R] B) = e₂ ↔ e₁ = e₂
  proof: toBialgHom_injective.eq_iff

中文:
定理 toBialgHom_inj
  条件: {e₁ e₂ : A ≃ₐc[R] B}
  结论: (↑e₁ : A ->ₐc[R] B) = e₂ ↔ e₁ = e₂
  证明: toBialgHom_injective.eq_iff

Depends on / 依赖: eq_iff, toBialgHom_injective, toBialgHom_injective.eq_iff
-/
theorem toBialgHom_inj {e₁ e₂ : A ≃ₐc[R] B} : (↑e₁ : A ->ₐc[R] B) = e₂ ↔ e₁ = e₂ :=
  toBialgHom_injective.eq_iff

/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (e : A ≃ₗc[R] B) (h)
  statement: mk e h = e
  proof: rfl

中文:
引理 coe_mk
  条件: (e : A ≃ₗc[R] B) (h)
  结论: mk e h = e
  证明: rfl
-/
@[simp] lemma coe_mk (e : A ≃ₗc[R] B) (h) : mk e h = e := rfl

end

section

variable [Semiring A] [Semiring B] [Semiring C] [Algebra R A] [Algebra R B]
  [Algebra R C] [CoalgebraStruct R A] [CoalgebraStruct R B] [CoalgebraStruct R C]

variable (e e' : A ≃ₐc[R] B)

@[simp, norm_cast]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  statement: ⇑(e : A ->ₐc[R] B) = e
  proof: rfl

@[simp]

中文:
定理 coe_coe
  结论: ⇑(e : A ->ₐc[R] B) = e
  证明: rfl

@[simp]
-/
theorem coe_coe : ⇑(e : A ->ₐc[R] B) = e :=
  rfl

@[simp]
/--
theorem `toCoalgEquiv_eq_coe` / 定理 `toCoalgEquiv_eq_coe`

English:
theorem toCoalgEquiv_eq_coe
  given: (f : A ≃ₐc[R] B)
  statement: f.toCoalgEquiv = f
  proof: rfl

@[simp]

中文:
定理 toCoalgEquiv_eq_coe
  条件: (f : A ≃ₐc[R] B)
  结论: f.toCoalgEquiv = f
  证明: rfl

@[simp]
-/
theorem toCoalgEquiv_eq_coe (f : A ≃ₐc[R] B) : f.toCoalgEquiv = f :=
  rfl

@[simp]
/--
theorem `toBialgHom_eq_coe` / 定理 `toBialgHom_eq_coe`

English:
theorem toBialgHom_eq_coe
  given: (f : A ≃ₐc[R] B)
  statement: f.toBialgHom = f
  proof: rfl

@[deprecated "Now a syntactic tautology" (since := "2026-04-09"), nolint synTaut]

中文:
定理 toBialgHom_eq_coe
  条件: (f : A ≃ₐc[R] B)
  结论: f.toBialgHom = f
  证明: rfl

@[deprecated "Now a syntactic tautology" (since := "2026-04-09"), nolint synTaut]
-/
theorem toBialgHom_eq_coe (f : A ≃ₐc[R] B) : f.toBialgHom = f :=
  rfl

@[deprecated "Now a syntactic tautology" (since := "2026-04-09"), nolint synTaut]
/--
theorem `toAlgEquiv_eq_coe` / 定理 `toAlgEquiv_eq_coe`

English:
theorem toAlgEquiv_eq_coe
  given: (f : A ≃ₐc[R] B)
  statement: f.toAlgEquiv = f
  proof: rfl

@[simp]

中文:
定理 toAlgEquiv_eq_coe
  条件: (f : A ≃ₐc[R] B)
  结论: f.toAlgEquiv = f
  证明: rfl

@[simp]
-/
theorem toAlgEquiv_eq_coe (f : A ≃ₐc[R] B) : f.toAlgEquiv = f :=
  rfl

@[simp]
/--
theorem `coe_toCoalgEquiv` / 定理 `coe_toCoalgEquiv`

English:
theorem coe_toCoalgEquiv
  statement: ⇑(e : A ≃ₐ[R] B) = e
  proof: rfl

@[simp]

中文:
定理 coe_toCoalgEquiv
  结论: ⇑(e : A ≃ₐ[R] B) = e
  证明: rfl

@[simp]
-/
theorem coe_toCoalgEquiv : ⇑(e : A ≃ₐ[R] B) = e :=
  rfl

@[simp]
/--
theorem `coe_toBialgHom` / 定理 `coe_toBialgHom`

English:
theorem coe_toBialgHom
  statement: ⇑(e : A ->ₐc[R] B) = e
  proof: rfl

@[simp]

中文:
定理 coe_toBialgHom
  结论: ⇑(e : A ->ₐc[R] B) = e
  证明: rfl

@[simp]
-/
theorem coe_toBialgHom : ⇑(e : A ->ₐc[R] B) = e :=
  rfl

@[simp]
/--
theorem `coe_toAlgEquiv` / 定理 `coe_toAlgEquiv`

English:
theorem coe_toAlgEquiv
  statement: ⇑(e : A ≃ₐ[R] B) = e
  proof: rfl

中文:
定理 coe_toAlgEquiv
  结论: ⇑(e : A ≃ₐ[R] B) = e
  证明: rfl
-/
theorem coe_toAlgEquiv : ⇑(e : A ≃ₐ[R] B) = e :=
  rfl

/--
theorem `toCoalgEquiv_toCoalgHom` / 定理 `toCoalgEquiv_toCoalgHom`

English:
theorem toCoalgEquiv_toCoalgHom
  statement: ((e : A ≃ₐc[R] B) : A ->ₗc[R] B) = (e : A ->ₐc[R] B)
  proof: rfl

@[deprecated "Now a syntactic equality" (since := "2026-04-30"), nolint synTaut]

中文:
定理 toCoalgEquiv_toCoalgHom
  结论: ((e : A ≃ₐc[R] B) : A ->ₗc[R] B) = (e : A ->ₐc[R] B)
  证明: rfl

@[deprecated "Now a syntactic equality" (since := "2026-04-30"), nolint synTaut]
-/
theorem toCoalgEquiv_toCoalgHom : ((e : A ≃ₐc[R] B) : A ->ₗc[R] B) = (e : A ->ₐc[R] B) :=
  rfl

@[deprecated "Now a syntactic equality" (since := "2026-04-30"), nolint synTaut]
/--
theorem `toBialgHom_toAlgHom` / 定理 `toBialgHom_toAlgHom`

English:
theorem toBialgHom_toAlgHom
  statement: ((e : A ->ₐc[R] B) : A ->ₐ[R] B) = e
  proof: rfl

中文:
定理 toBialgHom_toAlgHom
  结论: ((e : A ->ₐc[R] B) : A ->ₐ[R] B) = e
  证明: rfl
-/
theorem toBialgHom_toAlgHom : ((e : A ->ₐc[R] B) : A ->ₐ[R] B) = e := rfl

section

variable {e e'}

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : forall x, e x = e' x)
  statement: e = e'
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: (h : 对任意 x, e x = e' x)
  结论: e = e'
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext (h : forall x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: {x x'}
  statement: x = x' -> e x = e x'
  proof: DFunLike.congr_arg e

中文:
定理 congr_arg
  条件: {x x'}
  结论: x = x' -> e x = e x'
  证明: DFunLike.congr_arg e
-/
protected theorem congr_arg {x x'} : x = x' -> e x = e x' :=
  DFunLike.congr_arg e

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: (h : e = e') (x : A)
  statement: e x = e' x
  proof: DFunLike.congr_fun h x

中文:
定理 congr_fun
  条件: (h : e = e') (x : A)
  结论: e x = e' x
  证明: DFunLike.congr_fun h x
-/
protected theorem congr_fun (h : e = e') (x : A) : e x = e' x :=
  DFunLike.congr_fun h x

end

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: {R : Type u} [CommSemiring R] {α : Type v} {β : Type w}
  body: f

中文:
定义 Simps.apply
  签名: {R : 类型u} [交换半环 R] {α : 类型v} {β : 类型 w}
  定义体: f
-/
def Simps.apply {R : Type u} [CommSemiring R] {α : Type v} {β : Type w}
    [Semiring α] [Semiring β] [Algebra R α]
    [Algebra R β] [CoalgebraStruct R α] [CoalgebraStruct R β]
    (f : α ≃ₐc[R] β) : α -> β := f

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: {R : Type*} [CommSemiring R]
  body: e.symm

initialize_simps_projections BialgEquiv (toFun -> apply, invFun -> symm_apply)

中文:
定义 Simps.symm_apply
  签名: {R : 类型} [交换半环 R]
  定义体: e.symm

initialize_simps_projections BialgEquiv (toFun -> apply, invFun -> symm_apply)
-/
def Simps.symm_apply {R : Type*} [CommSemiring R]
    {A : Type*} {B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B]
    (e : A ≃ₐc[R] B) : B -> A :=
  e.symm

initialize_simps_projections BialgEquiv (toFun -> apply, invFun -> symm_apply)

variable (A R) in
/-- The identity map is a bialgebra equivalence. -/
@[refl, simps! apply]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : A ≃ₐc[R] A
  body: { CoalgEquiv.refl R A, BialgHom.id R A with }

@[simp]

中文:
定义 refl
  签名: : A ≃ₐc[R] A
  定义体: { CoalgEquiv.refl R A, BialgHom.id R A with }

@[simp]

Depends on / 依赖: BialgHom, BialgHom.id, CoalgEquiv, CoalgEquiv.refl
-/
def refl : A ≃ₐc[R] A :=
  { CoalgEquiv.refl R A, BialgHom.id R A with }

@[simp]
/--
theorem `refl_toCoalgEquiv` / 定理 `refl_toCoalgEquiv`

English:
theorem refl_toCoalgEquiv
  statement: refl R A = CoalgEquiv.refl R A
  proof: rfl

@[simp]

中文:
定理 refl_toCoalgEquiv
  结论: refl R A = 余alg等价.refl R A
  证明: rfl

@[simp]
-/
theorem refl_toCoalgEquiv : refl R A = CoalgEquiv.refl R A := rfl

@[simp]
/--
theorem `refl_toBialgHom` / 定理 `refl_toBialgHom`

English:
theorem refl_toBialgHom
  statement: refl R A = BialgHom.id R A
  proof: rfl

中文:
定理 refl_toBialgHom
  结论: refl R A = Bialg态射.id R A
  证明: rfl
-/
theorem refl_toBialgHom : refl R A = BialgHom.id R A :=
  rfl

/-- Bialgebra equivalences are symmetric. -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (e : A ≃ₐc[R] B)
  body: { (e : A ≃ₗc[R] B).symm, (e : A ≃* B).symm with }

@[simp]

中文:
定义 symm
  签名: (e : A ≃ₐc[R] B)
  定义体: { (e : A ≃ₗc[R] B).symm, (e : A ≃* B).symm with }

@[simp]
-/
def symm (e : A ≃ₐc[R] B) : B ≃ₐc[R] A :=
  { (e : A ≃ₗc[R] B).symm, (e : A ≃* B).symm with }

@[simp]
/--
theorem `symm_toCoalgEquiv` / 定理 `symm_toCoalgEquiv`

English:
theorem symm_toCoalgEquiv
  given: (e : A ≃ₐc[R] B)
  proof: rfl

中文:
定理 symm_toCoalgEquiv
  条件: (e : A ≃ₐc[R] B)
  证明: rfl
-/
theorem symm_toCoalgEquiv (e : A ≃ₐc[R] B) :
    e.symm = (e : A ≃ₗc[R] B).symm := rfl

/--
theorem `invFun_eq_symm` / 定理 `invFun_eq_symm`

English:
theorem invFun_eq_symm
  statement: e.invFun = e.symm
  proof: rfl

中文:
定理 invFun_eq_symm
  结论: e.invFun = e.symm
  证明: rfl
-/
theorem invFun_eq_symm : e.invFun = e.symm :=
  rfl

/--
theorem `coe_toEquiv_symm` / 定理 `coe_toEquiv_symm`

English:
theorem coe_toEquiv_symm
  statement: e.toEquiv.symm = e.symm
  proof: rfl

@[simp]

中文:
定理 coe_toEquiv_symm
  结论: e.toEquiv.symm = e.symm
  证明: rfl

@[simp]
-/
theorem coe_toEquiv_symm : e.toEquiv.symm = e.symm := rfl

@[simp]
/--
theorem `toEquiv_symm` / 定理 `toEquiv_symm`

English:
theorem toEquiv_symm
  statement: e.symm.toEquiv = e.toEquiv.symm
  proof: rfl

@[simp]

中文:
定理 toEquiv_symm
  结论: e.symm.toEquiv = e.toEquiv.symm
  证明: rfl

@[simp]
-/
theorem toEquiv_symm : e.symm.toEquiv = e.toEquiv.symm :=
  rfl

@[simp]
/--
theorem `coe_toEquiv` / 定理 `coe_toEquiv`

English:
theorem coe_toEquiv
  statement: ⇑e.toEquiv = e
  proof: rfl

@[simp]

中文:
定理 coe_toEquiv
  结论: ⇑e.toEquiv = e
  证明: rfl

@[simp]
-/
theorem coe_toEquiv : ⇑e.toEquiv = e :=
  rfl

@[simp]
/--
theorem `coe_symm_toEquiv` / 定理 `coe_symm_toEquiv`

English:
theorem coe_symm_toEquiv
  statement: ⇑e.toEquiv.symm = e.symm
  proof: rfl

中文:
定理 coe_symm_toEquiv
  结论: ⇑e.toEquiv.symm = e.symm
  证明: rfl
-/
theorem coe_symm_toEquiv : ⇑e.toEquiv.symm = e.symm :=
  rfl

variable {e₁₂ : A ≃ₐc[R] B} {e₂₃ : B ≃ₐc[R] C}

/-- Bialgebra equivalences are transitive. -/
@[trans, simps! apply]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e₁₂ : A ≃ₐc[R] B) (e₂₃ : B ≃ₐc[R] C)
  body: { (e₁₂ : A ≃ₗc[R] B).trans (e₂₃ : B ≃ₗc[R] C), (e₁₂ : A ≃* B).trans (e₂₃ : B ≃* C) with }

@[simp]

中文:
定义 trans
  签名: (e₁₂ : A ≃ₐc[R] B) (e₂₃ : B ≃ₐc[R] C)
  定义体: { (e₁₂ : A ≃ₗc[R] B).trans (e₂₃ : B ≃ₗc[R] C), (e₁₂ : A ≃* B).trans (e₂₃ : B ≃* C) with }

@[simp]
-/
def trans (e₁₂ : A ≃ₐc[R] B) (e₂₃ : B ≃ₐc[R] C) : A ≃ₐc[R] C :=
  { (e₁₂ : A ≃ₗc[R] B).trans (e₂₃ : B ≃ₗc[R] C), (e₁₂ : A ≃* B).trans (e₂₃ : B ≃* C) with }

@[simp]
/--
theorem `trans_toCoalgEquiv` / 定理 `trans_toCoalgEquiv`

English:
theorem trans_toCoalgEquiv
  proof: rfl

@[simp]

中文:
定理 trans_toCoalgEquiv
  证明: rfl

@[simp]
-/
theorem trans_toCoalgEquiv :
    (e₁₂.trans e₂₃ : A ≃ₗc[R] C) = (e₁₂ : A ≃ₗc[R] B).trans (e₂₃ : B ≃ₗc[R] C) := rfl

@[simp]
/--
theorem `trans_toBialgHom` / 定理 `trans_toBialgHom`

English:
theorem trans_toBialgHom
  proof: rfl

@[simp]

中文:
定理 trans_toBialgHom
  证明: rfl

@[simp]
-/
theorem trans_toBialgHom :
    (e₁₂.trans e₂₃ : A ->ₐc[R] C) = (e₂₃ : B ->ₐc[R] C).comp e₁₂ := rfl

@[simp]
/--
theorem `coe_toEquiv_trans` / 定理 `coe_toEquiv_trans`

English:
theorem coe_toEquiv_trans
  statement: (e₁₂ : A ≃ B).trans e₂₃ = (e₁₂.trans e₂₃ : A ≃ C)
  proof: rfl

@[simp]

中文:
定理 coe_toEquiv_trans
  结论: (e₁₂ : A ≃ B).trans e₂₃ = (e₁₂.trans e₂₃ : A ≃ C)
  证明: rfl

@[simp]
-/
theorem coe_toEquiv_trans : (e₁₂ : A ≃ B).trans e₂₃ = (e₁₂.trans e₂₃ : A ≃ C) :=
  rfl

@[simp]
/--
lemma `apply_symm_apply` / 引理 `apply_symm_apply`

English:
lemma apply_symm_apply
  given: (e : A ≃ₐc[R] B)
  statement: forall x, e (e.symm x) = x
  proof: e.toEquiv.apply_symm_apply

@[simp]

中文:
引理 apply_symm_apply
  条件: (e : A ≃ₐc[R] B)
  结论: 对任意 x, e (e.symm x) = x
  证明: e.toEquiv.apply_symm_apply

@[simp]

Depends on / 依赖: apply_symm_apply, e.toEquiv.apply_symm_apply, toEquiv
-/
lemma apply_symm_apply (e : A ≃ₐc[R] B) : forall x, e (e.symm x) = x := e.toEquiv.apply_symm_apply

@[simp]
/--
lemma `symm_apply_apply` / 引理 `symm_apply_apply`

English:
lemma symm_apply_apply
  given: (e : A ≃ₐc[R] B)
  statement: forall x, e.symm (e x) = x
  proof: e.toEquiv.symm_apply_apply

中文:
引理 symm_apply_apply
  条件: (e : A ≃ₐc[R] B)
  结论: 对任意 x, e.symm (e x) = x
  证明: e.toEquiv.symm_apply_apply

Depends on / 依赖: e.toEquiv.symm_apply_apply, symm_apply_apply, toEquiv
-/
lemma symm_apply_apply (e : A ≃ₐc[R] B) : forall x, e.symm (e x) = x := e.toEquiv.symm_apply_apply

/--
lemma `comp_symm` / 引理 `comp_symm`

English:
lemma comp_symm
  given: (e : A ≃ₐc[R] B)
  statement: (e : A ->ₐc[R] B).comp e.symm = .id R B
  proof: BialgHom.coe_toAlgHom_injective e.toAlgEquiv.comp_symm

中文:
引理 comp_symm
  条件: (e : A ≃ₐc[R] B)
  结论: (e : A ->ₐc[R] B).comp e.symm = .id R B
  证明: BialgHom.coe_toAlgHom_injective e.toAlgEquiv.comp_symm
-/
@[simp] lemma comp_symm (e : A ≃ₐc[R] B) : (e : A ->ₐc[R] B).comp e.symm = .id R B :=
  BialgHom.coe_toAlgHom_injective e.toAlgEquiv.comp_symm

/--
lemma `symm_comp` / 引理 `symm_comp`

English:
lemma symm_comp
  given: (e : A ≃ₐc[R] B)
  statement: (e.symm : B ->ₐc[R] A).comp e = .id R A
  proof: BialgHom.coe_toAlgHom_injective e.toAlgEquiv.symm_comp

中文:
引理 symm_comp
  条件: (e : A ≃ₐc[R] B)
  结论: (e.symm : B ->ₐc[R] A).comp e = .id R A
  证明: BialgHom.coe_toAlgHom_injective e.toAlgEquiv.symm_comp
-/
@[simp] lemma symm_comp (e : A ≃ₐc[R] B) : (e.symm : B ->ₐc[R] A).comp e = .id R A :=
  BialgHom.coe_toAlgHom_injective e.toAlgEquiv.symm_comp

/--
lemma `toRingEquiv_toRingHom` / 引理 `toRingEquiv_toRingHom`

English:
lemma toRingEquiv_toRingHom
  given: (e : A ≃ₐc[R] B)
  statement: ((e : A ≃+* B) : A ->+* B) = e
  proof: rfl

中文:
引理 toRingEquiv_toRingHom
  条件: (e : A ≃ₐc[R] B)
  结论: ((e : A ≃+* B) : A ->+* B) = e
  证明: rfl
-/
@[simp] lemma toRingEquiv_toRingHom (e : A ≃ₐc[R] B) : ((e : A ≃+* B) : A ->+* B) = e := rfl
/--
lemma `toAlgEquiv_toRingHom` / 引理 `toAlgEquiv_toRingHom`

English:
lemma toAlgEquiv_toRingHom
  given: (e : A ≃ₐc[R] B)
  statement: ((e : A ≃ₐ[R] B) : A ->+* B) = e
  proof: rfl

中文:
引理 toAlgEquiv_toRingHom
  条件: (e : A ≃ₐc[R] B)
  结论: ((e : A ≃ₐ[R] B) : A ->+* B) = e
  证明: rfl
-/
@[simp] lemma toAlgEquiv_toRingHom (e : A ≃ₐc[R] B) : ((e : A ≃ₐ[R] B) : A ->+* B) = e := rfl

/--
Definition of `ofBialgHom` / `ofBialgHom` 的定义

English:
definition ofBialgHom
  signature: (f : A ->ₐc[R] B) (g : B ->ₐc[R] A) (h₁ : f.comp g = BialgHom.id R B)
  body: f
  toFun := f
  invFun := g
  left_inv := BialgHom.ext_iff.1 h₂
  right_inv := BialgHom.ext_iff.1 h₁

@[simp]

中文:
定义 ofBialgHom
  签名: (f : A ->ₐc[R] B) (g : B ->ₐc[R] A) (h₁ : f.comp g = Bialg态射.id R B)
  定义体: f
  toFun := f
  invFun := g
  left_inv := BialgHom.ext_iff.1 h₂
  right_inv := BialgHom.ext_iff.1 h₁

@[simp]
-/
def ofBialgHom (f : A ->ₐc[R] B) (g : B ->ₐc[R] A) (h₁ : f.comp g = BialgHom.id R B)
    (h₂ : g.comp f = BialgHom.id R A) : A ≃ₐc[R] B where
  __ := f
  toFun := f
  invFun := g
  left_inv := BialgHom.ext_iff.1 h₂
  right_inv := BialgHom.ext_iff.1 h₁

@[simp]
/--
theorem `coe_ofBialgHom` / 定理 `coe_ofBialgHom`

English:
theorem coe_ofBialgHom
  given: (f : A ->ₐc[R] B) (g : B ->ₐc[R] A) (h₁ h₂)
  proof: rfl

中文:
定理 coe_ofBialgHom
  条件: (f : A ->ₐc[R] B) (g : B ->ₐc[R] A) (h₁ h₂)
  证明: rfl
-/
theorem coe_ofBialgHom (f : A ->ₐc[R] B) (g : B ->ₐc[R] A) (h₁ h₂) :
    ofBialgHom f g h₁ h₂ = f :=
  rfl

/--
theorem `ofBialgHom_symm` / 定理 `ofBialgHom_symm`

English:
theorem ofBialgHom_symm
  given: (f : A ->ₐc[R] B) (g : B ->ₐc[R] A) (h₁ h₂)
  proof: rfl

中文:
定理 ofBialgHom_symm
  条件: (f : A ->ₐc[R] B) (g : B ->ₐc[R] A) (h₁ h₂)
  证明: rfl
-/
theorem ofBialgHom_symm (f : A ->ₐc[R] B) (g : B ->ₐc[R] A) (h₁ h₂) :
    (ofBialgHom f g h₁ h₂).symm = ofBialgHom g f h₂ h₁ :=
  rfl

end

variable [Semiring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]

/--
Definition of `ofAlgEquiv` / `ofAlgEquiv` 的定义

English:
definition ofAlgEquiv
  signature: (f : A ≃ₐ[R] B)
  body: f
  map_smul' := map_smul f
  counit_comp := congr($(counit_comp).toLinearMap)
  map_comp_comul := congr($(map_comp_comul).toLinearMap)

@[simp]

中文:
定义 ofAlgEquiv
  签名: (f : A ≃ₐ[R] B)
  定义体: f
  map_smul' := map_smul f
  counit_comp := congr($(counit_comp).toLinearMap)
  map_comp_comul := congr($(map_comp_comul).toLinearMap)

@[simp]
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
/--
lemma `toLinearMap_ofAlgEquiv` / 引理 `toLinearMap_ofAlgEquiv`

English:
lemma toLinearMap_ofAlgEquiv
  given: (f : A ≃ₐ[R] B) (counit_comp map_comp_comul)
  proof: rfl

中文:
引理 toLinearMap_ofAlgEquiv
  条件: (f : A ≃ₐ[R] B) (counit_comp map_comp_comul)
  证明: rfl
-/
lemma toLinearMap_ofAlgEquiv (f : A ≃ₐ[R] B) (counit_comp map_comp_comul) :
    (ofAlgEquiv f counit_comp map_comp_comul : A ->ₗ[R] B) = f := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Promotes a bijective bialgebra homomorphism to a bialgebra equivalence. -/
@[simps! apply]
/--
Definition of `ofBijective` / `ofBijective` 的定义

English:
definition ofBijective
  signature: (f : A ->ₐc[R] B) (hf : Bijective f)
  body: .ofAlgEquiv (.ofBijective (f : A ->ₐ[R] B) hf) (by ext; simp) (by ext; simp)

@[simp]

中文:
定义 ofBijective
  签名: (f : A ->ₐc[R] B) (hf : 双射 f)
  定义体: .ofAlgEquiv (.ofBijective (f : A ->ₐ[R] B) hf) (by ext; simp) (by ext; simp)

@[simp]

Depends on / 依赖: ofAlgEquiv, ofBijective
-/
noncomputable def ofBijective (f : A ->ₐc[R] B) (hf : Bijective f) : A ≃ₐc[R] B :=
  .ofAlgEquiv (.ofBijective (f : A ->ₐ[R] B) hf) (by ext; simp) (by ext; simp)

@[simp]
/--
lemma `coe_ofBijective` / 引理 `coe_ofBijective`

English:
lemma coe_ofBijective
  given: (f : A ->ₐc[R] B) (hf : Bijective f)
  statement: (ofBijective f hf : A -> B) = f
  proof: rfl

中文:
引理 coe_ofBijective
  条件: (f : A ->ₐc[R] B) (hf : 双射 f)
  结论: (ofBijective f hf : A -> B) = f
  证明: rfl
-/
lemma coe_ofBijective (f : A ->ₐc[R] B) (hf : Bijective f) : (ofBijective f hf : A -> B) = f := rfl

end BialgEquiv
