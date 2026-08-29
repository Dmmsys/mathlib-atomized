/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Basic

/-!
# Homomorphisms of `R`-algebras

This file defines bundled homomorphisms of `R`-algebras.

## Main definitions

* `AlgHom R A B`: the type of `R`-algebra morphisms from `A` to `B`.
* `Algebra.ofId R A : R →ₐ[R] A`: the canonical map from `R` to `A`, as an `AlgHom`.

## Notation

* `A →ₐ[R] B` : `R`-algebra homomorphism from `A` to `B`.
-/

@[expose] public section

universe u v w u₁ v₁

/--
Definition of `AlgHom` / `AlgHom` 的定义

English:
structure AlgHom
  parameters: (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]
  extends: RingHom A B
  axioms and operations (1):
    - commutes' : forall r : R, toFun (algebraMap R A r) = algebraMap R B r

中文:
结构 代数态射
  参数: (R : 类型u) (A : 类型v) (B : 类型 w) [交换半环 R] [半环 A] [半环 B]
  继承: 环态射 A B
  公理与运算 (1 个):
    - commutes' : 对任意 r : R, toFun (algebraMap R A r) = algebraMap R B r
-/
structure AlgHom (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] extends RingHom A B where
  commutes' : forall r : R, toFun (algebraMap R A r) = algebraMap R B r

/-- Reinterpret an `AlgHom` as a `RingHom` -/
add_decl_doc AlgHom.toRingHom

@[inherit_doc AlgHom]
infixr:25 " ->ₐ " => AlgHom _

@[inherit_doc]
notation:25 A " ->ₐ[" R "] " B => AlgHom R A B

/--
Definition of `AlgHomClass` / `AlgHomClass` 的定义

English:
class AlgHomClass
  parameters: (F : Type*) (R A B : outParam Type*)
  extends: RingHomClass F A B
  axioms and operations (1):
    - commutes : forall (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r

中文:
类 代数态射类
  参数: (F : 类型) (R A B : outParam 类型)
  继承: 环态射类 F A B
  公理与运算 (1 个):
    - commutes : 对任意 (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r
-/
class AlgHomClass (F : Type*) (R A B : outParam Type*)
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] [FunLike F A B] : Prop
    extends RingHomClass F A B where
  commutes : forall (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r

-- For now, don't replace `AlgHom.commutes` and `AlgHomClass.commutes` with the more generic lemma.
-- The file `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/FundamentalCone.lean` slows down by
-- 15% if we would do so (see benchmark on PR https://github.com/leanprover-community/mathlib4/pull/18040).
-- attribute [simp] AlgHomClass.commutes

namespace AlgHomClass

variable {R A B F : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] [FunLike F A B]

-- see Note [lower instance priority]
instance (priority := 100) linearMapClass [AlgHomClass F R A B] : LinearMapClass F R A B :=
  { ‹AlgHomClass F R A B› with
    map_smulₛₗ := fun f r x => by
      simp only [Algebra.smul_def, map_mul, commutes, RingHom.id_apply] }

/-- Turn an element of a type `F` satisfying `AlgHomClass F α β` into an actual
`AlgHom`. This is declared as the default coercion from `F` to `α →+* β`. -/
@[coe]
/--
Definition of `toAlgHom` / `toAlgHom` 的定义

English:
definition toAlgHom
  signature: {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F)
  body: (f : A ->+* B)
  toFun := f
  commutes' := AlgHomClass.commutes f

中文:
定义 toAlgHom
  签名: {F : 类型} [函数状 F A B] [代数态射类 F R A B] (f : F)
  定义体: (f : A ->+* B)
  toFun := f
  commutes' := AlgHomClass.commutes f
-/
def toAlgHom {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) : A ->ₐ[R] B where
  __ := (f : A ->+* B)
  toFun := f
  commutes' := AlgHomClass.commutes f

end AlgHomClass

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

section Semiring

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]
variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

/--
Instance `funLike` / 实例 `funLike`

English:
instance funLike
  signature: : FunLike (A ->ₐ[R] B) A B where
  body: f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩
    rcases g with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩
    congr

中文:
实例 funLike
  签名: : 函数状 (A ->ₐ[R] B) A B where
  定义体: f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩
    rcases g with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩
    congr

Depends on / 依赖: f.toFun
-/
instance funLike : FunLike (A ->ₐ[R] B) A B where
  coe f := f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩
    rcases g with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩
    congr

/--
Instance `algHomClass` / 实例 `algHomClass`

English:
instance algHomClass
  signature: : AlgHomClass (A ->ₐ[R] B) R A B where
  body: f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  commutes f := f.commutes'

中文:
实例 algHomClass
  签名: : 代数态射类 (A ->ₐ[R] B) R A B where
  定义体: f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  commutes f := f.commutes'

Depends on / 依赖: f.map_add, map_add
-/
instance algHomClass : AlgHomClass (A ->ₐ[R] B) R A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  commutes f := f.commutes'

/--
lemma `_root_.AlgHomClass.toLinearMap_toAlgHom` / 引理 `_root_.AlgHomClass.toLinearMap_toAlgHom`

English:
lemma _root_.AlgHomClass.toLinearMap_toAlgHom
  statement: {R A B F : Type*} [CommSemiring R]
  proof: rfl

中文:
引理 _root_.代数态射类.toLinearMap_toAlgHom
  结论: {R A B F : 类型} [交换半环 R]
  证明: rfl
-/
@[simp] lemma _root_.AlgHomClass.toLinearMap_toAlgHom {R A B F : Type*} [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] [FunLike F A B] [AlgHomClass F R A B]
    (f : F) : (AlgHomClass.toAlgHom f : A ->ₗ[R] B) = f := rfl

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: {R : Type u} {α : Type v} {β : Type w} [CommSemiring R]
  body: f

initialize_simps_projections AlgHom (toFun -> apply)

@[simp]

中文:
定义 Simps.apply
  签名: {R : 类型u} {α : 类型v} {β : 类型 w} [交换半环 R]
  定义体: f

initialize_simps_projections AlgHom (toFun -> apply)

@[simp]
-/
def Simps.apply {R : Type u} {α : Type v} {β : Type w} [CommSemiring R]
    [Semiring α] [Semiring β] [Algebra R α] [Algebra R β] (f : α ->ₐ[R] β) : α -> β := f

initialize_simps_projections AlgHom (toFun -> apply)

@[simp]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F)
  proof: rfl

@[simp]

中文:
定理 coe_coe
  条件: {F : 类型} [函数状 F A B] [代数态射类 F R A B] (f : F)
  证明: rfl

@[simp]
-/
protected theorem coe_coe {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) :
    ⇑(AlgHomClass.toAlgHom f : A ->ₐ[R] B) = f :=
  rfl

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (f : A ->ₐ[R] B)
  statement: f.toFun = f
  proof: rfl

中文:
定理 toFun_eq_coe
  条件: (f : A ->ₐ[R] B)
  结论: f.toFun = f
  证明: rfl
-/
theorem toFun_eq_coe (f : A ->ₐ[R] B) : f.toFun = f :=
  rfl

/-- Turn an algebra homomorphism into the corresponding multiplicative monoid homomorphism. -/
@[coe]
/--
Definition of `toMonoidHom'` / `toMonoidHom'` 的定义

English:
definition toMonoidHom'
  signature: (f : A ->ₐ[R] B)
  body: (f : A ->+* B)

中文:
定义 toMonoidHom'
  签名: (f : A ->ₐ[R] B)
  定义体: (f : A ->+* B)
-/
def toMonoidHom' (f : A ->ₐ[R] B) : A ->* B := (f : A ->+* B)

/--
Instance `coeOutMonoidHom` / 实例 `coeOutMonoidHom`

English:
instance coeOutMonoidHom
  signature: : CoeOut (A ->ₐ[R] B) (A ->* B)
  body: ⟨AlgHom.toMonoidHom'⟩

中文:
实例 coeOutMonoidHom
  签名: : CoeOut (A ->ₐ[R] B) (A ->* B)
  定义体: ⟨AlgHom.toMonoidHom'⟩

Depends on / 依赖: AlgHom, AlgHom.toMonoidHom, toMonoidHom
-/
instance coeOutMonoidHom : CoeOut (A ->ₐ[R] B) (A ->* B) :=
  ⟨AlgHom.toMonoidHom'⟩

/-- Turn an algebra homomorphism into the corresponding additive monoid homomorphism. -/
@[coe]
/--
Definition of `toAddMonoidHom'` / `toAddMonoidHom'` 的定义

English:
definition toAddMonoidHom'
  signature: (f : A ->ₐ[R] B)
  body: (f : A ->+* B)

中文:
定义 toAddMonoidHom'
  签名: (f : A ->ₐ[R] B)
  定义体: (f : A ->+* B)
-/
def toAddMonoidHom' (f : A ->ₐ[R] B) : A ->+ B := (f : A ->+* B)

/--
Instance `coeOutAddMonoidHom` / 实例 `coeOutAddMonoidHom`

English:
instance coeOutAddMonoidHom
  signature: : CoeOut (A ->ₐ[R] B) (A ->+ B)
  body: ⟨AlgHom.toAddMonoidHom'⟩

@[simp]

中文:
实例 coeOutAddMonoidHom
  签名: : CoeOut (A ->ₐ[R] B) (A ->+ B)
  定义体: ⟨AlgHom.toAddMonoidHom'⟩

@[simp]

Depends on / 依赖: AlgHom, AlgHom.toAddMonoidHom, toAddMonoidHom
-/
instance coeOutAddMonoidHom : CoeOut (A ->ₐ[R] B) (A ->+ B) :=
  ⟨AlgHom.toAddMonoidHom'⟩

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: {f : A ->+* B} (h)
  statement: ((⟨f, h⟩ : A ->ₐ[R] B) : A -> B) = f
  proof: rfl

@[norm_cast]

中文:
定理 coe_mk
  条件: {f : A ->+* B} (h)
  结论: ((⟨f, h⟩ : A ->ₐ[R] B) : A -> B) = f
  证明: rfl

@[norm_cast]
-/
theorem coe_mk {f : A ->+* B} (h) : ((⟨f, h⟩ : A ->ₐ[R] B) : A -> B) = f :=
  rfl

@[norm_cast]
/--
theorem `coe_mks` / 定理 `coe_mks`

English:
theorem coe_mks
  given: {f : A -> B} (h₁ h₂ h₃ h₄ h₅)
  statement: ⇑(⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩ : A ->ₐ[R] B) = f
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_mks
  条件: {f : A -> B} (h₁ h₂ h₃ h₄ h₅)
  结论: ⇑(⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩ : A ->ₐ[R] B) = f
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_mks {f : A -> B} (h₁ h₂ h₃ h₄ h₅) : ⇑(⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩ : A ->ₐ[R] B) = f :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_ringHom_mk` / 定理 `coe_ringHom_mk`

English:
theorem coe_ringHom_mk
  given: {f : A ->+* B} (h)
  statement: ((⟨f, h⟩ : A ->ₐ[R] B) : A ->+* B) = f
  proof: rfl

中文:
定理 coe_ringHom_mk
  条件: {f : A ->+* B} (h)
  结论: ((⟨f, h⟩ : A ->ₐ[R] B) : A ->+* B) = f
  证明: rfl
-/
theorem coe_ringHom_mk {f : A ->+* B} (h) : ((⟨f, h⟩ : A ->ₐ[R] B) : A ->+* B) = f :=
  rfl

-- make the coercion the simp-normal form
@[simp]
/--
theorem `toRingHom_eq_coe` / 定理 `toRingHom_eq_coe`

English:
theorem toRingHom_eq_coe
  given: (f : A ->ₐ[R] B)
  statement: f.toRingHom = f
  proof: rfl

@[simp, norm_cast]

中文:
定理 toRingHom_eq_coe
  条件: (f : A ->ₐ[R] B)
  结论: f.toRingHom = f
  证明: rfl

@[simp, norm_cast]
-/
theorem toRingHom_eq_coe (f : A ->ₐ[R] B) : f.toRingHom = f :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_toRingHom` / 定理 `coe_toRingHom`

English:
theorem coe_toRingHom
  given: (f : A ->ₐ[R] B)
  statement: ⇑(f : A ->+* B) = f
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_toRingHom
  条件: (f : A ->ₐ[R] B)
  结论: ⇑(f : A ->+* B) = f
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_toRingHom (f : A ->ₐ[R] B) : ⇑(f : A ->+* B) = f :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_toMonoidHom` / 定理 `coe_toMonoidHom`

English:
theorem coe_toMonoidHom
  given: (f : A ->ₐ[R] B)
  statement: ⇑(f : A ->* B) = f
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_toMonoidHom
  条件: (f : A ->ₐ[R] B)
  结论: ⇑(f : A ->* B) = f
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_toMonoidHom (f : A ->ₐ[R] B) : ⇑(f : A ->* B) = f :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_toAddMonoidHom` / 定理 `coe_toAddMonoidHom`

English:
theorem coe_toAddMonoidHom
  given: (f : A ->ₐ[R] B)
  statement: ⇑(f : A ->+ B) = f
  proof: rfl

@[simp]

中文:
定理 coe_toAddMonoidHom
  条件: (f : A ->ₐ[R] B)
  结论: ⇑(f : A ->+ B) = f
  证明: rfl

@[simp]
-/
theorem coe_toAddMonoidHom (f : A ->ₐ[R] B) : ⇑(f : A ->+ B) = f :=
  rfl

@[simp]
/--
theorem `toRingHom_toMonoidHom` / 定理 `toRingHom_toMonoidHom`

English:
theorem toRingHom_toMonoidHom
  given: (f : A ->ₐ[R] B)
  statement: ((f : A ->+* B) : A ->* B) = f
  proof: rfl

@[simp]

中文:
定理 toRingHom_toMonoidHom
  条件: (f : A ->ₐ[R] B)
  结论: ((f : A ->+* B) : A ->* B) = f
  证明: rfl

@[simp]
-/
theorem toRingHom_toMonoidHom (f : A ->ₐ[R] B) : ((f : A ->+* B) : A ->* B) = f :=
  rfl

@[simp]
/--
theorem `toRingHom_toAddMonoidHom` / 定理 `toRingHom_toAddMonoidHom`

English:
theorem toRingHom_toAddMonoidHom
  given: (f : A ->ₐ[R] B)
  statement: ((f : A ->+* B) : A ->+ B) = f
  proof: rfl

中文:
定理 toRingHom_toAddMonoidHom
  条件: (f : A ->ₐ[R] B)
  结论: ((f : A ->+* B) : A ->+ B) = f
  证明: rfl
-/
theorem toRingHom_toAddMonoidHom (f : A ->ₐ[R] B) : ((f : A ->+* B) : A ->+ B) = f :=
  rfl

variable (φ : A ->ₐ[R] B)

/--
theorem `coe_fn_injective` / 定理 `coe_fn_injective`

English:
theorem coe_fn_injective
  statement: @Function.Injective (A ->ₐ[R] B) (A -> B) (↑)
  proof: DFunLike.coe_injective

中文:
定理 coe_fn_injective
  结论: @函数.单射 (A ->ₐ[R] B) (A -> B) (↑)
  证明: DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_fn_injective : @Function.Injective (A ->ₐ[R] B) (A -> B) (↑) :=
  DFunLike.coe_injective

/--
theorem `coe_fn_inj` / 定理 `coe_fn_inj`

English:
theorem coe_fn_inj
  given: {φ₁ φ₂ : A ->ₐ[R] B}
  statement: (φ₁ : A -> B) = φ₂ ↔ φ₁ = φ₂
  proof: DFunLike.coe_fn_eq

中文:
定理 coe_fn_inj
  条件: {φ₁ φ₂ : A ->ₐ[R] B}
  结论: (φ₁ : A -> B) = φ₂ ↔ φ₁ = φ₂
  证明: DFunLike.coe_fn_eq

Depends on / 依赖: DFunLike, DFunLike.coe_fn_eq, coe_fn_eq
-/
theorem coe_fn_inj {φ₁ φ₂ : A ->ₐ[R] B} : (φ₁ : A -> B) = φ₂ ↔ φ₁ = φ₂ :=
  DFunLike.coe_fn_eq

/--
theorem `coe_ringHom_injective` / 定理 `coe_ringHom_injective`

English:
theorem coe_ringHom_injective
  statement: Function.Injective ((↑) : (A ->ₐ[R] B) -> A ->+* B)
  proof: fun φ₁ φ₂ H =>
coe_fn_injective show ((φ₁ : A ->+* B) : A -> B) = ((φ₂ : A ->+* B) : A -> B) from congr_arg _ H

中文:
定理 coe_ringHom_injective
  结论: 函数.单射 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
  证明: fun φ₁ φ₂ H =>
coe_fn_injective show ((φ₁ : A ->+* B) : A -> B) = ((φ₂ : A ->+* B) : A -> B) from congr_arg _ H
-/
theorem coe_ringHom_injective : Function.Injective ((↑) : (A ->ₐ[R] B) -> A ->+* B) := fun φ₁ φ₂ H =>
coe_fn_injective show ((φ₁ : A ->+* B) : A -> B) = ((φ₂ : A ->+* B) : A -> B) from congr_arg _ H

/--
theorem `coe_monoidHom_injective` / 定理 `coe_monoidHom_injective`

English:
theorem coe_monoidHom_injective
  statement: Function.Injective ((↑) : (A ->ₐ[R] B) -> A ->* B)
  proof: RingHom.coe_monoidHom_injective.comp coe_ringHom_injective

中文:
定理 coe_monoidHom_injective
  结论: 函数.单射 ((↑) : (A ->ₐ[R] B) -> A ->* B)
  证明: RingHom.coe_monoidHom_injective.comp coe_ringHom_injective

Depends on / 依赖: RingHom, RingHom.coe_monoidHom_injective.comp, coe_monoidHom_injective, coe_ringHom_injective
-/
theorem coe_monoidHom_injective : Function.Injective ((↑) : (A ->ₐ[R] B) -> A ->* B) :=
  RingHom.coe_monoidHom_injective.comp coe_ringHom_injective

/--
theorem `coe_addMonoidHom_injective` / 定理 `coe_addMonoidHom_injective`

English:
theorem coe_addMonoidHom_injective
  statement: Function.Injective ((↑) : (A ->ₐ[R] B) -> A ->+ B)
  proof: RingHom.coe_addMonoidHom_injective.comp coe_ringHom_injective

中文:
定理 coe_addMonoidHom_injective
  结论: 函数.单射 ((↑) : (A ->ₐ[R] B) -> A ->+ B)
  证明: RingHom.coe_addMonoidHom_injective.comp coe_ringHom_injective

Depends on / 依赖: RingHom, RingHom.coe_addMonoidHom_injective.comp, coe_addMonoidHom_injective, coe_ringHom_injective
-/
theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (A ->ₐ[R] B) -> A ->+ B) :=
  RingHom.coe_addMonoidHom_injective.comp coe_ringHom_injective

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {φ₁ φ₂ : A ->ₐ[R] B} (H : φ₁ = φ₂) (x : A)
  statement: φ₁ x = φ₂ x
  proof: DFunLike.congr_fun H x

中文:
定理 congr_fun
  条件: {φ₁ φ₂ : A ->ₐ[R] B} (H : φ₁ = φ₂) (x : A)
  结论: φ₁ x = φ₂ x
  证明: DFunLike.congr_fun H x
-/
protected theorem congr_fun {φ₁ φ₂ : A ->ₐ[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x :=
  DFunLike.congr_fun H x

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: (φ : A ->ₐ[R] B) {x y : A} (h : x = y)
  statement: φ x = φ y
  proof: DFunLike.congr_arg φ h

@[ext]

中文:
定理 congr_arg
  条件: (φ : A ->ₐ[R] B) {x y : A} (h : x = y)
  结论: φ x = φ y
  证明: DFunLike.congr_arg φ h

@[ext]
-/
protected theorem congr_arg (φ : A ->ₐ[R] B) {x y : A} (h : x = y) : φ x = φ y :=
  DFunLike.congr_arg φ h

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x)
  statement: φ₁ = φ₂
  proof: DFunLike.ext _ _ H

@[simp]

中文:
定理 ext
  条件: {φ₁ φ₂ : A ->ₐ[R] B} (H : 对任意 x, φ₁ x = φ₂ x)
  结论: φ₁ = φ₂
  证明: DFunLike.ext _ _ H

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
  DFunLike.ext _ _ H

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: {f : A ->ₐ[R] B} (h₁ h₂ h₃ h₄ h₅)
  statement: (⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩ : A ->ₐ[R] B) = f
  proof: rfl

中文:
定理 mk_coe
  条件: {f : A ->ₐ[R] B} (h₁ h₂ h₃ h₄ h₅)
  结论: (⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩ : A ->ₐ[R] B) = f
  证明: rfl
-/
theorem mk_coe {f : A ->ₐ[R] B} (h₁ h₂ h₃ h₄ h₅) : (⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩ : A ->ₐ[R] B) = f :=
  rfl

/--
lemma `addHomMk_coe` / 引理 `addHomMk_coe`

English:
lemma addHomMk_coe
  given: (f : A ->ₐ[R] B)
  statement: AddHom.mk f (map_add f) = f
  proof: rfl

@[simp]

中文:
引理 addHomMk_coe
  条件: (f : A ->ₐ[R] B)
  结论: 加法半群态射.mk f (map_add f) = f
  证明: rfl

@[simp]
-/
@[simp] lemma addHomMk_coe (f : A ->ₐ[R] B) : AddHom.mk f (map_add f) = f := rfl

@[simp]
/--
theorem `commutes` / 定理 `commutes`

English:
theorem commutes
  given: (r : R)
  statement: φ (algebraMap R A r) = algebraMap R B r
  proof: φ.commutes' r

中文:
定理 commutes
  条件: (r : R)
  结论: φ (algebraMap R A r) = algebraMap R B r
  证明: φ.commutes' r

Depends on / 依赖: commutes
-/
theorem commutes (r : R) : φ (algebraMap R A r) = algebraMap R B r :=
  φ.commutes' r

/--
theorem `comp_algebraMap` / 定理 `comp_algebraMap`

English:
theorem comp_algebraMap
  statement: (φ : A ->+* B).comp (algebraMap R A) = algebraMap R B
  proof: RingHom.ext φ.commutes

中文:
定理 comp_algebraMap
  结论: (φ : A ->+* B).comp (algebraMap R A) = algebraMap R B
  证明: RingHom.ext φ.commutes

Depends on / 依赖: RingHom, RingHom.ext, commutes
-/
theorem comp_algebraMap : (φ : A ->+* B).comp (algebraMap R A) = algebraMap R B :=
RingHom.ext φ.commutes

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (f : A ->+* B) (h : forall (c : R) (x), f (c • x) = c • f x)
  body: { f with
    toFun := f
    commutes' := fun c => by simp only [Algebra.algebraMap_eq_smul_one, h, f.map_one] }

@[simp]

中文:
定义 mk'
  签名: (f : A ->+* B) (h : 对任意 (c : R) (x), f (c • x) = c • f x)
  定义体: { f with
    toFun := f
    commutes' := fun c => by simp only [Algebra.algebraMap_eq_smul_one, h, f.map_one] }

@[simp]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one, commutes, f.map_one, map_one
-/
def mk' (f : A ->+* B) (h : forall (c : R) (x), f (c • x) = c • f x) : A ->ₐ[R] B :=
  { f with
    toFun := f
    commutes' := fun c => by simp only [Algebra.algebraMap_eq_smul_one, h, f.map_one] }

@[simp]
/--
theorem `coe_mk'` / 定理 `coe_mk'`

English:
theorem coe_mk'
  given: (f : A ->+* B) (h : forall (c : R) (x), f (c • x) = c • f x)
  statement: ⇑(mk' f h) = f
  proof: rfl

中文:
定理 coe_mk'
  条件: (f : A ->+* B) (h : 对任意 (c : R) (x), f (c • x) = c • f x)
  结论: ⇑(mk' f h) = f
  证明: rfl
-/
theorem coe_mk' (f : A ->+* B) (h : forall (c : R) (x), f (c • x) = c • f x) : ⇑(mk' f h) = f :=
  rfl

section

variable (R A)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : A ->ₐ[R] A
  body: { RingHom.id A with commutes' := fun _ => rfl }

@[simp, norm_cast]

中文:
定义 id
  签名: : A ->ₐ[R] A
  定义体: { RingHom.id A with commutes' := fun _ => rfl }

@[simp, norm_cast]
-/
protected def id : A ->ₐ[R] A :=
  { RingHom.id A with commutes' := fun _ => rfl }

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(AlgHom.id R A) = id
  proof: rfl

@[simp]

中文:
定理 coe_id
  结论: ⇑(代数态射.id R A) = id
  证明: rfl

@[simp]
-/
theorem coe_id : ⇑(AlgHom.id R A) = id :=
  rfl

@[simp]
/--
theorem `id_toRingHom` / 定理 `id_toRingHom`

English:
theorem id_toRingHom
  statement: (AlgHom.id R A : A ->+* A) = RingHom.id _
  proof: rfl

中文:
定理 id_toRingHom
  结论: (代数态射.id R A : A ->+* A) = 环态射.id _
  证明: rfl
-/
theorem id_toRingHom : (AlgHom.id R A : A ->+* A) = RingHom.id _ :=
  rfl

end

/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (p : A)
  statement: AlgHom.id R A p = p
  proof: rfl

中文:
定理 id_apply
  条件: (p : A)
  结论: 代数态射.id R A p = p
  证明: rfl
-/
theorem id_apply (p : A) : AlgHom.id R A p = p :=
  rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B)
  body: { φ₁.toRingHom.comp ↑φ₂ with
    commutes' := fun r : R => by rw [← φ₁.commutes, ← φ₂.commutes]; rfl }

@[simp]

中文:
定义 comp
  签名: (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B)
  定义体: { φ₁.toRingHom.comp ↑φ₂ with
    commutes' := fun r : R => by rw [← φ₁.commutes, ← φ₂.commutes]; rfl }

@[simp]

Depends on / 依赖: commutes, toRingHom, toRingHom.comp
-/
def comp (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) : A ->ₐ[R] C :=
  { φ₁.toRingHom.comp ↑φ₂ with
    commutes' := fun r : R => by rw [← φ₁.commutes, ← φ₂.commutes]; rfl }

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B)
  statement: ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂
  proof: rfl

中文:
定理 coe_comp
  条件: (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B)
  结论: ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂
  证明: rfl
-/
theorem coe_comp (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ :=
  rfl

/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) (p : A)
  statement: φ₁.comp φ₂ p = φ₁ (φ₂ p)
  proof: rfl

中文:
定理 comp_apply
  条件: (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) (p : A)
  结论: φ₁.comp φ₂ p = φ₁ (φ₂ p)
  证明: rfl
-/
theorem comp_apply (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) (p : A) : φ₁.comp φ₂ p = φ₁ (φ₂ p) :=
  rfl

/--
theorem `comp_toRingHom` / 定理 `comp_toRingHom`

English:
theorem comp_toRingHom
  given: (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B)
  proof: rfl

@[simp]

中文:
定理 comp_toRingHom
  条件: (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B)
  证明: rfl

@[simp]
-/
theorem comp_toRingHom (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) :
    (φ₁.comp φ₂ : A ->+* C) = (φ₁ : B ->+* C).comp ↑φ₂ :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  statement: φ.comp (AlgHom.id R A) = φ
  proof: rfl

@[simp]

中文:
定理 comp_id
  结论: φ.comp (代数态射.id R A) = φ
  证明: rfl

@[simp]
-/
theorem comp_id : φ.comp (AlgHom.id R A) = φ :=
  rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  statement: (AlgHom.id R B).comp φ = φ
  proof: rfl

中文:
定理 id_comp
  结论: (代数态射.id R B).comp φ = φ
  证明: rfl
-/
theorem id_comp : (AlgHom.id R B).comp φ = φ :=
  rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (φ₁ : C ->ₐ[R] D) (φ₂ : B ->ₐ[R] C) (φ₃ : A ->ₐ[R] B)
  proof: rfl

中文:
定理 comp_assoc
  条件: (φ₁ : C ->ₐ[R] D) (φ₂ : B ->ₐ[R] C) (φ₃ : A ->ₐ[R] B)
  证明: rfl
-/
theorem comp_assoc (φ₁ : C ->ₐ[R] D) (φ₂ : B ->ₐ[R] C) (φ₃ : A ->ₐ[R] B) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
  rfl

instance {φ₁ : B ->ₐ[R] C} {φ₂ : A ->ₐ[R] B} :
    RingHomCompTriple φ₂.toRingHom φ₁.toRingHom (φ₁.comp φ₂).toRingHom := ⟨rfl⟩

/--
Definition of `toLinearMap` / `toLinearMap` 的定义

English:
definition toLinearMap
  signature: : A ->ₗ[R] B where
  body: φ
  map_add' := map_add _
  map_smul' := map_smul _

@[simp]

中文:
定义 toLinearMap
  签名: : A ->ₗ[R] B where
  定义体: φ
  map_add' := map_add _
  map_smul' := map_smul _

@[simp]
-/
def toLinearMap : A ->ₗ[R] B where
  toFun := φ
  map_add' := map_add _
  map_smul' := map_smul _

@[simp]
/--
theorem `toLinearMap_apply` / 定理 `toLinearMap_apply`

English:
theorem toLinearMap_apply
  given: (p : A)
  statement: φ.toLinearMap p = φ p
  proof: rfl

@[simp]

中文:
定理 toLinearMap_apply
  条件: (p : A)
  结论: φ.toLinearMap p = φ p
  证明: rfl

@[simp]
-/
theorem toLinearMap_apply (p : A) : φ.toLinearMap p = φ p :=
  rfl

@[simp]
/--
lemma `coe_toLinearMap` / 引理 `coe_toLinearMap`

English:
lemma coe_toLinearMap
  statement: ⇑φ.toLinearMap = φ
  proof: rfl

中文:
引理 coe_toLinearMap
  结论: ⇑φ.toLinearMap = φ
  证明: rfl
-/
lemma coe_toLinearMap : ⇑φ.toLinearMap = φ := rfl

/--
theorem `toLinearMap_injective` / 定理 `toLinearMap_injective`

English:
theorem toLinearMap_injective
  proof: fun _φ₁ _φ₂ h =>
ext LinearMap.congr_fun h

@[simp]

中文:
定理 toLinearMap_injective
  证明: fun _φ₁ _φ₂ h =>
ext LinearMap.congr_fun h

@[simp]
-/
theorem toLinearMap_injective :
    Function.Injective (toLinearMap : _ -> A ->ₗ[R] B) := fun _φ₁ _φ₂ h =>
ext LinearMap.congr_fun h

@[simp]
/--
theorem `comp_toLinearMap` / 定理 `comp_toLinearMap`

English:
theorem comp_toLinearMap
  given: (f : A ->ₐ[R] B) (g : B ->ₐ[R] C)
  proof: rfl

@[simp]

中文:
定理 comp_toLinearMap
  条件: (f : A ->ₐ[R] B) (g : B ->ₐ[R] C)
  证明: rfl

@[simp]
-/
theorem comp_toLinearMap (f : A ->ₐ[R] B) (g : B ->ₐ[R] C) :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl

@[simp]
/--
theorem `toLinearMap_id` / 定理 `toLinearMap_id`

English:
theorem toLinearMap_id
  statement: toLinearMap (AlgHom.id R A) = LinearMap.id
  proof: rfl

中文:
定理 toLinearMap_id
  结论: toLinearMap (代数态射.id R A) = 线性映射.id
  证明: rfl
-/
theorem toLinearMap_id : toLinearMap (AlgHom.id R A) = LinearMap.id :=
  rfl

/--
lemma `linearMapMk_toAddHom` / 引理 `linearMapMk_toAddHom`

English:
lemma linearMapMk_toAddHom
  given: (f : A ->ₐ[R] B)
  statement: LinearMap.mk f (map_smul f) = f.toLinearMap
  proof: rfl

中文:
引理 linearMapMk_toAddHom
  条件: (f : A ->ₐ[R] B)
  结论: 线性映射.mk f (map_smul f) = f.toLinearMap
  证明: rfl
-/
@[simp] lemma linearMapMk_toAddHom (f : A ->ₐ[R] B) : LinearMap.mk f (map_smul f) = f.toLinearMap :=
  rfl

/-- Promote a `LinearMap` to an `AlgHom` by supplying proofs about the behavior on `1` and `*`. -/
@[simps]
/--
Definition of `ofLinearMap` / `ofLinearMap` 的定义

English:
definition ofLinearMap
  signature: (f : A ->ₗ[R] B) (map_one : f 1 = 1) (map_mul : forall x y, f (x * y) = f x * f y)
  body: { f.toAddMonoidHom with
    toFun := f
    map_one' := map_one
    map_mul' := map_mul
    commutes' c := by simp only [Algebra.algebraMap_eq_smul_one, f.map_smul, map_one] }

@[simp]

中文:
定义 ofLinearMap
  签名: (f : A ->ₗ[R] B) (map_one : f 1 = 1) (map_mul : 对任意 x y, f (x * y) = f x * f y)
  定义体: { f.toAddMonoidHom with
    toFun := f
    map_one' := map_one
    map_mul' := map_mul
    commutes' c := by simp only [Algebra.algebraMap_eq_smul_one, f.map_smul, map_one] }

@[simp]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one, commutes, f.map_smul, f.toAddMonoidHom, map_mul, map_one, map_smul, toAddMonoidHom
-/
def ofLinearMap (f : A ->ₗ[R] B) (map_one : f 1 = 1) (map_mul : forall x y, f (x * y) = f x * f y) :
    A ->ₐ[R] B :=
  { f.toAddMonoidHom with
    toFun := f
    map_one' := map_one
    map_mul' := map_mul
    commutes' c := by simp only [Algebra.algebraMap_eq_smul_one, f.map_smul, map_one] }

@[simp]
/--
theorem `ofLinearMap_toLinearMap` / 定理 `ofLinearMap_toLinearMap`

English:
theorem ofLinearMap_toLinearMap
  given: (map_one) (map_mul)
  proof: rfl

@[simp]

中文:
定理 ofLinearMap_toLinearMap
  条件: (map_one) (map_mul)
  证明: rfl

@[simp]
-/
theorem ofLinearMap_toLinearMap (map_one) (map_mul) :
    ofLinearMap φ.toLinearMap map_one map_mul = φ :=
  rfl

@[simp]
/--
theorem `toLinearMap_ofLinearMap` / 定理 `toLinearMap_ofLinearMap`

English:
theorem toLinearMap_ofLinearMap
  given: (f : A ->ₗ[R] B) (map_one) (map_mul)
  proof: rfl

@[simp]

中文:
定理 toLinearMap_ofLinearMap
  条件: (f : A ->ₗ[R] B) (map_one) (map_mul)
  证明: rfl

@[simp]
-/
theorem toLinearMap_ofLinearMap (f : A ->ₗ[R] B) (map_one) (map_mul) :
    toLinearMap (ofLinearMap f map_one map_mul) = f :=
  rfl

@[simp]
/--
theorem `ofLinearMap_id` / 定理 `ofLinearMap_id`

English:
theorem ofLinearMap_id
  given: (map_one) (map_mul)
  proof: rfl

中文:
定理 ofLinearMap_id
  条件: (map_one) (map_mul)
  证明: rfl
-/
theorem ofLinearMap_id (map_one) (map_mul) :
    ofLinearMap LinearMap.id map_one map_mul = AlgHom.id R A :=
  rfl

/--
theorem `map_smul_of_tower` / 定理 `map_smul_of_tower`

English:
theorem map_smul_of_tower
  statement: {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A B R' R] (r : R')
  proof: φ.toLinearMap.map_smul_of_tower r x

@[simps -isSimp toSemigroup_toMul_mul toOne_one]

中文:
定理 map_smul_of_tower
  结论: {R'} [标量乘法 R' A] [标量乘法 R' B] [线性映射.余mpatibleSMul A B R' R] (r : R')
  证明: φ.toLinearMap.map_smul_of_tower r x

@[simps -isSimp toSemigroup_toMul_mul toOne_one]

Depends on / 依赖: map_smul_of_tower, toLinearMap, toLinearMap.map_smul_of_tower
-/
theorem map_smul_of_tower {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A B R' R] (r : R')
    (x : A) : φ (r • x) = r • φ x :=
  φ.toLinearMap.map_smul_of_tower r x

@[simps -isSimp toSemigroup_toMul_mul toOne_one]
/--
Instance `End` / 实例 `End`

English:
instance End
  signature: : Monoid (A ->ₐ[R] A) where
  body: comp
  mul_assoc _ _ _ := rfl
  one := AlgHom.id R A
  one_mul _ := rfl
  mul_one _ := rfl

@[simp]

中文:
实例 End
  签名: : 幺半群 (A ->ₐ[R] A) where
  定义体: comp
  mul_assoc _ _ _ := rfl
  one := AlgHom.id R A
  one_mul _ := rfl
  mul_one _ := rfl

@[simp]
-/
instance End : Monoid (A ->ₐ[R] A) where
  mul := comp
  mul_assoc _ _ _ := rfl
  one := AlgHom.id R A
  one_mul _ := rfl
  mul_one _ := rfl

@[simp]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (x : A)
  statement: (1 : A ->ₐ[R] A) x = x
  proof: rfl

@[simp]

中文:
定理 one_apply
  条件: (x : A)
  结论: (1 : A ->ₐ[R] A) x = x
  证明: rfl

@[simp]
-/
theorem one_apply (x : A) : (1 : A ->ₐ[R] A) x = x :=
  rfl

@[simp]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (φ ψ : A ->ₐ[R] A) (x : A)
  statement: (φ * ψ) x = φ (ψ x)
  proof: rfl

中文:
定理 mul_apply
  条件: (φ ψ : A ->ₐ[R] A) (x : A)
  结论: (φ * ψ) x = φ (ψ x)
  证明: rfl
-/
theorem mul_apply (φ ψ : A ->ₐ[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
  rfl

/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (φ : A ->ₐ[R] A) (n : Nat)
  statement: ⇑(φ ^ n) = φ^[n]
  proof: n.rec (by ext; simp) fun _ ih => by ext; simp [pow_succ, ih]

中文:
定理 coe_pow
  条件: (φ : A ->ₐ[R] A) (n : 自然数)
  结论: ⇑(φ ^ n) = φ^[n]
  证明: n.rec (by ext; simp) fun _ ih => by ext; simp [pow_succ, ih]
-/
@[simp] theorem coe_pow (φ : A ->ₐ[R] A) (n : Nat) : ⇑(φ ^ n) = φ^[n] :=
  n.rec (by ext; simp) fun _ ih => by ext; simp [pow_succ, ih]

/--
theorem `algebraMap_eq_apply` / 定理 `algebraMap_eq_apply`

English:
theorem algebraMap_eq_apply
  given: (f : A ->ₐ[R] B) {y : R} {x : A} (h : algebraMap R A y = x)
  proof: h ▸ (f.commutes _).symm

中文:
定理 algebraMap_eq_apply
  条件: (f : A ->ₐ[R] B) {y : R} {x : A} (h : algebraMap R A y = x)
  证明: h ▸ (f.commutes _).symm

Depends on / 依赖: commutes, f.commutes
-/
theorem algebraMap_eq_apply (f : A ->ₐ[R] B) {y : R} {x : A} (h : algebraMap R A y = x) :
    algebraMap R B y = f x :=
  h ▸ (f.commutes _).symm

/--
lemma `cancel_right` / 引理 `cancel_right`

English:
lemma cancel_right
  given: {g₁ g₂ : B ->ₐ[R] C} {f : A ->ₐ[R] B} (hf : Function.Surjective f)
  proof: ⟨fun h => AlgHom.ext hf.forall.2 (AlgHom.ext_iff.1 h), fun h => h ▸ rfl⟩

中文:
引理 cancel_right
  条件: {g₁ g₂ : B ->ₐ[R] C} {f : A ->ₐ[R] B} (hf : 函数.满射 f)
  证明: ⟨fun h => AlgHom.ext hf.forall.2 (AlgHom.ext_iff.1 h), fun h => h ▸ rfl⟩

Depends on / 依赖: AlgHom, AlgHom.ext, AlgHom.ext_iff, ext_iff, hf.forall
-/
lemma cancel_right {g₁ g₂ : B ->ₐ[R] C} {f : A ->ₐ[R] B} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => AlgHom.ext hf.forall.2 (AlgHom.ext_iff.1 h), fun h => h ▸ rfl⟩

/--
lemma `cancel_left` / 引理 `cancel_left`

English:
lemma cancel_left
  given: {g₁ g₂ : A ->ₐ[R] B} {f : B ->ₐ[R] C} (hf : Function.Injective f)
  proof: ⟨fun h => AlgHom.ext fun _ => hf.eq_iff.mp AlgHom.ext_iff.mp h _, fun h => h ▸ rfl⟩

中文:
引理 cancel_left
  条件: {g₁ g₂ : A ->ₐ[R] B} {f : B ->ₐ[R] C} (hf : 函数.单射 f)
  证明: ⟨fun h => AlgHom.ext fun _ => hf.eq_iff.mp AlgHom.ext_iff.mp h _, fun h => h ▸ rfl⟩

Depends on / 依赖: AlgHom, AlgHom.ext, AlgHom.ext_iff.mp, eq_iff, ext_iff, hf.eq_iff.mp
-/
lemma cancel_left {g₁ g₂ : A ->ₐ[R] B} {f : B ->ₐ[R] C} (hf : Function.Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
⟨fun h => AlgHom.ext fun _ => hf.eq_iff.mp AlgHom.ext_iff.mp h _, fun h => h ▸ rfl⟩

/--
Definition of `toEnd` / `toEnd` 的定义

English:
definition toEnd
  signature: : (A ->ₐ[R] A) ->* Module.End R A where
  body: toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 toEnd
  签名: : (A ->ₐ[R] A) ->* 模.End R A where
  定义体: toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl
-/
@[simps] def toEnd : (A ->ₐ[R] A) ->* Module.End R A where
  toFun := toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

end Semiring
end AlgHom

namespace IsScalarTower

variable (R S A : Type*) [CommSemiring R] [CommSemiring S] [Semiring A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/--
Definition of `toAlgHom` / `toAlgHom` 的定义

English:
definition toAlgHom
  signature: : S ->ₐ[R] A where
  body: algebraMap S A
  commutes' r := by simpa [Algebra.smul_def] using smul_assoc r (1 : S) (1 : A)

中文:
定义 toAlgHom
  签名: : S ->ₐ[R] A where
  定义体: algebraMap S A
  commutes' r := by simpa [Algebra.smul_def] using smul_assoc r (1 : S) (1 : A)

Depends on / 依赖: algebraMap
-/
def toAlgHom : S ->ₐ[R] A where
  toRingHom := algebraMap S A
  commutes' r := by simpa [Algebra.smul_def] using smul_assoc r (1 : S) (1 : A)

/--
theorem `toAlgHom_apply` / 定理 `toAlgHom_apply`

English:
theorem toAlgHom_apply
  given: (y : S)
  statement: toAlgHom R S A y = algebraMap S A y
  proof: rfl

@[simp]

中文:
定理 toAlgHom_apply
  条件: (y : S)
  结论: toAlgHom R S A y = algebraMap S A y
  证明: rfl

@[simp]
-/
theorem toAlgHom_apply (y : S) : toAlgHom R S A y = algebraMap S A y := rfl

@[simp]
/--
theorem `coe_toAlgHom` / 定理 `coe_toAlgHom`

English:
theorem coe_toAlgHom
  statement: ↑(toAlgHom R S A) = algebraMap S A
  proof: RingHom.ext fun _ => rfl

@[simp]

中文:
定理 coe_toAlgHom
  结论: ↑(toAlgHom R S A) = algebraMap S A
  证明: RingHom.ext fun _ => rfl

@[simp]

Depends on / 依赖: RingHom, RingHom.ext
-/
theorem coe_toAlgHom : ↑(toAlgHom R S A) = algebraMap S A :=
  RingHom.ext fun _ => rfl

@[simp]
/--
theorem `coe_toAlgHom'` / 定理 `coe_toAlgHom'`

English:
theorem coe_toAlgHom'
  statement: (toAlgHom R S A : S -> A) = algebraMap S A
  proof: rfl

中文:
定理 coe_toAlgHom'
  结论: (toAlgHom R S A : S -> A) = algebraMap S A
  证明: rfl
-/
theorem coe_toAlgHom' : (toAlgHom R S A : S -> A) = algebraMap S A := rfl

end IsScalarTower

/-- The algebra morphism underlying `algebraMap`. -/
alias Algebra.algHom := IsScalarTower.toAlgHom

alias Algebra.algHom_apply := IsScalarTower.toAlgHom_apply

namespace AlgHomClass

@[simp]
/--
lemma `toRingHom_toAlgHom` / 引理 `toRingHom_toAlgHom`

English:
lemma toRingHom_toAlgHom
  statement: {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
  proof: rfl

中文:
引理 toRingHom_toAlgHom
  结论: {R A B : 类型} [交换半环 R] [半环 A] [半环 B] [代数 R A]
  证明: rfl
-/
lemma toRingHom_toAlgHom {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
    [Algebra R B] {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) :
    RingHomClass.toRingHom (AlgHomClass.toAlgHom f) = RingHomClass.toRingHom f := rfl

end AlgHomClass

namespace RingHom

variable {R S : Type*}

/--
Definition of `toNatAlgHom` / `toNatAlgHom` 的定义

English:
definition toNatAlgHom
  signature: [Semiring R] [Semiring S] (f : R ->+* S)
  body: { f with
    toFun := f
    commutes' := fun n => by simp }

@[simp]

中文:
定义 to自然数AlgHom
  签名: [半环 R] [半环 S] (f : R ->+* S)
  定义体: { f with
    toFun := f
    commutes' := fun n => by simp }

@[simp]

Depends on / 依赖: commutes
-/
def toNatAlgHom [Semiring R] [Semiring S] (f : R ->+* S) : R ->ₐ[Nat] S :=
  { f with
    toFun := f
    commutes' := fun n => by simp }

@[simp]
/--
lemma `toNatAlgHom_coe` / 引理 `toNatAlgHom_coe`

English:
lemma toNatAlgHom_coe
  given: [Semiring R] [Semiring S] (f : R ->+* S)
  proof: rfl

中文:
引理 to自然数AlgHom_coe
  条件: [半环 R] [半环 S] (f : R ->+* S)
  证明: rfl
-/
lemma toNatAlgHom_coe [Semiring R] [Semiring S] (f : R ->+* S) :
    ⇑f.toNatAlgHom = ⇑f := rfl

/--
lemma `toNatAlgHom_apply` / 引理 `toNatAlgHom_apply`

English:
lemma toNatAlgHom_apply
  given: [Semiring R] [Semiring S] (f : R ->+* S) (x : R)
  proof: rfl

中文:
引理 to自然数AlgHom_apply
  条件: [半环 R] [半环 S] (f : R ->+* S) (x : R)
  证明: rfl
-/
lemma toNatAlgHom_apply [Semiring R] [Semiring S] (f : R ->+* S) (x : R) :
    f.toNatAlgHom x = f x := rfl

variable (R) (S) in
/-- Ring homomorphisms are the same as `ℕ`-algebra homomorphisms. -/
@[simps]
/--
Definition of `equivNatAlgHom` / `equivNatAlgHom` 的定义

English:
definition equivNatAlgHom
  signature: [Semiring R] [Semiring S]
  body: RingHom.toNatAlgHom
  invFun := AlgHom.toRingHom

中文:
定义 equiv自然数AlgHom
  签名: [半环 R] [半环 S]
  定义体: RingHom.toNatAlgHom
  invFun := AlgHom.toRingHom

Depends on / 依赖: RingHom, RingHom.toNatAlgHom, toNatAlgHom
-/
def equivNatAlgHom [Semiring R] [Semiring S] : (R ->+* S) ≃ (R ->ₐ[Nat] S) where
  toFun := RingHom.toNatAlgHom
  invFun := AlgHom.toRingHom

/--
Definition of `toIntAlgHom` / `toIntAlgHom` 的定义

English:
definition toIntAlgHom
  signature: [Ring R] [Ring S] (f : R ->+* S)
  body: { f with commutes' := fun n => by simp }

@[simp]

中文:
定义 to整数AlgHom
  签名: [环 R] [环 S] (f : R ->+* S)
  定义体: { f with commutes' := fun n => by simp }

@[simp]

Depends on / 依赖: commutes
-/
def toIntAlgHom [Ring R] [Ring S] (f : R ->+* S) : R ->ₐ[Int] S :=
  { f with commutes' := fun n => by simp }

@[simp]
/--
lemma `toIntAlgHom_coe` / 引理 `toIntAlgHom_coe`

English:
lemma toIntAlgHom_coe
  given: [Ring R] [Ring S] (f : R ->+* S)
  proof: rfl

中文:
引理 to整数AlgHom_coe
  条件: [环 R] [环 S] (f : R ->+* S)
  证明: rfl
-/
lemma toIntAlgHom_coe [Ring R] [Ring S] (f : R ->+* S) :
    ⇑f.toIntAlgHom = ⇑f := rfl

/--
lemma `toIntAlgHom_apply` / 引理 `toIntAlgHom_apply`

English:
lemma toIntAlgHom_apply
  given: [Ring R] [Ring S] (f : R ->+* S) (x : R)
  proof: rfl

中文:
引理 to整数AlgHom_apply
  条件: [环 R] [环 S] (f : R ->+* S) (x : R)
  证明: rfl
-/
lemma toIntAlgHom_apply [Ring R] [Ring S] (f : R ->+* S) (x : R) :
    f.toIntAlgHom x = f x := rfl

/--
lemma `toIntAlgHom_injective` / 引理 `toIntAlgHom_injective`

English:
lemma toIntAlgHom_injective
  given: [Ring R] [Ring S]
  proof: fun _ _ e => DFunLike.ext _ _ (fun x => DFunLike.congr_fun e x)

中文:
引理 to整数AlgHom_injective
  条件: [环 R] [环 S]
  证明: fun _ _ e => DFunLike.ext _ _ (fun x => DFunLike.congr_fun e x)

Depends on / 依赖: DFunLike, DFunLike.congr_fun, DFunLike.ext, congr_fun
-/
lemma toIntAlgHom_injective [Ring R] [Ring S] :
    Function.Injective (RingHom.toIntAlgHom : (R ->+* S) -> _) :=
  fun _ _ e => DFunLike.ext _ _ (fun x => DFunLike.congr_fun e x)

variable (R) (S) in
/-- Ring homomorphisms are the same as `ℤ`-algebra homomorphisms. -/
@[simps]
/--
Definition of `equivIntAlgHom` / `equivIntAlgHom` 的定义

English:
definition equivIntAlgHom
  signature: [Ring R] [Ring S]
  body: RingHom.toIntAlgHom
  invFun := AlgHom.toRingHom

中文:
定义 equiv整数AlgHom
  签名: [环 R] [环 S]
  定义体: RingHom.toIntAlgHom
  invFun := AlgHom.toRingHom

Depends on / 依赖: RingHom, RingHom.toIntAlgHom, toIntAlgHom
-/
def equivIntAlgHom [Ring R] [Ring S] : (R ->+* S) ≃ (R ->ₐ[Int] S) where
  toFun := RingHom.toIntAlgHom
  invFun := AlgHom.toRingHom

end RingHom

namespace Algebra

variable (R : Type u) (A : Type v) (B : Type w)
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/--
Definition of `ofId` / `ofId` 的定义

English:
definition ofId
  signature: : R ->ₐ[R] A
  body: { algebraMap R A with commutes' := fun _ => rfl }

中文:
定义 ofId
  签名: : R ->ₐ[R] A
  定义体: { algebraMap R A with commutes' := fun _ => rfl }

Depends on / 依赖: algebraMap, commutes
-/
def ofId : R ->ₐ[R] A :=
  { algebraMap R A with commutes' := fun _ => rfl }

variable {R}

/--
lemma `ofId_self` / 引理 `ofId_self`

English:
lemma ofId_self
  statement: ofId R R = .id R R
  proof: rfl

中文:
引理 ofId_self
  结论: ofId R R = .id R R
  证明: rfl
-/
@[simp] lemma ofId_self : ofId R R = .id R R := rfl

/--
lemma `toRingHom_ofId` / 引理 `toRingHom_ofId`

English:
lemma toRingHom_ofId
  statement: ofId R A = algebraMap R A
  proof: rfl

@[simp]

中文:
引理 toRingHom_ofId
  结论: ofId R A = algebraMap R A
  证明: rfl

@[simp]
-/
@[simp] lemma toRingHom_ofId : ofId R A = algebraMap R A := rfl

@[simp]
/--
theorem `ofId_apply` / 定理 `ofId_apply`

English:
theorem ofId_apply
  given: (r)
  statement: ofId R A r = algebraMap R A r
  proof: rfl

中文:
定理 ofId_apply
  条件: (r)
  结论: ofId R A r = algebraMap R A r
  证明: rfl
-/
theorem ofId_apply (r) : ofId R A r = algebraMap R A r :=
  rfl

/--
Instance `subsingleton_id` / 实例 `subsingleton_id`

English:
instance subsingleton_id
  signature: : Subsingleton (R ->ₐ[R] A)
  body: ⟨fun f g => AlgHom.ext fun _ => (f.commutes _).trans (g.commutes _).symm⟩

中文:
实例 subsingleton_id
  签名: : 子单例 (R ->ₐ[R] A)
  定义体: ⟨fun f g => AlgHom.ext fun _ => (f.commutes _).trans (g.commutes _).symm⟩

Depends on / 依赖: AlgHom, AlgHom.ext, commutes, f.commutes, g.commutes
-/
instance subsingleton_id : Subsingleton (R ->ₐ[R] A) :=
  ⟨fun f g => AlgHom.ext fun _ => (f.commutes _).trans (g.commutes _).symm⟩

/-- This ext lemma closes trivial subgoals created when chaining heterobasic ext lemmas. -/
@[ext high]
/--
theorem `ext_id` / 定理 `ext_id`

English:
theorem ext_id
  given: (f g : R ->ₐ[R] A)
  statement: f = g
  proof: Subsingleton.elim _ _

@[simp]

中文:
定理 ext_id
  条件: (f g : R ->ₐ[R] A)
  结论: f = g
  证明: Subsingleton.elim _ _

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem ext_id (f g : R ->ₐ[R] A) : f = g := Subsingleton.elim _ _

@[simp]
/--
theorem `comp_ofId` / 定理 `comp_ofId`

English:
theorem comp_ofId
  given: (φ : A ->ₐ[R] B)
  statement: φ.comp (Algebra.ofId R A) = Algebra.ofId R B
  proof: by ext

中文:
定理 comp_ofId
  条件: (φ : A ->ₐ[R] B)
  结论: φ.comp (代数.ofId R A) = 代数.ofId R B
  证明: by ext
-/
theorem comp_ofId (φ : A ->ₐ[R] B) : φ.comp (Algebra.ofId R A) = Algebra.ofId R B := by ext

section MulDistribMulAction

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulDistribMulAction (A ->ₐ[R] A) Aˣ
  body: Units.map f
  one_smul _ := by ext; rfl
  mul_smul _ _ _ := by ext; rfl
  smul_mul _ _ _ := by ext; exact map_mul _ _ _
  smul_one _ := by ext; exact map_one _

@[simp]

中文:
实例 :
  签名: MulDistribMul作用 (A ->ₐ[R] A) Aˣ
  定义体: Units.map f
  one_smul _ := by ext; rfl
  mul_smul _ _ _ := by ext; rfl
  smul_mul _ _ _ := by ext; exact map_mul _ _ _
  smul_one _ := by ext; exact map_one _

@[simp]

Depends on / 依赖: Units.map
-/
instance : MulDistribMulAction (A ->ₐ[R] A) Aˣ where
  smul f := Units.map f
  one_smul _ := by ext; rfl
  mul_smul _ _ _ := by ext; rfl
  smul_mul _ _ _ := by ext; exact map_mul _ _ _
  smul_one _ := by ext; exact map_one _

@[simp]
/--
theorem `smul_units_def` / 定理 `smul_units_def`

English:
theorem smul_units_def
  given: (f : A ->ₐ[R] A) (x : Aˣ)
  proof: rfl

中文:
定理 smul_units_def
  条件: (f : A ->ₐ[R] A) (x : Aˣ)
  证明: rfl

Depends on / 依赖: dihedralAct
-/
theorem smul_units_def (f : A ->ₐ[R] A) (x : Aˣ) :
    f • x = Units.map (f : A ->* A) x := rfl

end MulDistribMulAction

variable (M : Submonoid R) {B : Type w} [Semiring B] [Algebra R B] {A}

/--
lemma `algebraMapSubmonoid_map_eq` / 引理 `algebraMapSubmonoid_map_eq`

English:
lemma algebraMapSubmonoid_map_eq
  given: (f : A ->ₐ[R] B)
  proof: by
  ext x
  constructor
  · rintro ⟨a, ⟨r, hr, rfl⟩, rfl⟩
    simp only [AlgHom.commutes]
    use r
  · rintro ⟨r, hr, rfl⟩
    simp only [Submonoid.mem_map]
    use (algebraMap R A r)
    simp only [AlgHom.commutes, and_true]
    use r

中文:
引理 algebraMapSubmonoid_map_eq
  条件: (f : A ->ₐ[R] B)
  证明: by
  ext x
  constructor
  · rintro ⟨a, ⟨r, hr, rfl⟩, rfl⟩
    simp only [AlgHom.commutes]
    use r
  · rintro ⟨r, hr, rfl⟩
    simp only [Submonoid.mem_map]
    use (algebraMap R A r)
    simp only [AlgHom.commutes, and_true]
    use r

Depends on / 依赖: AlgHom, AlgHom.commutes, Submonoid, Submonoid.mem_map, algebraMap, and_true, commutes, mem_map
-/
lemma algebraMapSubmonoid_map_eq (f : A ->ₐ[R] B) :
    (algebraMapSubmonoid A M).map f = algebraMapSubmonoid B M := by
  ext x
  constructor
  · rintro ⟨a, ⟨r, hr, rfl⟩, rfl⟩
    simp only [AlgHom.commutes]
    use r
  · rintro ⟨r, hr, rfl⟩
    simp only [Submonoid.mem_map]
    use (algebraMap R A r)
    simp only [AlgHom.commutes, and_true]
    use r

/--
lemma `algebraMapSubmonoid_le_comap` / 引理 `algebraMapSubmonoid_le_comap`

English:
lemma algebraMapSubmonoid_le_comap
  given: (f : A ->ₐ[R] B)
  proof: by
  rw [← algebraMapSubmonoid_map_eq M f]
  exact Submonoid.le_comap_map (Algebra.algebraMapSubmonoid A M)

中文:
引理 algebraMapSubmonoid_le_comap
  条件: (f : A ->ₐ[R] B)
  证明: by
  rw [← algebraMapSubmonoid_map_eq M f]
  exact Submonoid.le_comap_map (Algebra.algebraMapSubmonoid A M)

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, Submonoid, Submonoid.le_comap_map, algebraMapSubmonoid, algebraMapSubmonoid_map_eq, le_comap_map
-/
lemma algebraMapSubmonoid_le_comap (f : A ->ₐ[R] B) :
    algebraMapSubmonoid A M <= (algebraMapSubmonoid B M).comap f.toRingHom := by
  rw [← algebraMapSubmonoid_map_eq M f]
  exact Submonoid.le_comap_map (Algebra.algebraMapSubmonoid A M)

end Algebra

namespace MulSemiringAction

variable {M G : Type*} (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
variable [Monoid M] [MulSemiringAction M A] [SMulCommClass M R A]

/-- Each element of the monoid defines an algebra homomorphism.

This is a stronger version of `MulSemiringAction.toRingHom` and
`DistribSMul.toLinearMap`. -/
@[simps]
/--
Definition of `toAlgHom` / `toAlgHom` 的定义

English:
definition toAlgHom
  signature: (m : M)
  body: { MulSemiringAction.toRingHom _ _ m with
    toFun := fun a => m • a
    commutes' := smul_algebraMap _ }

中文:
定义 toAlgHom
  签名: (m : M)
  定义体: { MulSemiringAction.toRingHom _ _ m with
    toFun := fun a => m • a
    commutes' := smul_algebraMap _ }

Depends on / 依赖: MulSemiringAction, MulSemiringAction.toRingHom, commutes, smul_algebraMap, toRingHom
-/
def toAlgHom (m : M) : A ->ₐ[R] A :=
  { MulSemiringAction.toRingHom _ _ m with
    toFun := fun a => m • a
    commutes' := smul_algebraMap _ }

/--
theorem `toAlgHom_injective` / 定理 `toAlgHom_injective`

English:
theorem toAlgHom_injective
  given: [FaithfulSMul M A]
  proof: fun _m₁ _m₂ h =>
  eq_of_smul_eq_smul fun r => AlgHom.ext_iff.1 h r

中文:
定理 toAlgHom_injective
  条件: [忠实标量乘法 M A]
  证明: fun _m₁ _m₂ h =>
  eq_of_smul_eq_smul fun r => AlgHom.ext_iff.1 h r

Depends on / 依赖: PreEnvelGroupRel, PreEnvelGroupRel.rel
-/
theorem toAlgHom_injective [FaithfulSMul M A] :
    Function.Injective (MulSemiringAction.toAlgHom R A : M -> A ->ₐ[R] A) := fun _m₁ _m₂ h =>
  eq_of_smul_eq_smul fun r => AlgHom.ext_iff.1 h r

end MulSemiringAction

section

variable {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]
  [Subsingleton T]

/--
Instance `uniqueOfRight` / 实例 `uniqueOfRight`

English:
instance uniqueOfRight
  signature: : Unique (S ->ₐ[R] T) where
  body: AlgHom.ofLinearMap default (Subsingleton.elim _ _) (fun _ _ => (Subsingleton.elim _ _))
  uniq _ := AlgHom.ext fun _ => Subsingleton.elim _ _

@[simp]

中文:
实例 uniqueOfRight
  签名: : 唯一 (S ->ₐ[R] T) where
  定义体: AlgHom.ofLinearMap default (Subsingleton.elim _ _) (fun _ _ => (Subsingleton.elim _ _))
  uniq _ := AlgHom.ext fun _ => Subsingleton.elim _ _

@[simp]

Depends on / 依赖: AlgHom, AlgHom.ofLinearMap, Subsingleton, Subsingleton.elim, ofLinearMap
-/
instance uniqueOfRight : Unique (S ->ₐ[R] T) where
  default := AlgHom.ofLinearMap default (Subsingleton.elim _ _) (fun _ _ => (Subsingleton.elim _ _))
  uniq _ := AlgHom.ext fun _ => Subsingleton.elim _ _

@[simp]
/--
lemma `AlgHom.default_apply` / 引理 `AlgHom.default_apply`

English:
lemma AlgHom.default_apply
  given: (x : S)
  statement: (default : S ->ₐ[R] T) x = 0
  proof: rfl

中文:
引理 代数态射.default_apply
  条件: (x : S)
  结论: (default : S ->ₐ[R] T) x = 0
  证明: rfl
-/
lemma AlgHom.default_apply (x : S) : (default : S ->ₐ[R] T) x = 0 :=
  rfl

end
