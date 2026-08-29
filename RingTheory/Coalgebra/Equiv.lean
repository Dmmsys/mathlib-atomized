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

/--
Definition of `CoalgEquiv` / `CoalgEquiv` 的定义

English:
structure CoalgEquiv
  parameters: (R : Type*) [CommSemiring R] (A B : Type*)
  extends: A ->ₗc[R] B, A ≃ₗ[R] B
  (no additional axioms)

中文:
结构 余alg等价
  参数: (R : 类型) [交换半环 R] (A B : 类型)
  继承: A ->ₗc[R] B, A ≃ₗ[R] B
  (无附加公理)
-/
structure CoalgEquiv (R : Type*) [CommSemiring R] (A B : Type*)
    [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] extends A ->ₗc[R] B, A ≃ₗ[R] B where

attribute [nolint docBlame] CoalgEquiv.toCoalgHom
attribute [nolint docBlame] CoalgEquiv.toLinearEquiv

@[inherit_doc CoalgEquiv]
notation:50 A " ≃ₗc[" R "] " B => CoalgEquiv R A B

/--
Definition of `CoalgEquivClass` / `CoalgEquivClass` 的定义

English:
class CoalgEquivClass
  parameters: (F : Type*) (R A B : outParam Type*) [CommSemiring R]
  extends: CoalgHomClass F R A B, SemilinearEquivClass F (RingHom.id R) A B
  (no additional axioms)

中文:
类 余alg等价类
  参数: (F : 类型) (R A B : outParam 类型) [交换半环 R]
  继承: 余alg态射类 F R A B, 半线性等价类 F (环态射.id R) A B
  (无附加公理)
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
/--
Definition of `toCoalgEquiv` / `toCoalgEquiv` 的定义

English:
definition toCoalgEquiv
  signature: [EquivLike F A B] [CoalgEquivClass F R A B] (f : F)
  body: { (f : A ->ₗc[R] B), (SemilinearEquivClass.semilinearEquiv f : A ≃ₗ[R] B) with }

中文:
定义 toCoalgEquiv
  签名: [等价状 F A B] [余alg等价类 F R A B] (f : F)
  定义体: { (f : A ->ₗc[R] B), (SemilinearEquivClass.semilinearEquiv f : A ≃ₗ[R] B) with }

Depends on / 依赖: SemilinearEquivClass, SemilinearEquivClass.semilinearEquiv, semilinearEquiv
-/
def toCoalgEquiv [EquivLike F A B] [CoalgEquivClass F R A B] (f : F) : A ≃ₗc[R] B :=
  { (f : A ->ₗc[R] B), (SemilinearEquivClass.semilinearEquiv f : A ≃ₗ[R] B) with }

/--
Instance `instCoeToCoalgEquiv` / 实例 `instCoeToCoalgEquiv`

English:
instance instCoeToCoalgEquiv
  body: toCoalgEquiv f

中文:
实例 instCoeToCoalgEquiv
  定义体: toCoalgEquiv f

Depends on / 依赖: toCoalgEquiv
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

/--
Definition of `toEquiv` / `toEquiv` 的定义

English:
definition toEquiv
  signature: : (A ≃ₗc[R] B) -> A ≃ B
  body: fun f => f.toLinearEquiv.toEquiv

中文:
定义 toEquiv
  签名: : (A ≃ₗc[R] B) -> A ≃ B
  定义体: fun f => f.toLinearEquiv.toEquiv

Depends on / 依赖: f.toLinearEquiv.toEquiv, toEquiv, toLinearEquiv
-/
def toEquiv : (A ≃ₗc[R] B) -> A ≃ B := fun f => f.toLinearEquiv.toEquiv

/--
theorem `toEquiv_injective` / 定理 `toEquiv_injective`

English:
theorem toEquiv_injective
  statement: Function.Injective (toEquiv : (A ≃ₗc[R] B) -> A ≃ B)
  proof: fun ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h =>
    (CoalgEquiv.mk.injEq _ _ _ _ _ _ _ _).mpr
      ⟨CoalgHom.ext (congr_fun (Equiv.mk.inj h).1), (Equiv.mk.inj h).2⟩

@[simp]

中文:
定理 toEquiv_injective
  结论: 函数.单射 (toEquiv : (A ≃ₗc[R] B) -> A ≃ B)
  证明: fun ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h =>
    (CoalgEquiv.mk.injEq _ _ _ _ _ _ _ _).mpr
      ⟨CoalgHom.ext (congr_fun (Equiv.mk.inj h).1), (Equiv.mk.inj h).2⟩

@[simp]

Depends on / 依赖: CoalgEquiv, CoalgEquiv.mk.injEq, CoalgHom, CoalgHom.ext, Equiv.mk.inj, congr_fun
-/
theorem toEquiv_injective : Function.Injective (toEquiv : (A ≃ₗc[R] B) -> A ≃ B) :=
  fun ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h =>
    (CoalgEquiv.mk.injEq _ _ _ _ _ _ _ _).mpr
      ⟨CoalgHom.ext (congr_fun (Equiv.mk.inj h).1), (Equiv.mk.inj h).2⟩

@[simp]
/--
theorem `toEquiv_inj` / 定理 `toEquiv_inj`

English:
theorem toEquiv_inj
  given: {e₁ e₂ : A ≃ₗc[R] B}
  statement: e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂
  proof: toEquiv_injective.eq_iff

中文:
定理 toEquiv_inj
  条件: {e₁ e₂ : A ≃ₗc[R] B}
  结论: e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂
  证明: toEquiv_injective.eq_iff

Depends on / 依赖: eq_iff, toEquiv_injective, toEquiv_injective.eq_iff
-/
theorem toEquiv_inj {e₁ e₂ : A ≃ₗc[R] B} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff

/--
theorem `toCoalgHom_injective` / 定理 `toCoalgHom_injective`

English:
theorem toCoalgHom_injective
  statement: Function.Injective (toCoalgHom : (A ≃ₗc[R] B) -> A ->ₗc[R] B)
  proof: fun _ _ H => toEquiv_injective Equiv.ext CoalgHom.congr_fun H

中文:
定理 toCoalgHom_injective
  结论: 函数.单射 (toCoalgHom : (A ≃ₗc[R] B) -> A ->ₗc[R] B)
  证明: fun _ _ H => toEquiv_injective Equiv.ext CoalgHom.congr_fun H

Depends on / 依赖: CoalgHom, CoalgHom.congr_fun, Equiv.ext, congr_fun, toEquiv_injective
-/
theorem toCoalgHom_injective : Function.Injective (toCoalgHom : (A ≃ₗc[R] B) -> A ->ₗc[R] B) :=
fun _ _ H => toEquiv_injective Equiv.ext CoalgHom.congr_fun H

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (A ≃ₗc[R] B) A B
  body: e.toFun
  inv := CoalgEquiv.invFun
  coe_injective' _ _ h _ := toCoalgHom_injective (DFunLike.coe_injective h)
  left_inv := CoalgEquiv.left_inv
  right_inv := CoalgEquiv.right_inv

中文:
实例 :
  签名: 等价状 (A ≃ₗc[R] B) A B
  定义体: e.toFun
  inv := CoalgEquiv.invFun
  coe_injective' _ _ h _ := toCoalgHom_injective (DFunLike.coe_injective h)
  left_inv := CoalgEquiv.left_inv
  right_inv := CoalgEquiv.right_inv

Depends on / 依赖: e.toFun
-/
instance : EquivLike (A ≃ₗc[R] B) A B where
  coe e := e.toFun
  inv := CoalgEquiv.invFun
  coe_injective' _ _ h _ := toCoalgHom_injective (DFunLike.coe_injective h)
  left_inv := CoalgEquiv.left_inv
  right_inv := CoalgEquiv.right_inv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (A ≃ₗc[R] B) A B
  body: DFunLike.coe
  coe_injective := DFunLike.coe_injective

中文:
实例 :
  签名: 函数状 (A ≃ₗc[R] B) A B
  定义体: DFunLike.coe
  coe_injective := DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe
-/
instance : FunLike (A ≃ₗc[R] B) A B where
  coe := DFunLike.coe
  coe_injective := DFunLike.coe_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoalgEquivClass (A ≃ₗc[R] B) R A B
  body: (·.map_add')
  map_smulₛₗ := (·.map_smul')
  counit_comp := (·.counit_comp)
  map_comp_comul := (·.map_comp_comul)

中文:
实例 :
  签名: 余alg等价类 (A ≃ₗc[R] B) R A B
  定义体: (·.map_add')
  map_smulₛₗ := (·.map_smul')
  counit_comp := (·.counit_comp)
  map_comp_comul := (·.map_comp_comul)

Depends on / 依赖: map_add
-/
instance : CoalgEquivClass (A ≃ₗc[R] B) R A B where
  map_add := (·.map_add')
  map_smulₛₗ := (·.map_smul')
  counit_comp := (·.counit_comp)
  map_comp_comul := (·.map_comp_comul)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (A ≃ₗc[R] B) (A ≃ₗ[R] B)
  body: toLinearEquiv

@[simp, norm_cast]

中文:
实例 :
  签名: CoeOut (A ≃ₗc[R] B) (A ≃ₗ[R] B)
  定义体: toLinearEquiv

@[simp, norm_cast]

Depends on / 依赖: toLinearEquiv
-/
instance : CoeOut (A ≃ₗc[R] B) (A ≃ₗ[R] B) where coe := toLinearEquiv

@[simp, norm_cast]
/--
theorem `toCoalgHom_inj` / 定理 `toCoalgHom_inj`

English:
theorem toCoalgHom_inj
  given: {e₁ e₂ : A ≃ₗc[R] B}
  statement: (↑e₁ : A ->ₗc[R] B) = e₂ ↔ e₁ = e₂
  proof: toCoalgHom_injective.eq_iff

@[simp]

中文:
定理 toCoalgHom_inj
  条件: {e₁ e₂ : A ≃ₗc[R] B}
  结论: (↑e₁ : A ->ₗc[R] B) = e₂ ↔ e₁ = e₂
  证明: toCoalgHom_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, toCoalgHom_injective, toCoalgHom_injective.eq_iff
-/
theorem toCoalgHom_inj {e₁ e₂ : A ≃ₗc[R] B} : (↑e₁ : A ->ₗc[R] B) = e₂ ↔ e₁ = e₂ :=
  toCoalgHom_injective.eq_iff

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: {f h h₀ h₁ h₂ h₃ h₄ h₅}
  proof: rfl

中文:
定理 coe_mk
  条件: {f h h₀ h₁ h₂ h₃ h₄ h₅}
  证明: rfl
-/
theorem coe_mk {f h h₀ h₁ h₂ h₃ h₄ h₅} :
    (⟨⟨⟨⟨f, h⟩, h₀⟩, h₁, h₂⟩, h₃, h₄, h₅⟩ : A ≃ₗc[R] B) = f := rfl

end

section

variable [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [Module R A] [Module R B]
  [Module R C] [CoalgebraStruct R A] [CoalgebraStruct R B] [CoalgebraStruct R C]

variable (e e' : A ≃ₗc[R] B)

@[simp, norm_cast]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  statement: ⇑(e : A ->ₗc[R] B) = e
  proof: rfl

@[nolint synTaut, deprecated "Now a syntactic tautology" (since := "2026-04-12")]

中文:
定理 coe_coe
  结论: ⇑(e : A ->ₗc[R] B) = e
  证明: rfl

@[nolint synTaut, deprecated "Now a syntactic tautology" (since := "2026-04-12")]
-/
theorem coe_coe : ⇑(e : A ->ₗc[R] B) = e :=
  rfl

@[nolint synTaut, deprecated "Now a syntactic tautology" (since := "2026-04-12")]
/--
theorem `toLinearEquiv_eq_coe` / 定理 `toLinearEquiv_eq_coe`

English:
theorem toLinearEquiv_eq_coe
  given: (f : A ≃ₗc[R] B)
  statement: f.toLinearEquiv = f
  proof: rfl

@[simp]

中文:
定理 toLinearEquiv_eq_coe
  条件: (f : A ≃ₗc[R] B)
  结论: f.toLinearEquiv = f
  证明: rfl

@[simp]
-/
theorem toLinearEquiv_eq_coe (f : A ≃ₗc[R] B) : f.toLinearEquiv = f :=
  rfl

@[simp]
/--
theorem `toCoalgHom_eq_coe` / 定理 `toCoalgHom_eq_coe`

English:
theorem toCoalgHom_eq_coe
  given: (f : A ≃ₗc[R] B)
  statement: f.toCoalgHom = f
  proof: rfl

@[simp]

中文:
定理 toCoalgHom_eq_coe
  条件: (f : A ≃ₗc[R] B)
  结论: f.toCoalgHom = f
  证明: rfl

@[simp]
-/
theorem toCoalgHom_eq_coe (f : A ≃ₗc[R] B) : f.toCoalgHom = f :=
  rfl

@[simp]
/--
theorem `coe_toLinearEquiv` / 定理 `coe_toLinearEquiv`

English:
theorem coe_toLinearEquiv
  statement: ⇑(e : A ≃ₗ[R] B) = e
  proof: rfl

@[simp]

中文:
定理 coe_toLinearEquiv
  结论: ⇑(e : A ≃ₗ[R] B) = e
  证明: rfl

@[simp]
-/
theorem coe_toLinearEquiv : ⇑(e : A ≃ₗ[R] B) = e :=
  rfl

@[simp]
/--
theorem `coe_toCoalgHom` / 定理 `coe_toCoalgHom`

English:
theorem coe_toCoalgHom
  statement: ⇑(e : A ->ₗc[R] B) = e
  proof: rfl

中文:
定理 coe_toCoalgHom
  结论: ⇑(e : A ->ₗc[R] B) = e
  证明: rfl

Depends on / 依赖: ToType, ToType.toOrd
-/
theorem coe_toCoalgHom : ⇑(e : A ->ₗc[R] B) = e :=
  rfl

/--
theorem `toLinearEquiv_toLinearMap` / 定理 `toLinearEquiv_toLinearMap`

English:
theorem toLinearEquiv_toLinearMap
  statement: ((e : A ≃ₗ[R] B) : A ->ₗ[R] B) = (e : A ->ₗc[R] B)
  proof: rfl

中文:
定理 toLinearEquiv_toLinearMap
  结论: ((e : A ≃ₗ[R] B) : A ->ₗ[R] B) = (e : A ->ₗc[R] B)
  证明: rfl

Depends on / 依赖: x.toOrd
-/
theorem toLinearEquiv_toLinearMap : ((e : A ≃ₗ[R] B) : A ->ₗ[R] B) = (e : A ->ₗc[R] B) :=
  rfl

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

/-- Coalgebra equivalences are symmetric. -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (e : A ≃ₗc[R] B)
  body: { (e : A ≃ₗ[R] B).symm with
    counit_comp := (LinearEquiv.comp_toLinearMap_symm_eq _ _).2 e.counit_comp.symm
    map_comp_comul := by
      change (TensorProduct.congr (e : A ≃ₗ[R] B) (e : A ≃ₗ[R] B)).symm.toLinearMap ∘ₗ comul
        = comul ∘ₗ (e : A ≃ₗ[R] B).symm
      rw [LinearEquiv.toLinearM

中文:
定义 symm
  签名: (e : A ≃ₗc[R] B)
  定义体: { (e : A ≃ₗ[R] B).symm with
    counit_comp := (LinearEquiv.comp_toLinearMap_symm_eq _ _).2 e.counit_comp.symm
    map_comp_comul := by
      change (TensorProduct.congr (e : A ≃ₗ[R] B) (e : A ≃ₗ[R] B)).symm.toLinearMap ∘ₗ comul
        = comul ∘ₗ (e : A ≃ₗ[R] B).symm
      rw [LinearEquiv.toLinearM

Depends on / 依赖: CoalgHom, CoalgHom.toLinearMap_eq_coe, CoalgHomClass, CoalgHomClass.map_comp_comul, LinearEquiv, LinearEquiv.comp_toLinearMap_symm_eq, LinearEquiv.toLinearMap_ofLinearMap, LinearEquiv.toLinearMap_symm_comp_eq, LinearMap, LinearMap.comp_assoc, TensorProduct, TensorProduct.congr, comp_assoc, comp_toLinearMap_symm_eq, counit_comp, e.counit_comp.symm, map_comp_comul, symm.toLinearMap, toCoalgHom_eq_coe, toLinearEquiv_toLinearMap
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
      rw [← toLinearEquiv_toLinearMap]; rw [LinearEquiv.comp_symm_cancel_right] }

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: {R : Type*} [CommSemiring R] {α β : Type*}
  body: f

中文:
定义 Simps.apply
  签名: {R : 类型} [交换半环 R] {α β : 类型}
  定义体: f
-/
def Simps.apply {R : Type*} [CommSemiring R] {α β : Type*}
    [AddCommMonoid α] [AddCommMonoid β] [Module R α]
    [Module R β] [CoalgebraStruct R α] [CoalgebraStruct R β]
    (f : α ≃ₗc[R] β) : α -> β := f

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: {R : Type*} [CommSemiring R]
  body: e.symm

initialize_simps_projections CoalgEquiv (toFun -> apply, invFun -> symm_apply)

中文:
定义 Simps.symm_apply
  签名: {R : 类型} [交换半环 R]
  定义体: e.symm

initialize_simps_projections CoalgEquiv (toFun -> apply, invFun -> symm_apply)
-/
def Simps.symm_apply {R : Type*} [CommSemiring R]
    {A : Type*} {B : Type*} [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B]
    (e : A ≃ₗc[R] B) : B -> A :=
  e.symm

initialize_simps_projections CoalgEquiv (toFun -> apply, invFun -> symm_apply)

variable (A R) in
/-- The identity map is a coalgebra equivalence. -/
@[refl, simps!]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : A ≃ₗc[R] A
  body: { CoalgHom.id R A, LinearEquiv.refl R A with }

@[simp]

中文:
定义 refl
  签名: : A ≃ₗc[R] A
  定义体: { CoalgHom.id R A, LinearEquiv.refl R A with }

@[simp]

Depends on / 依赖: CoalgHom, CoalgHom.id, LinearEquiv, LinearEquiv.refl
-/
def refl : A ≃ₗc[R] A :=
  { CoalgHom.id R A, LinearEquiv.refl R A with }

@[simp]
/--
theorem `refl_toLinearEquiv` / 定理 `refl_toLinearEquiv`

English:
theorem refl_toLinearEquiv
  statement: refl R A = LinearEquiv.refl R A
  proof: rfl

@[simp]

中文:
定理 refl_toLinearEquiv
  结论: refl R A = 线性等价.refl R A
  证明: rfl

@[simp]
-/
theorem refl_toLinearEquiv : refl R A = LinearEquiv.refl R A := rfl

@[simp]
/--
theorem `refl_toCoalgHom` / 定理 `refl_toCoalgHom`

English:
theorem refl_toCoalgHom
  statement: refl R A = CoalgHom.id R A
  proof: rfl

@[simp]

中文:
定理 refl_toCoalgHom
  结论: refl R A = 余alg态射.id R A
  证明: rfl

@[simp]
-/
theorem refl_toCoalgHom : refl R A = CoalgHom.id R A :=
  rfl

@[simp]
/--
theorem `symm_toLinearEquiv` / 定理 `symm_toLinearEquiv`

English:
theorem symm_toLinearEquiv
  given: (e : A ≃ₗc[R] B)
  proof: rfl

中文:
定理 symm_toLinearEquiv
  条件: (e : A ≃ₗc[R] B)
  证明: rfl
-/
theorem symm_toLinearEquiv (e : A ≃ₗc[R] B) :
    e.symm = (e : A ≃ₗ[R] B).symm := rfl

/--
theorem `coe_symm_toLinearEquiv` / 定理 `coe_symm_toLinearEquiv`

English:
theorem coe_symm_toLinearEquiv
  given: (e : A ≃ₗc[R] B)
  proof: rfl

@[simp]

中文:
定理 coe_symm_toLinearEquiv
  条件: (e : A ≃ₗc[R] B)
  证明: rfl

@[simp]
-/
theorem coe_symm_toLinearEquiv (e : A ≃ₗc[R] B) :
    ⇑(e : A ≃ₗ[R] B).symm = e.symm := rfl

@[simp]
/--
theorem `symm_toCoalgHom` / 定理 `symm_toCoalgHom`

English:
theorem symm_toCoalgHom
  given: (e : A ≃ₗc[R] B)
  proof: rfl

@[simp]

中文:
定理 symm_toCoalgHom
  条件: (e : A ≃ₗc[R] B)
  证明: rfl

@[simp]
-/
theorem symm_toCoalgHom (e : A ≃ₗc[R] B) :
    ((e.symm : B ->ₗc[R] A) : B ->ₗ[R] A) = (e : A ≃ₗ[R] B).symm := rfl

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : A ≃ₗc[R] B) (x)
  proof: LinearEquiv.symm_apply_apply (e : A ≃ₗ[R] B) x

@[simp]

中文:
定理 symm_apply_apply
  条件: (e : A ≃ₗc[R] B) (x)
  证明: LinearEquiv.symm_apply_apply (e : A ≃ₗ[R] B) x

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_apply, symm_apply_apply
-/
theorem symm_apply_apply (e : A ≃ₗc[R] B) (x) :
    e.symm (e x) = x :=
  LinearEquiv.symm_apply_apply (e : A ≃ₗ[R] B) x

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : A ≃ₗc[R] B) (x)
  proof: LinearEquiv.apply_symm_apply (e : A ≃ₗ[R] B) x

@[simp]

中文:
定理 apply_symm_apply
  条件: (e : A ≃ₗc[R] B) (x)
  证明: LinearEquiv.apply_symm_apply (e : A ≃ₗ[R] B) x

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.apply_symm_apply, apply_symm_apply
-/
theorem apply_symm_apply (e : A ≃ₗc[R] B) (x) :
    e (e.symm x) = x :=
  LinearEquiv.apply_symm_apply (e : A ≃ₗ[R] B) x

@[simp]
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

variable {e₁₂ : A ≃ₗc[R] B} {e₂₃ : B ≃ₗc[R] C}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Coalgebra equivalences are transitive. -/
@[trans, simps!]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e₁₂ : A ≃ₗc[R] B) (e₂₃ : B ≃ₗc[R] C)
  body: { (e₂₃ : B ->ₗc[R] C).comp (e₁₂ : A ->ₗc[R] B), e₁₂.toLinearEquiv ≪≫ₗ e₂₃.toLinearEquiv with }

中文:
定义 trans
  签名: (e₁₂ : A ≃ₗc[R] B) (e₂₃ : B ≃ₗc[R] C)
  定义体: { (e₂₃ : B ->ₗc[R] C).comp (e₁₂ : A ->ₗc[R] B), e₁₂.toLinearEquiv ≪≫ₗ e₂₃.toLinearEquiv with }

Depends on / 依赖: toLinearEquiv
-/
def trans (e₁₂ : A ≃ₗc[R] B) (e₂₃ : B ≃ₗc[R] C) : A ≃ₗc[R] C :=
  { (e₂₃ : B ->ₗc[R] C).comp (e₁₂ : A ->ₗc[R] B), e₁₂.toLinearEquiv ≪≫ₗ e₂₃.toLinearEquiv with }

/--
theorem `trans_toLinearEquiv` / 定理 `trans_toLinearEquiv`

English:
theorem trans_toLinearEquiv
  proof: rfl

@[simp]

中文:
定理 trans_toLinearEquiv
  证明: rfl

@[simp]
-/
theorem trans_toLinearEquiv :
    (e₁₂.trans e₂₃ : A ≃ₗ[R] C) = (e₁₂ : A ≃ₗ[R] B) ≪≫ₗ e₂₃ := rfl

@[simp]
/--
theorem `trans_toCoalgHom` / 定理 `trans_toCoalgHom`

English:
theorem trans_toCoalgHom
  proof: rfl

@[simp]

中文:
定理 trans_toCoalgHom
  证明: rfl

@[simp]
-/
theorem trans_toCoalgHom :
    (e₁₂.trans e₂₃ : A ->ₗc[R] C) = e₂₃.comp e₁₂ := rfl

@[simp]
/--
theorem `coe_toEquiv_trans` / 定理 `coe_toEquiv_trans`

English:
theorem coe_toEquiv_trans
  statement: (e₁₂ : A ≃ B).trans e₂₃ = (e₁₂.trans e₂₃ : A ≃ C)
  proof: rfl

中文:
定理 coe_toEquiv_trans
  结论: (e₁₂ : A ≃ B).trans e₂₃ = (e₁₂.trans e₂₃ : A ≃ C)
  证明: rfl
-/
theorem coe_toEquiv_trans : (e₁₂ : A ≃ B).trans e₂₃ = (e₁₂.trans e₂₃ : A ≃ C) :=
  rfl

/--
Definition of `ofCoalgHom` / `ofCoalgHom` 的定义

English:
definition ofCoalgHom
  signature: (f : A ->ₗc[R] B) (g : B ->ₗc[R] A) (h₁ : f.comp g = CoalgHom.id R B)
  body: f
  toFun := f
  invFun := g
  left_inv := CoalgHom.ext_iff.1 h₂
  right_inv := CoalgHom.ext_iff.1 h₁

@[simp]

中文:
定义 ofCoalgHom
  签名: (f : A ->ₗc[R] B) (g : B ->ₗc[R] A) (h₁ : f.comp g = 余alg态射.id R B)
  定义体: f
  toFun := f
  invFun := g
  left_inv := CoalgHom.ext_iff.1 h₂
  right_inv := CoalgHom.ext_iff.1 h₁

@[simp]
-/
def ofCoalgHom (f : A ->ₗc[R] B) (g : B ->ₗc[R] A) (h₁ : f.comp g = CoalgHom.id R B)
    (h₂ : g.comp f = CoalgHom.id R A) : A ≃ₗc[R] B where
  __ := f
  toFun := f
  invFun := g
  left_inv := CoalgHom.ext_iff.1 h₂
  right_inv := CoalgHom.ext_iff.1 h₁

@[simp]
/--
theorem `coe_ofCoalgHom` / 定理 `coe_ofCoalgHom`

English:
theorem coe_ofCoalgHom
  given: (f : A ->ₗc[R] B) (g : B ->ₗc[R] A) (h₁ h₂)
  proof: rfl

中文:
定理 coe_ofCoalgHom
  条件: (f : A ->ₗc[R] B) (g : B ->ₗc[R] A) (h₁ h₂)
  证明: rfl
-/
theorem coe_ofCoalgHom (f : A ->ₗc[R] B) (g : B ->ₗc[R] A) (h₁ h₂) :
    ofCoalgHom f g h₁ h₂ = f :=
  rfl

/--
theorem `ofCoalgHom_symm` / 定理 `ofCoalgHom_symm`

English:
theorem ofCoalgHom_symm
  given: (f : A ->ₗc[R] B) (g : B ->ₗc[R] A) (h₁ h₂)
  proof: rfl

中文:
定理 ofCoalgHom_symm
  条件: (f : A ->ₗc[R] B) (g : B ->ₗc[R] A) (h₁ h₂)
  证明: rfl
-/
theorem ofCoalgHom_symm (f : A ->ₗc[R] B) (g : B ->ₗc[R] A) (h₁ h₂) :
    (ofCoalgHom f g h₁ h₂).symm = ofCoalgHom g f h₂ h₁ :=
  rfl

variable {f : A ->ₗc[R] B} (hf : Function.Bijective f)

/-- Promotes a bijective coalgebra homomorphism to a coalgebra equivalence. -/
@[simps apply]
/--
Definition of `ofBijective` / `ofBijective` 的定义

English:
definition ofBijective
  signature: : A ≃ₗc[R] B where
  body: f
  __ := f
  __ := LinearEquiv.ofBijective (f : A ->ₗ[R] B) hf

@[simp]

中文:
定义 ofBijective
  签名: : A ≃ₗc[R] B where
  定义体: f
  __ := f
  __ := LinearEquiv.ofBijective (f : A ->ₗ[R] B) hf

@[simp]
-/
noncomputable def ofBijective : A ≃ₗc[R] B where
  toFun := f
  __ := f
  __ := LinearEquiv.ofBijective (f : A ->ₗ[R] B) hf

@[simp]
/--
theorem `coe_ofBijective` / 定理 `coe_ofBijective`

English:
theorem coe_ofBijective
  statement: (CoalgEquiv.ofBijective hf : A -> B) = f
  proof: rfl

中文:
定理 coe_ofBijective
  结论: (余alg等价.ofBijective hf : A -> B) = f
  证明: rfl
-/
theorem coe_ofBijective : (CoalgEquiv.ofBijective hf : A -> B) = f :=
  rfl

end
variable
  [AddCommMonoid A] [Module R A] [Coalgebra R A]
  [AddCommMonoid B] [Module R B] [CoalgebraStruct R B]

/--
Definition of `toCoalgebra` / `toCoalgebra` 的定义

English:
definition toCoalgebra
  signature: (f : A ≃ₗc[R] B)
  body: by
    simp only [← ((f : A ≃ₗ[R] B).comp_toLinearMap_symm_eq _ _).2 f.map_comp_comul,
      ← LinearMap.comp_assoc]
    congr 1
    ext x
    simpa only [toCoalgHom_eq_coe, CoalgHom.toLinearMap_eq_coe, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, ← (ℛ R _).eq, map_sum, Tensor

中文:
定义 toCoalgebra
  签名: (f : A ≃ₗc[R] B)
  定义体: by
    simp only [← ((f : A ≃ₗ[R] B).comp_toLinearMap_symm_eq _ _).2 f.map_comp_comul,
      ← LinearMap.comp_assoc]
    congr 1
    ext x
    simpa only [toCoalgHom_eq_coe, CoalgHom.toLinearMap_eq_coe, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, ← (ℛ R _).eq, map_sum, Tensor
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
