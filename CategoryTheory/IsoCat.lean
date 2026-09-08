/-
Copyright (c) 2026 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.EqToHom

/-!
# Isomorphisms of categories

An `IsoCat C D` is an isomorphism of categories: a pair of functors `C ⥤ D` and `D ⥤ C`
whose composites are *equal* (not merely naturally isomorphic) to the identity functors.
This is a strict notion, stronger than an equivalence of categories `C ≌ D`.
We also define `Functor.IsIso` as a property saying that a functor is fully faithful and
bijective on objects. We develop basic api for these two concepts.

Unless the application explicitly demands an isomorphism, the equivalence of categories is
to be preferred.

## Main definitions

* `CategoryTheory.IsoCat`: the type of isomorphisms between categories `C` and `D`.
* `CategoryTheory.Functor.IsIso`: a typeclass expressing that a functor is full,
  faithful and bijective on objects, hence underlies an isomorphism of categories.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor NatIso Category

variable {C : Type*} {D : Type*} {E : Type*} [Category* C] [Category* D] [Category* E]
variable (F : C ⥤ D) (G : D ⥤ E)

variable (C) (D) in
/-- An isomorphism of categories: a pair of functors whose composites are equal to the
identity functors. -/
/-
**CategoryTheory.IsoCat** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u_1) →   (D : Type u_2) →     [CategoryTheory.Category.{v_1, u_1
} C] →       [CategoryTheory.Category.{v_2, u_2} D] → Type (max (max (max u_1 u_
2) v_1) v_2)
参数：max (max u_1 u_2) v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of categories: a pair of functors whose composites are equal to t
he
identity functors.
-/
structure IsoCat where
  /-- The forward functor of an isomorphism of categories. -/
  functor : C ⥤ D
  /-- The inverse functor of an isomorphism of categories. -/
  inverse : D ⥤ C
  /-- The composition `functor ⋙ inverse` is equal to the identity. -/
  unit_eq : 𝟭 C = functor ⋙ inverse
  /-- The composition `inverse ⋙ functor` is equal to the identity. -/
  counit_eq : inverse ⋙ functor = 𝟭 D

variable (C) in
/-- The identity isomorphism of categories. -/
@[simps, refl]
/-
**CategoryTheory.IsoCat.refl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsoCat`。
形式化陈述：(C : Type u_1) → [inst : CategoryTheory.Category.{v_1, u_1} C] → CategoryT
heory.IsoCat C C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity isomorphism of categories.
-/
def IsoCat.refl : IsoCat C C where
  functor := 𝟭 C
  inverse := 𝟭 C
  unit_eq := (Functor.comp_id _).symm
  counit_eq := Functor.comp_id _

/-- The inverse isomorphism of categories, obtained by swapping `functor` and `inverse`. -/
@[simps, symm]
/-
**CategoryTheory.IsoCat.symm** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsoCat`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] → CategoryTh
eory.IsoCat C D → CategoryTheory.IsoCat D C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse isomorphism of categories, obtained by swapping `functor` and `inver
se`.
-/
def IsoCat.symm (e : IsoCat C D) : IsoCat D C where
  functor := e.inverse
  inverse := e.functor
  unit_eq := e.counit_eq.symm
  counit_eq := e.unit_eq.symm

/-- Composition of isomorphisms of categories. -/
@[simps, trans]
/-
**CategoryTheory.IsoCat.trans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsoCat`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     {E : Type u_3} →       [inst : Cat
egoryTheory.Category.{v_1, u_1} C] →         [inst_1 : CategoryTheory.Category.{
v_2, u_2} D] →           [inst_2 : CategoryTheory.Category.{v_3, u_3} E] →      
       CategoryTheory.IsoCat C D → CategoryTheory.IsoCat D E → CategoryTheory.Is
oCat C E
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of isomorphisms of categories.
-/
def IsoCat.trans (e : IsoCat C D) (f : IsoCat D E) : IsoCat C E where
  functor := e.functor ⋙ f.functor
  inverse := f.inverse ⋙ e.inverse
  unit_eq := by
    rw [Functor.assoc, ← Functor.assoc f.functor, ← f.unit_eq, Functor.id_comp]
    exact e.unit_eq
  counit_eq := by
    rw [Functor.assoc, ← Functor.assoc e.inverse, e.counit_eq, Functor.id_comp]
    exact f.counit_eq

namespace Functor

/-- A functor `F : C ⥤ D` is an isomorphism of categories if it is full, faithful and
bijective on objects. Such a functor has a strict inverse `Functor.strictInv` and assembles
into an `IsoCat` via `Functor.asIsomorphism`. -/
/-
**CategoryTheory.Functor.IsIso** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] → CategoryTh
eory.Functor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` is an isomorphism of categories if it is full, faithful an
d
bijective on objects. Such a functor has a strict inverse `Functor.strictInv` an
d assembles
into an `IsoCat` via `Functor.asIsomorphism`.
-/
protected class IsIso (F : C ⥤ D) : Prop where
  /-- A functor which is an isomorphism of categories is faithful. -/
  faithful : F.Faithful := by infer_instance
  /-- A functor which is an isomorphism of categories is full. -/
  full : F.Full := by infer_instance
  /-- A functor which is an isomorphism of categories is bijective on objects. -/
  bijective_obj (F) : F.obj.Bijective

export Functor.IsIso (bijective_obj)

attribute [instance] Functor.IsIso.faithful Functor.IsIso.full
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (𝟭 C).IsIso where
  bijective_obj := Function.bijective_id

variable [F.IsIso] [G.IsIso]

/-- The bijection on objects induced by a functor that is an isomorphism of categories. -/
/-
**CategoryTheory.Functor.objEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：objEquiv : C ≃ D
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsIso.bijective_obj`：∀ {C : Type u_1} {D : Type u
_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} D} (F : Categor…

--- 原说明 ---
The bijection on objects induced by a functor that is an isomorphism of categori
es.
-/
noncomputable def objEquiv : C ≃ D := .ofBijective _ (F.bijective_obj)

@[simp]
/-
**CategoryTheory.Functor.objEquiv_symm_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：objEquiv_symm_apply_apply (X : C) : F.objEquiv.symm (F.obj X) = X
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma objEquiv_symm_apply_apply (X : C) :
    F.objEquiv.symm (F.obj X) = X :=
  F.objEquiv.symm_apply_apply X

@[simp]
/-
**CategoryTheory.Functor.objEquiv_apply_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：objEquiv_apply_symm_apply (Y : D) : F.obj (F.objEquiv.symm Y) = Y
参数：Y : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma objEquiv_apply_symm_apply (Y : D) :
    F.obj (F.objEquiv.symm Y) = Y :=
  F.objEquiv.apply_symm_apply Y
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : F.IsEquivalence where
  essSurj := ⟨fun Y ↦ ⟨F.objEquiv.symm Y, ⟨eqToIso (by simp)⟩⟩⟩

/-- The strict inverse of a functor that is an isomorphism of categories, defined using
`Functor.objEquiv` on objects and `Functor.preimage` on morphisms. -/
@[no_expose]
/-
**CategoryTheory.Functor.strictInv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：strictInv : D ⥤ C where obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Functor.IsIso.full`：∀ {C : Type u_1} {D : Type u_2} {inst
 : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryTheory.Category.{v_
2, u_2} D} {F : Categor…

--- 原说明 ---
The strict inverse of a functor that is an isomorphism of categories, defined us
ing
`Functor.objEquiv` on objects and `Functor.preimage` on morphisms.
-/
noncomputable def strictInv : D ⥤ C where
  obj := F.objEquiv.symm
  map f := F.preimage (eqToHom (by simp) ≫ f ≫ eqToHom (by simp))
  map_comp _ _ := by simp [← preimage_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functor that is an isomorphism of categories assembles into an `IsoCat`,
with `Functor.strictInv` as its inverse. -/
/-
**CategoryTheory.Functor.asIsomorphism** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：asIsomorphism : IsoCat C D where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor that is an isomorphism of categories assembles into an `IsoCat`,
with `Functor.strictInv` as its inverse.
-/
noncomputable def asIsomorphism : IsoCat C D where
  functor := F
  inverse := F.strictInv
  unit_eq :=
    ext (fun x ↦ by simp [strictInv])
      (fun _ _ _ ↦ F.map_injective (by simp [eqToHom_map, strictInv]))
  counit_eq :=
    ext (fun x ↦ by simp [strictInv])
      (fun _ _ _ ↦ by simp [strictInv])

end Functor

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence of categories underlying an `IsoCat`, with the unit and counit
isomorphisms induced by the defining equalities. -/
/-
**CategoryTheory.IsoCat.toEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
IsoCat`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] → CategoryTh
eory.IsoCat C D → (C ≌ D)
参数：C ≌ D。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsoCat.unit_eq`：∀ {C : Type u_1} {D : Type u_2} [inst : C
ategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u
_2} D] (self : Cate…
· 使用定理 `CategoryTheory.IsoCat.counit_eq`：∀ {C : Type u_1} {D : Type u_2} [inst :
 CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2,
 u_2} D] (self : Cate…

--- 原说明 ---
The equivalence of categories underlying an `IsoCat`, with the unit and counit
isomorphisms induced by the defining equalities.
-/
def IsoCat.toEquivalence (e : IsoCat C D) : C ≌ D where
  functor := e.functor
  inverse := e.inverse
  unitIso := eqToIso e.unit_eq
  counitIso := eqToIso e.counit_eq
  functor_unitIso_comp X := by simp [eqToHom_map]

/-- Promotes an equivalence of categories `e : C ≌ D` whose unit and counit isomorphisms are
given by equalities of objects into an `IsoCat C D`. -/
@[simps]
/-
**CategoryTheory.Equivalence.toIsoCat** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Equivalence`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         (e
 : C ≌ D) →           (h : ∀ (X : C), e.inverse.obj (e.functor.obj X) = X) →    
         (h' : ∀ (Y : D), e.functor.obj (e.inverse.obj Y) = Y) →               a
utoParam (∀ (X : C), e.unitIso.hom.app X = CategoryTheory.eqToHom ⋯)            
       CategoryTheory.Equivalence.toIsoCat._auto_1 →                 autoParam (
∀ (Y : D), e.counitIso.hom.app Y = CategoryTheory.eqToHom ⋯)                    
 CategoryTheory.Equivalence.toIsoCat._auto_3 →                   CategoryTheory.
IsoCat C D
参数：e : C ≌ D；h : ∀ (X : C), e.inverse.obj (e.functor.obj X) = X；h' : ∀ (Y : D), 
e.functor.obj (e.inverse.obj Y) = Y；∀ (X : C), e.unitIso.hom.app X = CategoryThe
ory.eqToHom ⋯；∀ (Y : D), e.counitIso.hom.app Y = CategoryTheory.eqToHom ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Promotes an equivalence of categories `e : C ≌ D` whose unit and counit isomorph
isms are
given by equalities of objects into an `IsoCat C D`.
-/
def Equivalence.toIsoCat (e : C ≌ D)
    (h : ∀ (X : C), e.inverse.obj (e.functor.obj X) = X)
    (h' : ∀ (Y : D), e.functor.obj (e.inverse.obj Y) = Y)
    (k : ∀ (X : C), e.unitIso.hom.app X = eqToHom (h X).symm := by cat_disch)
    (k' : ∀ (Y : D), e.counitIso.hom.app Y = eqToHom (h' Y) := by cat_disch) : IsoCat C D where
  functor := e.functor
  inverse := e.inverse
  unit_eq := Functor.ext_of_iso e.unitIso (by simp [h])
  counit_eq := Functor.ext_of_iso e.counitIso (by simp [h'])
/-
**CategoryTheory.IsoCat.isIso_functor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
IsoCat`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (e : CategoryTheory.IsoCat
 C D), e.functor.IsIso
参数：e : CategoryTheory.IsoCat C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `CategoryTheory.IsoCat.unit_eq`：∀ {C : Type u_1} {D : Type u_2} [inst : C
ategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u
_2} D] (self : Cate…
· 使用定理 `CategoryTheory.IsoCat.counit_eq`：∀ {C : Type u_1} {D : Type u_2} [inst :
 CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2,
 u_2} D] (self : Cate…
-/
instance IsoCat.isIso_functor (e : IsoCat C D) : e.functor.IsIso where
  faithful := e.toEquivalence.faithful_functor
  full := e.toEquivalence.full_functor
  bijective_obj := Function.bijective_iff_has_inverse.mpr
    ⟨e.inverse.obj, fun X => (Functor.congr_obj e.unit_eq X).symm,
      Functor.congr_obj e.counit_eq⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (e : IsoCat C D) : e.inverse.IsIso := e.symm.isIso_functor
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.IsIso] : F.strictInv.IsIso := F.asIsomorphism.symm.isIso_functor
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.IsIso] [G.IsIso] : (F ⋙ G).IsIso :=
  (F.asIsomorphism.trans G.asIsomorphism).isIso_functor

end CategoryTheory

