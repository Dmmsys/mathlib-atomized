/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.CategoryTheory.Category.Pointed
public import Mathlib.Data.PFun

/-!
# The category of types with partial functions

This defines `PartialFun`, the category of types equipped with partial functions.

This category is classically equivalent to the category of pointed types. The reason it doesn't hold
constructively stems from the difference between `Part` and `Option`. Both can model partial
functions, but the latter forces a decidable domain.

Precisely, `PartialFunToPointed` turns a partial function `α →. β` into a function
`Option α → Option β` by sending to `none` the undefined values (and `none` to `none`). But being
defined is (generally) undecidable while being sent to `none` is decidable. So it can't be
constructive.

## References

* [nLab, *The category of sets and partial functions*]
  (https://ncatlab.org/nlab/show/partial+function)
-/

@[expose] public section

open CategoryTheory Option

universe u

/-- The category of types equipped with partial functions. -/
/-
**PartialFun** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PartialFun : Type (u + 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of types equipped with partial functions.
-/
def PartialFun : Type (u + 1) := Type u

namespace PartialFun

/-
**PartialFun.** 是 Mathlib 中的一个实例，位于命名空间 `PartialFun`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort PartialFun Type* :=
  ⟨id⟩

/-- Turns a type into a `PartialFun`. -/
/-
**PartialFun.of** 是 Mathlib 中的一个定义，位于命名空间 `PartialFun`。
形式化陈述：of : Type* -> PartialFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turns a type into a `PartialFun`.
-/
def of : Type* → PartialFun :=
  id
/-
**PartialFun.** 是 Mathlib 中的一个实例，位于命名空间 `PartialFun`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited PartialFun.{u} :=
  ⟨PartialFun.of PUnit⟩

-- TODO: wrap morphisms in this category into a one-field `PFun.Hom` structure
set_option backward.isDefEq.respectTransparency.types false in
/-
**PartialFun.largeCategory** 是 Mathlib 中的一个实例，位于命名空间 `PartialFun`。
形式化陈述：largeCategory : LargeCategory.{u} PartialFun where Hom X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance largeCategory : LargeCategory.{u} PartialFun where
  Hom X Y := PFun X Y
  id X := PFun.id X
  comp f g := g.comp f

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructs a partial function isomorphism between types from an equivalence between them. -/
@[simps]
/-
**PartialFun.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `PartialFun.Iso`。
形式化陈述：{α β : PartialFun} → α ≃ β → (α ≅ β)
参数：α ≅ β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Constructs a partial function isomorphism between types from an equivalence betw
een them.
-/
def Iso.mk {α β : PartialFun.{u}} (e : α ≃ β) : α ≅ β where
  hom x := e x
  inv x := e.symm x
  hom_inv_id := (PFun.coe_comp _ _).symm.trans (by
    simp only [Equiv.symm_comp_self, PFun.coe_id]
    rfl)
  inv_hom_id := (PFun.coe_comp _ _).symm.trans (by
    simp only [Equiv.self_comp_symm, PFun.coe_id]
    rfl)

end PartialFun

set_option backward.isDefEq.respectTransparency.types false in
/-- The forgetful functor from `Type` to `PartialFun` which forgets that the maps are total. -/
/-
**typeToPartialFun** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：typeToPartialFun : Type u ⥤ PartialFun where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `Type` to `PartialFun` which forgets that the maps ar
e total.
-/
def typeToPartialFun : Type u ⥤ PartialFun where
  obj := id
  map f := PFun.lift (f : _ → _)
  map_comp _ _ := PFun.coe_comp _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : typeToPartialFun.Faithful where
  map_injective h := by
    ext x
    exact congrFun (PFun.lift_injective h) x

-- b ∈ PFun.toSubtype (fun x ↦ x ≠ X.point) Subtype.val a ↔ b ∈ Part.some a
set_option backward.isDefEq.respectTransparency false in
/-- The functor which deletes the point of a pointed type. In return, this makes the maps partial.
This is the computable part of the equivalence `PartialFunEquivPointed`. -/
@[simps obj map]
/-
**pointedToPartialFun** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：pointedToPartialFun : Pointed.{u} ⥤ PartialFun where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor which deletes the point of a pointed type. In return, this makes the
 maps partial.
This is the computable part of the equivalence `PartialFunEquivPointed`.
-/
def pointedToPartialFun : Pointed.{u} ⥤ PartialFun where
  obj X := PartialFun.of { x : X // x ≠ X.point }
  map f := PFun.toSubtype _ f.toFun ∘ Subtype.val
  map_id _ :=
    PFun.ext fun _ b =>
      PFun.mem_toSubtype_iff (b := b).trans (Subtype.coe_inj.trans Part.mem_some_iff.symm)
  map_comp {X Y Z} f g := by
    refine PFun.ext fun ⟨a, ha⟩ ⟨c, hc⟩ =>
      (PFun.mem_toSubtype_iff.trans ?_).trans Part.mem_bind_iff.symm
    suffices c = g.toFun (f.toFun a) → ¬Y.point = f.toFun a ∧ ¬Z.point = g.toFun (f.toFun a) from
      ⟨by aesop, by simp; grind⟩
    rintro rfl
    refine ⟨fun h => hc.symm <| g.map_point ▸ congr_arg g.toFun h, hc.symm⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor which maps undefined values to a new point. This makes the maps total and creates
pointed types. This is the noncomputable part of the equivalence `PartialFunEquivPointed`. It can't
be computable because `= Option.none` is decidable while the domain of a general `Part` isn't. -/
@[simps obj map]
/-
**partialFunToPointed** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：partialFunToPointed : PartialFun ⥤ Pointed
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…

--- 原说明 ---
The functor which maps undefined values to a new point. This makes the maps tota
l and creates
pointed types. This is the noncomputable part of the equivalence `PartialFunEqui
vPointed`. It can't
be computable because `= Option.none` is decidable while the domain of a general
 `Part` isn't.
-/
noncomputable def partialFunToPointed : PartialFun ⥤ Pointed := by
  classical
  exact
    { obj := fun X => ⟨(Option X), none⟩
      map := fun f => ⟨Option.elim' none fun a => (f a).toOption, rfl⟩
      map_id := fun X => Pointed.Hom.ext <| funext fun o => Option.recOn o rfl fun a => (by
        dsimp [CategoryStruct.id]
        convert! Part.some_toOption a)
      map_comp := fun f g => Pointed.Hom.ext <| funext fun o => Option.recOn o rfl fun a => by
        dsimp [CategoryStruct.comp]
        rw [Part.bind_toOption g (f a), Option.elim'_eq_elim] }

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence induced by `PartialFunToPointed` and `PointedToPartialFun`.
`Part.equivOption` made functorial. -/
@[simps!]
/-
**partialFunEquivPointed** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：partialFunEquivPointed : PartialFun.{u} ≌ Pointed where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence induced by `PartialFunToPointed` and `PointedToPartialFun`.
`Part.equivOption` made functorial.
-/
noncomputable def partialFunEquivPointed : PartialFun.{u} ≌ Pointed where
  functor := partialFunToPointed
  inverse := pointedToPartialFun
  unitIso := NatIso.ofComponents (fun X => PartialFun.Iso.mk
      { toFun := fun a => ⟨some a, some_ne_none a⟩
        invFun := fun a => Option.get _ (Option.ne_none_iff_isSome.1 a.2)
        left_inv := fun _ => Option.get_some _ _
        right_inv := fun a => by simp only [some_get, Subtype.coe_eta] })
      fun f =>
        PFun.ext fun a b => by
          dsimp [PartialFun.Iso.mk, CategoryStruct.comp, pointedToPartialFun]
          rw [Part.bind_some]
          refine (Part.mem_bind_iff.trans ?_).trans PFun.mem_toSubtype_iff.symm
          obtain ⟨b | b, hb⟩ := b
          · exact (hb rfl).elim
          · simp only [ne_eq, Part.mem_some_iff]
            classical
            refine ⟨fun ⟨w, hw, h⟩ ↦ ?_, fun h ↦ ⟨b, Part.mem_toOption.mp h.symm, rfl⟩⟩
            rw [Subtype.ext_iff] at h
            dsimp at h
            rw [h]
            rw [← Part.mem_toOption, mem_def] at hw
            exact hw.symm
  counitIso :=
    NatIso.ofComponents
      (fun X ↦ Pointed.Iso.mk (by classical exact Equiv.optionSubtypeNe X.point) rfl)
      fun {X Y} f ↦ Pointed.Hom.ext <| funext fun a ↦ by
        obtain _ | ⟨a, ha⟩ := a
        · exact f.map_point.symm
        simp_all [Equiv.optionSubtypeNe, Equiv.optionSubtype,
          Option.casesOn'_eq_elim, Part.elim_toOption]
  functor_unitIso_comp X := by
    ext (_ | x)
    · rfl
    · simp
      rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Forgetting that maps are total and making them total again by adding a point is the same as just
adding a point. -/
@[simps!]
/-
**typeToPartialFunIsoPartialFunToPointed** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：typeToPartialFunIsoPartialFunToPointed : typeToPartialFun ⋙ partialFunToPo
inted ≅ typeToPointed
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Forgetting that maps are total and making them total again by adding a point is 
the same as just
adding a point.
-/
noncomputable def typeToPartialFunIsoPartialFunToPointed :
    typeToPartialFun ⋙ partialFunToPointed ≅ typeToPointed :=
  NatIso.ofComponents
    (fun _ =>
      { hom := ⟨id, rfl⟩
        inv := ⟨id, rfl⟩
        hom_inv_id := rfl
        inv_hom_id := rfl })
    fun f =>
    Pointed.Hom.ext <|
      funext fun a => Option.recOn a rfl fun a => by
        convert! Part.some_toOption _
        simpa using! (Part.get_eq_iff_mem (by trivial)).mp rfl
