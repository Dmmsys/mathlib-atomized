/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.CategoryTheory.Category.Bipointed
public import Mathlib.Data.TwoPointing

/-!
# The category of two-pointed types

This defines `TwoP`, the category of two-pointed types.

## References

* [nLab, *coalgebra of the real interval*]
  (https://ncatlab.org/nlab/show/coalgebra+of+the+real+interval)
-/

@[expose] public section


open CategoryTheory Option

universe u

variable {α β : Type*}


/-- The category of two-pointed types. -/
/-
**TwoP** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of two-pointed types.
-/
structure TwoP : Type (u + 1) where
  /-- The underlying type of a two-pointed type. -/
  protected X : Type u
  /-- The two points of a bipointed type, bundled together as a pair of distinct elements. -/
  toTwoPointing : TwoPointing X

namespace TwoP

/-
**TwoP.** 是 Mathlib 中的一个实例，位于命名空间 `TwoP`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort TwoP Type* :=
  ⟨TwoP.X⟩

/-- Turns a two-pointing into a two-pointed type. -/
/-
**TwoP.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `TwoP`。
形式化陈述：of {X : Type*} (toTwoPointing : TwoPointing X) : TwoP
参数：toTwoPointing : TwoPointing X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turns a two-pointing into a two-pointed type.
-/
abbrev of {X : Type*} (toTwoPointing : TwoPointing X) : TwoP :=
  ⟨X, toTwoPointing⟩
/-
**TwoP.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `TwoP`。
形式化陈述：coe_of {X : Type*} (toTwoPointing : TwoPointing X) : ↥(of toTwoPointing) =
 X
参数：toTwoPointing : TwoPointing X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of {X : Type*} (toTwoPointing : TwoPointing X) : ↥(of toTwoPointing) = X :=
  rfl

alias _root_.TwoPointing.TwoP := of
/-
**TwoP.** 是 Mathlib 中的一个实例，位于命名空间 `TwoP`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited TwoP :=
  ⟨of TwoPointing.bool⟩

/-- Turns a two-pointed type into a bipointed type, by forgetting that the pointed elements are
distinct. -/
/-
**TwoP.toBipointed** 是 Mathlib 中的一个定义，位于命名空间 `TwoP`。
形式化陈述：toBipointed (X : TwoP) : Bipointed
参数：X : TwoP。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turns a two-pointed type into a bipointed type, by forgetting that the pointed e
lements are
distinct.
-/
noncomputable def toBipointed (X : TwoP) : Bipointed :=
  X.toTwoPointing.toProd.Bipointed

@[simp]
/-
**TwoP.coe_toBipointed** 是 Mathlib 中的一个定理，位于命名空间 `TwoP`。
形式化陈述：coe_toBipointed (X : TwoP) : ↥X.toBipointed = ↥X
参数：X : TwoP。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toBipointed (X : TwoP) : ↥X.toBipointed = ↥X :=
  rfl
/-
**TwoP.largeCategory** 是 Mathlib 中的一个实例，位于命名空间 `TwoP`。
形式化陈述：largeCategory : LargeCategory TwoP
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance largeCategory : LargeCategory TwoP :=
  inferInstanceAs <| Category (InducedCategory _ toBipointed)

set_option backward.isDefEq.respectTransparency.types false in
/-
**TwoP.concreteCategory** 是 Mathlib 中的一个实例，位于命名空间 `TwoP`。
形式化陈述：concreteCategory : ConcreteCategory TwoP (fun X Y => Bipointed.HomSubtype 
X.toBipointed Y.toBipointed)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance concreteCategory : ConcreteCategory TwoP
    (fun X Y => Bipointed.HomSubtype X.toBipointed Y.toBipointed) :=
  inferInstanceAs <| ConcreteCategory (InducedCategory _ toBipointed) _

set_option backward.isDefEq.respectTransparency.types false in
/-
**TwoP.hasForgetToBipointed** 是 Mathlib 中的一个实例，位于命名空间 `TwoP`。
形式化陈述：hasForgetToBipointed : HasForget₂ TwoP Bipointed
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance hasForgetToBipointed : HasForget₂ TwoP Bipointed :=
  inferInstanceAs <| HasForget₂ (InducedCategory _ toBipointed) _

@[ext]
/-
**TwoP.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `TwoP`。
形式化陈述：hom_ext {X Y : TwoP} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
参数：h : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.InducedCategory.hom_ext`：hom_ext {X Y : InducedCategory D
 F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
-/
lemma hom_ext {X Y : TwoP} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  InducedCategory.hom_ext h

/-- Swaps the pointed elements of a two-pointed type. `TwoPointing.swap` as a functor. -/
@[simps]
/-
**TwoP.swap** 是 Mathlib 中的一个定义，位于命名空间 `TwoP`。
形式化陈述：swap : TwoP ⥤ TwoP where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Swaps the pointed elements of a two-pointed type. `TwoPointing.swap` as a functo
r.
-/
noncomputable def swap : TwoP ⥤ TwoP where
  obj X := ⟨X, X.toTwoPointing.swap⟩
  map f :=
    InducedCategory.homMk
      { toFun := f.hom
        map_fst := f.hom.map_snd
        map_snd := f.hom.map_fst }

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence between `TwoP` and itself induced by `Prod.swap` both ways. -/
@[simps!]
/-
**TwoP.swapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `TwoP`。
形式化陈述：swapEquiv : TwoP ≌ TwoP where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `TwoP` and itself induced by `Prod.swap` both ways.
-/
noncomputable def swapEquiv : TwoP ≌ TwoP where
  functor := swap
  inverse := swap
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simp]
/-
**TwoP.swapEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `TwoP`。
形式化陈述：swapEquiv_symm : swapEquiv.symm = swapEquiv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swapEquiv_symm : swapEquiv.symm = swapEquiv :=
  rfl

end TwoP

set_option backward.isDefEq.respectTransparency.types false in
@[simp, nolint simpNF] -- mathlib builds without this simp attribute
/-
**TwoP_swap_comp_forget_to_Bipointed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TwoP_swap_comp_forget_to_Bipointed : TwoP.swap ⋙ forget₂ TwoP Bipointed = 
forget₂ TwoP Bipointed ⋙ Bipointed.swap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem TwoP_swap_comp_forget_to_Bipointed :
    TwoP.swap ⋙ forget₂ TwoP Bipointed = forget₂ TwoP Bipointed ⋙ Bipointed.swap :=
  rfl

/-- The functor from `Pointed` to `TwoP` which adds a second point. -/
@[simps]
/-
**pointedToTwoPFst** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：pointedToTwoPFst : Pointed.{u} ⥤ TwoP where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from `Pointed` to `TwoP` which adds a second point.
-/
noncomputable def pointedToTwoPFst : Pointed.{u} ⥤ TwoP where
  obj X := ⟨Option X, ⟨X.point, none⟩, some_ne_none _⟩
  map f := ⟨Option.map f.toFun, congr_arg _ f.map_point, rfl⟩
  map_comp f g := by
    ext : 3
    exact (Option.map_comp_map f.1 g.1).symm

/-- The functor from `Pointed` to `TwoP` which adds a first point. -/
@[simps]
/-
**pointedToTwoPSnd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：pointedToTwoPSnd : Pointed.{u} ⥤ TwoP where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from `Pointed` to `TwoP` which adds a first point.
-/
noncomputable def pointedToTwoPSnd : Pointed.{u} ⥤ TwoP where
  obj X := ⟨Option X, ⟨none, X.point⟩, (some_ne_none _).symm⟩
  map f := ⟨Option.map f.toFun, rfl, congr_arg _ f.map_point⟩
  map_comp f g := by
    ext : 3
    exact (Option.map_comp_map f.1 g.1).symm

@[simp]
/-
**pointedToTwoPFst_comp_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pointedToTwoPFst_comp_swap : pointedToTwoPFst ⋙ TwoP.swap = pointedToTwoPS
nd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointedToTwoPFst_comp_swap : pointedToTwoPFst ⋙ TwoP.swap = pointedToTwoPSnd :=
  rfl

@[simp]
/-
**pointedToTwoPSnd_comp_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pointedToTwoPSnd_comp_swap : pointedToTwoPSnd ⋙ TwoP.swap = pointedToTwoPF
st
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointedToTwoPSnd_comp_swap : pointedToTwoPSnd ⋙ TwoP.swap = pointedToTwoPFst :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp, nolint simpNF] -- mathlib builds without this simp attribute
/-
**pointedToTwoPFst_comp_forget_to_bipointed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pointedToTwoPFst_comp_forget_to_bipointed : pointedToTwoPFst ⋙ forget₂ Two
P Bipointed = pointedToBipointedFst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointedToTwoPFst_comp_forget_to_bipointed :
    pointedToTwoPFst ⋙ forget₂ TwoP Bipointed = pointedToBipointedFst :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp, nolint simpNF] -- mathlib builds without this simp attribute
/-
**pointedToTwoPSnd_comp_forget_to_bipointed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pointedToTwoPSnd_comp_forget_to_bipointed : pointedToTwoPSnd ⋙ forget₂ Two
P Bipointed = pointedToBipointedSnd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointedToTwoPSnd_comp_forget_to_bipointed :
    pointedToTwoPSnd ⋙ forget₂ TwoP Bipointed = pointedToBipointedSnd :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Adding a second point is left adjoint to forgetting the second point. -/
/-
**pointedToTwoPFstForgetCompBipointedToPointedFstAdjunction** 是 Mathlib 中的一个定义，位
于命名空间 ``。
形式化陈述：pointedToTwoPFstForgetCompBipointedToPointedFstAdjunction : pointedToTwoPF
st ⊣ forget₂ TwoP Bipointed ⋙ bipointedToPointedFst
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adding a second point is left adjoint to forgetting the second point.
-/
noncomputable def pointedToTwoPFstForgetCompBipointedToPointedFstAdjunction :
    pointedToTwoPFst ⊣ forget₂ TwoP Bipointed ⋙ bipointedToPointedFst :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.hom.toFun ∘ Option.some, f.hom.map_fst⟩
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.2 f.toFun, f.map_point, rfl⟩
          left_inv := fun f => by
            ext (_ | _) : 4
            · exact f.hom.map_snd.symm
            · rfl }
      homEquiv_naturality_left_symm := fun f g => by ext (_ | _) : 4 <;> rfl }

set_option backward.isDefEq.respectTransparency.types false in
/-- Adding a first point is left adjoint to forgetting the first point. -/
/-
**pointedToTwoPSndForgetCompBipointedToPointedSndAdjunction** 是 Mathlib 中的一个定义，位
于命名空间 ``。
形式化陈述：pointedToTwoPSndForgetCompBipointedToPointedSndAdjunction : pointedToTwoPS
nd ⊣ forget₂ TwoP Bipointed ⋙ bipointedToPointedSnd
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adding a first point is left adjoint to forgetting the first point.
-/
noncomputable def pointedToTwoPSndForgetCompBipointedToPointedSndAdjunction :
    pointedToTwoPSnd ⊣ forget₂ TwoP Bipointed ⋙ bipointedToPointedSnd :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.hom.toFun ∘ Option.some, f.hom.map_snd⟩
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.1 f.toFun, rfl, f.map_point⟩
          left_inv := fun f => by
            ext (_ | _) : 4
            · exact f.hom.map_fst.symm
            · rfl }
      homEquiv_naturality_left_symm := fun f g => by
        ext (_ | _) : 4 <;> rfl }
