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


/--
Definition of `TwoP` / `TwoP` 的定义

English:
structure TwoP
  parameters: : Type (u + 1) where
  axioms and operations (2):
    - X : Type u
    - toTwoPointing : TwoPointing X

中文:
结构 TwoP
  参数: : 类型 (u + 1) where
  公理与运算 (2 个):
    - X : 类型u
    - toTwoPointing : TwoPointing X
-/
structure TwoP : Type (u + 1) where
  /-- The underlying type of a two-pointed type. -/
  protected X : Type u
  /-- The two points of a bipointed type, bundled together as a pair of distinct elements. -/
  toTwoPointing : TwoPointing X

namespace TwoP

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort TwoP Type*
  body: ⟨TwoP.X⟩

中文:
实例 :
  签名: CoeSort TwoP 类型
  定义体: ⟨TwoP.X⟩

Depends on / 依赖: TwoP.X
-/
instance : CoeSort TwoP Type* :=
  ⟨TwoP.X⟩

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: {X : Type*} (toTwoPointing : TwoPointing X)
  body: ⟨X, toTwoPointing⟩

中文:
缩写 of
  签名: {X : 类型} (toTwoPointing : TwoPointing X)
  定义体: ⟨X, toTwoPointing⟩

Depends on / 依赖: toTwoPointing
-/
abbrev of {X : Type*} (toTwoPointing : TwoPointing X) : TwoP :=
  ⟨X, toTwoPointing⟩

/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: {X : Type*} (toTwoPointing : TwoPointing X)
  statement: ↥(of toTwoPointing) = X
  proof: rfl

alias _root_.TwoPointing.TwoP := of

中文:
定理 coe_of
  条件: {X : 类型} (toTwoPointing : TwoPointing X)
  结论: ↥(of toTwoPointing) = X
  证明: rfl

alias _root_.TwoPointing.TwoP := of
-/
theorem coe_of {X : Type*} (toTwoPointing : TwoPointing X) : ↥(of toTwoPointing) = X :=
  rfl

alias _root_.TwoPointing.TwoP := of

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited TwoP
  body: ⟨of TwoPointing.bool⟩

中文:
实例 :
  签名: 可居 TwoP
  定义体: ⟨of TwoPointing.bool⟩

Depends on / 依赖: TwoPointing, TwoPointing.bool
-/
instance : Inhabited TwoP :=
  ⟨of TwoPointing.bool⟩

/--
Definition of `toBipointed` / `toBipointed` 的定义

English:
definition toBipointed
  signature: (X : TwoP)
  body: X.toTwoPointing.toProd.Bipointed

@[simp]

中文:
定义 toBipointed
  签名: (X : TwoP)
  定义体: X.toTwoPointing.toProd.Bipointed

@[simp]

Depends on / 依赖: Bipointed, X.toTwoPointing.toProd.Bipointed, toProd, toTwoPointing
-/
noncomputable def toBipointed (X : TwoP) : Bipointed :=
  X.toTwoPointing.toProd.Bipointed

@[simp]
/--
theorem `coe_toBipointed` / 定理 `coe_toBipointed`

English:
theorem coe_toBipointed
  given: (X : TwoP)
  statement: ↥X.toBipointed = ↥X
  proof: rfl

中文:
定理 coe_toBipointed
  条件: (X : TwoP)
  结论: ↥X.toBipointed = ↥X
  证明: rfl
-/
theorem coe_toBipointed (X : TwoP) : ↥X.toBipointed = ↥X :=
  rfl

/--
Instance `largeCategory` / 实例 `largeCategory`

English:
instance largeCategory
  signature: : LargeCategory TwoP
  body: inferInstanceAs Category (InducedCategory _ toBipointed)

中文:
实例 largeCategory
  签名: : 大范畴 TwoP
  定义体: inferInstanceAs Category (InducedCategory _ toBipointed)

Depends on / 依赖: Category, InducedCategory, toBipointed
-/
noncomputable instance largeCategory : LargeCategory TwoP :=
inferInstanceAs Category (InducedCategory _ toBipointed)

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `concreteCategory` / 实例 `concreteCategory`

English:
instance concreteCategory
  signature: : ConcreteCategory TwoP
  body: inferInstanceAs ConcreteCategory (InducedCategory _ toBipointed) _

中文:
实例 concreteCategory
  签名: : 余ncrete范畴 TwoP
  定义体: inferInstanceAs ConcreteCategory (InducedCategory _ toBipointed) _

Depends on / 依赖: ConcreteCategory, InducedCategory, toBipointed
-/
noncomputable instance concreteCategory : ConcreteCategory TwoP
    (fun X Y => Bipointed.HomSubtype X.toBipointed Y.toBipointed) :=
inferInstanceAs ConcreteCategory (InducedCategory _ toBipointed) _

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `hasForgetToBipointed` / 实例 `hasForgetToBipointed`

English:
instance hasForgetToBipointed
  signature: : HasForget₂ TwoP Bipointed
  body: inferInstanceAs HasForget₂ (InducedCategory _ toBipointed) _

@[ext]

中文:
实例 hasForgetToBipointed
  签名: : 有Forget₂ TwoP Bipointed
  定义体: inferInstanceAs HasForget₂ (InducedCategory _ toBipointed) _

@[ext]

Depends on / 依赖: InducedCategory, toBipointed
-/
noncomputable instance hasForgetToBipointed : HasForget₂ TwoP Bipointed :=
inferInstanceAs HasForget₂ (InducedCategory _ toBipointed) _

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : TwoP} {f g : X ⟶ Y} (h : f.hom = g.hom)
  statement: f = g
  proof: InducedCategory.hom_ext h

中文:
引理 hom_ext
  条件: {X Y : TwoP} {f g : X ⟶ Y} (h : f.hom = g.hom)
  结论: f = g
  证明: InducedCategory.hom_ext h

Depends on / 依赖: InducedCategory, InducedCategory.hom_ext, hom_ext
-/
lemma hom_ext {X Y : TwoP} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  InducedCategory.hom_ext h

/-- Swaps the pointed elements of a two-pointed type. `TwoPointing.swap` as a functor. -/
@[simps]
/--
Definition of `swap` / `swap` 的定义

English:
definition swap
  signature: : TwoP ⥤ TwoP where
  body: ⟨X, X.toTwoPointing.swap⟩
  map f :=
    InducedCategory.homMk
      { toFun := f.hom
        map_fst := f.hom.map_snd
        map_snd := f.hom.map_fst }

#adaptation_note

中文:
定义 swap
  签名: : TwoP ⥤ TwoP where
  定义体: ⟨X, X.toTwoPointing.swap⟩
  map f :=
    InducedCategory.homMk
      { toFun := f.hom
        map_fst := f.hom.map_snd
        map_snd := f.hom.map_fst }

#adaptation_note

Depends on / 依赖: X.toTwoPointing.swap, toTwoPointing
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
/--
Definition of `swapEquiv` / `swapEquiv` 的定义

English:
definition swapEquiv
  signature: : TwoP ≌ TwoP where
  body: swap
  inverse := swap
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simp]

中文:
定义 swapEquiv
  签名: : TwoP ≌ TwoP where
  定义体: swap
  inverse := swap
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simp]
-/
noncomputable def swapEquiv : TwoP ≌ TwoP where
  functor := swap
  inverse := swap
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simp]
/--
theorem `swapEquiv_symm` / 定理 `swapEquiv_symm`

English:
theorem swapEquiv_symm
  statement: swapEquiv.symm = swapEquiv
  proof: rfl

中文:
定理 swapEquiv_symm
  结论: swapEquiv.symm = swapEquiv
  证明: rfl
-/
theorem swapEquiv_symm : swapEquiv.symm = swapEquiv :=
  rfl

end TwoP

set_option backward.isDefEq.respectTransparency.types false in
@[simp, nolint simpNF] -- mathlib builds without this simp attribute
/--
theorem `TwoP_swap_comp_forget_to_Bipointed` / 定理 `TwoP_swap_comp_forget_to_Bipointed`

English:
theorem TwoP_swap_comp_forget_to_Bipointed
  proof: rfl

中文:
定理 TwoP_swap_comp_forget_to_Bipointed
  证明: rfl
-/
theorem TwoP_swap_comp_forget_to_Bipointed :
    TwoP.swap ⋙ forget₂ TwoP Bipointed = forget₂ TwoP Bipointed ⋙ Bipointed.swap :=
  rfl

/-- The functor from `Pointed` to `TwoP` which adds a second point. -/
@[simps]
/--
Definition of `pointedToTwoPFst` / `pointedToTwoPFst` 的定义

English:
definition pointedToTwoPFst
  signature: : Pointed.{u} ⥤ TwoP where
  body: ⟨Option X, ⟨X.point, none⟩, some_ne_none _⟩
  map f := ⟨Option.map f.toFun, congr_arg _ f.map_point, rfl⟩
  map_comp f g := by
    ext : 3
    exact (Option.map_comp_map f.1 g.1).symm

中文:
定义 pointedToTwoPFst
  签名: : Pointed.{u} ⥤ TwoP where
  定义体: ⟨Option X, ⟨X.point, none⟩, some_ne_none _⟩
  map f := ⟨Option.map f.toFun, congr_arg _ f.map_point, rfl⟩
  map_comp f g := by
    ext : 3
    exact (Option.map_comp_map f.1 g.1).symm

Depends on / 依赖: X.point, some_ne_none
-/
noncomputable def pointedToTwoPFst : Pointed.{u} ⥤ TwoP where
  obj X := ⟨Option X, ⟨X.point, none⟩, some_ne_none _⟩
  map f := ⟨Option.map f.toFun, congr_arg _ f.map_point, rfl⟩
  map_comp f g := by
    ext : 3
    exact (Option.map_comp_map f.1 g.1).symm

/-- The functor from `Pointed` to `TwoP` which adds a first point. -/
@[simps]
/--
Definition of `pointedToTwoPSnd` / `pointedToTwoPSnd` 的定义

English:
definition pointedToTwoPSnd
  signature: : Pointed.{u} ⥤ TwoP where
  body: ⟨Option X, ⟨none, X.point⟩, (some_ne_none _).symm⟩
  map f := ⟨Option.map f.toFun, rfl, congr_arg _ f.map_point⟩
  map_comp f g := by
    ext : 3
    exact (Option.map_comp_map f.1 g.1).symm

@[simp]

中文:
定义 pointedToTwoPSnd
  签名: : Pointed.{u} ⥤ TwoP where
  定义体: ⟨Option X, ⟨none, X.point⟩, (some_ne_none _).symm⟩
  map f := ⟨Option.map f.toFun, rfl, congr_arg _ f.map_point⟩
  map_comp f g := by
    ext : 3
    exact (Option.map_comp_map f.1 g.1).symm

@[simp]

Depends on / 依赖: X.point, some_ne_none
-/
noncomputable def pointedToTwoPSnd : Pointed.{u} ⥤ TwoP where
  obj X := ⟨Option X, ⟨none, X.point⟩, (some_ne_none _).symm⟩
  map f := ⟨Option.map f.toFun, rfl, congr_arg _ f.map_point⟩
  map_comp f g := by
    ext : 3
    exact (Option.map_comp_map f.1 g.1).symm

@[simp]
/--
theorem `pointedToTwoPFst_comp_swap` / 定理 `pointedToTwoPFst_comp_swap`

English:
theorem pointedToTwoPFst_comp_swap
  statement: pointedToTwoPFst ⋙ TwoP.swap = pointedToTwoPSnd
  proof: rfl

@[simp]

中文:
定理 pointedToTwoPFst_comp_swap
  结论: pointedToTwoPFst ⋙ TwoP.swap = pointedToTwoPSnd
  证明: rfl

@[simp]
-/
theorem pointedToTwoPFst_comp_swap : pointedToTwoPFst ⋙ TwoP.swap = pointedToTwoPSnd :=
  rfl

@[simp]
/--
theorem `pointedToTwoPSnd_comp_swap` / 定理 `pointedToTwoPSnd_comp_swap`

English:
theorem pointedToTwoPSnd_comp_swap
  statement: pointedToTwoPSnd ⋙ TwoP.swap = pointedToTwoPFst
  proof: rfl

中文:
定理 pointedToTwoPSnd_comp_swap
  结论: pointedToTwoPSnd ⋙ TwoP.swap = pointedToTwoPFst
  证明: rfl
-/
theorem pointedToTwoPSnd_comp_swap : pointedToTwoPSnd ⋙ TwoP.swap = pointedToTwoPFst :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp, nolint simpNF] -- mathlib builds without this simp attribute
/--
theorem `pointedToTwoPFst_comp_forget_to_bipointed` / 定理 `pointedToTwoPFst_comp_forget_to_bipointed`

English:
theorem pointedToTwoPFst_comp_forget_to_bipointed
  proof: rfl

中文:
定理 pointedToTwoPFst_comp_forget_to_bipointed
  证明: rfl
-/
theorem pointedToTwoPFst_comp_forget_to_bipointed :
    pointedToTwoPFst ⋙ forget₂ TwoP Bipointed = pointedToBipointedFst :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp, nolint simpNF] -- mathlib builds without this simp attribute
/--
theorem `pointedToTwoPSnd_comp_forget_to_bipointed` / 定理 `pointedToTwoPSnd_comp_forget_to_bipointed`

English:
theorem pointedToTwoPSnd_comp_forget_to_bipointed
  proof: rfl

中文:
定理 pointedToTwoPSnd_comp_forget_to_bipointed
  证明: rfl
-/
theorem pointedToTwoPSnd_comp_forget_to_bipointed :
    pointedToTwoPSnd ⋙ forget₂ TwoP Bipointed = pointedToBipointedSnd :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `pointedToTwoPFstForgetCompBipointedToPointedFstAdjunction` / `pointedToTwoPFstForgetCompBipointedToPointedFstAdjunction` 的定义

English:
definition pointedToTwoPFstForgetCompBipointedToPointedFstAdjunction
  signature: :
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.hom.toFun ∘ Option.some, f.hom.map_fst⟩
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.2 f.toFun, f.map_point, rfl⟩
          left_inv := fun f => by
            ext (_ | _) : 4
            · exact f.hom.map_snd.symm
            · rfl }
      homEquiv_naturality_left_symm := fun f g => by ext (_ | _) : 4 <;> rfl }

中文:
定义 pointedToTwoPFstForgetCompBipointedToPointedFstAdjunction
  签名: :
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.hom.toFun ∘ Option.some, f.hom.map_fst⟩
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.2 f.toFun, f.map_point, rfl⟩
          left_inv := fun f => by
            ext (_ | _) : 4
            · exact f.hom.map_snd.symm
            · rfl }
      homEquiv_naturality_left_symm := fun f g => by ext (_ | _) : 4 <;> rfl }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, Option.some, Y.toTwoPointing.toProd, f.hom.map_fst, f.hom.map_snd.symm, f.hom.toFun, f.map_point, f.toFun, homEquiv, homEquiv_naturality_left_symm, invFun, left_inv, map_fst, map_point, map_snd, mkOfHomEquiv, o.elim, toProd, toTwoPointing
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
/--
Definition of `pointedToTwoPSndForgetCompBipointedToPointedSndAdjunction` / `pointedToTwoPSndForgetCompBipointedToPointedSndAdjunction` 的定义

English:
definition pointedToTwoPSndForgetCompBipointedToPointedSndAdjunction
  signature: :
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.hom.toFun ∘ Option.some, f.hom.map_snd⟩
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.1 f.toFun, rfl, f.map_point⟩
          left_inv := fun f => by
            ext (_ | _) : 4
            · exact f.hom.map_fst.symm
            · rfl }
      homEquiv_naturality_left_symm := fun f g => by
        ext (_ | _) : 4 <;> rfl }

中文:
定义 pointedToTwoPSndForgetCompBipointedToPointedSndAdjunction
  签名: :
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.hom.toFun ∘ Option.some, f.hom.map_snd⟩
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.1 f.toFun, rfl, f.map_point⟩
          left_inv := fun f => by
            ext (_ | _) : 4
            · exact f.hom.map_fst.symm
            · rfl }
      homEquiv_naturality_left_symm := fun f g => by
        ext (_ | _) : 4 <;> rfl }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, Option.some, Y.toTwoPointing.toProd, f.hom.map_fst.symm, f.hom.map_snd, f.hom.toFun, f.map_point, f.toFun, homEquiv, homEquiv_naturality_left_symm, invFun, left_inv, map_fst, map_point, map_snd, mkOfHomEquiv, o.elim, toProd, toTwoPointing
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
