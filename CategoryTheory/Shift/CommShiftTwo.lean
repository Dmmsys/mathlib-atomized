/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Center.NegOnePow
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Shift.Twist
public import Mathlib.CategoryTheory.Shift.Pullback

/-!
# Commutation with shifts of functors in two variables

We introduce a typeclass `Functor.CommShift₂Int` for a bifunctor `G : C₁ ⥤ C₂ ⥤ D`
(with `D` a preadditive category) as the two variable analogue of `Functor.CommShift`.
We require that `G` commutes with the shifts in both variables and that the two
ways to identify `(G.obj (X₁⟦p⟧)).obj (X₂⟦q⟧)` to `((G.obj X₁).obj X₂)⟦p + q⟧`
differ by the sign `(-1) ^ (p + q)`.

This is implemented using a structure `Functor.CommShift₂` which does not depend
on the preadditive structure on `D`: instead of signs, elements in `(CatCenter D)ˣ`
are used. These elements are part of a `CommShift₂Setup` structure which extends
a `TwistShiftData` structure (see the file `Mathlib.CategoryTheory.Shift.Twist`).

## TODO (@joelriou)
* Show that `G : C₁ ⥤ C₂ ⥤ D` satisfies `Functor.CommShift₂Int` iff the uncurried
  functor `C₁ × C₂ ⥤ D` commutes with the shift by `ℤ × ℤ`, where `C₁ × C₂` is
  equipped with the obvious product shift, and `D` is equipped with
  the twisted shift.

-/

@[expose] public section

namespace CategoryTheory

variable {C₁ C₁' C₂ C₂' D : Type*} [Category* C₁] [Category* C₁']
  [Category* C₂] [Category* C₂'] [Category* D]

variable (D) in
/--
Definition of `CommShift₂Setup` / `CommShift₂Setup` 的定义

English:
structure CommShift₂Setup
  parameters: (M : Type*) [AddCommMonoid M] [HasShift D M]
  axioms and operations (4):
    - z_zero₁((m₁ m₂ : M)) : z (0, m₁) (0, m₂) = 1  [default: by aesop]
    - z_zero₂((m₁ m₂ : M)) : z (m₁, 0) (m₂, 0) = 1  [default: by aesop]
    - ε((m n : M)) : (CatCenter D)ˣ
    - hε((m n : M)) : ε m n = (z (0, n) (m, 0))⁻¹ * z (m, 0) (0, n)  [default: by aesop]

中文:
结构 交换Shift₂Setup
  参数: (M : 类型) [加法交换幺半群 M] [有Shift D M]
  公理与运算 (4 个):
    - z_zero₁((m₁ m₂ : M)) : z (0, m₁) (0, m₂) = 1  [默认: by aesop]
    - z_zero₂((m₁ m₂ : M)) : z (m₁, 0) (m₂, 0) = 1  [默认: by aesop]
    - ε((m n : M)) : (CatCenter D)ˣ
    - hε((m n : M)) : ε m n = (z (0, n) (m, 0))⁻¹ * z (m, 0) (0, n)  [默认: by aesop]
-/
structure CommShift₂Setup (M : Type*) [AddCommMonoid M] [HasShift D M] extends
    TwistShiftData (PullbackShift D (AddMonoidHom.fst M M + AddMonoidHom.snd _ _)) (M × M) where
  z_zero₁ (m₁ m₂ : M) : z (0, m₁) (0, m₂) = 1 := by aesop
  z_zero₂ (m₁ m₂ : M) : z (m₁, 0) (m₂, 0) = 1 := by aesop
  /-- The invertible elements in the center of `D` that are equal
  to `(z (0, n) (m, 0))⁻¹ * z (m, 0) (0, n)`. -/
  ε (m n : M) : (CatCenter D)ˣ
  hε (m n : M) : ε m n = (z (0, n) (m, 0))⁻¹ * z (m, 0) (0, n) := by aesop

set_option backward.defeqAttrib.useBackward true in
/-- The standard setup for the commutation of bifunctors with shifts by `ℤ`. -/
@[simps]
/--
Definition of `CommShift₂Setup.int` / `CommShift₂Setup.int` 的定义

English:
definition CommShift₂Setup.int
  signature: [Preadditive D] [HasShift D Int]
  body: (-1) ^ (m.1 * n.2)
  assoc _ _ _ := by
    dsimp
    rw [← zpow_add]; rw [← zpow_add]
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  commShift _ _ := ⟨by cat_dis

中文:
定义 交换Shift₂Setup.int
  签名: [预加性 D] [有Shift D 整数]
  定义体: (-1) ^ (m.1 * n.2)
  assoc _ _ _ := by
    dsimp
    rw [← zpow_add]; rw [← zpow_add]
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  commShift _ _ := ⟨by cat_dis
-/
noncomputable def CommShift₂Setup.int [Preadditive D] [HasShift D Int]
    [forall (n : Int), (shiftFunctor D n).Additive] :
    CommShift₂Setup D Int where
  z m n := (-1) ^ (m.1 * n.2)
  assoc _ _ _ := by
    dsimp
    rw [← zpow_add]; rw [← zpow_add]
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  commShift _ _ := ⟨by cat_disch⟩
  ε p q := (-1) ^ (p * q)

namespace Functor

/--
Definition of `CommShift₂` / `CommShift₂` 的定义

English:
class CommShift₂
  parameters: {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]
  axioms and operations (5):
    - commShiftObj((X₁ : C₁)) : (G.obj X₁).CommShift M  [default: by infer_instance]
    - commShift_map({X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁)) : NatTrans.CommShift (G.map f) M  [default: by infer_instance]
    - commShiftFlipObj((X₂ : C₂)) : (G.flip.obj X₂).CommShift M  [default: by infer_instance]
    - commShift_flip_map({X₂ Y₂ : C₂} (g : X₂ ⟶ Y₂)) : NatTrans.CommShift (G.flip.map g) M  [default: by infer_instance]
    - comm((G h) (X₁ : C₁) (X₂ : C₂) (m n : M)) : ((G.obj (X₁⟦m⟧)).commShiftIso n).hom.app X₂ ≫ (((G.flip.obj X₂).commShiftIso m).hom.app X₁)⟦n⟧' = ((G.flip.obj (X₂⟦n⟧)).commShiftIso m).hom.app X₁ ≫ (((G.obj X₁).commShiftIso n).hom.app X₂)⟦m⟧' ≫ (shiftComm ((G.obj X₁).obj X₂) m n).inv ≫ (h.ε m n).val.app _

中文:
类 交换Shift₂
  参数: {M : 类型} [加法交换幺半群 M] [有Shift C₁ M] [有Shift C₂ M] [有Shift D M]
  公理与运算 (5 个):
    - commShiftObj((X₁ : C₁)) : (G.obj X₁).交换Shift M  [默认: by infer_instance]
    - commShift_map({X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁)) : 自然变换.交换Shift (G.map f) M  [默认: by infer_instance]
    - commShiftFlipObj((X₂ : C₂)) : (G.flip.obj X₂).交换Shift M  [默认: by infer_instance]
    - commShift_flip_map({X₂ Y₂ : C₂} (g : X₂ ⟶ Y₂)) : 自然变换.交换Shift (G.flip.map g) M  [默认: by infer_instance]
    - comm((G h) (X₁ : C₁) (X₂ : C₂) (m n : M)) : ((G.obj (X₁⟦m⟧)).commShiftIso n).hom.app X₂ ≫ (((G.flip.obj X₂).commShiftIso m).hom.app X₁)⟦n⟧' = ((G.flip.obj (X₂⟦n⟧)).commShiftIso m).hom.app X₁ ≫ (((G.obj X₁).commShiftIso n).hom.app X₂)⟦m⟧' ≫ (shiftComm ((G.obj X₁).obj X₂) m n).inv ≫ (h.ε m n).val.app _

Depends on / 依赖: CommShift, G.flip.map, G.flip.obj, G.map, G.obj, NatTrans, NatTrans.CommShift, commShiftFlipObj, commShiftIso, commShift_flip_map, commShift_map, hom.app, infer_instance
-/
class CommShift₂ {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]
    (G : C₁ ⥤ C₂ ⥤ D) (h : CommShift₂Setup D M) where
  commShiftObj (X₁ : C₁) : (G.obj X₁).CommShift M := by infer_instance
  commShift_map {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) : NatTrans.CommShift (G.map f) M := by infer_instance
  commShiftFlipObj (X₂ : C₂) : (G.flip.obj X₂).CommShift M := by infer_instance
  commShift_flip_map {X₂ Y₂ : C₂} (g : X₂ ⟶ Y₂) : NatTrans.CommShift (G.flip.map g) M := by
    infer_instance
  comm (G h) (X₁ : C₁) (X₂ : C₂) (m n : M) :
    ((G.obj (X₁⟦m⟧)).commShiftIso n).hom.app X₂ ≫
      (((G.flip.obj X₂).commShiftIso m).hom.app X₁)⟦n⟧' =
        ((G.flip.obj (X₂⟦n⟧)).commShiftIso m).hom.app X₁ ≫
          (((G.obj X₁).commShiftIso n).hom.app X₂)⟦m⟧' ≫
            (shiftComm ((G.obj X₁).obj X₂) m n).inv ≫ (h.ε m n).val.app _

/-- This alias for `Functor.CommShift₂.comm` allows to use the dot notation. -/
alias commShift₂_comm := CommShift₂.comm

attribute [reassoc] commShift₂_comm

/--
Definition of `CommShift₂Int` / `CommShift₂Int` 的定义

English:
abbreviation CommShift₂Int
  signature: [HasShift C₁ Int] [HasShift C₂ Int] [HasShift D Int] [Preadditive D]
  body: G.CommShift₂ .int

中文:
缩写 CommShift₂整数
  签名: [有Shift C₁ 整数] [有Shift C₂ 整数] [有Shift D 整数] [预加性 D]
  定义体: G.CommShift₂ .int

Depends on / 依赖: G.CommShift
-/
abbrev CommShift₂Int [HasShift C₁ Int] [HasShift C₂ Int] [HasShift D Int] [Preadditive D]
    [forall (n : Int), (shiftFunctor D n).Additive] (G : C₁ ⥤ C₂ ⥤ D) : Type _ :=
  G.CommShift₂ .int

namespace CommShift₂

attribute [instance_reducible] commShiftObj commShiftFlipObj
attribute [instance] commShiftObj commShiftFlipObj commShift_map commShift_flip_map

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `precomp₁` / 实例 `precomp₁`

English:
instance precomp₁
  signature: {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₁' M]
  body: inferInstanceAs ((G.obj (F.obj X₁')).CommShift M)
  commShift_map {X₁' Y₁' : C₁'} (f : X₁' ⟶ Y₁') := by dsimp; infer_instance
  commShiftFlipObj (X₂ : C₂) := CommShift.comp F (G.flip.obj X₂)
  commShift_flip_map {X₂ Y₂ : C₂} (g : X₂ ⟶ Y₂) :=
    inferInstanceAs (NatTrans.CommShift (whiskerLeft F (G.

中文:
实例 precomp₁
  签名: {M : 类型} [加法交换幺半群 M] [有Shift C₁ M] [有Shift C₁' M]
  定义体: inferInstanceAs ((G.obj (F.obj X₁')).CommShift M)
  commShift_map {X₁' Y₁' : C₁'} (f : X₁' ⟶ Y₁') := by dsimp; infer_instance
  commShiftFlipObj (X₂ : C₂) := CommShift.comp F (G.flip.obj X₂)
  commShift_flip_map {X₂ Y₂ : C₂} (g : X₂ ⟶ Y₂) :=
    inferInstanceAs (NatTrans.CommShift (whiskerLeft F (G.

Depends on / 依赖: CommShift, F.obj, G.obj
-/
instance precomp₁ {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₁' M]
    [HasShift C₂ M] [HasShift D M] (F : C₁' ⥤ C₁) [F.CommShift M]
    (G : C₁ ⥤ C₂ ⥤ D) (h : CommShift₂Setup D M) [G.CommShift₂ h] :
    (F ⋙ G).CommShift₂ h where
  commShiftObj (X₁' : C₁') := inferInstanceAs ((G.obj (F.obj X₁')).CommShift M)
  commShift_map {X₁' Y₁' : C₁'} (f : X₁' ⟶ Y₁') := by dsimp; infer_instance
  commShiftFlipObj (X₂ : C₂) := CommShift.comp F (G.flip.obj X₂)
  commShift_flip_map {X₂ Y₂ : C₂} (g : X₂ ⟶ Y₂) :=
    inferInstanceAs (NatTrans.CommShift (whiskerLeft F (G.flip.map g)) M)
  comm X₁' X₂ m n := by
    have := G.commShift₂_comm h (F.obj X₁') X₂ m n
    dsimp [commShiftIso] at this ⊢
    simp only [Category.comp_id, Category.id_comp, map_comp, Category.assoc]
    rw [NatTrans.shift_app (G.map ((F.commShiftIso m).hom.app X₁')) n X₂]
    simp [this]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `precomp₂` / 实例 `precomp₂`

English:
instance precomp₂
  signature: {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂' M]
  body: CommShift.comp F (G.obj X₁)
  commShift_map {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) := by dsimp; infer_instance
  commShiftFlipObj (X₂' : C₂') := inferInstanceAs ((G.flip.obj (F.obj X₂')).CommShift M)
  commShift_flip_map {X₂' Y₂' : C₂'} (g : X₂' ⟶ Y₂') :=
    inferInstanceAs (NatTrans.CommShift (G.flip.map (F.m

中文:
实例 precomp₂
  签名: {M : 类型} [加法交换幺半群 M] [有Shift C₁ M] [有Shift C₂' M]
  定义体: CommShift.comp F (G.obj X₁)
  commShift_map {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) := by dsimp; infer_instance
  commShiftFlipObj (X₂' : C₂') := inferInstanceAs ((G.flip.obj (F.obj X₂')).CommShift M)
  commShift_flip_map {X₂' Y₂' : C₂'} (g : X₂' ⟶ Y₂') :=
    inferInstanceAs (NatTrans.CommShift (G.flip.map (F.m

Depends on / 依赖: CommShift, CommShift.comp, G.obj
-/
instance precomp₂ {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂' M]
    [HasShift C₂ M] [HasShift D M] (F : C₂' ⥤ C₂) [F.CommShift M]
    (G : C₁ ⥤ C₂ ⥤ D) (h : CommShift₂Setup D M) [G.CommShift₂ h] :
    (G ⋙ (whiskeringLeft C₂' C₂ D).obj F).CommShift₂ h where
  commShiftObj (X₁ : C₁) := CommShift.comp F (G.obj X₁)
  commShift_map {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) := by dsimp; infer_instance
  commShiftFlipObj (X₂' : C₂') := inferInstanceAs ((G.flip.obj (F.obj X₂')).CommShift M)
  commShift_flip_map {X₂' Y₂' : C₂'} (g : X₂' ⟶ Y₂') :=
    inferInstanceAs (NatTrans.CommShift (G.flip.map (F.map g)) M)
  comm X₁ X₂' m n := by
    have := G.commShift₂_comm h X₁ (F.obj X₂') m n
    dsimp [commShiftIso] at this ⊢
    simp only [Category.comp_id, Category.id_comp, Category.assoc, map_comp]
    refine ((G.obj _).map _ ≫= this).trans ?_
    simp only [← Category.assoc]; congr 3
    exact (NatTrans.shift_app_comm (G.flip.map ((F.commShiftIso n).hom.app X₂')) m X₁).symm

/- TODO : If `G : C₁ ⥤ C₂ ⥤ D` and `H : D ⥤ D'` and commute with shifts,
and we have compatible "setups" on `D` and `D'`, show that `G ⋙ H` also commutes
with shifts. -/

end CommShift₂

end Functor

namespace NatTrans

section

variable {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]
  {G₁ G₂ G₃ : C₁ ⥤ C₂ ⥤ D} (τ : G₁ ⟶ G₂) (τ' : G₂ ⟶ G₃) (h : CommShift₂Setup D M)
  [G₁.CommShift₂ h] [G₂.CommShift₂ h] [G₃.CommShift₂ h]

/--
Definition of `CommShift₂` / `CommShift₂` 的定义

English:
class CommShift₂
  parameters: : Prop where
  axioms and operations (2):
    - commShift_app((X₁ : C₁)) : NatTrans.CommShift (τ.app X₁) M  [default: by infer_instance]
    - commShift_flipApp((X₂ : C₂)) : NatTrans.CommShift (τ.flipApp X₂) M  [default: by infer_instance]

中文:
类 交换Shift₂
  参数: : 命题 where
  公理与运算 (2 个):
    - commShift_app((X₁ : C₁)) : 自然变换.交换Shift (τ.app X₁) M  [默认: by infer_instance]
    - commShift_flipApp((X₂ : C₂)) : 自然变换.交换Shift (τ.flipApp X₂) M  [默认: by infer_instance]

Depends on / 依赖: CommShift, NatTrans, NatTrans.CommShift, commShift_flipApp, flipApp, infer_instance
-/
class CommShift₂ : Prop where
  commShift_app (X₁ : C₁) : NatTrans.CommShift (τ.app X₁) M := by infer_instance
  commShift_flipApp (X₂ : C₂) : NatTrans.CommShift (τ.flipApp X₂) M := by infer_instance

namespace CommShift₂

attribute [instance] commShift_app commShift_flipApp

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommShift₂ (𝟙 G₁) h
  body: by dsimp; infer_instance
  commShift_flipApp _ := by
    simp only [flipApp, flipFunctor_obj, Functor.map_id, id_app]
    infer_instance

中文:
实例 :
  签名: 交换Shift₂ (𝟙 G₁) h
  定义体: by dsimp; infer_instance
  commShift_flipApp _ := by
    simp only [flipApp, flipFunctor_obj, Functor.map_id, id_app]
    infer_instance

Depends on / 依赖: Functor, Functor.map_id, commShift_flipApp, flipApp, flipFunctor_obj, id_app, infer_instance, map_id
-/
instance : CommShift₂ (𝟙 G₁) h where
  commShift_app _ := by dsimp; infer_instance
  commShift_flipApp _ := by
    simp only [flipApp, flipFunctor_obj, Functor.map_id, id_app]
    infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommShift₂
  signature: τ h] [CommShift₂ τ' h] : CommShift₂ (τ ≫ τ') h where
  body: by dsimp; infer_instance
  commShift_flipApp _ := by
    simp only [flipApp, flipFunctor_obj, Functor.map_comp, comp_app]
    infer_instance

中文:
实例 [交换Shift₂
  签名: τ h] [交换Shift₂ τ' h] : 交换Shift₂ (τ ≫ τ') h where
  定义体: by dsimp; infer_instance
  commShift_flipApp _ := by
    simp only [flipApp, flipFunctor_obj, Functor.map_comp, comp_app]
    infer_instance

Depends on / 依赖: Functor, Functor.map_comp, commShift_flipApp, comp_app, flipApp, flipFunctor_obj, infer_instance, map_comp
-/
instance [CommShift₂ τ h] [CommShift₂ τ' h] : CommShift₂ (τ ≫ τ') h where
  commShift_app _ := by dsimp; infer_instance
  commShift_flipApp _ := by
    simp only [flipApp, flipFunctor_obj, Functor.map_comp, comp_app]
    infer_instance

end CommShift₂

end

/--
Definition of `CommShift₂Int` / `CommShift₂Int` 的定义

English:
abbreviation CommShift₂Int
  signature: [HasShift C₁ Int] [HasShift C₂ Int] [HasShift D Int] [Preadditive D]
  body: NatTrans.CommShift₂ τ .int

中文:
缩写 CommShift₂整数
  签名: [有Shift C₁ 整数] [有Shift C₂ 整数] [有Shift D 整数] [预加性 D]
  定义体: NatTrans.CommShift₂ τ .int

Depends on / 依赖: NatTrans, NatTrans.CommShift
-/
abbrev CommShift₂Int [HasShift C₁ Int] [HasShift C₂ Int] [HasShift D Int] [Preadditive D]
    [forall (n : Int), (shiftFunctor D n).Additive]
    {G₁ G₂ : C₁ ⥤ C₂ ⥤ D} [G₁.CommShift₂Int] [G₂.CommShift₂Int] (τ : G₁ ⟶ G₂) : Prop :=
  NatTrans.CommShift₂ τ .int

end NatTrans

end CategoryTheory
