/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Bicategory.Strict.Basic

/-!
# Locally discrete bicategories

A category `C` can be promoted to a strict bicategory `LocallyDiscrete C`. The objects and the
1-morphisms in `LocallyDiscrete C` are the same as the objects and the morphisms, respectively,
in `C`, and the 2-morphisms in `LocallyDiscrete C` are the equalities between 1-morphisms. In
other words, the category consisting of the 1-morphisms between each pair of objects `X` and `Y`
in `LocallyDiscrete C` is defined as the discrete category associated with the type `X ⟶ Y`.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory Discrete

universe w₂ w₁ v₂ v₁ v u₂ u₁ u

section

variable {C : Type u}

/-- A wrapper for promoting any category to a bicategory,
with the only 2-morphisms being equalities.
-/
@[ext]
/--
Definition of `LocallyDiscrete` / `LocallyDiscrete` 的定义

English:
structure LocallyDiscrete
  parameters: (C : Type u)
  axioms and operations (1):
    - as : C

中文:
结构 LocallyDiscrete
  参数: (C : 类型u)
  公理与运算 (1 个):
    - as : C
-/
structure LocallyDiscrete (C : Type u) where
  /-- A wrapper for promoting any category to a bicategory,
  with the only 2-morphisms being equalities.
  -/
  as : C

namespace LocallyDiscrete

@[simp]
/--
theorem `mk_as` / 定理 `mk_as`

English:
theorem mk_as
  given: (a : LocallyDiscrete C)
  statement: mk a.as = a
  proof: rfl

中文:
定理 mk_as
  条件: (a : LocallyDiscrete C)
  结论: mk a.as = a
  证明: rfl
-/
theorem mk_as (a : LocallyDiscrete C) : mk a.as = a := rfl

/-- `LocallyDiscrete C` is equivalent to the original type `C`. -/
@[simps]
/--
Definition of `locallyDiscreteEquiv` / `locallyDiscreteEquiv` 的定义

English:
definition locallyDiscreteEquiv
  signature: : LocallyDiscrete C ≃ C where
  body: LocallyDiscrete.as
  invFun := LocallyDiscrete.mk
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 locallyDiscreteEquiv
  签名: : LocallyDiscrete C ≃ C where
  定义体: LocallyDiscrete.as
  invFun := LocallyDiscrete.mk
  left_inv := by cat_disch
  right_inv := by cat_disch

Depends on / 依赖: LocallyDiscrete, LocallyDiscrete.as
-/
def locallyDiscreteEquiv : LocallyDiscrete C ≃ C where
  toFun := LocallyDiscrete.as
  invFun := LocallyDiscrete.mk
  left_inv := by cat_disch
  right_inv := by cat_disch

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: C] : DecidableEq (LocallyDiscrete C)
  body: locallyDiscreteEquiv.decidableEq

中文:
实例 [DecidableEq
  签名: C] : DecidableEq (LocallyDiscrete C)
  定义体: locallyDiscreteEquiv.decidableEq

Depends on / 依赖: decidableEq, locallyDiscreteEquiv, locallyDiscreteEquiv.decidableEq
-/
instance [DecidableEq C] : DecidableEq (LocallyDiscrete C) :=
  locallyDiscreteEquiv.decidableEq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: C] : Inhabited (LocallyDiscrete C)
  body: ⟨⟨default⟩⟩

中文:
实例 [Inhabited
  签名: C] : Inhabited (LocallyDiscrete C)
  定义体: ⟨⟨default⟩⟩
-/
instance [Inhabited C] : Inhabited (LocallyDiscrete C) :=
  ⟨⟨default⟩⟩

/--
Instance `categoryStruct` / 实例 `categoryStruct`

English:
instance categoryStruct
  signature: [CategoryStruct.{v} C]
  body: Discrete (a.as ⟶ b.as)
  id a := ⟨𝟙 a.as⟩
  comp f g := ⟨f.as ≫ g.as⟩

中文:
实例 categoryStruct
  签名: [CategoryStruct.{v} C]
  定义体: Discrete (a.as ⟶ b.as)
  id a := ⟨𝟙 a.as⟩
  comp f g := ⟨f.as ≫ g.as⟩

Depends on / 依赖: Discrete, a.as, b.as
-/
instance categoryStruct [CategoryStruct.{v} C] : CategoryStruct (LocallyDiscrete C) where
  Hom a b := Discrete (a.as ⟶ b.as)
  id a := ⟨𝟙 a.as⟩
  comp f g := ⟨f.as ≫ g.as⟩

variable [CategoryStruct.{v} C]

@[simp]
/--
lemma `id_as` / 引理 `id_as`

English:
lemma id_as
  given: (a : LocallyDiscrete C)
  statement: (𝟙 a : Discrete (a.as ⟶ a.as)).as = 𝟙 a.as
  proof: rfl

@[simp]

中文:
引理 id_as
  条件: (a : LocallyDiscrete C)
  结论: (𝟙 a : Discrete (a.as ⟶ a.as)).as = 𝟙 a.as
  证明: rfl

@[simp]
-/
lemma id_as (a : LocallyDiscrete C) : (𝟙 a : Discrete (a.as ⟶ a.as)).as = 𝟙 a.as :=
  rfl

@[simp]
/--
lemma `comp_as` / 引理 `comp_as`

English:
lemma comp_as
  given: {a b c : LocallyDiscrete C} (f : a ⟶ b) (g : b ⟶ c)
  statement: (f ≫ g).as = f.as ≫ g.as
  proof: rfl

中文:
引理 comp_as
  条件: {a b c : LocallyDiscrete C} (f : a ⟶ b) (g : b ⟶ c)
  结论: (f ≫ g).as = f.as ≫ g.as
  证明: rfl
-/
lemma comp_as {a b c : LocallyDiscrete C} (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).as = f.as ≫ g.as :=
  rfl

instance (priority := 900) homSmallCategory (a b : LocallyDiscrete C) : SmallCategory (a ⟶ b) :=
  CategoryTheory.discreteCategory (a.as ⟶ b.as)

/--
Instance `subsingleton2Hom` / 实例 `subsingleton2Hom`

English:
instance subsingleton2Hom
  signature: {a b : LocallyDiscrete C} (f g : a ⟶ b)
  body: instSubsingletonDiscreteHom f g

中文:
实例 subsingleton2Hom
  签名: {a b : LocallyDiscrete C} (f g : a ⟶ b)
  定义体: instSubsingletonDiscreteHom f g

Depends on / 依赖: instSubsingletonDiscreteHom
-/
instance subsingleton2Hom {a b : LocallyDiscrete C} (f g : a ⟶ b) : Subsingleton (f ⟶ g) :=
  instSubsingletonDiscreteHom f g

/--
theorem `eq_of_hom` / 定理 `eq_of_hom`

English:
theorem eq_of_hom
  given: {X Y : LocallyDiscrete C} {f g : X ⟶ Y} (η : f ⟶ g)
  statement: f = g
  proof: Discrete.ext η.1.1

中文:
定理 eq_of_hom
  条件: {X Y : LocallyDiscrete C} {f g : X ⟶ Y} (η : f ⟶ g)
  结论: f = g
  证明: Discrete.ext η.1.1

Depends on / 依赖: Discrete, Discrete.ext
-/
theorem eq_of_hom {X Y : LocallyDiscrete C} {f g : X ⟶ Y} (η : f ⟶ g) : f = g :=
  Discrete.ext η.1.1

end LocallyDiscrete

variable (C)
variable [Category.{v} C]

/--
Instance `locallyDiscreteBicategory` / 实例 `locallyDiscreteBicategory`

English:
instance locallyDiscreteBicategory
  signature: : Bicategory (LocallyDiscrete C) where
  body: eqToHom (congr_arg₂ (· ≫ ·) rfl (LocallyDiscrete.eq_of_hom η))
  whiskerRight η _ := eqToHom (congr_arg₂ (· ≫ ·) (LocallyDiscrete.eq_of_hom η) rfl)
associator f g h := eqToIso by apply Discrete.ext; simp
leftUnitor f := eqToIso by apply Discrete.ext; simp
rightUnitor f := eqToIso by apply Discrete.e

中文:
实例 locallyDiscreteBicategory
  签名: : Bicategory (LocallyDiscrete C) where
  定义体: eqToHom (congr_arg₂ (· ≫ ·) rfl (LocallyDiscrete.eq_of_hom η))
  whiskerRight η _ := eqToHom (congr_arg₂ (· ≫ ·) (LocallyDiscrete.eq_of_hom η) rfl)
associator f g h := eqToIso by apply Discrete.ext; simp
leftUnitor f := eqToIso by apply Discrete.ext; simp
rightUnitor f := eqToIso by apply Discrete.e

Depends on / 依赖: LocallyDiscrete, LocallyDiscrete.eq_of_hom, eqToHom, eq_of_hom
-/
instance locallyDiscreteBicategory : Bicategory (LocallyDiscrete C) where
  whiskerLeft _ _ _ η := eqToHom (congr_arg₂ (· ≫ ·) rfl (LocallyDiscrete.eq_of_hom η))
  whiskerRight η _ := eqToHom (congr_arg₂ (· ≫ ·) (LocallyDiscrete.eq_of_hom η) rfl)
associator f g h := eqToIso by apply Discrete.ext; simp
leftUnitor f := eqToIso by apply Discrete.ext; simp
rightUnitor f := eqToIso by apply Discrete.ext; simp

/--
Instance `locallyDiscreteBicategory.strict` / 实例 `locallyDiscreteBicategory.strict`

English:
instance locallyDiscreteBicategory.strict
  signature: : Strict (LocallyDiscrete C) where
  body: Discrete.ext (Category.id_comp _)
  comp_id _ := Discrete.ext (Category.comp_id _)
  assoc _ _ _ := Discrete.ext (Category.assoc _ _ _)

中文:
实例 locallyDiscreteBicategory.strict
  签名: : Strict (LocallyDiscrete C) where
  定义体: Discrete.ext (Category.id_comp _)
  comp_id _ := Discrete.ext (Category.comp_id _)
  assoc _ _ _ := Discrete.ext (Category.assoc _ _ _)

Depends on / 依赖: Category, Category.id_comp, Discrete, Discrete.ext, id_comp
-/
instance locallyDiscreteBicategory.strict : Strict (LocallyDiscrete C) where
  id_comp _ := Discrete.ext (Category.id_comp _)
  comp_id _ := Discrete.ext (Category.comp_id _)
  assoc _ _ _ := Discrete.ext (Category.assoc _ _ _)

end

namespace Bicategory

/--
Definition of `IsLocallyDiscrete` / `IsLocallyDiscrete` 的定义

English:
abbreviation IsLocallyDiscrete
  signature: (B : Type*) [Bicategory B]
  body: forall (b c : B), IsDiscrete (b ⟶ c)

中文:
缩写 IsLocallyDiscrete
  签名: (B : 类型) [Bicategory B]
  定义体: forall (b c : B), IsDiscrete (b ⟶ c)

Depends on / 依赖: IsDiscrete
-/
abbrev IsLocallyDiscrete (B : Type*) [Bicategory B] := forall (b c : B), IsDiscrete (b ⟶ c)

instance (C : Type*) [Category* C] : IsLocallyDiscrete (LocallyDiscrete C) :=
  fun _ _ => Discrete.isDiscrete _

instance (B : Type*) [Bicategory B] [IsLocallyDiscrete B] : Strict B where
  id_comp f := obj_ext_of_isDiscrete (leftUnitor f).hom
  comp_id f := obj_ext_of_isDiscrete (rightUnitor f).hom
  assoc f g h := obj_ext_of_isDiscrete (associator f g h).hom

end Bicategory

end CategoryTheory

section

open CategoryTheory LocallyDiscrete

universe v u

namespace Quiver.Hom

variable {C : Type u} [CategoryStruct.{v} C]

/-- The 1-morphism in `LocallyDiscrete C` associated to a given morphism `f : a ⟶ b` in `C` -/
@[simps]
/--
Definition of `toLoc` / `toLoc` 的定义

English:
definition toLoc
  signature: {a b : C} (f : a ⟶ b)
  body: ⟨f⟩

@[simp]

中文:
定义 toLoc
  签名: {a b : C} (f : a ⟶ b)
  定义体: ⟨f⟩

@[simp]
-/
def toLoc {a b : C} (f : a ⟶ b) : LocallyDiscrete.mk a ⟶ LocallyDiscrete.mk b :=
  ⟨f⟩

@[simp]
/--
lemma `id_toLoc` / 引理 `id_toLoc`

English:
lemma id_toLoc
  given: (a : C)
  statement: (𝟙 a).toLoc = 𝟙 (LocallyDiscrete.mk a)
  proof: rfl

@[simp, grind _=_]

中文:
引理 id_toLoc
  条件: (a : C)
  结论: (𝟙 a).toLoc = 𝟙 (LocallyDiscrete.mk a)
  证明: rfl

@[simp, grind _=_]
-/
lemma id_toLoc (a : C) : (𝟙 a).toLoc = 𝟙 (LocallyDiscrete.mk a) :=
  rfl

@[simp, grind _=_]
/--
lemma `comp_toLoc` / 引理 `comp_toLoc`

English:
lemma comp_toLoc
  given: {a b c : C} (f : a ⟶ b) (g : b ⟶ c)
  statement: (f ≫ g).toLoc = f.toLoc ≫ g.toLoc
  proof: rfl

中文:
引理 comp_toLoc
  条件: {a b c : C} (f : a ⟶ b) (g : b ⟶ c)
  结论: (f ≫ g).toLoc = f.toLoc ≫ g.toLoc
  证明: rfl
-/
lemma comp_toLoc {a b c : C} (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).toLoc = f.toLoc ≫ g.toLoc :=
  rfl

end Quiver.Hom

@[simp]
/--
lemma `CategoryTheory.LocallyDiscrete.eqToHom_toLoc` / 引理 `CategoryTheory.LocallyDiscrete.eqToHom_toLoc`

English:
lemma CategoryTheory.LocallyDiscrete.eqToHom_toLoc
  statement: {C : Type u} [Category.{v} C] {a b : C}
  proof: by
  subst h; rfl

中文:
引理 CategoryTheory.LocallyDiscrete.eqToHom_toLoc
  结论: {C : 类型u} [Category.{v} C] {a b : C}
  证明: by
  subst h; rfl
-/
lemma CategoryTheory.LocallyDiscrete.eqToHom_toLoc {C : Type u} [Category.{v} C] {a b : C}
    (h : a = b) : (eqToHom h).toLoc = eqToHom (congrArg LocallyDiscrete.mk h) := by
  subst h; rfl

/--
lemma `CategoryTheory.CommSq.toLoc` / 引理 `CategoryTheory.CommSq.toLoc`

English:
lemma CategoryTheory.CommSq.toLoc
  statement: {C : Type*} [Category C] {X₁ X₂ X₃ X₄ : C}
  proof: ⟨by simp only [← Quiver.Hom.comp_toLoc, h.w]⟩

中文:
引理 CategoryTheory.CommSq.toLoc
  结论: {C : 类型} [Category C] {X₁ X₂ X₃ X₄ : C}
  证明: ⟨by simp only [← Quiver.Hom.comp_toLoc, h.w]⟩

Depends on / 依赖: Quiver, Quiver.Hom.comp_toLoc, comp_toLoc
-/
lemma CategoryTheory.CommSq.toLoc {C : Type*} [Category C] {X₁ X₂ X₃ X₄ : C}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (h : CommSq t l r b) :
    CommSq t.toLoc l.toLoc r.toLoc b.toLoc :=
  ⟨by simp only [← Quiver.Hom.comp_toLoc, h.w]⟩

end
