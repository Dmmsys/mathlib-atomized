/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.SmallObject.Iteration.Basic

/-!
# The functor from `Set.Iic j` deduced from a cocone

Given a functor `F : Set.Iio j ⥤ C` and `c : Cocone F`, we define
an extension of `F` as a functor `Set.Iic j ⥤ C` for which
the top element is mapped to `c.pt`.

-/

@[expose] public section

universe u

namespace CategoryTheory

open Category Limits

namespace SmallObject

namespace SuccStruct

variable {C : Type*} [Category* C]
  {J : Type u} [LinearOrder J]
  {j : J} {F : Set.Iio j ⥤ C} (c : Cocone F)

namespace ofCocone

/-- Auxiliary definition for `ofCocone`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.ofCocone.obj** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.SmallObject.SuccStruct.ofCocone`。
形式化陈述：obj (i : J) : C
参数：i : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `ofCocone`.
-/
def obj (i : J) : C :=
  if hi : i < j then
    F.obj ⟨i, hi⟩
  else c.pt

/-- Auxiliary definition for `ofCocone`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.ofCocone.objIso** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.SmallObject.SuccStruct.ofCocone`。
形式化陈述：objIso (i : J) (hi : i < j) : obj c i ≅ F.obj ⟨i, hi⟩
参数：i : J；hi : i < j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `ofCocone`.
-/
def objIso (i : J) (hi : i < j) :
    obj c i ≅ F.obj ⟨i, hi⟩ :=
  eqToIso (dif_pos hi)

/-- Auxiliary definition for `ofCocone`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.ofCocone.objIsoPt** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.SmallObject.SuccStruct.ofCocone`。
形式化陈述：objIsoPt : obj c j ≅ c.pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `ofCocone`.
-/
def objIsoPt :
    obj c j ≅ c.pt :=
  eqToIso (dif_neg (by simp))

/-- Auxiliary definition for `ofCocone`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.ofCocone.map** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.SmallObject.SuccStruct.ofCocone`。
形式化陈述：map (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j) : obj c i₁ ⟶ obj c i₂
参数：i₁ i₂ : J；hi : i₁ <= i₂；hi₂ : i₂ <= j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `ofCocone`.
-/
def map (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ j) :
    obj c i₁ ⟶ obj c i₂ :=
  if h₂ : i₂ < j then
    (objIso c i₁ (lt_of_le_of_lt hi h₂)).hom ≫ F.map (homOfLE hi) ≫ (objIso c i₂ h₂).inv
  else
    have h₂' : i₂ = j := le_antisymm hi₂ (by simpa using h₂)
    if h₁ : i₁ < j then
      (objIso c i₁ h₁).hom ≫ c.ι.app ⟨i₁, h₁⟩ ≫ (objIsoPt c).inv ≫ eqToHom (by subst h₂'; rfl)
    else
      have h₁' : i₁ = j := le_antisymm (hi.trans hi₂) (by simpa using h₁)
      eqToHom (by subst h₁' h₂'; rfl)
/-
**CategoryTheory.SmallObject.SuccStruct.ofCocone.map_id** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.SmallObject.SuccStruct.ofCocone`。
形式化陈述：map_id (i : J) (hi : i <= j) : map c i i (by rfl) hi = 𝟙 _
参数：i : J；hi : i <= j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_id (i : J) (hi : i ≤ j) :
    map c i i (by rfl) hi = 𝟙 _ := by
  dsimp [map]
  grind

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.SmallObject.SuccStruct.ofCocone.map_comp** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.SmallObject.SuccStruct.ofCocone`。
形式化陈述：map_comp (i₁ i₂ i₃ : J) (hi : i₁ <= i₂) (hi' : i₂ <= i₃) (hi₃ : i₃ <= j) :
 map c i₁ i₃ (hi.trans hi') hi₃ = map c i₁ i₂ hi (hi'.trans hi₃) ≫ map c i₂ i₃ h
i' hi₃
参数：i₁ i₂ i₃ : J；hi : i₁ <= i₂；hi' : i₂ <= i₃；hi₃ : i₃ <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.homOfLE_comp`：homOfLE_comp {x y z : X} (h : x <= y) (k : 
y <= z) : homOfLE h ≫ homOfLE k = homOfLE (h.trans k)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `CategoryTheory.eqToHom_refl`：eqToHom_refl {C : Type u₁} [CategoryStruct.
{v₁} C] (X : C) (p : X = X) : eqToHom p = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.Cocone.w_assoc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u
₃} C]   {F : CategoryTheor…
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.ofCocone.map_id`：map_id (i : J) (h
i : i <= j) : map c i i (by rfl) hi = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma map_comp (i₁ i₂ i₃ : J) (hi : i₁ ≤ i₂) (hi' : i₂ ≤ i₃) (hi₃ : i₃ ≤ j) :
    map c i₁ i₃ (hi.trans hi') hi₃ =
      map c i₁ i₂ hi (hi'.trans hi₃) ≫
        map c i₂ i₃ hi' hi₃ := by
  obtain hi₁₂ | rfl := hi.lt_or_eq
  · obtain hi₂₃ | rfl := hi'.lt_or_eq
    · dsimp [map]
      obtain hi₃' | rfl := hi₃.lt_or_eq
      · rw [dif_pos hi₃', dif_pos (hi₂₃.trans hi₃'), dif_pos hi₃', assoc, assoc,
          Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, homOfLE_comp]
      · rw [dif_neg (by simp), dif_pos (hi₁₂.trans hi₂₃), dif_pos hi₂₃, dif_neg (by simp),
          dif_pos hi₂₃, eqToHom_refl, comp_id, assoc, assoc, Iso.inv_hom_id_assoc,
          Cocone.w_assoc]
    · rw [map_id, comp_id]
  · rw [map_id, id_comp]

end ofCocone

/-- Given a functor `F : Set.Iio j ⥤ C` and a cocone `c : Cocone F`,
where `j : J` and `J` is linearly ordered, this is the functor
`Set.Iic j ⥤ C` which extends `F` and sends the top element to `c.pt`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.ofCocone** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.SmallObject.SuccStruct`。
形式化陈述：ofCocone : Set.Iic j ⥤ C where obj i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : Set.Iio j ⥤ C` and a cocone `c : Cocone F`,
where `j : J` and `J` is linearly ordered, this is the functor
`Set.Iic j ⥤ C` which extends `F` and sends the top element to `c.pt`.
-/
def ofCocone : Set.Iic j ⥤ C where
  obj i := ofCocone.obj c i.1
  map {_ j} f := ofCocone.map c _ _ (leOfHom f) j.2
  map_id i := ofCocone.map_id _ _ i.2
  map_comp {_ _ i₃} _ _ := ofCocone.map_comp _ _ _ _ _ _ i₃.2
/-
**CategoryTheory.SmallObject.SuccStruct.ofCocone_obj_eq** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：ofCocone_obj_eq (i : J) (hi : i < j) : (ofCocone c).obj ⟨i, hi.le⟩ = F.obj
 ⟨i, hi⟩
参数：i : J；hi : i < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma ofCocone_obj_eq (i : J) (hi : i < j) :
    (ofCocone c).obj ⟨i, hi.le⟩ = F.obj ⟨i, hi⟩ :=
  dif_pos hi

/-- The isomorphism `(ofCocone c).obj ⟨i, _⟩ ≅ F.obj ⟨i, _⟩` when `i < j`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.ofCoconeObjIso** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：ofCoconeObjIso (i : J) (hi : i < j) : (ofCocone c).obj ⟨i, hi.le⟩ ≅ F.obj 
⟨i, hi⟩
参数：i : J；hi : i < j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `(ofCocone c).obj ⟨i, _⟩ ≅ F.obj ⟨i, _⟩` when `i < j`.
-/
def ofCoconeObjIso (i : J) (hi : i < j) :
    (ofCocone c).obj ⟨i, hi.le⟩ ≅ F.obj ⟨i, hi⟩ :=
  ofCocone.objIso c _ _
/-
**CategoryTheory.SmallObject.SuccStruct.ofCocone_obj_eq_pt** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：ofCocone_obj_eq_pt : (ofCocone c).obj ⟨j, by simp⟩ = c.pt
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma ofCocone_obj_eq_pt :
    (ofCocone c).obj ⟨j, by simp⟩ = c.pt :=
  dif_neg (by simp)

/-- The isomorphism `(ofCocone c).obj ⟨j, _⟩ ≅ c.pt`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.ofCoconeObjIsoPt** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：ofCoconeObjIsoPt : (ofCocone c).obj ⟨j, by simp⟩ ≅ c.pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `(ofCocone c).obj ⟨j, _⟩ ≅ c.pt`.
-/
def ofCoconeObjIsoPt :
    (ofCocone c).obj ⟨j, by simp⟩ ≅ c.pt :=
  ofCocone.objIsoPt c
/-
**CategoryTheory.SmallObject.SuccStruct.ofCocone_map_to_top** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：ofCocone_map_to_top (i : J) (hi : i < j) : (ofCocone c).map (homOfLE hi.le
) = (ofCoconeObjIso c i hi).hom ≫ c.ι.app ⟨i, hi⟩ ≫ (ofCoconeObjIsoPt c).inv
参数：i : J；hi : i < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma ofCocone_map_to_top (i : J) (hi : i < j) :
    (ofCocone c).map (homOfLE hi.le) =
      (ofCoconeObjIso c i hi).hom ≫ c.ι.app ⟨i, hi⟩ ≫ (ofCoconeObjIsoPt c).inv := by
  dsimp [ofCocone, ofCocone.map, ofCoconeObjIso, ofCoconeObjIsoPt]
  rw [dif_neg (by simp), dif_pos hi, comp_id]

@[reassoc]
/-
**CategoryTheory.SmallObject.SuccStruct.ofCocone_map** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：ofCocone_map (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ < j) : (ofCocone c).map
 (homOfLE hi : ⟨i₁, hi.trans hi₂.le⟩ ⟶ ⟨i₂, hi₂.le⟩) = (ofCoconeObjIso c i₁ (lt_
of_le_of_lt hi hi₂)).hom ≫ F.map (homOfLE hi) ≫ (ofCoconeObjIso c i₂ hi₂).inv
参数：i₁ i₂ : J；hi : i₁ <= i₂；hi₂ : i₂ < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma ofCocone_map (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ < j) :
    (ofCocone c).map (homOfLE hi : ⟨i₁, hi.trans hi₂.le⟩ ⟶ ⟨i₂, hi₂.le⟩) =
      (ofCoconeObjIso c i₁ (lt_of_le_of_lt hi hi₂)).hom ≫ F.map (homOfLE hi) ≫
        (ofCoconeObjIso c i₂ hi₂).inv := by
  dsimp [ofCocone, ofCoconeObjIso, ofCocone.map]
  rw [dif_pos hi₂]

@[reassoc]
/-
**CategoryTheory.SmallObject.SuccStruct.ofCoconeObjIso_hom_naturality** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：ofCoconeObjIso_hom_naturality (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ < j) :
 (ofCocone c).map (homOfLE hi : ⟨i₁, hi.trans hi₂.le⟩ ⟶ ⟨i₂, hi₂.le⟩) ≫ (ofCocon
eObjIso c i₂ hi₂).hom = (ofCoconeObjIso c i₁ (lt_of_le_of_lt hi hi₂)).hom ≫ F.ma
p (homOfLE hi)
参数：i₁ i₂ : J；hi : i₁ <= i₂；hi₂ : i₂ < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.ofCocone_map`：ofCocone_map (i₁ i₂ 
: J) (hi : i₁ <= i₂) (hi₂ : i₂ < j) : (ofCocone c).map (homOfLE hi : ⟨i₁, hi.tra
ns hi₂.le⟩ ⟶ ⟨i₂, hi₂.le⟩) = (ofCoconeOb…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma ofCoconeObjIso_hom_naturality (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ < j) :
    (ofCocone c).map (homOfLE hi : ⟨i₁, hi.trans hi₂.le⟩ ⟶ ⟨i₂, hi₂.le⟩) ≫
      (ofCoconeObjIso c i₂ hi₂).hom =
      (ofCoconeObjIso c i₁ (lt_of_le_of_lt hi hi₂)).hom ≫ F.map (homOfLE hi) := by
  rw [ofCocone_map c i₁ i₂ hi hi₂, assoc, assoc, Iso.inv_hom_id, comp_id]

/-- The isomorphism expressing that `ofCocone c` extends the functor `F`
when `c : Cocone F`. -/
@[simps!]
/-
**CategoryTheory.SmallObject.SuccStruct.restrictionLTOfCoconeIso** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：restrictionLTOfCoconeIso : SmallObject.restrictionLT (ofCocone c) (le_refl
 j) ≅ F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism expressing that `ofCocone c` extends the functor `F`
when `c : Cocone F`.
-/
def restrictionLTOfCoconeIso :
    SmallObject.restrictionLT (ofCocone c) (le_refl j) ≅ F :=
  NatIso.ofComponents (fun ⟨i, hi⟩ ↦ ofCoconeObjIso c i hi)
    (by intros; apply ofCoconeObjIso_hom_naturality)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {c} in
/-- If `c` is a colimit cocone, then so is `coconeOfLE (ofCocone c) (le_refl j)`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.isColimitCoconeOfLEOfCocone** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：isColimitCoconeOfLEOfCocone (hc : IsColimit c) : IsColimit (coconeOfLE (of
Cocone c) (le_refl j))
参数：hc : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a colimit cocone, then so is `coconeOfLE (ofCocone c) (le_refl j)`.
-/
def isColimitCoconeOfLEOfCocone (hc : IsColimit c) :
    IsColimit (coconeOfLE (ofCocone c) (le_refl j)) :=
  (IsColimit.precomposeInvEquiv (restrictionLTOfCoconeIso c) _).1
    (IsColimit.ofIsoColimit hc
      (Cocone.ext (ofCoconeObjIsoPt c).symm (fun ⟨i, hi⟩ ↦ by
        dsimp
        rw [ofCocone_map_to_top _ _ hi, Iso.inv_hom_id_assoc])))
/-
**CategoryTheory.SmallObject.SuccStruct.arrowMap_ofCocone** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：arrowMap_ofCocone (i₁ i₂ : J) (h₁₂ : i₁ <= i₂) (h₂ : i₂ < j) : arrowMap (o
fCocone c) i₁ i₂ h₁₂ h₂.le = Arrow.mk (F.map (homOfLE h₁₂ : ⟨i₁, lt_of_le_of_lt 
h₁₂ h₂⟩ ⟶ ⟨i₂, h₂⟩))
参数：i₁ i₂ : J；h₁₂ : i₁ <= i₂；h₂ : i₂ < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Arrow.ext`：ext {f g : Arrow T} (h₁ : f.left = g.left) (h₂
 : f.right = g.right) (h₃ : f.hom = eqToHom h₁ ≫ g.hom ≫ eqToHom h₂.symm) : f = 
g
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.ofCocone_obj_eq`：ofCocone_obj_eq (
i : J) (hi : i < j) : (ofCocone c).obj ⟨i, hi.le⟩ = F.obj ⟨i, hi⟩
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.ofCocone_map`：ofCocone_map (i₁ i₂ 
: J) (hi : i₁ <= i₂) (hi₂ : i₂ < j) : (ofCocone c).map (homOfLE hi : ⟨i₁, hi.tra
ns hi₂.le⟩ ⟶ ⟨i₂, hi₂.le⟩) = (ofCoconeOb…
-/
lemma arrowMap_ofCocone (i₁ i₂ : J) (h₁₂ : i₁ ≤ i₂) (h₂ : i₂ < j) :
    arrowMap (ofCocone c) i₁ i₂ h₁₂ h₂.le =
      Arrow.mk (F.map (homOfLE h₁₂ : ⟨i₁, lt_of_le_of_lt h₁₂ h₂⟩ ⟶ ⟨i₂, h₂⟩)) :=
  Arrow.ext (ofCocone_obj_eq _ _ _) (ofCocone_obj_eq _ _ _) (ofCocone_map _ _ _ _ _)
/-
**CategoryTheory.SmallObject.SuccStruct.arrowMap_ofCocone_to_top** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：arrowMap_ofCocone_to_top (i : J) (hi : i < j) : arrowMap (ofCocone c) i j 
hi.le (by simp) = Arrow.mk (c.ι.app ⟨i, hi⟩)
参数：i : J；hi : i < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SmallObject.SuccStruct.arrowMap.eq_1`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : LinearOrder J] {j :
 J}   (F : CategoryTheory.Functor (↑(Set.…
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.ofCocone_map_to_top`：ofCocone_map_
to_top (i : J) (hi : i < j) : (ofCocone c).map (homOfLE hi.le) = (ofCoconeObjIso
 c i hi).hom ≫ c.ι.app ⟨i, hi⟩ ≫ (ofCoconeObjIs…
· 使用引理 `CategoryTheory.Arrow.ext`：ext {f g : Arrow T} (h₁ : f.left = g.left) (h₂
 : f.right = g.right) (h₃ : f.hom = eqToHom h₁ ≫ g.hom ≫ eqToHom h₂.symm) : f = 
g
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.ofCocone_obj_eq`：ofCocone_obj_eq (
i : J) (hi : i < j) : (ofCocone c).obj ⟨i, hi.le⟩ = F.obj ⟨i, hi⟩
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.ofCocone_obj_eq_pt`：ofCocone_obj_e
q_pt : (ofCocone c).obj ⟨j, by simp⟩ = c.pt
-/
lemma arrowMap_ofCocone_to_top (i : J) (hi : i < j) :
    arrowMap (ofCocone c) i j hi.le (by simp) = Arrow.mk (c.ι.app ⟨i, hi⟩) := by
  rw [arrowMap, ofCocone_map_to_top _ _ hi]
  exact Arrow.ext (ofCocone_obj_eq _ _ _) (ofCocone_obj_eq_pt _) rfl

end SuccStruct

end SmallObject

end CategoryTheory

