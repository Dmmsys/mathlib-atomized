/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.SmallObject.Iteration.Basic

/-!
# Extension of a functor from `Set.Iic j` to `Set.Iic (Order.succ j)`

Given a linearly ordered type `J` with `SuccOrder J`, `j : J` that is not maximal,
we define the extension of a functor `F : Set.Iic j ⥤ C` as a
functor `Set.Iic (Order.succ j) ⥤ C` when an object `X : C` and a morphism
`τ : F.obj ⟨j, _⟩ ⟶ X` is given.

-/

@[expose] public section

universe u

namespace CategoryTheory

open Category

namespace SmallObject

variable {C : Type*} [Category* C]
  {J : Type u} [LinearOrder J] [SuccOrder J] {j : J} (hj : ¬IsMax j)
  (F : Set.Iic j ⥤ C) {X : C} (τ : F.obj ⟨j, by simp⟩ ⟶ X)

namespace SuccStruct

namespace extendToSucc

variable (X)

set_option backward.privateInPublic true in
/-- `extendToSucc`, on objects: it coincides with `F.obj` for `i ≤ j`, and
it sends `Order.succ j` to the given object `X`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.extendToSucc.obj** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.SmallObject.SuccStruct.extendToSucc`。
形式化陈述：obj (i : Set.Iic (Order.succ j)) : C
参数：i : Set.Iic (Order.succ j)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`extendToSucc`, on objects: it coincides with `F.obj` for `i ≤ j`, and
it sends `Order.succ j` to the given object `X`.
-/
def obj (i : Set.Iic (Order.succ j)) : C :=
  if hij : i.1 ≤ j then F.obj ⟨i.1, hij⟩ else X
/-
**CategoryTheory.SmallObject.SuccStruct.extendToSucc.obj_eq** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.SmallObject.SuccStruct.extendToSucc`。
形式化陈述：obj_eq (i : Set.Iic j) : obj F X ⟨i, i.2.trans (Order.le_succ j)⟩ = F.obj 
i
参数：i : Set.Iic j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
-/
lemma obj_eq (i : Set.Iic j) :
    obj F X ⟨i, i.2.trans (Order.le_succ j)⟩ = F.obj i := dif_pos i.2

/-- The isomorphism `obj F X ⟨i, _⟩ ≅ F.obj i` when `i : Set.Iic j`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.extendToSucc.objIso** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.SmallObject.SuccStruct.extendToSucc`。
形式化陈述：objIso (i : Set.Iic j) : obj F X ⟨i, i.2.trans (Order.le_succ j)⟩ ≅ F.obj 
i
参数：i : Set.Iic j。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.extendToSucc.obj_eq`：obj_eq (i : S
et.Iic j) : obj F X ⟨i, i.2.trans (Order.le_succ j)⟩ = F.obj i

--- 原说明 ---
The isomorphism `obj F X ⟨i, _⟩ ≅ F.obj i` when `i : Set.Iic j`.
-/
def objIso (i : Set.Iic j) :
    obj F X ⟨i, i.2.trans (Order.le_succ j)⟩ ≅ F.obj i :=
  eqToIso (obj_eq _ _ _)

include hj in
/-
**CategoryTheory.SmallObject.SuccStruct.extendToSucc.obj_succ_eq** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.extendToSucc`。
形式化陈述：obj_succ_eq : obj F X ⟨Order.succ j, by simp⟩ = X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma obj_succ_eq : obj F X ⟨Order.succ j, by simp⟩ = X :=
  dif_neg (by simpa only [Order.succ_le_iff_isMax] using hj)

/-- The isomorphism `obj F X ⟨Order.succ j, _⟩ ≅ X`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.extendToSucc.objSuccIso** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.extendToSucc`。
形式化陈述：objSuccIso : obj F X ⟨Order.succ j, by simp⟩ ≅ X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.extendToSucc.obj_succ_eq`：obj_succ
_eq : obj F X ⟨Order.succ j, by simp⟩ = X

--- 原说明 ---
The isomorphism `obj F X ⟨Order.succ j, _⟩ ≅ X`.
-/
def objSuccIso :
    obj F X ⟨Order.succ j, by simp⟩ ≅ X :=
  eqToIso (obj_succ_eq hj _ _)

variable {X}

/-- `extendToSucc`, on morphisms. -/
/-
**CategoryTheory.SmallObject.SuccStruct.extendToSucc.map** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.SmallObject.SuccStruct.extendToSucc`。
形式化陈述：map (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= Order.succ j) : obj F X ⟨i₁, 
hi.trans hi₂⟩ ⟶ obj F X ⟨i₂, hi₂⟩
参数：i₁ i₂ : J；hi : i₁ <= i₂；hi₂ : i₂ <= Order.succ j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`extendToSucc`, on morphisms.
-/
def map (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ Order.succ j) :
    obj F X ⟨i₁, hi.trans hi₂⟩ ⟶ obj F X ⟨i₂, hi₂⟩ :=
  if h₁ : i₂ ≤ j then
    (objIso F X ⟨i₁, hi.trans h₁⟩).hom ≫ F.map (homOfLE hi) ≫ (objIso F X ⟨i₂, h₁⟩).inv
  else
    if h₂ : i₁ ≤ j then
      (objIso F X ⟨i₁, h₂⟩).hom ≫ F.map (homOfLE h₂) ≫ τ ≫
        (objSuccIso hj F X).inv ≫ eqToHom (by
          congr
          exact le_antisymm (Order.succ_le_of_lt (not_le.1 h₁)) hi₂)
    else
      eqToHom (by
        congr
        rw [le_antisymm hi₂ (Order.succ_le_of_lt (not_le.1 h₁)),
          le_antisymm (hi.trans hi₂) (Order.succ_le_of_lt (not_le.1 h₂))])
/-
**CategoryTheory.SmallObject.SuccStruct.extendToSucc.map_eq** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.SmallObject.SuccStruct.extendToSucc`。
形式化陈述：map_eq (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j) : map hj F τ i₁ i₂ hi (
hi₂.trans (Order.le_succ j)) = (objIso F X ⟨i₁, hi.trans hi₂⟩).hom ≫ F.map (homO
fLE hi) ≫ (objIso F X ⟨i₂, hi₂⟩).inv
参数：i₁ i₂ : J；hi : i₁ <= i₂；hi₂ : i₂ <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
-/
lemma map_eq (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ j) :
    map hj F τ i₁ i₂ hi (hi₂.trans (Order.le_succ j)) =
      (objIso F X ⟨i₁, hi.trans hi₂⟩).hom ≫ F.map (homOfLE hi) ≫
        (objIso F X ⟨i₂, hi₂⟩).inv :=
  dif_pos hi₂
/-
**CategoryTheory.SmallObject.SuccStruct.extendToSucc.map_self_succ** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.extendToSucc`。
形式化陈述：map_self_succ : map hj F τ j (Order.succ j) (Order.le_succ j) (by rfl) = (
objIso F X ⟨j, by simp⟩).hom ≫ τ ≫ (objSuccIso hj F X).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma map_self_succ :
    map hj F τ j (Order.succ j) (Order.le_succ j) (by rfl) =
      (objIso F X ⟨j, by simp⟩).hom ≫ τ ≫ (objSuccIso hj F X).inv := by
  dsimp [map]
  rw [dif_neg (by simpa only [Order.succ_le_iff_isMax] using hj),
    dif_pos (by rfl), Functor.map_id, comp_id, id_comp]

@[simp]
/-
**CategoryTheory.SmallObject.SuccStruct.extendToSucc.map_id** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.SmallObject.SuccStruct.extendToSucc`。
形式化陈述：map_id (i : J) (hi : i <= Order.succ j) : map hj F τ i i (by rfl) hi = 𝟙 _
参数：i : J；hi : i <= Order.succ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
lemma map_id (i : J) (hi : i ≤ Order.succ j) :
    map hj F τ i i (by rfl) hi = 𝟙 _ := by
  dsimp [map]
  by_cases h₁ : i ≤ j
  · rw [dif_pos h₁, CategoryTheory.Functor.map_id, id_comp, Iso.hom_inv_id]
  · obtain rfl : i = Order.succ j := le_antisymm hi (Order.succ_le_of_lt (not_le.1 h₁))
    rw [dif_neg (by simpa only [Order.succ_le_iff_isMax] using hj),
      dif_neg h₁]
/-
**CategoryTheory.SmallObject.SuccStruct.extendToSucc.map_comp** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.extendToSucc`。
形式化陈述：map_comp (i₁ i₂ i₃ : J) (h₁₂ : i₁ <= i₂) (h₂₃ : i₂ <= i₃) (h : i₃ <= Order
.succ j) : map hj F τ i₁ i₃ (h₁₂.trans h₂₃) h = map hj F τ i₁ i₂ h₁₂ (h₂₃.trans 
h) ≫ map hj F τ i₂ i₃ h₂₃ h
参数：i₁ i₂ i₃ : J；h₁₂ : i₁ <= i₂；h₂₃ : i₂ <= i₃；h : i₃ <= Order.succ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.extendToSucc.map_eq`：map_eq (i₁ i₂
 : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j) : map hj F τ i₁ i₂ hi (hi₂.trans (Order.le
_succ j)) = (objIso F X ⟨i₁, hi.trans hi₂⟩).hom…
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
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `Order.lt_succ_iff_of_not_isMax`：lt_succ_iff_of_not_isMax (ha : ¬IsMax a)
 : b < succ a ↔ b <= a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.extendToSucc.map_id`：map_id (i : J
) (hi : i <= Order.succ j) : map hj F τ i i (by rfl) hi = 𝟙 _
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
lemma map_comp (i₁ i₂ i₃ : J) (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃) (h : i₃ ≤ Order.succ j) :
    map hj F τ i₁ i₃ (h₁₂.trans h₂₃) h =
      map hj F τ i₁ i₂ h₁₂ (h₂₃.trans h) ≫ map hj F τ i₂ i₃ h₂₃ h := by
  by_cases h₁ : i₃ ≤ j
  · rw [map_eq hj F τ i₁ i₂ _ (h₂₃.trans h₁), map_eq hj F τ i₂ i₃ _ h₁,
      map_eq hj F τ i₁ i₃ _ h₁, assoc, assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc,
      homOfLE_comp]
  · obtain rfl : i₃ = Order.succ j := le_antisymm h (Order.succ_le_of_lt (not_le.1 h₁))
    obtain h₂ | rfl := h₂₃.lt_or_eq
    · rw [Order.lt_succ_iff_of_not_isMax hj] at h₂
      rw [map_eq hj F τ i₁ i₂ _ h₂]
      dsimp [map]
      rw [dif_neg h₁, dif_pos (h₁₂.trans h₂), dif_neg h₁, dif_pos h₂, assoc, assoc,
        Iso.inv_hom_id_assoc, comp_id, ← Functor.map_comp_assoc, homOfLE_comp]
    · rw [map_id, comp_id]

end extendToSucc

open extendToSucc in
include hj in
/-- The extension to `Set.Iic (Order.succ j) ⥤ C` of a functor `F : Set.Iic j ⥤ C`,
when we specify a morphism `F.obj ⟨j, _⟩ ⟶ X`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.extendToSucc** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：extendToSucc : Set.Iic (Order.succ j) ⥤ C where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension to `Set.Iic (Order.succ j) ⥤ C` of a functor `F : Set.Iic j ⥤ C`,
when we specify a morphism `F.obj ⟨j, _⟩ ⟶ X`.
-/
def extendToSucc : Set.Iic (Order.succ j) ⥤ C where
  obj := obj F X
  map {i₁ i₂} f := map hj F τ i₁ i₂ (leOfHom f) i₂.2
  map_id _ := extendToSucc.map_id _ F τ _ _
  map_comp {i₁ i₂ i₃} f g := extendToSucc.map_comp hj F τ i₁ i₂ i₃ (leOfHom f) (leOfHom g) i₃.2
/-
**CategoryTheory.SmallObject.SuccStruct.extendToSucc_obj_eq** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：extendToSucc_obj_eq (i : J) (hi : i <= j) : (extendToSucc hj F τ).obj ⟨i, 
hi.trans (Order.le_succ j)⟩ = F.obj ⟨i, hi⟩
参数：i : J；hi : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.extendToSucc.obj_eq`：obj_eq (i : S
et.Iic j) : obj F X ⟨i, i.2.trans (Order.le_succ j)⟩ = F.obj i
-/
lemma extendToSucc_obj_eq (i : J) (hi : i ≤ j) :
    (extendToSucc hj F τ).obj ⟨i, hi.trans (Order.le_succ j)⟩ = F.obj ⟨i, hi⟩ :=
  extendToSucc.obj_eq F X ⟨i, hi⟩

/-- The isomorphism `(extendToSucc hj F τ).obj ⟨i, _⟩ ≅ F.obj i` when `i ≤ j` -/
/-
**CategoryTheory.SmallObject.SuccStruct.extendToSuccObjIso** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：extendToSuccObjIso (i : J) (hi : i <= j) : (extendToSucc hj F τ).obj ⟨i, h
i.trans (Order.le_succ j)⟩ ≅ F.obj ⟨i, hi⟩
参数：i : J；hi : i <= j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `(extendToSucc hj F τ).obj ⟨i, _⟩ ≅ F.obj i` when `i ≤ j`
-/
def extendToSuccObjIso (i : J) (hi : i ≤ j) :
    (extendToSucc hj F τ).obj ⟨i, hi.trans (Order.le_succ j)⟩ ≅ F.obj ⟨i, hi⟩ :=
  extendToSucc.objIso F X ⟨i, hi⟩
/-
**CategoryTheory.SmallObject.SuccStruct.extendToSucc_obj_succ_eq** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：extendToSucc_obj_succ_eq : (extendToSucc hj F τ).obj ⟨Order.succ j, by sim
p⟩ = X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.extendToSucc.obj_succ_eq`：obj_succ
_eq : obj F X ⟨Order.succ j, by simp⟩ = X
-/
lemma extendToSucc_obj_succ_eq :
    (extendToSucc hj F τ).obj ⟨Order.succ j, by simp⟩ = X :=
  extendToSucc.obj_succ_eq hj F X

/-- The isomorphism `(extendToSucc hj F τ).obj ⟨Order.succ j, _⟩ ≅ X`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.extendToSuccObjSuccIso** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：extendToSuccObjSuccIso : (extendToSucc hj F τ).obj ⟨Order.succ j, by simp⟩
 ≅ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `(extendToSucc hj F τ).obj ⟨Order.succ j, _⟩ ≅ X`.
-/
def extendToSuccObjSuccIso :
    (extendToSucc hj F τ).obj ⟨Order.succ j, by simp⟩ ≅ X :=
  extendToSucc.objSuccIso hj F X

@[reassoc]
/-
**CategoryTheory.SmallObject.SuccStruct.extendToSuccObjIso_hom_naturality** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：extendToSuccObjIso_hom_naturality (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <=
 j) : (extendToSucc hj F τ).map (homOfLE hi : ⟨i₁, hi.trans (hi₂.trans (Order.le
_succ j))⟩ ⟶ ⟨i₂, hi₂.trans (Order.le_succ j)⟩) ≫ (extendToSuccObjIso hj F τ i₂ 
hi₂).hom = (extendToSuccObjIso hj F τ i₁ (hi.trans hi₂)).hom ≫ F.map (homOfLE hi
)
参数：i₁ i₂ : J；hi : i₁ <= i₂；hi₂ : i₂ <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.extendToSucc.map_eq`：map_eq (i₁ i₂
 : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j) : map hj F τ i₁ i₂ hi (hi₂.trans (Order.le
_succ j)) = (objIso F X ⟨i₁, hi.trans hi₂⟩).hom…
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
lemma extendToSuccObjIso_hom_naturality (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ j) :
    (extendToSucc hj F τ).map (homOfLE hi :
      ⟨i₁, hi.trans (hi₂.trans (Order.le_succ j))⟩ ⟶ ⟨i₂, hi₂.trans (Order.le_succ j)⟩) ≫
    (extendToSuccObjIso hj F τ i₂ hi₂).hom =
      (extendToSuccObjIso hj F τ i₁ (hi.trans hi₂)).hom ≫ F.map (homOfLE hi) := by
  dsimp [extendToSucc, extendToSuccObjIso]
  rw [extendToSucc.map_eq _ _ _ _ _ _ hi₂, assoc, assoc, Iso.inv_hom_id, comp_id]

/-- The isomorphism expressing that `extendToSucc hj F τ` extends `F`. -/
@[simps!]
/-
**CategoryTheory.SmallObject.SuccStruct.extendToSuccRestrictionLEIso** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：extendToSuccRestrictionLEIso : SmallObject.restrictionLE (extendToSucc hj 
F τ) (Order.le_succ j) ≅ F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism expressing that `extendToSucc hj F τ` extends `F`.
-/
def extendToSuccRestrictionLEIso :
    SmallObject.restrictionLE (extendToSucc hj F τ) (Order.le_succ j) ≅ F :=
  NatIso.ofComponents (fun i ↦ extendToSuccObjIso hj F τ i.1 i.2) (by
    rintro ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ f
    apply extendToSuccObjIso_hom_naturality)
/-
**CategoryTheory.SmallObject.SuccStruct.extendToSucc_map** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：extendToSucc_map (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j) : (extendToSu
cc hj F τ).map (homOfLE hi : ⟨i₁, hi.trans (hi₂.trans (Order.le_succ j))⟩ ⟶ ⟨i₂,
 hi₂.trans (Order.le_succ j)⟩) = (extendToSuccObjIso hj F τ i₁ (hi.trans hi₂)).h
om ≫ F.map (homOfLE hi) ≫ (extendToSuccObjIso hj F τ i₂ hi₂).inv
参数：i₁ i₂ : J；hi : i₁ <= i₂；hi₂ : i₂ <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.SmallObject.SuccStruct.extendToSuccObjIso_hom_naturality_
assoc`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {J : Type 
u} [inst_1 : LinearOrder J]   [inst_2 : SuccOrder J] {j : J} (hj : …
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma extendToSucc_map (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ j) :
    (extendToSucc hj F τ).map (homOfLE hi :
      ⟨i₁, hi.trans (hi₂.trans (Order.le_succ j))⟩ ⟶ ⟨i₂, hi₂.trans (Order.le_succ j)⟩) =
      (extendToSuccObjIso hj F τ i₁ (hi.trans hi₂)).hom ≫ F.map (homOfLE hi) ≫
      (extendToSuccObjIso hj F τ i₂ hi₂).inv := by
  rw [← extendToSuccObjIso_hom_naturality_assoc, Iso.hom_inv_id, comp_id]
/-
**CategoryTheory.SmallObject.SuccStruct.extendToSucc_map_le_succ** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：extendToSucc_map_le_succ : (extendToSucc hj F τ).map (homOfLE (Order.le_su
cc j)) = (extendToSuccObjIso hj F τ j (by simp)).hom ≫ τ ≫ (extendToSuccObjSuccI
so hj F τ).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.extendToSucc.map_self_succ`：map_se
lf_succ : map hj F τ j (Order.succ j) (Order.le_succ j) (by rfl) = (objIso F X ⟨
j, by simp⟩).hom ≫ τ ≫ (objSuccIso hj F X).inv
-/
lemma extendToSucc_map_le_succ :
    (extendToSucc hj F τ).map (homOfLE (Order.le_succ j)) =
        (extendToSuccObjIso hj F τ j (by simp)).hom ≫ τ ≫
          (extendToSuccObjSuccIso hj F τ).inv :=
  extendToSucc.map_self_succ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.SmallObject.SuccStruct.arrowMap_extendToSucc** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：arrowMap_extendToSucc (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j) : arrowM
ap (extendToSucc hj F τ) i₁ i₂ hi (hi₂.trans (Order.le_succ j)) = arrowMap F i₁ 
i₂ hi hi₂
参数：i₁ i₂ : J；hi : i₁ <= i₂；hi₂ : i₂ <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.extendToSucc.obj_eq`：obj_eq (i : S
et.Iic j) : obj F X ⟨i, i.2.trans (Order.le_succ j)⟩ = F.obj i
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.extendToSucc_map`：extendToSucc_map
 (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j) : (extendToSucc hj F τ).map (homOfL
E hi : ⟨i₁, hi.trans (hi₂.trans (Order.le_su…
· 使用引理 `CategoryTheory.Arrow.arrow_mk_eqToHom_comp`：arrow_mk_eqToHom_comp {X' X 
Y : T} (f : X ⟶ Y) (h : X' = X) : Arrow.mk (eqToHom h ≫ f) = Arrow.mk f
· 使用引理 `CategoryTheory.Arrow.arrow_mk_comp_eqToHom`：arrow_mk_comp_eqToHom {X Y Y
' : T} (f : X ⟶ Y) (h : Y = Y') : Arrow.mk (f ≫ eqToHom h) = Arrow.mk f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma arrowMap_extendToSucc (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ j) :
    arrowMap (extendToSucc hj F τ) i₁ i₂ hi (hi₂.trans (Order.le_succ j)) =
      arrowMap F i₁ i₂ hi hi₂ := by
  simp [arrowMap, extendToSucc_map hj F τ i₁ i₂ hi hi₂,
    extendToSuccObjIso, extendToSucc.objIso]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.SmallObject.SuccStruct.arrowSucc_extendToSucc** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：arrowSucc_extendToSucc : arrowSucc (extendToSucc hj F τ) j (Order.lt_succ_
of_not_isMax hj) = Arrow.mk τ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Order.lt_succ_of_not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [inst_1
 : SuccOrder α] {a : α}, ¬IsMax a → a < Order.succ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.extendToSucc.obj_succ_eq`：obj_succ
_eq : obj F X ⟨Order.succ j, by simp⟩ = X
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.extendToSucc.obj_eq`：obj_eq (i : S
et.Iic j) : obj F X ⟨i, i.2.trans (Order.le_succ j)⟩ = F.obj i
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.extendToSucc_map_le_succ`：extendTo
Succ_map_le_succ : (extendToSucc hj F τ).map (homOfLE (Order.le_succ j)) = (exte
ndToSuccObjIso hj F τ j (by simp)).hom ≫ τ ≫ (extend…
· 使用引理 `CategoryTheory.Arrow.arrow_mk_eqToHom_comp`：arrow_mk_eqToHom_comp {X' X 
Y : T} (f : X ⟶ Y) (h : X' = X) : Arrow.mk (eqToHom h ≫ f) = Arrow.mk f
· 使用引理 `CategoryTheory.Arrow.arrow_mk_comp_eqToHom`：arrow_mk_comp_eqToHom {X Y Y
' : T} (f : X ⟶ Y) (h : Y = Y') : Arrow.mk (f ≫ eqToHom h) = Arrow.mk f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma arrowSucc_extendToSucc :
    arrowSucc (extendToSucc hj F τ) j (Order.lt_succ_of_not_isMax hj) =
      Arrow.mk τ := by
  simp [arrowSucc, arrowMap, extendToSucc_map_le_succ, extendToSuccObjIso,
    extendToSucc.objIso, extendToSuccObjSuccIso, extendToSucc.objSuccIso]

end SuccStruct

end SmallObject

end CategoryTheory

