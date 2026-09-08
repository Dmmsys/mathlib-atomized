/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic

/-!
# The heart of a t-structure

Let `t` be a t-structure on a triangulated category `C`. We define
the heart of `t` as a property `t.heart : ObjectProperty C`. As the
the heart is usually identified to a particular category in the applications
(e.g. the heart of the canonical t-structure on the derived category of
an abelian category `A` identifies to `A`), instead of working
with the full subcategory defined by `t.heart`, we introduce a typeclass
`t.Heart H` which says that the additive category `H` identifies to
the full subcategory `t.heart`.

## TODO (@joelriou)
* Show that the heart is an abelian category.

## References
* [Beilinson, Bernstein, Deligne, Gabber, *Faisceaux pervers*][bbd-1982]

-/

@[expose] public section

universe v' u' v u

namespace CategoryTheory.Triangulated.TStructure

open Pretriangulated Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C)

/-- The heart of a t-structure, as the property of objects
that are both `≤ 0` and `≥ 0`. -/
/-
**CategoryTheory.Triangulated.TStructure.heart** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Triangulated.TStructure`。
形式化陈述：heart : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The heart of a t-structure, as the property of objects
that are both `≤ 0` and `≥ 0`.
-/
def heart : ObjectProperty C := t.le 0 ⊓ t.ge 0
  deriving ObjectProperty.IsClosedUnderIsomorphisms
/-
**CategoryTheory.Triangulated.TStructure.mem_heart_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：mem_heart_iff (X : C) : t.heart X ↔ t.IsLE X 0 ∧ t.IsGE X 0
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_heart_iff (X : C) :
    t.heart X ↔ t.IsLE X 0 ∧ t.IsGE X 0 := by
  simp [heart]

variable (H : Type u') [Category.{v'} H] [Preadditive H]

/-- Given `t : TStructure C` and a preadditive category `H`, this typeclass
contains the data of a fully faithful additive functor `H ⥤ C` which identifies
`H` to the full subcategory of `C` consisting of the objects satisfying
the property `t.heart`. -/
/-
**CategoryTheory.Triangulated.TStructure.Heart** 是 Mathlib 中的一个类，位于命名空间 `Categor
yTheory.Triangulated.TStructure`。
形式化陈述：Heart where /-- The inclusion functor. -/ ι : H ⥤ C additive_ι : ι.Additiv
e
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `t : TStructure C` and a preadditive category `H`, this typeclass
contains the data of a fully faithful additive functor `H ⥤ C` which identifies
`H` to the full subcategory of `C` consisting of the objects satisfying
the property `t.heart`.
-/
class Heart where
  /-- The inclusion functor. -/
  ι : H ⥤ C
  additive_ι : ι.Additive := by infer_instance
  full_ι : ι.Full := by infer_instance
  faithful_ι : ι.Faithful := by infer_instance
  essImage_eq_heart : ι.essImage = t.heart := by simp

/-- Unless a better candidate category is available, the full subcategory
of objects satisfying `t.heart` can be chosen as the heart of a t-structure `t`. -/
@[instance_reducible]
/-
**CategoryTheory.Triangulated.TStructure.hasHeartFullSubcategory** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：hasHeartFullSubcategory : t.Heart t.heart.FullSubcategory where ι
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unless a better candidate category is available, the full subcategory
of objects satisfying `t.heart` can be chosen as the heart of a t-structure `t`.
-/
def hasHeartFullSubcategory : t.Heart t.heart.FullSubcategory where
  ι := t.heart.ι
  essImage_eq_heart := by
    ext X
    exact ⟨fun ⟨⟨Y, hY⟩, ⟨e⟩⟩ ↦ t.heart.prop_of_iso e hY,
      fun hX ↦ ⟨⟨X, hX⟩, ⟨Iso.refl _⟩⟩⟩

variable [t.Heart H]

variable {H} in
/-- The inclusion `H ⥤ C` when `H` is the heart of a t-structure `t` on `C`. -/
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `H ⥤ C` when `H` is the heart of a t-structure `t` on `C`.
-/
def ιHeart : H ⥤ C := Heart.ι t
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (t.ιHeart (H := H)).Additive := Heart.additive_ι
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (t.ιHeart (H := H)).Full := Heart.full_ι
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (t.ιHeart (H := H)).Faithful := Heart.faithful_ι

@[simp]
/-
**CategoryTheory.Triangulated.TStructure.essImage_** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma essImage_ιHeart :
    (t.ιHeart (H := H)).essImage = t.heart :=
  Heart.essImage_eq_heart

variable {H} in
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιHeart_obj_mem (X : H) : t.heart (t.ιHeart.obj X) := by
  rw [← t.essImage_ιHeart H]
  exact t.ιHeart.obj_mem_essImage X
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : H) : t.IsLE (t.ιHeart.obj X) 0 :=
  ⟨(t.ιHeart_obj_mem X).1⟩
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : H) : t.IsGE (t.ιHeart.obj X) 0 :=
  ⟨(t.ιHeart_obj_mem X).2⟩

end CategoryTheory.Triangulated.TStructure

