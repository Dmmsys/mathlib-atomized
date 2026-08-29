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

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C Int]
  [forall (n : Int), (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C)

/--
Definition of `heart` / `heart` 的定义

English:
definition heart
  signature: : ObjectProperty C
  body: t.le 0 ⊓ t.ge 0
  deriving ObjectProperty.IsClosedUnderIsomorphisms

中文:
定义 heart
  签名: : Object命题erty C
  定义体: t.le 0 ⊓ t.ge 0
  deriving ObjectProperty.IsClosedUnderIsomorphisms

Depends on / 依赖: t.ge, t.le
-/
def heart : ObjectProperty C := t.le 0 ⊓ t.ge 0
  deriving ObjectProperty.IsClosedUnderIsomorphisms

/--
lemma `mem_heart_iff` / 引理 `mem_heart_iff`

English:
lemma mem_heart_iff
  given: (X : C)
  proof: by
  simp [heart]

中文:
引理 mem_heart_iff
  条件: (X : C)
  证明: by
  simp [heart]
-/
lemma mem_heart_iff (X : C) :
    t.heart X ↔ t.IsLE X 0 ∧ t.IsGE X 0 := by
  simp [heart]

variable (H : Type u') [Category.{v'} H] [Preadditive H]

/--
Definition of `Heart` / `Heart` 的定义

English:
class Heart
  parameters: where
  axioms and operations (5):
    - ι : H ⥤ C
    - additive_ι : ι.Additive  [default: by infer_instance]
    - full_ι : ι.Full  [default: by infer_instance]
    - faithful_ι : ι.Faithful  [default: by infer_instance]
    - essImage_eq_heart : ι.essImage = t.heart  [default: by simp]

中文:
类 Heart
  参数: where
  公理与运算 (5 个):
    - ι : H ⥤ C
    - additive_ι : ι.Additive  [默认: by infer_instance]
    - full_ι : ι.Full  [默认: by infer_instance]
    - faithful_ι : ι.Faithful  [默认: by infer_instance]
    - essImage_eq_heart : ι.essImage = t.heart  [默认: by simp]

Depends on / 依赖: Faithful, essImage, essImage_eq_heart, infer_instance, t.heart
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
/--
Definition of `hasHeartFullSubcategory` / `hasHeartFullSubcategory` 的定义

English:
definition hasHeartFullSubcategory
  signature: : t.Heart t.heart.FullSubcategory where
  body: t.heart.ι
  essImage_eq_heart := by
    ext X
    exact ⟨fun ⟨⟨Y, hY⟩, ⟨e⟩⟩ => t.heart.prop_of_iso e hY,
      fun hX => ⟨⟨X, hX⟩, ⟨Iso.refl _⟩⟩⟩

中文:
定义 hasHeartFullSubcategory
  签名: : t.Heart t.heart.FullSubcategory where
  定义体: t.heart.ι
  essImage_eq_heart := by
    ext X
    exact ⟨fun ⟨⟨Y, hY⟩, ⟨e⟩⟩ => t.heart.prop_of_iso e hY,
      fun hX => ⟨⟨X, hX⟩, ⟨Iso.refl _⟩⟩⟩

Depends on / 依赖: t.heart
-/
def hasHeartFullSubcategory : t.Heart t.heart.FullSubcategory where
  ι := t.heart.ι
  essImage_eq_heart := by
    ext X
    exact ⟨fun ⟨⟨Y, hY⟩, ⟨e⟩⟩ => t.heart.prop_of_iso e hY,
      fun hX => ⟨⟨X, hX⟩, ⟨Iso.refl _⟩⟩⟩

variable [t.Heart H]

variable {H} in
/--
Definition of `ιHeart` / `ιHeart` 的定义

English:
definition ιHeart
  signature: : H ⥤ C
  body: Heart.ι t

中文:
定义 ιHeart
  签名: : H ⥤ C
  定义体: Heart.ι t
-/
def ιHeart : H ⥤ C := Heart.ι t

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (t.ιHeart (H := H)).Additive
  body: Heart.additive_ι

中文:
实例 :
  签名: (t.ιHeart (H := H)).Additive
  定义体: Heart.additive_ι

Depends on / 依赖: Additive, Heart.additive_
-/
instance : (t.ιHeart (H := H)).Additive := Heart.additive_ι
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (t.ιHeart (H := H)).Full
  body: Heart.full_ι

中文:
实例 :
  签名: (t.ιHeart (H := H)).Full
  定义体: Heart.full_ι

Depends on / 依赖: Heart.full_
-/
instance : (t.ιHeart (H := H)).Full := Heart.full_ι
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (t.ιHeart (H := H)).Faithful
  body: Heart.faithful_ι

@[simp]

中文:
实例 :
  签名: (t.ιHeart (H := H)).Faithful
  定义体: Heart.faithful_ι

@[simp]

Depends on / 依赖: Faithful, Heart.faithful_
-/
instance : (t.ιHeart (H := H)).Faithful := Heart.faithful_ι

@[simp]
/--
lemma `essImage_ιHeart` / 引理 `essImage_ιHeart`

English:
lemma essImage_ιHeart
  proof: Heart.essImage_eq_heart

中文:
引理 essImage_ιHeart
  证明: Heart.essImage_eq_heart

Depends on / 依赖: essImage, t.heart
-/
lemma essImage_ιHeart :
    (t.ιHeart (H := H)).essImage = t.heart :=
  Heart.essImage_eq_heart

variable {H} in
/--
lemma `ιHeart_obj_mem` / 引理 `ιHeart_obj_mem`

English:
lemma ιHeart_obj_mem
  given: (X : H)
  statement: t.heart (t.ιHeart.obj X)
  proof: by
  rw [← t.essImage_ιHeart H]
  exact t.ιHeart.obj_mem_essImage X

中文:
引理 ιHeart_obj_mem
  条件: (X : H)
  结论: t.heart (t.ιHeart.obj X)
  证明: by
  rw [← t.essImage_ιHeart H]
  exact t.ιHeart.obj_mem_essImage X

Depends on / 依赖: Heart.obj_mem_essImage, obj_mem_essImage, t.essImage_
-/
lemma ιHeart_obj_mem (X : H) : t.heart (t.ιHeart.obj X) := by
  rw [← t.essImage_ιHeart H]
  exact t.ιHeart.obj_mem_essImage X

instance (X : H) : t.IsLE (t.ιHeart.obj X) 0 :=
  ⟨(t.ιHeart_obj_mem X).1⟩

instance (X : H) : t.IsGE (t.ιHeart.obj X) 0 :=
  ⟨(t.ιHeart_obj_mem X).2⟩

end CategoryTheory.Triangulated.TStructure
