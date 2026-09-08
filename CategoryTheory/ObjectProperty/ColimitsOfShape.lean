/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Limits.Presentation

import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Objects that are colimits of objects satisfying a certain property

Given a property of objects `P : ObjectProperty C` and a category `J`,
we introduce two properties of objects `P.strictColimitsOfShape J`
and `P.colimitsOfShape J`. The former contains exactly the objects
of the form `colimit F` for any functor `F : J ⥤ C` that has
a colimit and such that `F.obj j` satisfies `P` for any `j`, while
the latter contains all the objects that are isomorphic to
these "chosen" objects `colimit F`.

Under certain circumstances, the type of objects satisfying
`P.strictColimitsOfShape J` is small: the main reason this variant is
introduced is to deduce that the full subcategory of `P.colimitsOfShape J`
is essentially small.

By requiring `P.colimitsOfShape J ≤ P`, we introduce a typeclass
`P.IsClosedUnderColimitsOfShape J`.

We also show that `colimitsOfShape` in a category `C` is related
to `limitsOfShape` in the opposite category `Cᵒᵖ` and vice versa.

## TODO

* refactor `ObjectProperty.ind` by saying that it is the supremum
  of `P.colimitsOfShape J` for a filtered category `J`
  (generalize also to `κ`-filtered categories?)
* formalize the closure of `P` under finite colimits (which require
  iterating over `ℕ`), and more generally the closure under colimits
  indexed by a category whose type of arrows has a cardinality
  that is bounded by a certain regular cardinal (@joelriou)

-/

@[expose] public section

universe w v'' v' u'' u' v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C D : Type*} [Category* C] [Category* D] (P : ObjectProperty C)
  (J : Type u') [Category.{v'} J]
  {J' : Type u''} [Category.{v''} J']

/-- The property of objects that are *equal* to `colimit F` for some
functor `F : J ⥤ C` where all `F.obj j` satisfy `P`. -/
/-
**CategoryTheory.ObjectProperty.strictColimitsOfShape** 是 Mathlib 中的一个归纳类型，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     Cat
egoryTheory.ObjectProperty C →       (J : Type u') → [CategoryTheory.Category.{v
', u'} J] → CategoryTheory.ObjectProperty C
参数：J : Type u'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects that are *equal* to `colimit F` for some
functor `F : J ⥤ C` where all `F.obj j` satisfy `P`.
-/
inductive strictColimitsOfShape : ObjectProperty C
  | colimit (F : J ⥤ C) [HasColimit F] (hF : ∀ j, P (F.obj j)) :
    strictColimitsOfShape (colimit F)

variable {P} in
/-
**CategoryTheory.ObjectProperty.strictColimitsOfShape_monotone** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：strictColimitsOfShape_monotone {Q : ObjectProperty C} (h : P <= Q) : P.str
ictColimitsOfShape J <= Q.strictColimitsOfShape J
参数：h : P <= Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma strictColimitsOfShape_monotone {Q : ObjectProperty C} (h : P ≤ Q) :
    P.strictColimitsOfShape J ≤ Q.strictColimitsOfShape J := by
  rintro _ ⟨F, hF⟩
  exact ⟨F, fun j ↦ h _ (hF j)⟩

@[simp]
/-
**CategoryTheory.ObjectProperty.strictColimitsOfShape_bot** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：strictColimitsOfShape_bot [Nonempty J] : strictColimitsOfShape (⊥ : Object
Property C) J = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma strictColimitsOfShape_bot [Nonempty J] :
    strictColimitsOfShape (⊥ : ObjectProperty C) J = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨_, h⟩
  exact h (Classical.arbitrary J)

/-- A structure expressing that `X : C` is the colimit of a functor
`diag : J ⥤ C` such that `P (diag.obj j)` holds for all `j`. -/
/-
**CategoryTheory.ObjectProperty.ColimitOfShape** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.ObjectProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     Cat
egoryTheory.ObjectProperty C →       (J : Type u') → [CategoryTheory.Category.{v
', u'} J] → C → Type (max (max (max u' u_1) v') v_1)
参数：J : Type u'；max (max (max u' u_1) v') v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure expressing that `X : C` is the colimit of a functor
`diag : J ⥤ C` such that `P (diag.obj j)` holds for all `j`.
-/
structure ColimitOfShape (X : C) extends ColimitPresentation J X where
  prop_diag_obj (j : J) : P (diag.obj j)

namespace ColimitOfShape

variable {P J}

/-- If `F : J ⥤ C` is a functor that has a colimit and is such that for all `j`,
`F.obj j` satisfies a property `P`, then this structure expresses that `colimit F`
is indeed a colimit of objects satisfying `P`. -/
@[simps toColimitPresentation]
/-
**CategoryTheory.ObjectProperty.ColimitOfShape.colimit** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.ObjectProperty.ColimitOfShape`。
形式化陈述：colimit (F : J ⥤ C) [HasColimit F] (hF : forall j, P (F.obj j)) : P.Colimi
tOfShape J (colimit F) where toColimitPresentation
参数：F : J ⥤ C；hF : forall j, P (F.obj j)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : J ⥤ C` is a functor that has a colimit and is such that for all `j`,
`F.obj j` satisfies a property `P`, then this structure expresses that `colimit 
F`
is indeed a colimit of objects satisfying `P`.
-/
noncomputable def colimit (F : J ⥤ C) [HasColimit F] (hF : ∀ j, P (F.obj j)) :
    P.ColimitOfShape J (colimit F) where
  toColimitPresentation := .colimit F
  prop_diag_obj := hF

/-- If `X` is a colimit indexed by `J` of objects satisfying a property `P`, then
any object that is isomorphic to `X` also is. -/
@[simps toColimitPresentation]
/-
**CategoryTheory.ObjectProperty.ColimitOfShape.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ObjectProperty.ColimitOfShape`。
形式化陈述：ofIso {X : C} (h : P.ColimitOfShape J X) {Y : C} (e : X ≅ Y) : P.ColimitOf
Shape J Y where toColimitPresentation
参数：h : P.ColimitOfShape J X；e : X ≅ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.ColimitOfShape.prop_diag_obj`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPro
perty C} {J : Type u'}   [inst_1 : CategoryTheor…

--- 原说明 ---
If `X` is a colimit indexed by `J` of objects satisfying a property `P`, then
any object that is isomorphic to `X` also is.
-/
def ofIso {X : C} (h : P.ColimitOfShape J X) {Y : C} (e : X ≅ Y) :
    P.ColimitOfShape J Y where
  toColimitPresentation := .ofIso h.toColimitPresentation e
  prop_diag_obj := h.prop_diag_obj

/-- If `X` is a colimit indexed by `J` of objects satisfying a property `P`,
it is also a colimit indexed by `J` of objects satisfying `Q` if `P ≤ Q`. -/
@[simps toColimitPresentation]
/-
**CategoryTheory.ObjectProperty.ColimitOfShape.ofLE** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.ObjectProperty.ColimitOfShape`。
形式化陈述：ofLE {X : C} (h : P.ColimitOfShape J X) {Q : ObjectProperty C} (hPQ : P <=
 Q) : Q.ColimitOfShape J X where toColimitPresentation
参数：h : P.ColimitOfShape J X；hPQ : P <= Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is a colimit indexed by `J` of objects satisfying a property `P`,
it is also a colimit indexed by `J` of objects satisfying `Q` if `P ≤ Q`.
-/
def ofLE {X : C} (h : P.ColimitOfShape J X) {Q : ObjectProperty C} (hPQ : P ≤ Q) :
    Q.ColimitOfShape J X where
  toColimitPresentation := h.toColimitPresentation
  prop_diag_obj j := hPQ _ (h.prop_diag_obj j)

/-- Change the index category for `ObjectProperty.ColimitOfShape`. -/
@[simps toColimitPresentation]
/-
**CategoryTheory.ObjectProperty.ColimitOfShape.reindex** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.ObjectProperty.ColimitOfShape`。
形式化陈述：reindex {X : C} (h : P.ColimitOfShape J X) (G : J' ⥤ J) [G.Final] : P.Coli
mitOfShape J' X where toColimitPresentation
参数：h : P.ColimitOfShape J X；G : J' ⥤ J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Change the index category for `ObjectProperty.ColimitOfShape`.
-/
noncomputable def reindex {X : C} (h : P.ColimitOfShape J X) (G : J' ⥤ J) [G.Final] :
    P.ColimitOfShape J' X where
  toColimitPresentation := h.toColimitPresentation.reindex G
  prop_diag_obj _ := h.prop_diag_obj _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given `P : ObjectProperty C`, and a presentation `P.ColimitOfShape J X`
of an object `X : C`, this is the induced functor `J ⥤ CostructuredArrow P.ι X`. -/
@[simps]
/-
**CategoryTheory.ObjectProperty.ColimitOfShape.toCostructuredArrow** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.ObjectProperty.ColimitOfShape`。
形式化陈述：toCostructuredArrow {X : C} (p : P.ColimitOfShape J X) : J ⥤ CostructuredA
rrow P.ι X where obj j
参数：p : P.ColimitOfShape J X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.ColimitOfShape.prop_diag_obj`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPro
perty C} {J : Type u'}   [inst_1 : CategoryTheor…

--- 原说明 ---
Given `P : ObjectProperty C`, and a presentation `P.ColimitOfShape J X`
of an object `X : C`, this is the induced functor `J ⥤ CostructuredArrow P.ι X`.
-/
def toCostructuredArrow
    {X : C} (p : P.ColimitOfShape J X) :
    J ⥤ CostructuredArrow P.ι X where
  obj j := CostructuredArrow.mk (Y := ⟨_, p.prop_diag_obj j⟩) (by exact p.ι.app j)
  map f := CostructuredArrow.homMk (ObjectProperty.homMk (by exact p.diag.map f))

end ColimitOfShape

/-- The property of objects that are the point of a colimit cocone for a
functor `F : J ⥤ C` where all objects `F.obj j` satisfy `P`. -/
/-
**CategoryTheory.ObjectProperty.colimitsOfShape** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.ObjectProperty`。
形式化陈述：colimitsOfShape : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects that are the point of a colimit cocone for a
functor `F : J ⥤ C` where all objects `F.obj j` satisfy `P`.
-/
def colimitsOfShape : ObjectProperty C :=
  fun X ↦ Nonempty (P.ColimitOfShape J X)

variable {P J} in
/-
**CategoryTheory.ObjectProperty.ColimitOfShape.colimitsOfShape** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.ObjectProperty.ColimitOfShape`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : Catego
ryTheory.ObjectProperty C} {J : Type u'}   [inst_1 : CategoryTheory.Category.{v'
, u'} J] {X : C} (h : P.ColimitOfShape J X), P.colimitsOfShape J X
参数：h : P.ColimitOfShape J X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ColimitOfShape.colimitsOfShape {X : C} (h : P.ColimitOfShape J X) :
    P.colimitsOfShape J X :=
  ⟨h⟩
/-
**CategoryTheory.ObjectProperty.strictColimitsOfShape_le_colimitsOfShape** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：strictColimitsOfShape_le_colimitsOfShape : P.strictColimitsOfShape J <= P.
colimitsOfShape J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma strictColimitsOfShape_le_colimitsOfShape :
    P.strictColimitsOfShape J ≤ P.colimitsOfShape J := by
  rintro X ⟨F, hF⟩
  exact ⟨.colimit F hF⟩

@[simp]
/-
**CategoryTheory.ObjectProperty.colimitsOfShape_bot** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：colimitsOfShape_bot [Nonempty J] : colimitsOfShape (⊥ : ObjectProperty C) 
J = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
-/
lemma colimitsOfShape_bot [Nonempty J] : colimitsOfShape (⊥ : ObjectProperty C) J = ⊥ := by
  rw [eq_bot_iff]
  rintro X ⟨⟨_, h⟩⟩
  exact h (Classical.arbitrary J)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (P.colimitsOfShape J).IsClosedUnderIsomorphisms where
  of_iso := by rintro _ _ e ⟨h⟩; exact ⟨h.ofIso e⟩

@[simp]
/-
**CategoryTheory.ObjectProperty.isoClosure_strictColimitsOfShape** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isoClosure_strictColimitsOfShape : (P.strictColimitsOfShape J).isoClosure 
= P.colimitsOfShape J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isoClosure_le_iff`：isoClosure_le_iff [IsCl
osedUnderIsomorphisms Q] : isoClosure P <= Q ↔ P <= Q
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsColimitsOfSha
pe`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : Category
Theory.ObjectProperty C) (J : Type u')   [inst_1 : CategoryTheor…
· 使用引理 `CategoryTheory.ObjectProperty.strictColimitsOfShape_le_colimitsOfShape`：
strictColimitsOfShape_le_colimitsOfShape : P.strictColimitsOfShape J <= P.colimi
tsOfShape J
· 使用引理 `CategoryTheory.Limits.ColimitPresentation.hasColimit`：hasColimit (pres :
 ColimitPresentation J X) : HasColimit pres.diag
· 使用定理 `CategoryTheory.ObjectProperty.ColimitOfShape.prop_diag_obj`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPro
perty C} {J : Type u'}   [inst_1 : CategoryTheor…
-/
lemma isoClosure_strictColimitsOfShape :
    (P.strictColimitsOfShape J).isoClosure = P.colimitsOfShape J := by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    apply strictColimitsOfShape_le_colimitsOfShape
  · intro X ⟨h⟩
    have := h.hasColimit
    exact ⟨colimit h.diag, strictColimitsOfShape.colimit h.diag h.prop_diag_obj,
      ⟨h.isColimit.coconePointUniqueUpToIso (colimit.isColimit _)⟩⟩

variable {P} in
/-
**CategoryTheory.ObjectProperty.colimitsOfShape_monotone** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.ObjectProperty`。
形式化陈述：colimitsOfShape_monotone {Q : ObjectProperty C} (hPQ : P <= Q) : P.colimit
sOfShape J <= Q.colimitsOfShape J
参数：hPQ : P <= Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma colimitsOfShape_monotone {Q : ObjectProperty C} (hPQ : P ≤ Q) :
    P.colimitsOfShape J ≤ Q.colimitsOfShape J := by
  intro X ⟨h⟩
  exact ⟨h.ofLE hPQ⟩

@[simp]
/-
**CategoryTheory.ObjectProperty.colimitsOfShape_isoClosure** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：colimitsOfShape_isoClosure : P.isoClosure.colimitsOfShape J = P.colimitsOf
Shape J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `CategoryTheory.ObjectProperty.ColimitOfShape.prop_diag_obj`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPro
perty C} {J : Type u'}   [inst_1 : CategoryTheor…
· 使用引理 `CategoryTheory.ObjectProperty.colimitsOfShape_monotone`：colimitsOfShape_
monotone {Q : ObjectProperty C} (hPQ : P <= Q) : P.colimitsOfShape J <= Q.colimi
tsOfShape J
· 使用引理 `CategoryTheory.ObjectProperty.le_isoClosure`：le_isoClosure : P <= isoClo
sure P
-/
lemma colimitsOfShape_isoClosure :
    P.isoClosure.colimitsOfShape J = P.colimitsOfShape J := by
  refine le_antisymm ?_ (colimitsOfShape_monotone _ (P.le_isoClosure))
  intro X ⟨h⟩
  choose obj h₁ h₂ using h.prop_diag_obj
  exact
   ⟨{ toColimitPresentation := h.changeDiag (h.diag.isoCopyObj obj (fun j ↦ (h₂ j).some)).symm
      prop_diag_obj := h₁ }⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ObjectProperty.Small.{w} P] [LocallySmall.{w} C] [Small.{w} J] [LocallySmall.{w} J] :
    ObjectProperty.Small.{w} (P.strictColimitsOfShape J) := by
  refine small_of_surjective
    (f := fun (F : { F : J ⥤ P.FullSubcategory // HasColimit (F ⋙ P.ι) }) ↦
      (⟨_, letI := F.2; ⟨F.1 ⋙ P.ι, fun j ↦ (F.1.obj j).2⟩⟩)) ?_
  rintro ⟨_, ⟨F, hF⟩⟩
  exact ⟨⟨P.lift F hF, by assumption⟩, rfl⟩

/-- A property of objects satisfies `P.IsClosedUnderColimitsOfShape J` if it
is stable by colimits of shape `J`. -/
@[mk_iff]
/-
**CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape** 是 Mathlib 中的一个归纳类
型，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     Cat
egoryTheory.ObjectProperty C → (J : Type u') → [CategoryTheory.Category.{v', u'}
 J] → Prop
参数：J : Type u'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property of objects satisfies `P.IsClosedUnderColimitsOfShape J` if it
is stable by colimits of shape `J`.
-/
class IsClosedUnderColimitsOfShape (P : ObjectProperty C) (J : Type u') [Category.{v'} J] where
  colimitsOfShape_le (P J) : P.colimitsOfShape J ≤ P

variable {P J} in
/-
**CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape.mk'** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : Catego
ryTheory.ObjectProperty C} {J : Type u'}   [inst_1 : CategoryTheory.Category.{v'
, u'} J] [P.IsClosedUnderIsomorphisms],   P.strictColimitsOfShape J ≤ P → P.IsCl
osedUnderColimitsOfShape J
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.isoClosure_eq_self`：isoClosure_eq_self [Is
ClosedUnderIsomorphisms P] : isoClosure P = P
· 使用引理 `CategoryTheory.ObjectProperty.isoClosure_strictColimitsOfShape`：isoClosu
re_strictColimitsOfShape : (P.strictColimitsOfShape J).isoClosure = P.colimitsOf
Shape J
· 使用引理 `CategoryTheory.ObjectProperty.monotone_isoClosure`：monotone_isoClosure (
h : P <= Q) : isoClosure P <= isoClosure Q
-/
lemma IsClosedUnderColimitsOfShape.mk' [P.IsClosedUnderIsomorphisms]
    (h : P.strictColimitsOfShape J ≤ P) :
    P.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    conv_rhs => rw [← P.isoClosure_eq_self]
    rw [← isoClosure_strictColimitsOfShape]
    exact monotone_isoClosure h
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty J] : IsClosedUnderColimitsOfShape (⊥ : ObjectProperty C) J where
  colimitsOfShape_le := by rw [colimitsOfShape_bot]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsClosedUnderColimitsOfShape (⊤ : ObjectProperty C) J where
  colimitsOfShape_le _ _ := by trivial

export IsClosedUnderColimitsOfShape (colimitsOfShape_le)

section

variable {J} [P.IsClosedUnderColimitsOfShape J]

variable {P} in
/-
**CategoryTheory.ObjectProperty.ColimitOfShape.prop** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.ObjectProperty.ColimitOfShape`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : Catego
ryTheory.ObjectProperty C} {J : Type u'}   [inst_1 : CategoryTheory.Category.{v'
, u'} J] [P.IsClosedUnderColimitsOfShape J] {X : C} (h : P.ColimitOfShape J X), 
  P X
参数：h : P.ColimitOfShape J X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape.colimitsOfSha
pe_le`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} (P : Categ
oryTheory.ObjectProperty C) (J : Type u')   {inst_1 : CategoryTheor…
-/
lemma ColimitOfShape.prop {X : C} (h : P.ColimitOfShape J X) : P X :=
  P.colimitsOfShape_le J _ ⟨h⟩
/-
**CategoryTheory.ObjectProperty.prop_of_isColimit** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：prop_of_isColimit {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) (hF : fora
ll (j : J), P (F.obj j)) : P c.pt
参数：hc : IsColimit c；hF : forall (j : J), P (F.obj j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape.colimitsOfSha
pe_le`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} (P : Categ
oryTheory.ObjectProperty C) (J : Type u')   {inst_1 : CategoryTheor…
-/
lemma prop_of_isColimit {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ (j : J), P (F.obj j)) : P c.pt :=
  P.colimitsOfShape_le J _ ⟨{ diag := _, ι := _, isColimit := hc, prop_diag_obj := hF }⟩
/-
**CategoryTheory.ObjectProperty.prop_colimit** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ObjectProperty`。
形式化陈述：prop_colimit (F : J ⥤ C) [HasColimit F] (hF : forall (j : J), P (F.obj j))
 : P (colimit F)
参数：F : J ⥤ C；hF : forall (j : J), P (F.obj j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isColimit`：prop_of_isColimit {F : 
J ⥤ C} {c : Cocone F} (hc : IsColimit c) (hF : forall (j : J), P (F.obj j)) : P 
c.pt
-/
lemma prop_colimit (F : J ⥤ C) [HasColimit F] (hF : ∀ (j : J), P (F.obj j)) :
    P (colimit F) :=
  P.prop_of_isColimit (colimit.isColimit F) hF

end

variable {J} in
/-
**CategoryTheory.ObjectProperty.colimitsOfShape_le_of_final** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：colimitsOfShape_le_of_final (G : J ⥤ J') [G.Final] : P.colimitsOfShape J' 
<= P.colimitsOfShape J
参数：G : J ⥤ J'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma colimitsOfShape_le_of_final (G : J ⥤ J') [G.Final] :
    P.colimitsOfShape J' ≤ P.colimitsOfShape J :=
  fun _h ⟨h⟩ ↦ ⟨h.reindex G⟩

variable {J} in
/-
**CategoryTheory.ObjectProperty.colimitsOfShape_congr** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ObjectProperty`。
形式化陈述：colimitsOfShape_congr (e : J ≌ J') : P.colimitsOfShape J = P.colimitsOfSha
pe J'
参数：e : J ≌ J'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.ObjectProperty.colimitsOfShape_le_of_final`：colimitsOfSha
pe_le_of_final (G : J ⥤ J') [G.Final] : P.colimitsOfShape J' <= P.colimitsOfShap
e J
· 使用定理 `CategoryTheory.Functor.final_of_isRightAdjoint`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
lemma colimitsOfShape_congr (e : J ≌ J') :
    P.colimitsOfShape J = P.colimitsOfShape J' :=
  le_antisymm (P.colimitsOfShape_le_of_final e.inverse)
    (P.colimitsOfShape_le_of_final e.functor)

variable {J} in
/-
**CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_iff_of_equivalence*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isClosedUnderColimitsOfShape_iff_of_equivalence (e : J ≌ J') : P.IsClosedU
nderColimitsOfShape J ↔ P.IsClosedUnderColimitsOfShape J'
参数：e : J ≌ J'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.ObjectProperty.colimitsOfShape_congr`：colimitsOfShape_con
gr (e : J ≌ J') : P.colimitsOfShape J = P.colimitsOfShape J'
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isClosedUnderColimitsOfShape_iff_of_equivalence (e : J ≌ J') :
    P.IsClosedUnderColimitsOfShape J ↔
      P.IsClosedUnderColimitsOfShape J' := by
  simp [isClosedUnderColimitsOfShape_iff, P.colimitsOfShape_congr e]

variable {P J} in
/-
**CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShap
e`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : Catego
ryTheory.ObjectProperty C} {J : Type u'}   [inst_1 : CategoryTheory.Category.{v'
, u'} J] {J' : Type u''} [inst_2 : CategoryTheory.Category.{v'', u''} J']   (e :
 J ≌ J') [P.IsClosedUnderColimitsOfShape J], P.IsClosedUnderColimitsOfShape J'
参数：e : J ≌ J'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_iff_of_equiva
lence`：isClosedUnderColimitsOfShape_iff_of_equivalence (e : J ≌ J') : P.IsClosed
UnderColimitsOfShape J ↔ P.IsClosedUnderColimitsOfShape J'
-/
lemma IsClosedUnderColimitsOfShape.of_equivalence (e : J ≌ J')
    [P.IsClosedUnderColimitsOfShape J] :
    P.IsClosedUnderColimitsOfShape J' := by
  rwa [← P.isClosedUnderColimitsOfShape_iff_of_equivalence e]
/-
**CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape.inverseImage** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape`
。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (J : Type u') [inst_2 : Ca
tegoryTheory.Category.{v', u'} J]   (P : CategoryTheory.ObjectProperty D) (F : C
ategoryTheory.Functor C D) [P.IsClosedUnderColimitsOfShape J]   [CategoryTheory.
Limits.PreservesColimitsOfShape J F], (P.inverseImage F).IsClosedUnderColimitsOf
Shape J
参数：J : Type u'；P : CategoryTheory.ObjectProperty D；F : CategoryTheory.Functor C 
D；P.inverseImage F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.ColimitOfShape.prop`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectProperty C} 
{J : Type u'}   [inst_1 : CategoryTheor…
-/
instance IsClosedUnderColimitsOfShape.inverseImage
    (P : ObjectProperty D) (F : C ⥤ D) [P.IsClosedUnderColimitsOfShape J]
    [PreservesColimitsOfShape J F] : (P.inverseImage F).IsClosedUnderColimitsOfShape J :=
  ⟨fun _ ⟨c, H⟩ ↦ ColimitOfShape.prop (P := P) ⟨c.map F, H⟩⟩
/-
**CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_inverseImage_iff** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isClosedUnderColimitsOfShape_inverseImage_iff (P : ObjectProperty D) [P.Is
ClosedUnderIsomorphisms] (e : C ≌ D) : (P.inverseImage e.functor).IsClosedUnderC
olimitsOfShape J ↔ P.IsClosedUnderColimitsOfShape J
参数：P : ObjectProperty D；e : C ≌ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.ObjectProperty.prop_iff_of_iso`：prop_iff_of_iso [IsClosed
UnderIsomorphisms P] {X Y : C} (e : X ≅ Y) : P X ↔ P Y
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape.inverseImage`
：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (J : Type u'…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
lemma isClosedUnderColimitsOfShape_inverseImage_iff (P : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] (e : C ≌ D) :
    (P.inverseImage e.functor).IsClosedUnderColimitsOfShape J ↔
      P.IsClosedUnderColimitsOfShape J := by
  refine ⟨fun H ↦ ?_, fun _ ↦ inferInstance⟩
  convert!
    (inferInstance :
      ((P.inverseImage e.functor).inverseImage e.inverse).IsClosedUnderColimitsOfShape J)
  ext X
  simpa using P.prop_iff_of_iso (e.counitIso.app X).symm
/-
**CategoryTheory.ObjectProperty.colimitsOfShape_eq_unop_limitsOfShape** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：colimitsOfShape_eq_unop_limitsOfShape : P.colimitsOfShape J = (P.op.limits
OfShape Jᵒᵖ).unop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ObjectProperty.ColimitOfShape.prop_diag_obj`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPro
perty C} {J : Type u'}   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.ObjectProperty.LimitOfShape.prop_diag_obj`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPrope
rty C} {J : Type u'}   [inst_1 : CategoryTheor…
-/
lemma colimitsOfShape_eq_unop_limitsOfShape :
    P.colimitsOfShape J = (P.op.limitsOfShape Jᵒᵖ).unop := by
  ext X
  refine ⟨fun ⟨h⟩ => ⟨?_⟩, fun ⟨h⟩ => ⟨?_⟩⟩
  · exact
      { diag := h.diag.op
        π := NatTrans.op h.ι
        isLimit := isLimitOfUnop h.isColimit
        prop_diag_obj _ := h.prop_diag_obj _ }
  · exact
      { diag := h.diag.unop
        ι := NatTrans.unop h.π
        isColimit := isColimitOfOp h.isLimit
        prop_diag_obj _ := h.prop_diag_obj _ }
/-
**CategoryTheory.ObjectProperty.limitsOfShape_eq_unop_colimitsOfShape** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：limitsOfShape_eq_unop_colimitsOfShape : P.limitsOfShape J = (P.op.colimits
OfShape Jᵒᵖ).unop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ObjectProperty.LimitOfShape.prop_diag_obj`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPrope
rty C} {J : Type u'}   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.ObjectProperty.ColimitOfShape.prop_diag_obj`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPro
perty C} {J : Type u'}   [inst_1 : CategoryTheor…
-/
lemma limitsOfShape_eq_unop_colimitsOfShape :
    P.limitsOfShape J = (P.op.colimitsOfShape Jᵒᵖ).unop := by
  ext X
  refine ⟨fun ⟨h⟩ => ⟨?_⟩, fun ⟨h⟩ => ⟨?_⟩⟩
  · exact
      { diag := h.diag.op
        ι := NatTrans.op h.π
        isColimit := isColimitOfUnop h.isLimit
        prop_diag_obj _ := h.prop_diag_obj _ }
  · exact
      { diag := h.diag.unop
        π := NatTrans.unop h.ι
        isLimit := isLimitOfOp h.isColimit
        prop_diag_obj _ := h.prop_diag_obj _ }
/-
**CategoryTheory.ObjectProperty.limitsOfShape_op** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ObjectProperty`。
形式化陈述：limitsOfShape_op : P.op.limitsOfShape J = (P.colimitsOfShape Jᵒᵖ).op
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.colimitsOfShape_eq_unop_limitsOfShape`：col
imitsOfShape_eq_unop_limitsOfShape : P.colimitsOfShape J = (P.op.limitsOfShape J
ᵒᵖ).unop
· 使用引理 `CategoryTheory.ObjectProperty.op_unop`：op_unop (P : ObjectProperty Cᵒᵖ) 
: P.unop.op = P
· 使用引理 `CategoryTheory.ObjectProperty.limitsOfShape_congr`：limitsOfShape_congr (
e : J ≌ J') : P.limitsOfShape J = P.limitsOfShape J'
-/
lemma limitsOfShape_op :
    P.op.limitsOfShape J = (P.colimitsOfShape Jᵒᵖ).op := by
  rw [colimitsOfShape_eq_unop_limitsOfShape, op_unop,
    P.op.limitsOfShape_congr (opOpEquivalence J)]
/-
**CategoryTheory.ObjectProperty.colimitsOfShape_op** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：colimitsOfShape_op : P.op.colimitsOfShape J = (P.limitsOfShape Jᵒᵖ).op
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.limitsOfShape_eq_unop_colimitsOfShape`：lim
itsOfShape_eq_unop_colimitsOfShape : P.limitsOfShape J = (P.op.colimitsOfShape J
ᵒᵖ).unop
· 使用引理 `CategoryTheory.ObjectProperty.op_unop`：op_unop (P : ObjectProperty Cᵒᵖ) 
: P.unop.op = P
· 使用引理 `CategoryTheory.ObjectProperty.colimitsOfShape_congr`：colimitsOfShape_con
gr (e : J ≌ J') : P.colimitsOfShape J = P.colimitsOfShape J'
-/
lemma colimitsOfShape_op :
    P.op.colimitsOfShape J = (P.limitsOfShape Jᵒᵖ).op := by
  rw [limitsOfShape_eq_unop_colimitsOfShape, op_unop,
    P.op.colimitsOfShape_congr (opOpEquivalence J)]
/-
**CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_iff_op** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isClosedUnderColimitsOfShape_iff_op : P.IsClosedUnderColimitsOfShape J ↔ P
.op.IsClosedUnderLimitsOfShape Jᵒᵖ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_iff`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.Objec
tProperty C) (J : Type u')   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_iff`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.ObjectP
roperty C) (J : Type u')   [inst_1 : CategoryTheor…
· 使用引理 `CategoryTheory.ObjectProperty.colimitsOfShape_eq_unop_limitsOfShape`：col
imitsOfShape_eq_unop_limitsOfShape : P.colimitsOfShape J = (P.op.limitsOfShape J
ᵒᵖ).unop
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.op_monotone_iff`：op_monotone_iff {P Q : Ob
jectProperty C} : P.op <= Q.op ↔ P <= Q
· 使用引理 `CategoryTheory.ObjectProperty.op_unop`：op_unop (P : ObjectProperty Cᵒᵖ) 
: P.unop.op = P
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isClosedUnderColimitsOfShape_iff_op :
    P.IsClosedUnderColimitsOfShape J ↔
      P.op.IsClosedUnderLimitsOfShape Jᵒᵖ := by
  rw [isClosedUnderColimitsOfShape_iff, isClosedUnderLimitsOfShape_iff,
    colimitsOfShape_eq_unop_limitsOfShape, ← op_monotone_iff, op_unop]
/-
**CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_iff_op** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isClosedUnderLimitsOfShape_iff_op : P.IsClosedUnderLimitsOfShape J ↔ P.op.
IsClosedUnderColimitsOfShape Jᵒᵖ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_iff`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.Objec
tProperty C) (J : Type u')   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_iff`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.ObjectP
roperty C) (J : Type u')   [inst_1 : CategoryTheor…
· 使用引理 `CategoryTheory.ObjectProperty.limitsOfShape_eq_unop_colimitsOfShape`：lim
itsOfShape_eq_unop_colimitsOfShape : P.limitsOfShape J = (P.op.colimitsOfShape J
ᵒᵖ).unop
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.op_monotone_iff`：op_monotone_iff {P Q : Ob
jectProperty C} : P.op <= Q.op ↔ P <= Q
· 使用引理 `CategoryTheory.ObjectProperty.op_unop`：op_unop (P : ObjectProperty Cᵒᵖ) 
: P.unop.op = P
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isClosedUnderLimitsOfShape_iff_op :
    P.IsClosedUnderLimitsOfShape J ↔
      P.op.IsClosedUnderColimitsOfShape Jᵒᵖ := by
  rw [isClosedUnderColimitsOfShape_iff, isClosedUnderLimitsOfShape_iff,
    limitsOfShape_eq_unop_colimitsOfShape, ← op_monotone_iff, op_unop]
/-
**CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_op_iff_op** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isClosedUnderColimitsOfShape_op_iff_op : P.IsClosedUnderColimitsOfShape Jᵒ
ᵖ ↔ P.op.IsClosedUnderLimitsOfShape J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_iff`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.Objec
tProperty C) (J : Type u')   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_iff`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.ObjectP
roperty C) (J : Type u')   [inst_1 : CategoryTheor…
· 使用引理 `CategoryTheory.ObjectProperty.limitsOfShape_op`：limitsOfShape_op : P.op.
limitsOfShape J = (P.colimitsOfShape Jᵒᵖ).op
· 使用引理 `CategoryTheory.ObjectProperty.op_monotone_iff`：op_monotone_iff {P Q : Ob
jectProperty C} : P.op <= Q.op ↔ P <= Q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isClosedUnderColimitsOfShape_op_iff_op :
    P.IsClosedUnderColimitsOfShape Jᵒᵖ ↔
      P.op.IsClosedUnderLimitsOfShape J := by
  rw [isClosedUnderColimitsOfShape_iff, isClosedUnderLimitsOfShape_iff,
    limitsOfShape_op, op_monotone_iff]
/-
**CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_op_iff_op** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isClosedUnderLimitsOfShape_op_iff_op : P.IsClosedUnderLimitsOfShape Jᵒᵖ ↔ 
P.op.IsClosedUnderColimitsOfShape J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_iff`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.Objec
tProperty C) (J : Type u')   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_iff`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.ObjectP
roperty C) (J : Type u')   [inst_1 : CategoryTheor…
· 使用引理 `CategoryTheory.ObjectProperty.colimitsOfShape_op`：colimitsOfShape_op : P
.op.colimitsOfShape J = (P.limitsOfShape Jᵒᵖ).op
· 使用引理 `CategoryTheory.ObjectProperty.op_monotone_iff`：op_monotone_iff {P Q : Ob
jectProperty C} : P.op <= Q.op ↔ P <= Q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isClosedUnderLimitsOfShape_op_iff_op :
    P.IsClosedUnderLimitsOfShape Jᵒᵖ ↔
      P.op.IsClosedUnderColimitsOfShape J := by
  rw [isClosedUnderColimitsOfShape_iff, isClosedUnderLimitsOfShape_iff,
    colimitsOfShape_op, op_monotone_iff]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsClosedUnderColimitsOfShape J] :
    P.op.IsClosedUnderLimitsOfShape Jᵒᵖ := by
  rwa [← isClosedUnderColimitsOfShape_iff_op]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsClosedUnderLimitsOfShape J] :
    P.op.IsClosedUnderColimitsOfShape Jᵒᵖ := by
  rwa [← isClosedUnderLimitsOfShape_iff_op]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsClosedUnderColimitsOfShape Jᵒᵖ] :
    P.op.IsClosedUnderLimitsOfShape J := by
  rwa [← isClosedUnderColimitsOfShape_op_iff_op]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsClosedUnderLimitsOfShape Jᵒᵖ] :
    P.op.IsClosedUnderColimitsOfShape J := by
  rwa [← isClosedUnderLimitsOfShape_op_iff_op]

section

variable (Q : ObjectProperty Cᵒᵖ)

/-
**CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_iff_unop** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isClosedUnderColimitsOfShape_iff_unop : Q.IsClosedUnderColimitsOfShape J ↔
 Q.unop.IsClosedUnderLimitsOfShape Jᵒᵖ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_op_iff_op`：isCl
osedUnderLimitsOfShape_op_iff_op : P.IsClosedUnderLimitsOfShape Jᵒᵖ ↔ P.op.IsClo
sedUnderColimitsOfShape J
-/
lemma isClosedUnderColimitsOfShape_iff_unop :
    Q.IsClosedUnderColimitsOfShape J ↔
      Q.unop.IsClosedUnderLimitsOfShape Jᵒᵖ :=
  (Q.unop.isClosedUnderLimitsOfShape_op_iff_op J).symm
/-
**CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_iff_unop** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isClosedUnderLimitsOfShape_iff_unop : Q.IsClosedUnderLimitsOfShape J ↔ Q.u
nop.IsClosedUnderColimitsOfShape Jᵒᵖ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_op_iff_op`：is
ClosedUnderColimitsOfShape_op_iff_op : P.IsClosedUnderColimitsOfShape Jᵒᵖ ↔ P.op
.IsClosedUnderLimitsOfShape J
-/
lemma isClosedUnderLimitsOfShape_iff_unop :
    Q.IsClosedUnderLimitsOfShape J ↔
      Q.unop.IsClosedUnderColimitsOfShape Jᵒᵖ :=
  (Q.unop.isClosedUnderColimitsOfShape_op_iff_op J).symm
/-
**CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_op_iff_unop** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isClosedUnderColimitsOfShape_op_iff_unop : Q.IsClosedUnderColimitsOfShape 
Jᵒᵖ ↔ Q.unop.IsClosedUnderLimitsOfShape J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_iff_op`：isClose
dUnderLimitsOfShape_iff_op : P.IsClosedUnderLimitsOfShape J ↔ P.op.IsClosedUnder
ColimitsOfShape Jᵒᵖ
-/
lemma isClosedUnderColimitsOfShape_op_iff_unop :
    Q.IsClosedUnderColimitsOfShape Jᵒᵖ ↔
      Q.unop.IsClosedUnderLimitsOfShape J :=
  (Q.unop.isClosedUnderLimitsOfShape_iff_op J).symm
/-
**CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_op_iff_unop** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isClosedUnderLimitsOfShape_op_iff_unop : Q.IsClosedUnderLimitsOfShape Jᵒᵖ 
↔ Q.unop.IsClosedUnderColimitsOfShape J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_iff_op`：isClo
sedUnderColimitsOfShape_iff_op : P.IsClosedUnderColimitsOfShape J ↔ P.op.IsClose
dUnderLimitsOfShape Jᵒᵖ
-/
lemma isClosedUnderLimitsOfShape_op_iff_unop :
    Q.IsClosedUnderLimitsOfShape Jᵒᵖ ↔
      Q.unop.IsClosedUnderColimitsOfShape J :=
  (Q.unop.isClosedUnderColimitsOfShape_iff_op J).symm
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Q.IsClosedUnderColimitsOfShape J] :
    Q.unop.IsClosedUnderLimitsOfShape Jᵒᵖ := by
  rwa [← isClosedUnderColimitsOfShape_iff_unop]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Q.IsClosedUnderLimitsOfShape J] :
    Q.unop.IsClosedUnderColimitsOfShape Jᵒᵖ := by
  rwa [← isClosedUnderLimitsOfShape_iff_unop]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Q.IsClosedUnderColimitsOfShape Jᵒᵖ] :
    Q.unop.IsClosedUnderLimitsOfShape J := by
  rwa [← isClosedUnderColimitsOfShape_op_iff_unop]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Q.IsClosedUnderLimitsOfShape Jᵒᵖ] :
    Q.unop.IsClosedUnderColimitsOfShape J := by
  rwa [← isClosedUnderLimitsOfShape_op_iff_unop]

end

/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsClosedUnderColimitsOfShape WalkingParallelPair] :
    P.IsStableUnderRetracts where
  of_retract {X Y} h hY := by
    let c : Cofork (h.r ≫ h.i) (𝟙 Y) := Cofork.ofπ h.r (by simp)
    have hc : IsColimit c :=
      Cofork.IsColimit.mk _ (fun s ↦ h.i ≫ s.π)
        (fun s ↦ by simpa using! s.condition)
        (fun s m hm ↦ by dsimp [c] at hm; simp [← hm])
    exact P.prop_of_isColimit hc (by rintro (_ | _) <;> exact hY)
/-
**CategoryTheory.ObjectProperty.limitsOfShape_isEmpty_iff** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：limitsOfShape_isEmpty_iff [IsEmpty J] (X : C) : P.limitsOfShape J X ↔ None
mpty (IsTerminal X)
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma limitsOfShape_isEmpty_iff [IsEmpty J] (X : C) :
    P.limitsOfShape J X ↔ Nonempty (IsTerminal X) :=
  ⟨fun ⟨⟨f, p, q⟩, d⟩ ↦ .intro <| isLimitEquivIsTerminalOfIsEmpty _ _ q, fun ⟨h⟩ ↦
    ⟨⟨(Functor.const _).obj X, 𝟙 _, (isLimitEquivIsTerminalOfIsEmpty _ _).symm h⟩, by simp⟩⟩
/-
**CategoryTheory.ObjectProperty.colimitsOfShape_isEmpty_iff** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：colimitsOfShape_isEmpty_iff [IsEmpty J] (X : C) : P.colimitsOfShape J X ↔ 
Nonempty (IsInitial X)
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma colimitsOfShape_isEmpty_iff [IsEmpty J] (X : C) :
    P.colimitsOfShape J X ↔ Nonempty (IsInitial X) :=
  ⟨fun ⟨⟨f, p, q⟩, d⟩ ↦ .intro <| isColimitEquivIsInitialOfIsEmpty _ _ q, fun ⟨h⟩ ↦
    ⟨⟨(Functor.const _).obj X, 𝟙 _, (isColimitEquivIsInitialOfIsEmpty _ _).symm h⟩, by simp⟩⟩

end ObjectProperty

end CategoryTheory

