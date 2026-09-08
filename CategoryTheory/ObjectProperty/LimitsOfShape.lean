/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Limits.Presentation

import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Objects that are limits of objects satisfying a certain property

Given a property of objects `P : ObjectProperty C` and a category `J`,
we introduce two properties of objects `P.strictLimitsOfShape J`
and `P.limitsOfShape J`. The former contains exactly the objects
of the form `limit F` for any functor `F : J ⥤ C` that has
a limit and such that `F.obj j` satisfies `P` for any `j`, while
the latter contains all the objects that are isomorphic to
these "chosen" objects `limit F`.

Under certain circumstances, the type of objects satisfying
`P.strictLimitsOfShape J` is small: the main reason this variant is
introduced is to deduce that the full subcategory of `P.limitsOfShape J`
is essentially small.

By requiring `P.limitsOfShape J ≤ P`, we introduce a typeclass
`P.IsClosedUnderLimitsOfShape J`.


## TODO

* formalize the closure of `P` under finite limits (which require
  iterating over `ℕ`), and more generally the closure under limits
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

/-- The property of objects that are *equal* to `limit F` for some
functor `F : J ⥤ C` where all `F.obj j` satisfy `P`. -/
/-
**CategoryTheory.ObjectProperty.strictLimitsOfShape** 是 Mathlib 中的一个归纳类型，位于命名空间 
`CategoryTheory.ObjectProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     Cat
egoryTheory.ObjectProperty C →       (J : Type u') → [CategoryTheory.Category.{v
', u'} J] → CategoryTheory.ObjectProperty C
参数：J : Type u'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects that are *equal* to `limit F` for some
functor `F : J ⥤ C` where all `F.obj j` satisfy `P`.
-/
inductive strictLimitsOfShape : ObjectProperty C
  | limit (F : J ⥤ C) [HasLimit F] (hF : ∀ j, P (F.obj j)) :
    strictLimitsOfShape (limit F)

variable {P} in
/-
**CategoryTheory.ObjectProperty.strictLimitsOfShape_monotone** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：strictLimitsOfShape_monotone {Q : ObjectProperty C} (h : P <= Q) : P.stric
tLimitsOfShape J <= Q.strictLimitsOfShape J
参数：h : P <= Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma strictLimitsOfShape_monotone {Q : ObjectProperty C} (h : P ≤ Q) :
    P.strictLimitsOfShape J ≤ Q.strictLimitsOfShape J := by
  rintro _ ⟨F, hF⟩
  exact ⟨F, fun j ↦ h _ (hF j)⟩

@[simp]
/-
**CategoryTheory.ObjectProperty.strictLimitsOfShape_bot** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：strictLimitsOfShape_bot [Nonempty J] : strictLimitsOfShape (⊥ : ObjectProp
erty C) J = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma strictLimitsOfShape_bot [Nonempty J] :
    strictLimitsOfShape (⊥ : ObjectProperty C) J = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨_, h⟩
  exact h (Classical.arbitrary J)

/-- A structure expressing that `X : C` is the limit of a functor
`diag : J ⥤ C` such that `P (diag.obj j)` holds for all `j`. -/
/-
**CategoryTheory.ObjectProperty.LimitOfShape** 是 Mathlib 中的一个归纳类型，位于命名空间 `Catego
ryTheory.ObjectProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     Cat
egoryTheory.ObjectProperty C →       (J : Type u') → [CategoryTheory.Category.{v
', u'} J] → C → Type (max (max (max u' u_1) v') v_1)
参数：J : Type u'；max (max (max u' u_1) v') v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure expressing that `X : C` is the limit of a functor
`diag : J ⥤ C` such that `P (diag.obj j)` holds for all `j`.
-/
structure LimitOfShape (X : C) extends LimitPresentation J X where
  prop_diag_obj (j : J) : P (diag.obj j)

namespace LimitOfShape

variable {P J}

/-- If `F : J ⥤ C` is a functor that has a limit and is such that for all `j`,
`F.obj j` satisfies a property `P`, then this structure expresses that `limit F`
is indeed a limit of objects satisfying `P`. -/
/-
**CategoryTheory.ObjectProperty.LimitOfShape.limit** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ObjectProperty.LimitOfShape`。
形式化陈述：limit (F : J ⥤ C) [HasLimit F] (hF : forall j, P (F.obj j)) : P.LimitOfSha
pe J (limit F) where toLimitPresentation
参数：F : J ⥤ C；hF : forall j, P (F.obj j)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : J ⥤ C` is a functor that has a limit and is such that for all `j`,
`F.obj j` satisfies a property `P`, then this structure expresses that `limit F`
is indeed a limit of objects satisfying `P`.
-/
noncomputable def limit (F : J ⥤ C) [HasLimit F] (hF : ∀ j, P (F.obj j)) :
    P.LimitOfShape J (limit F) where
  toLimitPresentation := .limit F
  prop_diag_obj := hF

/-- If `X` is a limit indexed by `J` of objects satisfying a property `P`, then
any object that is isomorphic to `X` also is. -/
@[simps toLimitPresentation]
/-
**CategoryTheory.ObjectProperty.LimitOfShape.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ObjectProperty.LimitOfShape`。
形式化陈述：ofIso {X : C} (h : P.LimitOfShape J X) {Y : C} (e : X ≅ Y) : P.LimitOfShap
e J Y where toLimitPresentation
参数：h : P.LimitOfShape J X；e : X ≅ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.LimitOfShape.prop_diag_obj`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPrope
rty C} {J : Type u'}   [inst_1 : CategoryTheor…

--- 原说明 ---
If `X` is a limit indexed by `J` of objects satisfying a property `P`, then
any object that is isomorphic to `X` also is.
-/
def ofIso {X : C} (h : P.LimitOfShape J X) {Y : C} (e : X ≅ Y) :
    P.LimitOfShape J Y where
  toLimitPresentation := .ofIso h.toLimitPresentation e
  prop_diag_obj := h.prop_diag_obj

/-- If `X` is a limit indexed by `J` of objects satisfying a property `P`,
it is also a limit indexed by `J` of objects satisfying `Q` if `P ≤ Q`. -/
@[simps toLimitPresentation]
/-
**CategoryTheory.ObjectProperty.LimitOfShape.ofLE** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.ObjectProperty.LimitOfShape`。
形式化陈述：ofLE {X : C} (h : P.LimitOfShape J X) {Q : ObjectProperty C} (hPQ : P <= Q
) : Q.LimitOfShape J X where toLimitPresentation
参数：h : P.LimitOfShape J X；hPQ : P <= Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is a limit indexed by `J` of objects satisfying a property `P`,
it is also a limit indexed by `J` of objects satisfying `Q` if `P ≤ Q`.
-/
def ofLE {X : C} (h : P.LimitOfShape J X) {Q : ObjectProperty C} (hPQ : P ≤ Q) :
    Q.LimitOfShape J X where
  toLimitPresentation := h.toLimitPresentation
  prop_diag_obj j := hPQ _ (h.prop_diag_obj j)

/-- Change the index category for `ObjectProperty.LimitOfShape`. -/
@[simps toLimitPresentation]
/-
**CategoryTheory.ObjectProperty.LimitOfShape.reindex** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ObjectProperty.LimitOfShape`。
形式化陈述：reindex {X : C} (h : P.LimitOfShape J X) (G : J' ⥤ J) [G.Initial] : P.Limi
tOfShape J' X where toLimitPresentation
参数：h : P.LimitOfShape J X；G : J' ⥤ J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Change the index category for `ObjectProperty.LimitOfShape`.
-/
noncomputable def reindex {X : C} (h : P.LimitOfShape J X) (G : J' ⥤ J) [G.Initial] :
    P.LimitOfShape J' X where
  toLimitPresentation := h.toLimitPresentation.reindex G
  prop_diag_obj _ := h.prop_diag_obj _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given `P : ObjectProperty C`, and a presentation `P.LimitOfShape J X`
of an object `X : C`, this is the induced functor `J ⥤ StructuredArrow P.ι X`. -/
@[simps]
/-
**CategoryTheory.ObjectProperty.LimitOfShape.toStructuredArrow** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.ObjectProperty.LimitOfShape`。
形式化陈述：toStructuredArrow {X : C} (p : P.LimitOfShape J X) : J ⥤ StructuredArrow X
 P.ι where obj j
参数：p : P.LimitOfShape J X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.LimitOfShape.prop_diag_obj`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPrope
rty C} {J : Type u'}   [inst_1 : CategoryTheor…

--- 原说明 ---
Given `P : ObjectProperty C`, and a presentation `P.LimitOfShape J X`
of an object `X : C`, this is the induced functor `J ⥤ StructuredArrow P.ι X`.
-/
def toStructuredArrow
    {X : C} (p : P.LimitOfShape J X) :
    J ⥤ StructuredArrow X P.ι where
  obj j := StructuredArrow.mk (Y := ⟨_, p.prop_diag_obj j⟩) (by exact p.π.app j)
  map f := StructuredArrow.homMk (ObjectProperty.homMk (by exact p.diag.map f))
    (by simpa using (p.π.naturality f).symm)

end LimitOfShape

/-- The property of objects that are the point of a limit cone for a
functor `F : J ⥤ C` where all objects `F.obj j` satisfy `P`. -/
/-
**CategoryTheory.ObjectProperty.limitsOfShape** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ObjectProperty`。
形式化陈述：limitsOfShape : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects that are the point of a limit cone for a
functor `F : J ⥤ C` where all objects `F.obj j` satisfy `P`.
-/
def limitsOfShape : ObjectProperty C :=
  fun X ↦ Nonempty (P.LimitOfShape J X)

variable {P J} in
/-
**CategoryTheory.ObjectProperty.LimitOfShape.limitsOfShape** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.ObjectProperty.LimitOfShape`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : Catego
ryTheory.ObjectProperty C} {J : Type u'}   [inst_1 : CategoryTheory.Category.{v'
, u'} J] {X : C} (h : P.LimitOfShape J X), P.limitsOfShape J X
参数：h : P.LimitOfShape J X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LimitOfShape.limitsOfShape {X : C} (h : P.LimitOfShape J X) :
    P.limitsOfShape J X :=
  ⟨h⟩
/-
**CategoryTheory.ObjectProperty.strictLimitsOfShape_le_limitsOfShape** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：strictLimitsOfShape_le_limitsOfShape : P.strictLimitsOfShape J <= P.limits
OfShape J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma strictLimitsOfShape_le_limitsOfShape :
    P.strictLimitsOfShape J ≤ P.limitsOfShape J := by
  rintro X ⟨F, hF⟩
  exact ⟨.limit F hF⟩

@[simp]
/-
**CategoryTheory.ObjectProperty.limitsOfShape_bot** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：limitsOfShape_bot [Nonempty J] : limitsOfShape (⊥ : ObjectProperty C) J = 
⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
-/
lemma limitsOfShape_bot [Nonempty J] : limitsOfShape (⊥ : ObjectProperty C) J = ⊥ := by
  rw [eq_bot_iff]
  rintro X ⟨⟨_, h⟩⟩
  exact h (Classical.arbitrary J)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (P.limitsOfShape J).IsClosedUnderIsomorphisms where
  of_iso := by rintro _ _ e ⟨h⟩; exact ⟨h.ofIso e⟩

@[simp]
/-
**CategoryTheory.ObjectProperty.isoClosure_strictLimitsOfShape** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isoClosure_strictLimitsOfShape : (P.strictLimitsOfShape J).isoClosure = P.
limitsOfShape J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isoClosure_le_iff`：isoClosure_le_iff [IsCl
osedUnderIsomorphisms Q] : isoClosure P <= Q ↔ P <= Q
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsLimitsOfShape
`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTh
eory.ObjectProperty C) (J : Type u')   [inst_1 : CategoryTheor…
· 使用引理 `CategoryTheory.ObjectProperty.strictLimitsOfShape_le_limitsOfShape`：stri
ctLimitsOfShape_le_limitsOfShape : P.strictLimitsOfShape J <= P.limitsOfShape J
· 使用引理 `CategoryTheory.Limits.LimitPresentation.hasLimit`：hasLimit (pres : Limit
Presentation J X) : HasLimit pres.diag
· 使用定理 `CategoryTheory.ObjectProperty.LimitOfShape.prop_diag_obj`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPrope
rty C} {J : Type u'}   [inst_1 : CategoryTheor…
-/
lemma isoClosure_strictLimitsOfShape :
    (P.strictLimitsOfShape J).isoClosure = P.limitsOfShape J := by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    apply strictLimitsOfShape_le_limitsOfShape
  · intro X ⟨h⟩
    have := h.hasLimit
    exact ⟨limit h.diag, strictLimitsOfShape.limit h.diag h.prop_diag_obj,
      ⟨h.isLimit.conePointUniqueUpToIso (limit.isLimit _)⟩⟩

variable {P} in
/-
**CategoryTheory.ObjectProperty.limitsOfShape_monotone** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ObjectProperty`。
形式化陈述：limitsOfShape_monotone {Q : ObjectProperty C} (hPQ : P <= Q) : P.limitsOfS
hape J <= Q.limitsOfShape J
参数：hPQ : P <= Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma limitsOfShape_monotone {Q : ObjectProperty C} (hPQ : P ≤ Q) :
    P.limitsOfShape J ≤ Q.limitsOfShape J := by
  intro X ⟨h⟩
  exact ⟨h.ofLE hPQ⟩

@[simp]
/-
**CategoryTheory.ObjectProperty.limitsOfShape_isoClosure** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.ObjectProperty`。
形式化陈述：limitsOfShape_isoClosure : P.isoClosure.limitsOfShape J = P.limitsOfShape 
J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `CategoryTheory.ObjectProperty.LimitOfShape.prop_diag_obj`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPrope
rty C} {J : Type u'}   [inst_1 : CategoryTheor…
· 使用引理 `CategoryTheory.ObjectProperty.limitsOfShape_monotone`：limitsOfShape_mono
tone {Q : ObjectProperty C} (hPQ : P <= Q) : P.limitsOfShape J <= Q.limitsOfShap
e J
· 使用引理 `CategoryTheory.ObjectProperty.le_isoClosure`：le_isoClosure : P <= isoClo
sure P
-/
lemma limitsOfShape_isoClosure :
    P.isoClosure.limitsOfShape J = P.limitsOfShape J := by
  refine le_antisymm ?_ (limitsOfShape_monotone _ P.le_isoClosure)
  intro X ⟨h⟩
  choose obj h₁ h₂ using h.prop_diag_obj
  exact
   ⟨{ toLimitPresentation := h.changeDiag (h.diag.isoCopyObj obj (fun j ↦ (h₂ j).some)).symm
      prop_diag_obj := h₁ }⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ObjectProperty.Small.{w} P] [LocallySmall.{w} C] [Small.{w} J] [LocallySmall.{w} J] :
    ObjectProperty.Small.{w} (P.strictLimitsOfShape J) := by
  refine small_of_surjective
    (f := fun (F : { F : J ⥤ P.FullSubcategory // HasLimit (F ⋙ P.ι) }) ↦
      (⟨_, letI := F.2; ⟨F.1 ⋙ P.ι, fun j ↦ (F.1.obj j).2⟩⟩)) ?_
  rintro ⟨_, ⟨F, hF⟩⟩
  exact ⟨⟨P.lift F hF, by assumption⟩, rfl⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ObjectProperty.Small.{w} P] [LocallySmall.{w} C] [Small.{w} J] [LocallySmall.{w} J] :
    ObjectProperty.EssentiallySmall.{w} (P.limitsOfShape J) := by
  rw [← isoClosure_strictLimitsOfShape]
  infer_instance

/-- A property of objects satisfies `P.IsClosedUnderLimitsOfShape J` if it
is stable by limits of shape `J`. -/
@[mk_iff]
/-
**CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape** 是 Mathlib 中的一个归纳类型，
位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     Cat
egoryTheory.ObjectProperty C → (J : Type u') → [CategoryTheory.Category.{v', u'}
 J] → Prop
参数：J : Type u'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property of objects satisfies `P.IsClosedUnderLimitsOfShape J` if it
is stable by limits of shape `J`.
-/
class IsClosedUnderLimitsOfShape (P : ObjectProperty C) (J : Type u') [Category.{v'} J] where
  limitsOfShape_le (P J) : P.limitsOfShape J ≤ P

variable {P J} in
/-
**CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape.mk'** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : Catego
ryTheory.ObjectProperty C} {J : Type u'}   [inst_1 : CategoryTheory.Category.{v'
, u'} J] [P.IsClosedUnderIsomorphisms],   P.strictLimitsOfShape J ≤ P → P.IsClos
edUnderLimitsOfShape J
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.isoClosure_eq_self`：isoClosure_eq_self [Is
ClosedUnderIsomorphisms P] : isoClosure P = P
· 使用引理 `CategoryTheory.ObjectProperty.isoClosure_strictLimitsOfShape`：isoClosure
_strictLimitsOfShape : (P.strictLimitsOfShape J).isoClosure = P.limitsOfShape J
· 使用引理 `CategoryTheory.ObjectProperty.monotone_isoClosure`：monotone_isoClosure (
h : P <= Q) : isoClosure P <= isoClosure Q
-/
lemma IsClosedUnderLimitsOfShape.mk' [P.IsClosedUnderIsomorphisms]
    (h : P.strictLimitsOfShape J ≤ P) :
    P.IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    conv_rhs => rw [← P.isoClosure_eq_self]
    rw [← isoClosure_strictLimitsOfShape]
    exact monotone_isoClosure h
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty J] : IsClosedUnderLimitsOfShape (⊥ : ObjectProperty C) J where
  limitsOfShape_le := by rw [limitsOfShape_bot]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsClosedUnderLimitsOfShape (⊤ : ObjectProperty C) J where
  limitsOfShape_le _ _ := by trivial

export IsClosedUnderLimitsOfShape (limitsOfShape_le)

section

variable {J} [P.IsClosedUnderLimitsOfShape J]

variable {P} in
/-
**CategoryTheory.ObjectProperty.LimitOfShape.prop** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.ObjectProperty.LimitOfShape`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : Catego
ryTheory.ObjectProperty C} {J : Type u'}   [inst_1 : CategoryTheory.Category.{v'
, u'} J] [P.IsClosedUnderLimitsOfShape J] {X : C} (h : P.LimitOfShape J X), P X
参数：h : P.LimitOfShape J X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape.limitsOfShape_l
e`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} (P : CategoryT
heory.ObjectProperty C) (J : Type u')   {inst_1 : CategoryTheor…
-/
lemma LimitOfShape.prop {X : C} (h : P.LimitOfShape J X) : P X :=
  P.limitsOfShape_le J _ ⟨h⟩
/-
**CategoryTheory.ObjectProperty.prop_of_isLimit** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ObjectProperty`。
形式化陈述：prop_of_isLimit {F : J ⥤ C} {c : Cone F} (hc : IsLimit c) (hF : forall (j 
: J), P (F.obj j)) : P c.pt
参数：hc : IsLimit c；hF : forall (j : J), P (F.obj j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape.limitsOfShape_l
e`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} (P : CategoryT
heory.ObjectProperty C) (J : Type u')   {inst_1 : CategoryTheor…
-/
lemma prop_of_isLimit {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
    (hF : ∀ (j : J), P (F.obj j)) : P c.pt :=
  P.limitsOfShape_le J _ ⟨{ diag := _, π := _, isLimit := hc, prop_diag_obj := hF }⟩
/-
**CategoryTheory.ObjectProperty.prop_limit** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.ObjectProperty`。
形式化陈述：prop_limit (F : J ⥤ C) [HasLimit F] (hF : forall (j : J), P (F.obj j)) : P
 (limit F)
参数：F : J ⥤ C；hF : forall (j : J), P (F.obj j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isLimit`：prop_of_isLimit {F : J ⥤ 
C} {c : Cone F} (hc : IsLimit c) (hF : forall (j : J), P (F.obj j)) : P c.pt
-/
lemma prop_limit (F : J ⥤ C) [HasLimit F] (hF : ∀ (j : J), P (F.obj j)) :
    P (limit F) :=
  P.prop_of_isLimit (limit.isLimit F) hF

end

/-
**CategoryTheory.ObjectProperty.prop_pi** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.ObjectProperty`。
形式化陈述：prop_pi {J : Type*} [P.IsClosedUnderLimitsOfShape (Discrete J)] (X : J -> 
C) [HasProduct X] (hF : forall (j : J), P (X j)) : P (∏ᶜ X)
参数：Discrete J；X : J -> C；hF : forall (j : J), P (X j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isLimit`：prop_of_isLimit {F : J ⥤ 
C} {c : Cone F} (hc : IsLimit c) (hF : forall (j : J), P (F.obj j)) : P c.pt
-/
lemma prop_pi {J : Type*} [P.IsClosedUnderLimitsOfShape (Discrete J)] (X : J → C)
    [HasProduct X] (hF : ∀ (j : J), P (X j)) :
    P (∏ᶜ X) :=
  P.prop_of_isLimit (productIsProduct X) (fun _ ↦ hF _)

variable {J} in
/-
**CategoryTheory.ObjectProperty.limitsOfShape_le_of_initial** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：limitsOfShape_le_of_initial (G : J ⥤ J') [G.Initial] : P.limitsOfShape J' 
<= P.limitsOfShape J
参数：G : J ⥤ J'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma limitsOfShape_le_of_initial (G : J ⥤ J') [G.Initial] :
    P.limitsOfShape J' ≤ P.limitsOfShape J :=
  fun _h ⟨h⟩ ↦ ⟨h.reindex G⟩

variable {J} in
/-
**CategoryTheory.ObjectProperty.limitsOfShape_congr** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：limitsOfShape_congr (e : J ≌ J') : P.limitsOfShape J = P.limitsOfShape J'
参数：e : J ≌ J'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.ObjectProperty.limitsOfShape_le_of_initial`：limitsOfShape
_le_of_initial (G : J ⥤ J') [G.Initial] : P.limitsOfShape J' <= P.limitsOfShape 
J
· 使用定理 `CategoryTheory.Functor.initial_of_isLeftAdjoint`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   (F : CategoryTheor…
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
lemma limitsOfShape_congr (e : J ≌ J') :
    P.limitsOfShape J = P.limitsOfShape J' :=
  le_antisymm (P.limitsOfShape_le_of_initial e.inverse)
    (P.limitsOfShape_le_of_initial e.functor)

variable {J} in
/-
**CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_iff_of_equivalence** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isClosedUnderLimitsOfShape_iff_of_equivalence (e : J ≌ J') : P.IsClosedUnd
erLimitsOfShape J ↔ P.IsClosedUnderLimitsOfShape J'
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
· 使用引理 `CategoryTheory.ObjectProperty.limitsOfShape_congr`：limitsOfShape_congr (
e : J ≌ J') : P.limitsOfShape J = P.limitsOfShape J'
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isClosedUnderLimitsOfShape_iff_of_equivalence (e : J ≌ J') :
    P.IsClosedUnderLimitsOfShape J ↔
      P.IsClosedUnderLimitsOfShape J' := by
  simp only [isClosedUnderLimitsOfShape_iff, P.limitsOfShape_congr e]

variable {P J} in
/-
**CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape.of_equivalence** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : Catego
ryTheory.ObjectProperty C} {J : Type u'}   [inst_1 : CategoryTheory.Category.{v'
, u'} J] {J' : Type u''} [inst_2 : CategoryTheory.Category.{v'', u''} J']   (e :
 J ≌ J') [P.IsClosedUnderLimitsOfShape J], P.IsClosedUnderLimitsOfShape J'
参数：e : J ≌ J'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_iff_of_equivale
nce`：isClosedUnderLimitsOfShape_iff_of_equivalence (e : J ≌ J') : P.IsClosedUnde
rLimitsOfShape J ↔ P.IsClosedUnderLimitsOfShape J'
-/
lemma IsClosedUnderLimitsOfShape.of_equivalence (e : J ≌ J')
    [P.IsClosedUnderLimitsOfShape J] :
    P.IsClosedUnderLimitsOfShape J' := by
  rwa [← P.isClosedUnderLimitsOfShape_iff_of_equivalence e]
/-
**CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape.inverseImage** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (J : Type u') [inst_2 : Ca
tegoryTheory.Category.{v', u'} J]   (P : CategoryTheory.ObjectProperty D) (F : C
ategoryTheory.Functor C D) [P.IsClosedUnderLimitsOfShape J]   [CategoryTheory.Li
mits.PreservesLimitsOfShape J F], (P.inverseImage F).IsClosedUnderLimitsOfShape 
J
参数：J : Type u'；P : CategoryTheory.ObjectProperty D；F : CategoryTheory.Functor C 
D；P.inverseImage F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.LimitOfShape.prop`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectProperty C} {J
 : Type u'}   [inst_1 : CategoryTheor…
-/
instance IsClosedUnderLimitsOfShape.inverseImage
    (P : ObjectProperty D) (F : C ⥤ D) [P.IsClosedUnderLimitsOfShape J]
    [PreservesLimitsOfShape J F] : (P.inverseImage F).IsClosedUnderLimitsOfShape J :=
  ⟨fun _ ⟨c, H⟩ ↦ ObjectProperty.LimitOfShape.prop (P := P) ⟨c.map F, H⟩⟩
/-
**CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_inverseImage_iff** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isClosedUnderLimitsOfShape_inverseImage_iff (P : ObjectProperty D) [P.IsCl
osedUnderIsomorphisms] (e : C ≌ D) : (P.inverseImage e.functor).IsClosedUnderLim
itsOfShape J ↔ P.IsClosedUnderLimitsOfShape J
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
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape.inverseImage`：∀
 {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [
inst_1 : CategoryTheory.Category.{v_2, u_2} D] (J : Type u'…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
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
lemma isClosedUnderLimitsOfShape_inverseImage_iff (P : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] (e : C ≌ D) :
    (P.inverseImage e.functor).IsClosedUnderLimitsOfShape J ↔ P.IsClosedUnderLimitsOfShape J := by
  refine ⟨fun H ↦ ?_, fun _ ↦ inferInstance⟩
  convert!
    (inferInstance :
      ((P.inverseImage e.functor).inverseImage e.inverse).IsClosedUnderLimitsOfShape J)
  ext X
  simpa using P.prop_iff_of_iso (e.counitIso.app X).symm

end ObjectProperty

end CategoryTheory

