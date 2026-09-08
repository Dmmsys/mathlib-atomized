/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.Presentable.Basic

/-!
# Finitely Presentable Objects

We define finitely presentable objects as a synonym for `ℵ₀`-presentable objects,
and link this definition with the preservation of filtered colimits.

-/

@[expose] public section


universe w v' v u' u

namespace CategoryTheory

open Limits Opposite Cardinal

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

attribute [local instance] fact_isRegular_aleph0

/-- A functor `F : C ⥤ D` is finitely accessible if it is `ℵ₀`-accessible.
Equivalently, it preserves all filtered colimits.
See `CategoryTheory.Functor.IsFinitelyAccessible_iff_preservesFilteredColimits`. -/
/-
**CategoryTheory.Functor.IsFinitelyAccessible** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u'} → [inst_1 : CategoryTheory.Category.{v', u'} D] → CategoryTheory.Functor C 
D → Prop
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.fact_isRegular_aleph0`：fact_isRegular_aleph0 : Fact (IsRegular 
ℵ₀) where out

--- 原说明 ---
A functor `F : C ⥤ D` is finitely accessible if it is `ℵ₀`-accessible.
Equivalently, it preserves all filtered colimits.
See `CategoryTheory.Functor.IsFinitelyAccessible_iff_preservesFilteredColimits`.
-/
abbrev Functor.IsFinitelyAccessible (F : C ⥤ D) : Prop := IsCardinalAccessible.{w} F ℵ₀
/-
**CategoryTheory.Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSiz
e** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   {F : CategoryTheory.Functor C D},  
 F.IsFinitelyAccessible ↔ CategoryTheory.Limits.PreservesFilteredColimitsOfSize.
{w, w, v, v', u, u'} F
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.fact_isRegular_aleph0`：fact_isRegular_aleph0 : Fact (IsRegular 
ℵ₀) where out
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize {F : C ⥤ D} :
    IsFinitelyAccessible.{w} F ↔ PreservesFilteredColimitsOfSize.{w, w} F := by
  refine ⟨fun ⟨H⟩ ↦ ⟨?_⟩, fun ⟨H⟩ ↦ ⟨?_⟩⟩ <;>
    simp only [isCardinalFiltered_aleph0_iff] at * <;>
    exact H
/-
**CategoryTheory.Functor.isFinitelyAccessible_iff_preservesFilteredColimits** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   {F : CategoryTheory.Functor C D}, F
.IsFinitelyAccessible ↔ CategoryTheory.Limits.PreservesFilteredColimits F
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsFinitelyAccessible_iff_preservesFilteredColimit
sOfSize`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} 
[inst_1 : CategoryTheory.Category.{v', u'} D]   {F : CategoryTheory.F…
-/
lemma Functor.isFinitelyAccessible_iff_preservesFilteredColimits {F : C ⥤ D} :
    IsFinitelyAccessible.{v'} F ↔ PreservesFilteredColimits F :=
  IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize

/-- An object `X` is finitely presentable if `Hom(X, -)` preserves all filtered colimits. -/
/-
**CategoryTheory.IsFinitelyPresentable** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry`。
形式化陈述：IsFinitelyPresentable (X : C) : Prop
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.fact_isRegular_aleph0`：fact_isRegular_aleph0 : Fact (IsRegular 
ℵ₀) where out

--- 原说明 ---
An object `X` is finitely presentable if `Hom(X, -)` preserves all filtered coli
mits.
-/
abbrev IsFinitelyPresentable (X : C) : Prop :=
  IsCardinalPresentable.{w} X ℵ₀

variable (C) in
/-- `IsFinitelyPresentable` as an `ObjectProperty` on `C`. This is sometimes called "compact". -/
/-
**CategoryTheory.ObjectProperty.isFinitelyPresentable** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.ObjectProperty`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
ObjectProperty C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsFinitelyPresentable` as an `ObjectProperty` on `C`. This is sometimes called 
"compact".
-/
def ObjectProperty.isFinitelyPresentable : ObjectProperty C := fun X ↦ IsFinitelyPresentable.{w} X
/-
**CategoryTheory.ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable**
 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C],   CategoryTheory
.ObjectProperty.isFinitelyPresentable C = CategoryTheory.isCardinalPresentable C
 Cardinal.aleph0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable :
    isFinitelyPresentable.{w} C = isCardinalPresentable.{w} C ℵ₀ :=
  rfl

variable (C) in
/-- A morphism `f : X ⟶ Y` is finitely presentable if it is so as an object of `Under X`. -/
/-
**CategoryTheory.MorphismProperty.isFinitelyPresentable** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.MorphismProperty`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
MorphismProperty C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `f : X ⟶ Y` is finitely presentable if it is so as an object of `Unde
r X`.
-/
def MorphismProperty.isFinitelyPresentable : MorphismProperty C :=
  fun _ _ f ↦ ObjectProperty.isFinitelyPresentable.{w} _ (CategoryTheory.Under.mk f)
/-
**CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimitsOfSize** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：isFinitelyPresentable_iff_preservesFilteredColimitsOfSize {X : C} : IsFini
telyPresentable.{w} X ↔ PreservesFilteredColimitsOfSize.{w, w} (coyoneda.obj (op
 X))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsFinitelyAccessible_iff_preservesFilteredColimit
sOfSize`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} 
[inst_1 : CategoryTheory.Category.{v', u'} D]   {F : CategoryTheory.F…
-/
lemma isFinitelyPresentable_iff_preservesFilteredColimitsOfSize {X : C} :
    IsFinitelyPresentable.{w} X ↔ PreservesFilteredColimitsOfSize.{w, w} (coyoneda.obj (op X)) :=
  Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize
/-
**CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimits** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：isFinitelyPresentable_iff_preservesFilteredColimits {X : C} : IsFinitelyPr
esentable.{v} X ↔ PreservesFilteredColimits (coyoneda.obj (op X))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsFinitelyAccessible_iff_preservesFilteredColimit
sOfSize`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} 
[inst_1 : CategoryTheory.Category.{v', u'} D]   {F : CategoryTheory.F…
-/
lemma isFinitelyPresentable_iff_preservesFilteredColimits {X : C} :
    IsFinitelyPresentable.{v} X ↔ PreservesFilteredColimits (coyoneda.obj (op X)) :=
  Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) [IsFinitelyPresentable.{w} X] :
    PreservesFilteredColimitsOfSize.{w, w} (coyoneda.obj (op X)) := by
  rw [← isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
  infer_instance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : (ObjectProperty.isFinitelyPresentable.{w} C).FullSubcategory) :
    IsFinitelyPresentable.{w} ((ObjectProperty.isFinitelyPresentable.{w} C).ι.obj X) :=
  X.property
/-
**CategoryTheory.IsFinitelyPresentable.exists_hom_of_isColimit** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.IsFinitelyPresentable`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} [ins
t_1 : CategoryTheory.SmallCategory J]   [CategoryTheory.IsFiltered J] {D : Categ
oryTheory.Functor J C} {c : CategoryTheory.Limits.Cocone D}   (hc : CategoryTheo
ry.Limits.IsColimit c) {X : C} [CategoryTheory.IsFinitelyPresentable X] (f : X ⟶
 c.pt),   ∃ j p, CategoryTheory.CategoryStruct.comp p (c.ι.app j) = f
参数：hc : CategoryTheory.Limits.IsColimit c；f : X ⟶ c.pt；c.ι.app j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective_of_isColimit`：jointly_sur
jective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t) (x : t.pt
) : exists j y, t.ι.app j y = x
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.instPreservesFilteredColimitsOfSizeObjOppositeFunctorType
CoyonedaOpOfIsFinitelyPresentable`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C) [CategoryTheory.IsFinitelyPresentable X],   CategoryTheory.L
imits.Preserves…
-/
lemma IsFinitelyPresentable.exists_hom_of_isColimit {J : Type w} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C} [IsFinitelyPresentable.{w} X]
    (f : X ⟶ c.pt) :
    ∃ (j : J) (p : X ⟶ D.obj j), p ≫ c.ι.app j = f :=
  Types.jointly_surjective_of_isColimit (isColimitOfPreserves (coyoneda.obj (op X)) hc) f
/-
**CategoryTheory.IsFinitelyPresentable.exists_eq_of_isColimit** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.IsFinitelyPresentable`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} [ins
t_1 : CategoryTheory.SmallCategory J]   [CategoryTheory.IsFiltered J] {D : Categ
oryTheory.Functor J C} {c : CategoryTheory.Limits.Cocone D}   (hc : CategoryTheo
ry.Limits.IsColimit c) {X : C} [CategoryTheory.IsFinitelyPresentable X] {i j : J
} (f : X ⟶ D.obj i)   (g : X ⟶ D.obj j),   CategoryTheory.CategoryStruct.comp f 
(c.ι.app i) = CategoryTheory.CategoryStruct.comp g (c.ι.app j) →     ∃ k u v, Ca
tegoryTheory.CategoryStruct.comp f (D.map u) = CategoryTheory.CategoryStruct.com
p g (D.map v)
参数：hc : CategoryTheory.Limits.IsColimit c；f : X ⟶ D.obj i；g : X ⟶ D.obj j；c.ι.ap
p i；c.ι.app j；D.map u；D.map v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff`：isColimit_
eq_iff {t : Cocone F} (ht : IsColimit t) {i j : J} {xi : F.obj i} {xj : F.obj j}
 : t.ι.app i xi = t.ι.app j xj ↔ exists (k : _) (f…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.instPreservesFilteredColimitsOfSizeObjOppositeFunctorType
CoyonedaOpOfIsFinitelyPresentable`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C) [CategoryTheory.IsFinitelyPresentable X],   CategoryTheory.L
imits.Preserves…
-/
lemma IsFinitelyPresentable.exists_eq_of_isColimit {J : Type w} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C} [IsFinitelyPresentable.{w} X]
    {i j : J} (f : X ⟶ D.obj i) (g : X ⟶ D.obj j) (h : f ≫ c.ι.app i = g ≫ c.ι.app j) :
    ∃ (k : J) (u : i ⟶ k) (v : j ⟶ k), f ≫ D.map u = g ≫ D.map v :=
  (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (coyoneda.obj (op X)) hc)).mp h
/-
**CategoryTheory.IsFinitelyPresentable.exists_hom_of_isColimit_under** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.IsFinitelyPresentable`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} [ins
t_1 : CategoryTheory.SmallCategory J]   [CategoryTheory.IsFiltered J] {D : Categ
oryTheory.Functor J C} {c : CategoryTheory.Limits.Cocone D}   (hc : CategoryTheo
ry.Limits.IsColimit c) {X A : C} (p : X ⟶ A) (s : (CategoryTheory.Functor.const 
J).obj X ⟶ D)   [CategoryTheory.IsFinitelyPresentable (CategoryTheory.Under.mk p
)] (f : A ⟶ c.pt),   (∀ (j : J), CategoryTheory.CategoryStruct.comp (s.app j) (c
.ι.app j) = CategoryTheory.CategoryStruct.comp p f) →     ∃ j q, CategoryTheory.
CategoryStruct.comp p q = s.app j ∧ CategoryTheory.CategoryStruct.comp q (c.ι.ap
p j) = f
参数：hc : CategoryTheory.Limits.IsColimit c；p : X ⟶ A；s : (CategoryTheory.Functor.
const J).obj X ⟶ D；CategoryTheory.Under.mk p；f : A ⟶ c.pt；∀ (j : J), CategoryThe
ory.CategoryStruct.comp (s.app j) (c.ι.app j) = CategoryTheory.CategoryStruct.co
mp p f；c.ι.app j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFiltered.nonempty`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.IsFiltered C], Nonempty C
· 使用定理 `CategoryTheory.IsFinitelyPresentable.exists_hom_of_isColimit`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : CategoryTh
eory.SmallCategory J]   [CategoryTheory.IsFiltered…
· 使用定理 `CategoryTheory.Under.w`：w : f.hom ≫ φ.right = g.hom
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma IsFinitelyPresentable.exists_hom_of_isColimit_under
    {J : Type w} [SmallCategory J] [IsFiltered J] {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c)
    {X A : C} (p : X ⟶ A) (s : (Functor.const J).obj X ⟶ D)
    [IsFinitelyPresentable.{w} (Under.mk p)]
    (f : A ⟶ c.pt) (h : ∀ (j : J), s.app j ≫ c.ι.app j = p ≫ f) :
    ∃ (j : J) (q : A ⟶ D.obj j), p ≫ q = s.app j ∧ q ≫ c.ι.app j = f := by
  have : Nonempty J := IsFiltered.nonempty
  let hc' := Under.isColimitLiftCocone D s c (p ≫ f) h hc
  obtain ⟨j, q, hq⟩ := exists_hom_of_isColimit (X := Under.mk p) hc' (Under.homMk f rfl)
  use j, q.right, Under.w q, congr($(hq).right)
/-
**CategoryTheory.HasCardinalFilteredColimits_iff_hasFilteredColimitsOfSize** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：HasCardinalFilteredColimits_iff_hasFilteredColimitsOfSize : HasCardinalFil
teredColimits.{w} C ℵ₀ ↔ HasFilteredColimitsOfSize.{w, w} C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.fact_isRegular_aleph0`：fact_isRegular_aleph0 : Fact (IsRegular 
ℵ₀) where out
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma HasCardinalFilteredColimits_iff_hasFilteredColimitsOfSize :
    HasCardinalFilteredColimits.{w} C ℵ₀ ↔ HasFilteredColimitsOfSize.{w, w} C := by
  refine ⟨fun ⟨H⟩ ↦ ⟨?_⟩, fun ⟨H⟩ ↦ ⟨?_⟩⟩ <;>
    simp only [isCardinalFiltered_aleph0_iff] at * <;>
    exact H
/-
**CategoryTheory.HasCardinalFilteredColimits_iff_hasFilteredColimits** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：HasCardinalFilteredColimits_iff_hasFilteredColimits : HasCardinalFilteredC
olimits.{v} C ℵ₀ ↔ HasFilteredColimits C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.HasCardinalFilteredColimits_iff_hasFilteredColimitsOfSize
`：HasCardinalFilteredColimits_iff_hasFilteredColimitsOfSize : HasCardinalFiltere
dColimits.{w} C ℵ₀ ↔ HasFilteredColimitsOfSize.{w, w} C
-/
lemma HasCardinalFilteredColimits_iff_hasFilteredColimits :
    HasCardinalFilteredColimits.{v} C ℵ₀ ↔ HasFilteredColimits C :=
  HasCardinalFilteredColimits_iff_hasFilteredColimitsOfSize

end CategoryTheory

