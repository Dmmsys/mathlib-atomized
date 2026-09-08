/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.HasIterationOfShape
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.PrincipalSeg
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.SuccPred.Limit
public import Mathlib.Order.Interval.Set.InitialSeg

/-! # Transfinite iterations of a successor structure

In this file, we introduce the structure `SuccStruct` on a category `C`.
It consists of the data of an object `X₀ : C`, a successor map `succ : C → C`
and a morphism `toSucc : X ⟶ succ X` for any `X : C`. The map `toSucc`
does not have to be natural in `X`. For any element `j : J` in a
well-ordered type `J`, we would like to define
the iteration of `Φ : SuccStruct C`, as a functor `F : J ⥤ C`
such that `F.obj ⊥ = X₀`, `F.obj j ⟶ F.obj (Order.succ j)` is `toSucc (F.obj j)`
when `j` is not maximal, and when `j` is limit, `F.obj j` should be the
colimit of the `F.obj k` for `k < j`.

In the small object argument, we shall apply this to the iteration of
a functor `F : C ⥤ C` equipped with a natural transformation `ε : 𝟭 C ⟶ F`:
this will correspond to the case of
`SuccStruct.ofNatTrans ε : SuccStruct (C ⥤ C)`, for which `X₀ := 𝟭 C`,
`succ G := G ⋙ F` and `toSucc G : G ⟶ G ⋙ F` is given by `whiskerLeft G ε`.

The construction of the iteration of `Φ : SuccStruct C` is done
by transfinite induction, under an assumption `HasIterationOfShape C J`.
However, for a limit element `j : J`, the definition of `F.obj j`
does not involve only the objects `F.obj i` for `i < j`, but it also
involves the maps `F.obj i₁ ⟶ F.obj i₂` for `i₁ ≤ i₂ < j`.
Then, this is not a straightforward application of definitions by
transfinite induction. In order to solve this technical difficulty,
we introduce a structure `Φ.Iteration j` for any `j : J`. This
structure contains all the expected data and properties for
all the indices that are `≤ j`. In this file, we show that
`Φ.Iteration j` is a subsingleton. The existence shall be
obtained in the file `Mathlib/CategoryTheory/SmallObject/Iteration/Nonempty.lean`, and
the construction of the functor `Φ.iterationFunctor J : J ⥤ C`
and of its colimit `Φ.iteration J : C` will be done in the
file `Mathlib/CategoryTheory/SmallObject/TransfiniteIteration.lean`.

The map `Φ.toSucc X : X ⟶ Φ.succ X` does not have to be natural
(and it is not in certain applications). Then, two isomorphic
objects `X` and `Y` may have non-isomorphic successors. This is
the reason why we make an extensive use of equalities in
`C` and in `Arrow C` in the definitions.

## Note

The iteration was first introduced in mathlib by Joël Riou, using
a different approach as the one described above. After refactoring
his code, he found that the approach described above had already
been used in the pioneering formalization work in Lean 3 by
Reid Barton in 2018 towards the model category structure on
topological spaces.

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Category Limits

namespace SmallObject

variable {C : Type u} [Category.{v} C] {J : Type w}

section

variable [PartialOrder J] {j : J} (F : Set.Iic j ⥤ C) {i : J} (hi : i ≤ j)

/-- The functor `Set.Iio i ⥤ C` obtained by "restriction" of `F : Set.Iic j ⥤ C`
when `i ≤ j`. -/
/-
**CategoryTheory.SmallObject.restrictionLT** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.SmallObject`。
形式化陈述：restrictionLT : Set.Iio i ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Set.Iio i ⥤ C` obtained by "restriction" of `F : Set.Iic j ⥤ C`
when `i ≤ j`.
-/
def restrictionLT : Set.Iio i ⥤ C :=
  (Set.principalSegIioIicOfLE hi).monotone.functor ⋙ F


@[simp]
/-
**CategoryTheory.SmallObject.restrictionLT_obj** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.SmallObject`。
形式化陈述：restrictionLT_obj (k : J) (hk : k < i) : (restrictionLT F hi).obj ⟨k, hk⟩ 
= F.obj ⟨k, hk.le.trans hi⟩
参数：k : J；hk : k < i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictionLT_obj (k : J) (hk : k < i) :
    (restrictionLT F hi).obj ⟨k, hk⟩ = F.obj ⟨k, hk.le.trans hi⟩ := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.SmallObject.restrictionLT_map** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.SmallObject`。
形式化陈述：restrictionLT_map {k₁ k₂ : Set.Iio i} (φ : k₁ ⟶ k₂) : (restrictionLT F hi)
.map φ = F.map (homOfLE (by simpa using leOfHom φ))
参数：φ : k₁ ⟶ k₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictionLT_map {k₁ k₂ : Set.Iio i} (φ : k₁ ⟶ k₂) :
    (restrictionLT F hi).map φ = F.map (homOfLE (by simpa using leOfHom φ)) := rfl

/-- Given `F : Set.Iic j ⥤ C`, `i : J` such that `hi : i ≤ j`, this is the
cocone consisting of all maps `F.obj ⟨k, hk⟩ ⟶ F.obj ⟨i, hi⟩` for `k : J` such that `k < i`. -/
@[simps!]
/-
**CategoryTheory.SmallObject.coconeOfLE** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.SmallObject`。
形式化陈述：coconeOfLE : Cocone (restrictionLT F hi)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : Set.Iic j ⥤ C`, `i : J` such that `hi : i ≤ j`, this is the
cocone consisting of all maps `F.obj ⟨k, hk⟩ ⟶ F.obj ⟨i, hi⟩` for `k : J` such t
hat `k < i`.
-/
def coconeOfLE : Cocone (restrictionLT F hi) :=
  (Set.principalSegIioIicOfLE hi).cocone F

/-- The functor `Set.Iic i ⥤ C` obtained by "restriction" of `F : Set.Iic j ⥤ C`
when `i ≤ j`. -/
/-
**CategoryTheory.SmallObject.restrictionLE** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.SmallObject`。
形式化陈述：restrictionLE : Set.Iic i ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Set.Iic i ⥤ C` obtained by "restriction" of `F : Set.Iic j ⥤ C`
when `i ≤ j`.
-/
def restrictionLE : Set.Iic i ⥤ C :=
  (Set.initialSegIicIicOfLE hi).monotone.functor ⋙ F

@[simp]
/-
**CategoryTheory.SmallObject.restrictionLE_obj** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.SmallObject`。
形式化陈述：restrictionLE_obj (k : J) (hk : k <= i) : (restrictionLE F hi).obj ⟨k, hk⟩
 = F.obj ⟨k, hk.trans hi⟩
参数：k : J；hk : k <= i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictionLE_obj (k : J) (hk : k ≤ i) :
    (restrictionLE F hi).obj ⟨k, hk⟩ = F.obj ⟨k, hk.trans hi⟩ := rfl

@[simp]
/-
**CategoryTheory.SmallObject.restrictionLE_map** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.SmallObject`。
形式化陈述：restrictionLE_map {k₁ k₂ : Set.Iic i} (φ : k₁ ⟶ k₂) : (restrictionLE F hi)
.map φ = F.map (homOfLE (by simpa using leOfHom φ))
参数：φ : k₁ ⟶ k₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictionLE_map {k₁ k₂ : Set.Iic i} (φ : k₁ ⟶ k₂) :
    (restrictionLE F hi).map φ = F.map (homOfLE (by simpa using leOfHom φ)) := rfl

end

variable (C) in
/-- A successor structure on a category consists of the
data of an object `succ X` for any `X : C`, a map `toSucc X : X ⟶ succ X`
(which does not need to be natural), and a zeroth object `X₀`.
-/
/-
**CategoryTheory.SmallObject.SuccStruct** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryThe
ory.SmallObject`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A successor structure on a category consists of the
data of an object `succ X` for any `X : C`, a map `toSucc X : X ⟶ succ X`
(which does not need to be natural), and a zeroth object `X₀`.
-/
structure SuccStruct where
  /-- the zeroth object -/
  X₀ : C
  /-- the successor of an object -/
  succ (X : C) : C
  /-- the map to the successor -/
  toSucc (X : C) : X ⟶ succ X

namespace SuccStruct

/-- Given a functor `Φ : C ⥤ C`, a natural transformation of the form `𝟭 C ⟶ Φ`
induces a successor structure on `C ⥤ C`. -/
@[simps]
/-
**CategoryTheory.SmallObject.SuccStruct.ofNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.SmallObject.SuccStruct`。
形式化陈述：ofNatTrans {F : C ⥤ C} (ε : 𝟭 C ⟶ F) : SuccStruct (C ⥤ C) where succ G
参数：ε : 𝟭 C ⟶ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `Φ : C ⥤ C`, a natural transformation of the form `𝟭 C ⟶ Φ`
induces a successor structure on `C ⥤ C`.
-/
def ofNatTrans {F : C ⥤ C} (ε : 𝟭 C ⟶ F) : SuccStruct (C ⥤ C) where
  succ G := G ⋙ F
  toSucc G := Functor.whiskerLeft G ε
  X₀ := 𝟭 C

variable (Φ : SuccStruct C)

/-- The class of morphisms that are of the form `toSucc X : X ⟶ succ X`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.prop** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.SmallObject.SuccStruct`。
形式化陈述：prop : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of morphisms that are of the form `toSucc X : X ⟶ succ X`.
-/
def prop : MorphismProperty C := .ofHoms (fun (X : C) ↦ Φ.toSucc X)
/-
**CategoryTheory.SmallObject.SuccStruct.prop_toSucc** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.SmallObject.SuccStruct`。
形式化陈述：prop_toSucc (X : C) : Φ.prop (Φ.toSucc X)
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prop_toSucc (X : C) : Φ.prop (Φ.toSucc X) := ⟨_⟩

/-- The map `Φ.toSucc X : X ⟶ Φ.Succ X`, as an element in `Arrow C`. -/
@[simps!]
/-
**CategoryTheory.SmallObject.SuccStruct.toSuccArrow** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.SmallObject.SuccStruct`。
形式化陈述：toSuccArrow (X : C) : Arrow C
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Φ.toSucc X : X ⟶ Φ.Succ X`, as an element in `Arrow C`.
-/
def toSuccArrow (X : C) : Arrow C := Arrow.mk (Φ.toSucc X)
/-
**CategoryTheory.SmallObject.SuccStruct.prop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.SmallObject.SuccStruct`。
形式化陈述：prop_iff {X Y : C} (f : X ⟶ Y) : Φ.prop f ↔ Arrow.mk f = Φ.toSuccArrow X
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.arrow_mk_mem_toSet_iff`：arrow_mk_mem_toS
et_iff {X Y : C} (f : X ⟶ Y) : Arrow.mk f in P.toSet ↔ P f
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.prop_toSucc`：prop_toSucc (X : C) :
 Φ.prop (Φ.toSucc X)
-/
lemma prop_iff {X Y : C} (f : X ⟶ Y) :
    Φ.prop f ↔ Arrow.mk f = Φ.toSuccArrow X := by
  constructor
  · rintro ⟨_⟩
    rfl
  · intro h
    rw [← Φ.prop.arrow_mk_mem_toSet_iff, h]
    apply prop_toSucc

variable {Φ}
/-
**CategoryTheory.SmallObject.SuccStruct.prop.succ_eq** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.SmallObject.SuccStruct.prop`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {Φ : CategoryTheo
ry.SmallObject.SuccStruct C} {X Y : C}   {f : X ⟶ Y}, Φ.prop f → Φ.succ X = Y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma prop.succ_eq {X Y : C} {f : X ⟶ Y} (hf : Φ.prop f) :
    Φ.succ X = Y := by
  cases hf
  rfl

@[reassoc]
/-
**CategoryTheory.SmallObject.SuccStruct.prop.fac** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.SmallObject.SuccStruct.prop`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {Φ : CategoryTheo
ry.SmallObject.SuccStruct C} {X Y : C}   {f : X ⟶ Y} (hf : Φ.prop f), f = Catego
ryTheory.CategoryStruct.comp (Φ.toSucc X) (CategoryTheory.eqToHom ⋯)
参数：hf : Φ.prop f；Φ.toSucc X；CategoryTheory.eqToHom ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SmallObject.SuccStruct.prop.succ_eq`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {Φ : CategoryTheory.SmallObject.SuccStruct 
C} {X Y : C}   {f : X ⟶ Y}, Φ.prop f → Φ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma prop.fac {X Y : C} {f : X ⟶ Y} (hf : Φ.prop f) :
    f = Φ.toSucc X ≫ eqToHom hf.succ_eq := by
  cases hf
  simp

set_option backward.defeqAttrib.useBackward true in
/-- If `Φ : SuccStruct C` and `f` is a morphism in `C` which
satisfies `Φ.prop f`, then this is the isomorphism of arrows
between `f` and `Φ.toSuccArrow X`. -/
@[simps!]
/-
**CategoryTheory.SmallObject.SuccStruct.prop.arrowIso** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.SmallObject.SuccStruct.prop`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {Φ : Cate
goryTheory.SmallObject.SuccStruct C} →       {X Y : C} → {f : X ⟶ Y} → Φ.prop f 
→ (CategoryTheory.Arrow.mk f ≅ Φ.toSuccArrow X)
参数：CategoryTheory.Arrow.mk f ≅ Φ.toSuccArrow X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Φ : SuccStruct C` and `f` is a morphism in `C` which
satisfies `Φ.prop f`, then this is the isomorphism of arrows
between `f` and `Φ.toSuccArrow X`.
-/
def prop.arrowIso {X Y : C} {f : X ⟶ Y} (hf : Φ.prop f) :
    Arrow.mk f ≅ Φ.toSuccArrow X :=
  Arrow.isoMk (Iso.refl _) (eqToIso hf.succ_eq.symm) (by simp [hf.fac])

variable (Φ)
variable [LinearOrder J]

/-- Given a functor `F : Set.Iic ⥤ C`, this is the morphism in `C`, as an element
in `Arrow C`, that is obtained by applying `F.map` to an inequality. -/
/-
**CategoryTheory.SmallObject.SuccStruct.arrowMap** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.SmallObject.SuccStruct`。
形式化陈述：arrowMap {j : J} (F : Set.Iic j ⥤ C) (i₁ i₂ : J) (h₁₂ : i₁ <= i₂) (h₂ : i₂
 <= j) : Arrow C
参数：F : Set.Iic j ⥤ C；i₁ i₂ : J；h₁₂ : i₁ <= i₂；h₂ : i₂ <= j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : Set.Iic ⥤ C`, this is the morphism in `C`, as an element
in `Arrow C`, that is obtained by applying `F.map` to an inequality.
-/
def arrowMap {j : J} (F : Set.Iic j ⥤ C) (i₁ i₂ : J) (h₁₂ : i₁ ≤ i₂) (h₂ : i₂ ≤ j) :
    Arrow C :=
  Arrow.mk (F.map (homOfLE h₁₂ : ⟨i₁, h₁₂.trans h₂⟩ ⟶ ⟨i₂, h₂⟩))

@[simp]
/-
**CategoryTheory.SmallObject.SuccStruct.arrowMap_refl** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：arrowMap_refl {j : J} (F : Set.Iic j ⥤ C) (i : J) (hi : i <= j) : arrowMap
 F i i (by simp) hi = Arrow.mk (𝟙 (F.obj ⟨i, hi⟩))
参数：F : Set.Iic j ⥤ C；i : J；hi : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma arrowMap_refl {j : J} (F : Set.Iic j ⥤ C) (i : J) (hi : i ≤ j) :
    arrowMap F i i (by simp) hi = Arrow.mk (𝟙 (F.obj ⟨i, hi⟩)) := by
  simp [arrowMap]
/-
**CategoryTheory.SmallObject.SuccStruct.arrowMap_restrictionLE** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：arrowMap_restrictionLE {j : J} (F : Set.Iic j ⥤ C) {j' : J} (hj' : j' <= j
) (i₁ i₂ : J) (h₁₂ : i₁ <= i₂) (h₂ : i₂ <= j') : arrowMap (restrictionLE F hj') 
i₁ i₂ h₁₂ h₂ = arrowMap F i₁ i₂ h₁₂ (h₂.trans hj')
参数：F : Set.Iic j ⥤ C；hj' : j' <= j；i₁ i₂ : J；h₁₂ : i₁ <= i₂；h₂ : i₂ <= j'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma arrowMap_restrictionLE {j : J} (F : Set.Iic j ⥤ C) {j' : J} (hj' : j' ≤ j)
    (i₁ i₂ : J) (h₁₂ : i₁ ≤ i₂) (h₂ : i₂ ≤ j') :
    arrowMap (restrictionLE F hj') i₁ i₂ h₁₂ h₂ =
      arrowMap F i₁ i₂ h₁₂ (h₂.trans hj') := rfl

section

variable [SuccOrder J] {j : J} (F : Set.Iic j ⥤ C) (i : J) (hi : i < j)

/-- Given a functor `F : Set.Iic j ⥤ C` and `i : J` such that `i < j`,
this is the arrow `F.obj ⟨i, _⟩ ⟶ F.obj ⟨Order.succ i, _⟩`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.arrowSucc** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.SmallObject.SuccStruct`。
形式化陈述：arrowSucc : Arrow C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : Set.Iic j ⥤ C` and `i : J` such that `i < j`,
this is the arrow `F.obj ⟨i, _⟩ ⟶ F.obj ⟨Order.succ i, _⟩`.
-/
def arrowSucc : Arrow C :=
    arrowMap F i (Order.succ i) (Order.le_succ i) (Order.succ_le_of_lt hi)
/-
**CategoryTheory.SmallObject.SuccStruct.arrowSucc_def** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：arrowSucc_def : arrowSucc F i hi = arrowMap F i (Order.succ i) (Order.le_s
ucc i) (Order.succ_le_of_lt hi)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma arrowSucc_def :
    arrowSucc F i hi = arrowMap F i (Order.succ i) (Order.le_succ i) (Order.succ_le_of_lt hi) :=
  rfl

end

section

variable [HasIterationOfShape J C]
  {i : J} (F : Set.Iio i ⥤ C) (hi : Order.IsSuccLimit i) (k : J) (hk : k < i)

/-- Given `F : Set.Iio i ⥤ C`, with `i` a limit element, and `k` such that `hk : k < i`,
this is the map `colimit.ι F ⟨k, hk⟩`, as an element in `Arrow C`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.arrow** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.SmallObject.SuccStruct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : Set.Iio i ⥤ C`, with `i` a limit element, and `k` such that `hk : k <
 i`,
this is the map `colimit.ι F ⟨k, hk⟩`, as an element in `Arrow C`.
-/
noncomputable def arrowι : Arrow C :=
  letI := hasColimitsOfShape_of_isSuccLimit C i hi
  Arrow.mk (colimit.ι F ⟨k, hk⟩)
/-
**CategoryTheory.SmallObject.SuccStruct.arrow** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.SmallObject.SuccStruct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma arrowι_def :
    letI := hasColimitsOfShape_of_isSuccLimit C i hi
    arrowι F hi k hk = Arrow.mk (colimit.ι F ⟨k, hk⟩) := rfl

end

variable [SuccOrder J] [OrderBot J] [HasIterationOfShape J C]

/-- The category of `j`th iterations of a successor structure `Φ : SuccStruct C`.
An object consists of the data of all iterations of `Φ` for `i : J` such
that `i ≤ j` (this is the field `F`). Such objects are
equipped with data and properties which characterizes uniquely the iterations
on three types of elements: `⊥`, successors, limit elements. -/
@[ext]
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.SmallObject.SuccStruct`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Type
 w} →       CategoryTheory.SmallObject.SuccStruct C →         [inst_1 : LinearOr
der J] →           [SuccOrder J] →             [OrderBot J] →               [Cat
egoryTheory.Limits.HasIterationOfShape J C] → [WellFoundedLT J] → J → Type (max 
(max u v) w)
参数：max (max u v) w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of `j`th iterations of a successor structure `Φ : SuccStruct C`.
An object consists of the data of all iterations of `Φ` for `i : J` such
that `i ≤ j` (this is the field `F`). Such objects are
equipped with data and properties which characterizes uniquely the iterations
on three types of elements: `⊥`, successors, limit elements.
-/
structure Iteration [WellFoundedLT J] (j : J) where
  /-- The data of all `i`th iterations for `i : J` such that `i ≤ j`. -/
  F : Set.Iic j ⥤ C
  /-- The zeroth iteration is the zeroth object . -/
  obj_bot : F.obj ⟨⊥, bot_le⟩ = Φ.X₀
  /-- The iteration on a successor element is the successor. -/
  arrowSucc_eq (i : J) (hi : i < j) : arrowSucc F i hi = Φ.toSuccArrow (F.obj ⟨i, hi.le⟩)
  /-- The iteration on a limit element identifies to the colimit of the
  value on smaller elements, see `Iteration.isColimit`. -/
  arrowMap_limit (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j) (k : J) (hk : k < i) :
    arrowMap F k i hk.le hij = arrowι (restrictionLT F hij) hi k hk

variable [WellFoundedLT J]

namespace Iteration

variable {Φ}
variable {j : J}

section

variable (iter : Φ.Iteration j)

/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.obj_succ** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration`。
形式化陈述：obj_succ (i : J) (hi : i < j) : iter.F.obj ⟨Order.succ i, Order.succ_le_of
_lt hi⟩ = Φ.succ (iter.F.obj ⟨i, hi.le⟩)
参数：i : J；hi : i < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `CategoryTheory.SmallObject.SuccStruct.Iteration.arrowSucc_eq`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} {Φ : CategoryTheory.
SmallObject.SuccStruct C}   [inst_1 : LinearOrder …
-/
lemma obj_succ (i : J) (hi : i < j) :
    iter.F.obj ⟨Order.succ i, Order.succ_le_of_lt hi⟩ = Φ.succ (iter.F.obj ⟨i, hi.le⟩) :=
  congr_arg Comma.right (iter.arrowSucc_eq i hi)
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.prop_map_succ** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration`。
形式化陈述：prop_map_succ (i : J) (hi : i < j) : Φ.prop (iter.F.map (homOfLE (Order.le
_succ i) : ⟨i, hi.le⟩ ⟶ ⟨Order.succ i, Order.succ_le_of_lt hi⟩))
参数：i : J；hi : i < j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.prop_iff`：prop_iff {X Y : C} (f : 
X ⟶ Y) : Φ.prop f ↔ Arrow.mk f = Φ.toSuccArrow X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.SmallObject.SuccStruct.arrowMap.eq_1`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : LinearOrder J] {j :
 J}   (F : CategoryTheory.Functor (↑(Set.…
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.arrowSucc_def`：arrowSucc_def : arr
owSucc F i hi = arrowMap F i (Order.succ i) (Order.le_succ i) (Order.succ_le_of_
lt hi)
· 使用定理 `CategoryTheory.SmallObject.SuccStruct.Iteration.arrowSucc_eq`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} {Φ : CategoryTheory.
SmallObject.SuccStruct C}   [inst_1 : LinearOrder …
-/
lemma prop_map_succ (i : J) (hi : i < j) :
    Φ.prop (iter.F.map (homOfLE (Order.le_succ i) :
      ⟨i, hi.le⟩ ⟶ ⟨Order.succ i, Order.succ_le_of_lt hi⟩)) := by
  rw [prop_iff, ← arrowMap, ← arrowSucc_def _ _ hi, iter.arrowSucc_eq]
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.obj_limit** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration`。
形式化陈述：obj_limit (i : J) (hi : Order.IsSuccLimit i) (hij : i <= j) : letI
参数：i : J；hi : Order.IsSuccLimit i；hij : i <= j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Order.IsSuccLimit.bot_lt`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → ⊥ < a
· 使用定理 `CategoryTheory.SmallObject.SuccStruct.Iteration.arrowMap_limit`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} {Φ : CategoryTheor
y.SmallObject.SuccStruct C}   [inst_1 : LinearOrder …
-/
lemma obj_limit (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j) :
    letI := hasColimitsOfShape_of_isSuccLimit C i hi
    iter.F.obj ⟨i, hij⟩ = colimit (restrictionLT iter.F hij) :=
  congr_arg Comma.right (iter.arrowMap_limit i hi hij ⊥ (Order.IsSuccLimit.bot_lt hi))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The iteration on a limit element identifies to the colimit of the
value on smaller elements. -/
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.isColimit** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration`。
形式化陈述：isColimit (i : J) (hi : Order.IsSuccLimit i) (hij : i <= j) : IsColimit (c
oconeOfLE iter.F hij)
参数：i : J；hi : Order.IsSuccLimit i；hij : i <= j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The iteration on a limit element identifies to the colimit of the
value on smaller elements.
-/
noncomputable def isColimit (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j) :
    IsColimit (coconeOfLE iter.F hij) := by
  letI := hasColimitsOfShape_of_isSuccLimit C i hi
  refine IsColimit.ofIsoColimit (colimit.isColimit (restrictionLT iter.F hij))
    (Cocone.ext (eqToIso (iter.obj_limit i hi hij).symm) ?_)
  rintro ⟨k, hk⟩
  apply Arrow.mk_injective
  dsimp
  rw [← arrowMap]
  simp [iter.arrowMap_limit i hi hij k hk, arrowι_def]

/-- The element in `Φ.Iteration i` that is deduced from an element
in `Φ.Iteration j` when `i ≤ j`. -/
@[simps F]
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.trunc** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.SmallObject.SuccStruct.Iteration`。
形式化陈述：trunc (iter : Φ.Iteration j) {j' : J} (hj' : j' <= j) : Φ.Iteration j' whe
re F
参数：iter : Φ.Iteration j；hj' : j' <= j。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SmallObject.SuccStruct.Iteration.obj_bot`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] {J : Type w} {Φ : CategoryTheory.Small
Object.SuccStruct C}   [inst_1 : LinearOrder …

--- 原说明 ---
The element in `Φ.Iteration i` that is deduced from an element
in `Φ.Iteration j` when `i ≤ j`.
-/
def trunc (iter : Φ.Iteration j) {j' : J} (hj' : j' ≤ j) : Φ.Iteration j' where
  F := restrictionLE iter.F hj'
  obj_bot := iter.obj_bot
  arrowSucc_eq i hi := iter.arrowSucc_eq i (lt_of_lt_of_le hi hj')
  arrowMap_limit i hi hij k hk := iter.arrowMap_limit i hi (hij.trans hj') k hk

end

namespace subsingleton

variable {K : Type w} [LinearOrder K] {x : K} (F G : Set.Iic x ⥤ C)

section

variable (k₁ k₂ : K) (h₁₂ : k₁ ≤ k₂) (h₂ : k₂ ≤ x)

/-- Auxiliary definition for the proof of `Subsingleton (Φ.Iteration j)`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton.MapEq** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton`。
形式化陈述：MapEq : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for the proof of `Subsingleton (Φ.Iteration j)`.
-/
def MapEq : Prop := arrowMap F k₁ k₂ h₁₂ h₂ = arrowMap G k₁ k₂ h₁₂ h₂

namespace MapEq

variable {k₁ k₂ h₁₂ h₂} (h : MapEq F G k₁ k₂ h₁₂ h₂)

include h

/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton.MapEq.src** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton
.MapEq`。
形式化陈述：src : F.obj ⟨k₁, h₁₂.trans h₂⟩ = G.obj ⟨k₁, h₁₂.trans h₂⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma src : F.obj ⟨k₁, h₁₂.trans h₂⟩ = G.obj ⟨k₁, h₁₂.trans h₂⟩ :=
  congr_arg Comma.left h
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton.MapEq.tgt** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton
.MapEq`。
形式化陈述：tgt : F.obj ⟨k₂, h₂⟩ = G.obj ⟨k₂, h₂⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma tgt : F.obj ⟨k₂, h₂⟩ = G.obj ⟨k₂, h₂⟩ :=
  congr_arg Comma.right h
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton.MapEq.w** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton.M
apEq`。
形式化陈述：w : F.map (homOfLE h₁₂ : ⟨k₁, h₁₂.trans h₂⟩ ⟶ ⟨k₂, h₂⟩) = eqToHom (by rw [
h.src]) ≫ G.map (homOfLE h₁₂ : ⟨k₁, h₁₂.trans h₂⟩ ⟶ ⟨k₂, h₂⟩) ≫ eqToHom (by rw [
h.tgt])
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.Arrow.mk_eq_mk_iff`：mk_eq_mk_iff {X Y X' Y' : T} (f : X ⟶
 Y) (f' : X' ⟶ Y') : Arrow.mk f = Arrow.mk f' ↔ exists (hX : X = X') (hY : Y = Y
'), f = eqToHom hX ≫ f'…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma w :
    F.map (homOfLE h₁₂ : ⟨k₁, h₁₂.trans h₂⟩ ⟶ ⟨k₂, h₂⟩) =
      eqToHom (by rw [h.src]) ≫ G.map (homOfLE h₁₂ : ⟨k₁, h₁₂.trans h₂⟩ ⟶ ⟨k₂, h₂⟩) ≫
        eqToHom (by rw [h.tgt]) := by
  have := (Arrow.mk_eq_mk_iff _ _).1 h
  tauto

end MapEq

end

variable {F G}

/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton.mapEq_refl** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleto
n`。
形式化陈述：mapEq_refl (k : K) (hk : k <= x) (h : F.obj ⟨k, hk⟩ = G.obj ⟨k, hk⟩) : Map
Eq F G k k (by simp) hk
参数：k : K；hk : k <= x；h : F.obj ⟨k, hk⟩ = G.obj ⟨k, hk⟩。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton.MapEq.eq_1`
：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {K : Type w} [inst_1 :
 LinearOrder K] {x : K}   (F G : CategoryTheory.Functor (↑(Se…
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.arrowMap_refl`：arrowMap_refl {j : 
J} (F : Set.Iic j ⥤ C) (i : J) (hi : i <= j) : arrowMap F i i (by simp) hi = Arr
ow.mk (𝟙 (F.obj ⟨i, hi⟩))
-/
lemma mapEq_refl (k : K) (hk : k ≤ x) (h : F.obj ⟨k, hk⟩ = G.obj ⟨k, hk⟩) :
    MapEq F G k k (by simp) hk := by
  rw [MapEq, arrowMap_refl, arrowMap_refl, h]
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton.mapEq_trans** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration.subsinglet
on`。
形式化陈述：mapEq_trans {i₁ i₂ i₃ : K} (h₁₂ : i₁ <= i₂) (h₂₃ : i₂ <= i₃) {h₃ : i₃ <= x
} (m₁₂ : MapEq F G i₁ i₂ h₁₂ (h₂₃.trans h₃)) (m₂₃ : MapEq F G i₂ i₃ h₂₃ h₃) : Ma
pEq F G i₁ i₃ (h₁₂.trans h₂₃) h₃
参数：h₁₂ : i₁ <= i₂；h₂₃ : i₂ <= i₃；m₁₂ : MapEq F G i₁ i₂ h₁₂ (h₂₃.trans h₃)；m₂₃ : 
MapEq F G i₂ i₃ h₂₃ h₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton.MapEq.src`：
src : F.obj ⟨k₁, h₁₂.trans h₂⟩ = G.obj ⟨k₁, h₁₂.trans h₂⟩
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton.MapEq.tgt`：
tgt : F.obj ⟨k₂, h₂⟩ = G.obj ⟨k₂, h₂⟩
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.homOfLE_comp`：homOfLE_comp {x y z : X} (h : x <= y) (k : 
y <= z) : homOfLE h ≫ homOfLE k = homOfLE (h.trans k)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton.MapEq.w`：w 
: F.map (homOfLE h₁₂ : ⟨k₁, h₁₂.trans h₂⟩ ⟶ ⟨k₂, h₂⟩) = eqToHom (by rw [h.src]) 
≫ G.map (homOfLE h₁₂ : ⟨k₁, h₁₂.trans h₂⟩ ⟶ ⟨k₂, h₂⟩) ≫ eq…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapEq_trans {i₁ i₂ i₃ : K} (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃) {h₃ : i₃ ≤ x}
    (m₁₂ : MapEq F G i₁ i₂ h₁₂ (h₂₃.trans h₃)) (m₂₃ : MapEq F G i₂ i₃ h₂₃ h₃) :
    MapEq F G i₁ i₃ (h₁₂.trans h₂₃) h₃ := by
  simp only [MapEq, arrowMap, Arrow.mk_eq_mk_iff]
  refine ⟨m₁₂.src, m₂₃.tgt, ?_⟩
  rw [← homOfLE_comp (y := ⟨i₂, h₂₃.trans h₃⟩) h₁₂ h₂₃]
  simp [-homOfLE_comp, m₁₂.w, m₂₃.w]
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton.ext** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton`。
形式化陈述：ext (h : forall (k₁ k₂ : K) (h₁₂ : k₁ <= k₂) (h₂ : k₂ <= x), MapEq F G k₁ 
k₂ h₁₂ h₂) : F = G
参数：h : forall (k₁ k₂ : K) (h₁₂ : k₁ <= k₂) (h₂ : k₂ <= x), MapEq F G k₁ k₂ h₁₂ h
₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Arrow.functor_ext`：∀ {C : Type u_1} {D : Type u_2} [inst 
: CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2
, u_2} D] {F G : Categ…
-/
lemma ext (h : ∀ (k₁ k₂ : K) (h₁₂ : k₁ ≤ k₂) (h₂ : k₂ ≤ x),
    MapEq F G k₁ k₂ h₁₂ h₂) :
    F = G := by
  apply Arrow.functor_ext
  rintro ⟨k₁, _⟩ ⟨k₂, h₂⟩ f
  apply h

end subsingleton

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open subsingleton in
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton** 是 Mathlib 中的一个实
例，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration`。
形式化陈述：subsingleton : Subsingleton (Φ.Iteration j) where allEq iter₁ iter₂
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton.ext`：ext (h
 : forall (k₁ k₂ : K) (h₁₂ : k₁ <= k₂) (h₂ : k₂ <= x), MapEq F G k₁ k₂ h₁₂ h₂) :
 F = G
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton.mapEq_refl`
：mapEq_refl (k : K) (hk : k <= x) (h : F.obj ⟨k, hk⟩ = G.obj ⟨k, hk⟩) : MapEq F 
G k k (by simp) hk
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SmallObject.SuccStruct.Iteration.obj_bot`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] {J : Type w} {Φ : CategoryTheory.Small
Object.SuccStruct C}   [inst_1 : LinearOrder …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsMin.eq_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot 
α] {a : α}, IsMin a → a = ⊥
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.arrowMap_restrictionLE`：arrowMap_r
estrictionLE {j : J} (F : Set.Iic j ⥤ C) {j' : J} (hj' : j' <= j) (i₁ i₂ : J) (h
₁₂ : i₁ <= i₂) (h₂ : i₂ <= j') : arrowMap (restric…
· 使用定理 `CategoryTheory.SmallObject.SuccStruct.arrowMap.congr_simp`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : LinearOrder J
] {j : J}   (F F_1 : CategoryTheory.Functor (↑(…
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.lt_succ_iff_of_not_isMax`：lt_succ_iff_of_not_isMax (ha : ¬IsMax a)
 : b < succ a ↔ b <= a
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton.mapEq_trans
`：mapEq_trans {i₁ i₂ i₃ : K} (h₁₂ : i₁ <= i₂) (h₂₃ : i₂ <= i₃) {h₃ : i₃ <= x} (m
₁₂ : MapEq F G i₁ i₂ h₁₂ (h₂₃.trans h₃)) (m₂₃ : MapEq F G i₂ i…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Order.lt_succ_of_not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [inst_1
 : SuccOrder α] {a : α}, ¬IsMax a → a < Order.succ a
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.arrowSucc_def`：arrowSucc_def : arr
owSucc F i hi = arrowMap F i (Order.succ i) (Order.le_succ i) (Order.succ_le_of_
lt hi)
· 使用定理 `CategoryTheory.SmallObject.SuccStruct.Iteration.arrowSucc_eq`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} {Φ : CategoryTheory.
SmallObject.SuccStruct C}   [inst_1 : LinearOrder …
· 使用定理 `CategoryTheory.SmallObject.SuccStruct.Iteration.subsingleton.MapEq.eq_1`
：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {K : Type w} [inst_1 :
 LinearOrder K] {x : K}   (F G : CategoryTheory.Functor (↑(Se…
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.arrowMap_refl`：arrowMap_refl {j : 
J} (F : Set.Iic j ⥤ C) (i : J) (hi : i <= j) : arrowMap F i i (by simp) hi = Arr
ow.mk (𝟙 (F.obj ⟨i, hi⟩))
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.Iteration.obj_succ`：obj_succ (i : 
J) (hi : i < j) : iter.F.obj ⟨Order.succ i, Order.succ_le_of_lt hi⟩ = Φ.succ (it
er.F.obj ⟨i, hi.le⟩)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 43 条，此处仅展示前 30 条）
-/
instance subsingleton : Subsingleton (Φ.Iteration j) where
  allEq iter₁ iter₂ := by
    suffices iter₁.F = iter₂.F by aesop
    revert iter₁ iter₂
    induction j using SuccOrder.limitRecOn with
    | isMin j h =>
      obtain rfl := h.eq_bot
      intro iter₁ iter₂
      refine ext (fun k₁ k₂ h₁₂ h₂ ↦ ?_)
      obtain rfl : k₂ = ⊥ := by simpa using h₂
      obtain rfl : k₁ = ⊥ := by simpa using h₁₂
      apply mapEq_refl _ _ (by simp only [obj_bot])
    | succ j hj₁ hj₂ =>
      intro iter₁ iter₂
      refine ext (fun k₁ k₂ h₁₂ h₂ ↦ ?_)
      have h₀ := Order.le_succ j
      replace hj₂ := hj₂ (iter₁.trunc h₀) (iter₂.trunc h₀)
      have hsucc := Functor.congr_obj hj₂ ⟨j, by simp⟩
      dsimp at hj₂ hsucc
      wlog h : k₂ ≤ j generalizing k₁ k₂
      · obtain h₂ | rfl := h₂.lt_or_eq
        · exact this _ _ _ _ ((Order.lt_succ_iff_of_not_isMax hj₁).1 h₂)
        · by_cases h' : k₁ ≤ j
          · apply mapEq_trans _ h₀ (this k₁ j h' h₀ (by simp))
            simp only [MapEq, ← arrowSucc_def _ _ (Order.lt_succ_of_not_isMax hj₁),
              arrowSucc_eq, hsucc]
          · simp only [not_le] at h'
            obtain rfl : k₁ = Order.succ j := le_antisymm h₁₂
              ((Order.succ_le_iff_of_not_isMax hj₁).2 h')
            rw [MapEq, arrowMap_refl, arrowMap_refl,
              obj_succ _ _ h', obj_succ _ _ h', hsucc]
      simp only [MapEq, ← arrowMap_restrictionLE _ (Order.le_succ j) _ _ _ h, hj₂]
    | isSuccLimit j h₁ h₂ =>
      intro iter₁ iter₂
      refine ext (fun k₁ k₂ h₁₂ h₃ ↦ ?_)
      wlog h₄ : k₂ < j generalizing k₁ k₂; swap
      · have := h₂ k₂ h₄ (iter₁.trunc h₄.le) (iter₂.trunc h₄.le)
        simp at this
        simp only [MapEq, ← arrowMap_restrictionLE _ h₄.le _ _ _ (by rfl), this]
      · obtain rfl : j = k₂ := le_antisymm (by simpa using h₄) h₃
        have : restrictionLT iter₁.F le_rfl = restrictionLT iter₂.F le_rfl :=
          Arrow.functor_ext (fun _ l _ ↦ this _ _ _ _ l.2)
        by_cases h₅ : k₁ < j
        · dsimp [MapEq]
          simp_rw [arrowMap_limit _ _ h₁ _ _ h₅, this]
        · obtain rfl : k₁ = j := le_antisymm h₁₂ (by simpa using h₅)
          apply mapEq_refl
          simp only [obj_limit _ _ h₁, this]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.congr_obj** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration`。
形式化陈述：congr_obj {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂) (k
 : J) (h₁ : k <= j₁) (h₂ : k <= j₂) : iter₁.F.obj ⟨k, h₁⟩ = iter₂.F.obj ⟨k, h₂⟩
参数：iter₁ : Φ.Iteration j₁；iter₂ : Φ.Iteration j₂；k : J；h₁ : k <= j₁；h₂ : k <= j₂
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma congr_obj {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂)
    (k : J) (h₁ : k ≤ j₁) (h₂ : k ≤ j₂) :
    iter₁.F.obj ⟨k, h₁⟩ = iter₂.F.obj ⟨k, h₂⟩ := by
  wlog h : j₁ ≤ j₂ generalizing j₁ j₂
  · exact (this iter₂ iter₁ h₂ h₁ (le_of_lt (by simpa using h))).symm
  rw [Subsingleton.elim iter₁ (iter₂.trunc h)]
  dsimp
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.congr_arrowMap** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration`。
形式化陈述：congr_arrowMap {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j
₂) {k₁ k₂ : J} (h : k₁ <= k₂) (h₁ : k₂ <= j₁) (h₂ : k₂ <= j₂) : arrowMap iter₁.F
 k₁ k₂ h h₁ = arrowMap iter₂.F k₁ k₂ h h₂
参数：iter₁ : Φ.Iteration j₁；iter₂ : Φ.Iteration j₂；h : k₁ <= k₂；h₁ : k₂ <= j₁；h₂ :
 k₂ <= j₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma congr_arrowMap {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂)
    {k₁ k₂ : J} (h : k₁ ≤ k₂) (h₁ : k₂ ≤ j₁) (h₂ : k₂ ≤ j₂) :
    arrowMap iter₁.F k₁ k₂ h h₁ = arrowMap iter₂.F k₁ k₂ h h₂ := by
  wlog hj : j₁ ≤ j₂ generalizing j₁ j₂
  · simp [this iter₂ iter₁ h₂ h₁ ((not_le.1 hj).le)]
  rw [Subsingleton.elim iter₁ (iter₂.trunc hj)]
  rfl
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.congr_map** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration`。
形式化陈述：congr_map {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂) {k
₁ k₂ : J} (h : k₁ <= k₂) (h₁ : k₂ <= j₁) (h₂ : k₂ <= j₂) : iter₁.F.map (homOfLE 
h : ⟨k₁, h.trans h₁⟩ ⟶ ⟨k₂, h₁⟩) = eqToHom (congr_obj iter₁ iter₂ k₁ (h.trans h₁
) (h.trans h₂)) ≫ iter₂.F.map (homOfLE h) ≫ eqToHom (congr_obj iter₁ iter₂ k₂ h₁
 h₂).symm
参数：iter₁ : Φ.Iteration j₁；iter₂ : Φ.Iteration j₂；h : k₁ <= k₂；h₁ : k₂ <= j₁；h₂ :
 k₂ <= j₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.Arrow.mk_eq_mk_iff`：mk_eq_mk_iff {X Y X' Y' : T} (f : X ⟶
 Y) (f' : X' ⟶ Y') : Arrow.mk f = Arrow.mk f' ↔ exists (hX : X = X') (hY : Y = Y
'), f = eqToHom hX ≫ f'…
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.Iteration.congr_arrowMap`：congr_ar
rowMap {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂) {k₁ k₂ : J}
 (h : k₁ <= k₂) (h₁ : k₂ <= j₁) (h₂ : k₂ <= j₂) : ar…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.Iteration.congr_obj`：congr_obj {j₁
 j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂) (k : J) (h₁ : k <= j₁
) (h₂ : k <= j₂) : iter₁.F.obj ⟨k, h₁⟩ = iter₂.…
-/
lemma congr_map {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂)
    {k₁ k₂ : J} (h : k₁ ≤ k₂) (h₁ : k₂ ≤ j₁) (h₂ : k₂ ≤ j₂) :
    iter₁.F.map (homOfLE h : ⟨k₁, h.trans h₁⟩ ⟶ ⟨k₂, h₁⟩) =
      eqToHom (congr_obj iter₁ iter₂ k₁ (h.trans h₁) (h.trans h₂)) ≫
        iter₂.F.map (homOfLE h) ≫
        eqToHom (congr_obj iter₁ iter₂ k₂ h₁ h₂).symm := by
  have := (Arrow.mk_eq_mk_iff _ _).1 (congr_arrowMap iter₁ iter₂ h h₁ h₂)
  tauto

/-- Given `iter₁ : Φ.Iteration j₁` and `iter₂ : Φ.Iteration j₂`, with `j₁ ≤ j₂`,
if `k₁ ≤ k₂` are elements such that `k₁ ≤ j₁` and `k₂ ≤ k₂`, then this
is the canonical map `iter₁.F.obj ⟨k₁, h₁⟩ ⟶ iter₂.F.obj ⟨k₂, h₂⟩`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.mapObj** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.SmallObject.SuccStruct.Iteration`。
形式化陈述：mapObj {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂) {k₁ k
₂ : J} (h₁₂ : k₁ <= k₂) (h₁ : k₁ <= j₁) (h₂ : k₂ <= j₂) (hj : j₁ <= j₂) : iter₁.
F.obj ⟨k₁, h₁⟩ ⟶ iter₂.F.obj ⟨k₂, h₂⟩
参数：iter₁ : Φ.Iteration j₁；iter₂ : Φ.Iteration j₂；h₁₂ : k₁ <= k₂；h₁ : k₁ <= j₁；h₂
 : k₂ <= j₂；hj : j₁ <= j₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `iter₁ : Φ.Iteration j₁` and `iter₂ : Φ.Iteration j₂`, with `j₁ ≤ j₂`,
if `k₁ ≤ k₂` are elements such that `k₁ ≤ j₁` and `k₂ ≤ k₂`, then this
is the canonical map `iter₁.F.obj ⟨k₁, h₁⟩ ⟶ iter₂.F.obj ⟨k₂, h₂⟩`.
-/
def mapObj {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂)
    {k₁ k₂ : J} (h₁₂ : k₁ ≤ k₂) (h₁ : k₁ ≤ j₁) (h₂ : k₂ ≤ j₂) (hj : j₁ ≤ j₂) :
    iter₁.F.obj ⟨k₁, h₁⟩ ⟶ iter₂.F.obj ⟨k₂, h₂⟩ :=
  eqToHom (congr_obj iter₁ iter₂ k₁ h₁ (h₁.trans hj)) ≫
    iter₂.F.map (homOfLE h₁₂)
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.arrow_mk_mapObj** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration`。
形式化陈述：arrow_mk_mapObj {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration 
j₂) {k₁ k₂ : J} (h₁₂ : k₁ <= k₂) (h₁ : k₁ <= j₁) (h₂ : k₂ <= j₂) (hj : j₁ <= j₂)
 : Arrow.mk (mapObj iter₁ iter₂ h₁₂ h₁ h₂ hj) = arrowMap iter₂.F k₁ k₂ h₁₂ h₂
参数：iter₁ : Φ.Iteration j₁；iter₂ : Φ.Iteration j₂；h₁₂ : k₁ <= k₂；h₁ : k₁ <= j₁；h₂
 : k₂ <= j₂；hj : j₁ <= j₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Arrow.arrow_mk_eqToHom_comp`：arrow_mk_eqToHom_comp {X' X 
Y : T} (f : X ⟶ Y) (h : X' = X) : Arrow.mk (eqToHom h ≫ f) = Arrow.mk f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma arrow_mk_mapObj {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂)
    {k₁ k₂ : J} (h₁₂ : k₁ ≤ k₂) (h₁ : k₁ ≤ j₁) (h₂ : k₂ ≤ j₂) (hj : j₁ ≤ j₂) :
    Arrow.mk (mapObj iter₁ iter₂ h₁₂ h₁ h₂ hj) =
      arrowMap iter₂.F k₁ k₂ h₁₂ h₂ := by
  simp [mapObj, arrowMap]

@[simp]
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.mapObj_refl** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration`。
形式化陈述：mapObj_refl {j : J} (iter : Φ.Iteration j) {k l : J} (h : k <= l) (h' : l 
<= j) : mapObj iter iter h (h.trans h') h' (by rfl) = iter.F.map (homOfLE h)
参数：iter : Φ.Iteration j；h : k <= l；h' : l <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapObj_refl {j : J} (iter : Φ.Iteration j)
    {k l : J} (h : k ≤ l) (h' : l ≤ j) :
    mapObj iter iter h (h.trans h') h' (by rfl) = iter.F.map (homOfLE h) := by
  simp [mapObj]

@[reassoc (attr := simp)]
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.mapObj_trans** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration`。
形式化陈述：mapObj_trans {j₁ j₂ j₃ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration 
j₂) (iter₃ : Φ.Iteration j₃) {k₁ k₂ k₃ : J} (h₁₂ : k₁ <= k₂) (h₂₃ : k₂ <= k₃) (h
₁ : k₁ <= j₁) (h₂ : k₂ <= j₂) (h₃ : k₃ <= j₃) (h₁₂' : j₁ <= j₂) (h₂₃' : j₂ <= j₃
) : mapObj iter₁ iter₂ h₁₂ h₁ h₂ h₁₂' ≫ mapObj iter₂ iter₃ h₂₃ h₂ h₃ h₂₃' = mapO
bj iter₁ iter₃ (h₁₂.trans h₂₃) h₁ h₃ (h₁₂'.trans h₂₃')
参数：iter₁ : Φ.Iteration j₁；iter₂ : Φ.Iteration j₂；iter₃ : Φ.Iteration j₃；h₁₂ : k₁
 <= k₂；h₂₃ : k₂ <= k₃；h₁ : k₁ <= j₁；h₂ : k₂ <= j₂；h₃ : k₃ <= j₃；h₁₂' : j₁ <= j₂；
h₂₃' : j₂ <= j₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.Iteration.congr_obj`：congr_obj {j₁
 j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂) (k : J) (h₁ : k <= j₁
) (h₂ : k <= j₂) : iter₁.F.obj ⟨k, h₁⟩ = iter₂.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.Iteration.congr_map`：congr_map {j₁
 j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂) {k₁ k₂ : J} (h : k₁ <
= k₂) (h₁ : k₂ <= j₁) (h₂ : k₂ <= j₂) : iter₁.F…
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapObj_trans {j₁ j₂ j₃ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂)
    (iter₃ : Φ.Iteration j₃) {k₁ k₂ k₃ : J} (h₁₂ : k₁ ≤ k₂) (h₂₃ : k₂ ≤ k₃)
    (h₁ : k₁ ≤ j₁) (h₂ : k₂ ≤ j₂) (h₃ : k₃ ≤ j₃) (h₁₂' : j₁ ≤ j₂) (h₂₃' : j₂ ≤ j₃) :
    mapObj iter₁ iter₂ h₁₂ h₁ h₂ h₁₂' ≫ mapObj iter₂ iter₃ h₂₃ h₂ h₃ h₂₃' =
      mapObj iter₁ iter₃ (h₁₂.trans h₂₃) h₁ h₃ (h₁₂'.trans h₂₃') := by
  simp [mapObj, congr_map iter₂ iter₃ h₁₂ h₂ (h₂.trans h₂₃'), ← Functor.map_comp]

end Iteration

end SuccStruct

end SmallObject

end CategoryTheory

