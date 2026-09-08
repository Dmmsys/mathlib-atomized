/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Data.List.Chain
public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.CategoryTheory.Sigma.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Connected components of a category

Defines a type `ConnectedComponents J` indexing the connected components of a category, and the
full subcategories giving each connected component: `Component j : Type u₁`.
We show that each `Component j` is in fact connected.

We show every category can be expressed as a disjoint union of its connected components, in
particular `Decomposed J` is the category (definitionally) given by the sigma-type of the connected
components of `J`, and it is shown that this is equivalent to `J`.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂

noncomputable section

open CategoryTheory.Category

namespace CategoryTheory

attribute [instance 100] IsConnected.is_nonempty

variable {J : Type u₁} [Category.{v₁} J]

/-- This type indexes the connected components of the category `J`. -/
/-
**CategoryTheory.ConnectedComponents** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：ConnectedComponents (J : Type u₁) [Category.{v₁} J] : Type u₁
参数：J : Type u₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This type indexes the connected components of the category `J`.
-/
def ConnectedComponents (J : Type u₁) [Category.{v₁} J] : Type u₁ :=
  Quotient (Zigzag.setoid J)

/-- The map `ConnectedComponents J → ConnectedComponents K` induced by a functor `J ⥤ K`. -/
/-
**CategoryTheory.Functor.mapConnectedComponents** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {K : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} K] →         Category
Theory.Functor J K → CategoryTheory.ConnectedComponents J → CategoryTheory.Conne
ctedComponents K
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `ConnectedComponents J → ConnectedComponents K` induced by a functor `J 
⥤ K`.
-/
def Functor.mapConnectedComponents {K : Type u₂} [Category.{v₂} K] (F : J ⥤ K)
    (x : ConnectedComponents J) : ConnectedComponents K :=
  x |> Quotient.lift (Quotient.mk (Zigzag.setoid _) ∘ F.obj)
    (fun _ _ ↦ Quot.sound ∘ zigzag_obj_of_zigzag F)

@[simp]
/-
**CategoryTheory.Functor.mapConnectedComponents_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {K : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} K]   (F : CategoryTheory.Functor J K)
 (j : J), F.mapConnectedComponents ⟦j⟧ = ⟦F.obj j⟧
参数：F : CategoryTheory.Functor J K；j : J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Functor.mapConnectedComponents_mk {K : Type u₂} [Category.{v₂} K] (F : J ⥤ K) (j : J) :
    F.mapConnectedComponents (Quotient.mk _ j) = Quotient.mk _ (F.obj j) := rfl
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited J] : Inhabited (ConnectedComponents J) :=
  ⟨Quotient.mk'' default⟩

/-- Every function from connected components of a category gives a functor to discrete category -/
/-
**CategoryTheory.ConnectedComponents.functorToDiscrete** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.ConnectedComponents`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     (X : T
ype u_1) → (CategoryTheory.ConnectedComponents J → X) → CategoryTheory.Functor J
 (CategoryTheory.Discrete X)
参数：X : Type u_1；CategoryTheory.ConnectedComponents J → X；CategoryTheory.Discrete
 X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every function from connected components of a category gives a functor to discre
te category
-/
def ConnectedComponents.functorToDiscrete (X : Type*)
    (f : ConnectedComponents J → X) : J ⥤ Discrete X where
  obj Y := Discrete.mk (f (Quotient.mk (Zigzag.setoid _) Y))
  map g := Discrete.eqToHom (congrArg f (Quotient.sound (Zigzag.of_hom g)))

/-- Every functor to a discrete category gives a function from connected components -/
/-
**CategoryTheory.ConnectedComponents.liftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ConnectedComponents`。
形式化陈述：(J : Type u_2) →   [inst : CategoryTheory.Category.{v_1, u_2} J] →     {X 
: Type u_1} → CategoryTheory.Functor J (CategoryTheory.Discrete X) → CategoryThe
ory.ConnectedComponents J → X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every functor to a discrete category gives a function from connected components
-/
def ConnectedComponents.liftFunctor (J) [Category* J] {X : Type*} (F : J ⥤ Discrete X) :
    (ConnectedComponents J → X) :=
  Quotient.lift (fun c => (F.obj c).as)
    (fun _ _ h => eq_of_zigzag X (zigzag_obj_of_zigzag F h))

/-- Functions from connected components and functors to discrete category are in bijection -/
/-
**CategoryTheory.ConnectedComponents.typeToCatHomEquiv** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.ConnectedComponents`。
形式化陈述：(J : Type u_2) →   [inst : CategoryTheory.Category.{v_1, u_2} J] →     (X 
: Type u_1) → (CategoryTheory.ConnectedComponents J → X) ≃ CategoryTheory.Functo
r J (CategoryTheory.Discrete X)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functions from connected components and functors to discrete category are in bij
ection
-/
def ConnectedComponents.typeToCatHomEquiv (J) [Category* J] (X : Type*) :
    (ConnectedComponents J → X) ≃ (J ⥤ Discrete X) where
  toFun := ConnectedComponents.functorToDiscrete _
  invFun := ConnectedComponents.liftFunctor _
  left_inv f := funext fun x ↦ by
    obtain ⟨x, h⟩ := Quotient.exists_rep x
    rw [← h]
    rfl
  right_inv fctr :=
    Functor.hext (fun _ ↦ rfl) (fun c d f ↦
      have : Subsingleton (fctr.obj c ⟶ fctr.obj d) := Discrete.instSubsingletonDiscreteHom _ _
      (Subsingleton.elim (fctr.map f) _).symm.heq)

/-- Given an index for a connected component, this is the property of the
objects which belong to this component. -/
/-
**CategoryTheory.ConnectedComponents.objectProperty** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.ConnectedComponents`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] → CategoryTh
eory.ConnectedComponents J → CategoryTheory.ObjectProperty J
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
Given an index for a connected component, this is the property of the
objects which belong to this component.
-/
def ConnectedComponents.objectProperty (j : ConnectedComponents J) :
    ObjectProperty J := fun k => Quotient.mk'' k = j

/-- Given an index for a connected component, produce the actual component as a full subcategory. -/
/-
**CategoryTheory.ConnectedComponents.Component** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ConnectedComponents`。
形式化陈述：{J : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} J] → CategoryTheo
ry.ConnectedComponents J → Type u₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an index for a connected component, produce the actual component as a full
 subcategory.
-/
abbrev ConnectedComponents.Component (j : ConnectedComponents J) : Type u₁ :=
  j.objectProperty.FullSubcategory

/-- The inclusion functor from a connected component to the whole category. -/
/-
**CategoryTheory.ConnectedComponents.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion functor from a connected component to the whole category.
-/
abbrev ConnectedComponents.ι (j : ConnectedComponents J) : j.Component ⥤ J := j.objectProperty.ι

/-- The connected component of an object in a category. -/
/-
**CategoryTheory.ConnectedComponents.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ConnectedComponents`。
形式化陈述：{J : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} J] → J → Category
Theory.ConnectedComponents J
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
The connected component of an object in a category.
-/
abbrev ConnectedComponents.mk (j : J) : ConnectedComponents J :=
  Quotient.mk'' j

/-- Each connected component of the category is nonempty. -/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each connected component of the category is nonempty.
-/
instance (j : ConnectedComponents J) : Nonempty j.Component := by
  induction j using Quotient.inductionOn'
  exact ⟨⟨_, rfl⟩⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (j : ConnectedComponents J) : Inhabited j.Component :=
  Classical.inhabited_of_nonempty'

/-- Each connected component of the category is connected. -/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each connected component of the category is connected.
-/
instance (j : ConnectedComponents J) : IsConnected j.Component := by
  -- Show it's connected by constructing a zigzag (in `j.Component`) between any two objects
  apply isConnected_of_zigzag
  rintro ⟨j₁, hj₁⟩ ⟨j₂, rfl⟩
  -- We know that the underlying objects j₁ j₂ have some zigzag between them in `J`
  have h₁₂ : Zigzag j₁ j₂ := Quotient.exact' hj₁
  -- Get an explicit zigzag as a list
  rcases List.exists_isChain_cons_of_relationReflTransGen h₁₂ with ⟨l, hl₁, hl₂⟩
  -- Everything which has a zigzag to j₂ can be lifted to the same component as `j₂`.
  let f : ∀ x, Zigzag x j₂ → (ConnectedComponents.mk j₂).Component :=
    fun x h => ⟨x, Quotient.sound' h⟩
  -- Everything in our chosen zigzag from `j₁` to `j₂` has a zigzag to `j₂`.
  have hf : ∀ a : J, a ∈ l → Zigzag a j₂ := by
    intro i hi
    apply hl₁.backwards_cons_induction (fun t => Zigzag t j₂) _ hl₂ _ _ _ (List.mem_of_mem_tail hi)
    · intro j k
      apply Relation.ReflTransGen.head
    · apply Relation.ReflTransGen.refl
  -- Now lift the zigzag from `j₁` to `j₂` in `J` to the same thing in `j.Component`.
  refine ⟨l.pmap f hf, ?_, by grind⟩
  refine @List.isChain_cons_pmap_of_isChain_cons _ _ Zag _ _ f
    (fun x y _ _ h => ?_) _ _ h₁₂ hl₁ _
  exact zag_of_zag_obj (ConnectedComponents.ι _) h

/-- The disjoint union of `J`'s connected components, written explicitly as a sigma-type with the
category structure.
This category is equivalent to `J`.
-/
/-
**CategoryTheory.Decomposed** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：Decomposed (J : Type u₁) [Category.{v₁} J]
参数：J : Type u₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The disjoint union of `J`'s connected components, written explicitly as a sigma-
type with the
category structure.
This category is equivalent to `J`.
-/
abbrev Decomposed (J : Type u₁) [Category.{v₁} J] :=
  Σ j : ConnectedComponents J, j.Component

-- This name may cause clashes further down the road, and so might need to be changed.
/--
The inclusion of each component into the decomposed category. This is just `sigma.incl` but having
this abbreviation helps guide typeclass search to get the right category instance on `decomposed J`.
-/
/-
**CategoryTheory.inclusion** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：inclusion (j : ConnectedComponents J) : j.Component ⥤ Decomposed J
参数：j : ConnectedComponents J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of each component into the decomposed category. This is just `sigm
a.incl` but having
this abbreviation helps guide typeclass search to get the right category instanc
e on `decomposed J`.
-/
abbrev inclusion (j : ConnectedComponents J) : j.Component ⥤ Decomposed J :=
  Sigma.incl _

/-- The forward direction of the equivalence between the decomposed category and the original. -/
@[simps!]
/-
**CategoryTheory.decomposedTo** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：decomposedTo (J : Type u₁) [Category.{v₁} J] : Decomposed J ⥤ J
参数：J : Type u₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forward direction of the equivalence between the decomposed category and the
 original.
-/
def decomposedTo (J : Type u₁) [Category.{v₁} J] : Decomposed J ⥤ J :=
  Sigma.desc ConnectedComponents.ι

@[simp]
/-
**CategoryTheory.inclusion_comp_decomposedTo** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory`。
形式化陈述：inclusion_comp_decomposedTo (j : ConnectedComponents J) : inclusion j ⋙ de
composedTo J = ConnectedComponents.ι j
参数：j : ConnectedComponents J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusion_comp_decomposedTo (j : ConnectedComponents J) :
    inclusion j ⋙ decomposedTo J = ConnectedComponents.ι j :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (decomposedTo J).Full where
  map_surjective := by
    rintro ⟨j', X, hX⟩ ⟨k', Y, hY⟩ f
    dsimp at f
    have : j' = k' := by
      rw [← hX, ← hY, Quotient.eq'']
      exact Relation.ReflTransGen.single (Or.inl ⟨f⟩)
    subst this
    exact ⟨Sigma.SigmaHom.mk (ObjectProperty.homMk f), rfl⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (decomposedTo J).Faithful where
  map_injective := by
    rintro ⟨_, j, rfl⟩ ⟨_, k, hY⟩ ⟨⟨f⟩⟩ ⟨⟨_⟩⟩ rfl
    rfl
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (decomposedTo J).EssSurj where mem_essImage j := ⟨⟨_, j, rfl⟩, ⟨Iso.refl _⟩⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (decomposedTo J).IsEquivalence where

/-- This gives that any category is equivalent to a disjoint union of connected categories. -/
@[simps! functor]
/-
**CategoryTheory.decomposedEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：decomposedEquiv : Decomposed J ≌ J
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instIsEquivalenceDecomposedDecomposedTo`：∀ {J : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} J], (CategoryTheory.decomposedTo J).IsE
quivalence

--- 原说明 ---
This gives that any category is equivalent to a disjoint union of connected cate
gories.
-/
def decomposedEquiv : Decomposed J ≌ J :=
  (decomposedTo J).asEquivalence

end CategoryTheory

