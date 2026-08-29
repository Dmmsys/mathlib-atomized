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

/--
Definition of `ConnectedComponents` / `ConnectedComponents` 的定义

English:
definition ConnectedComponents
  signature: (J : Type u₁) [Category.{v₁} J]
  body: Quotient (Zigzag.setoid J)

中文:
定义 ConnectedComponents
  签名: (J : 类型u₁) [范畴.{v₁} J]
  定义体: Quotient (Zigzag.setoid J)

Depends on / 依赖: Quotient, Zigzag, Zigzag.setoid, setoid
-/
def ConnectedComponents (J : Type u₁) [Category.{v₁} J] : Type u₁ :=
  Quotient (Zigzag.setoid J)

/--
Definition of `Functor.mapConnectedComponents` / `Functor.mapConnectedComponents` 的定义

English:
definition Functor.mapConnectedComponents
  signature: {K : Type u₂} [Category.{v₂} K] (F : J ⥤ K)
  body: Quotient.lift (Quotient.mk (Zigzag.setoid _) ∘ F.obj) x
    (fun _ _ => Quot.sound ∘ zigzag_obj_of_zigzag F)

@[simp]

中文:
定义 函子.mapConnectedComponents
  签名: {K : 类型u₂} [范畴.{v₂} K] (F : J ⥤ K)
  定义体: Quotient.lift (Quotient.mk (Zigzag.setoid _) ∘ F.obj) x
    (fun _ _ => Quot.sound ∘ zigzag_obj_of_zigzag F)

@[simp]

Depends on / 依赖: F.obj, Quot.sound, Quotient, Quotient.lift, Quotient.mk, Zigzag, Zigzag.setoid, setoid, zigzag_obj_of_zigzag
-/
def Functor.mapConnectedComponents {K : Type u₂} [Category.{v₂} K] (F : J ⥤ K)
    (x : ConnectedComponents J) : ConnectedComponents K :=
Quotient.lift (Quotient.mk (Zigzag.setoid _) ∘ F.obj) x
    (fun _ _ => Quot.sound ∘ zigzag_obj_of_zigzag F)

@[simp]
/--
lemma `Functor.mapConnectedComponents_mk` / 引理 `Functor.mapConnectedComponents_mk`

English:
lemma Functor.mapConnectedComponents_mk
  given: {K : Type u₂} [Category.{v₂} K] (F : J ⥤ K) (j : J)
  proof: rfl

中文:
引理 函子.mapConnectedComponents_mk
  条件: {K : 类型u₂} [范畴.{v₂} K] (F : J ⥤ K) (j : J)
  证明: rfl
-/
lemma Functor.mapConnectedComponents_mk {K : Type u₂} [Category.{v₂} K] (F : J ⥤ K) (j : J) :
    F.mapConnectedComponents (Quotient.mk _ j) = Quotient.mk _ (F.obj j) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: J] : Inhabited (ConnectedComponents J)
  body: ⟨Quotient.mk'' default⟩

中文:
实例 [可居
  签名: J] : 可居 (ConnectedComponents J)
  定义体: ⟨Quotient.mk'' default⟩

Depends on / 依赖: Quotient, Quotient.mk
-/
instance [Inhabited J] : Inhabited (ConnectedComponents J) :=
  ⟨Quotient.mk'' default⟩

/--
Definition of `ConnectedComponents.functorToDiscrete` / `ConnectedComponents.functorToDiscrete` 的定义

English:
definition ConnectedComponents.functorToDiscrete
  signature: (X : Type*)
  body: Discrete.mk (f (Quotient.mk (Zigzag.setoid _) Y))
  map g := Discrete.eqToHom (congrArg f (Quotient.sound (Zigzag.of_hom g)))

中文:
定义 ConnectedComponents.functorToDiscrete
  签名: (X : 类型)
  定义体: Discrete.mk (f (Quotient.mk (Zigzag.setoid _) Y))
  map g := Discrete.eqToHom (congrArg f (Quotient.sound (Zigzag.of_hom g)))

Depends on / 依赖: Discrete, Discrete.mk, Quotient, Quotient.mk, Zigzag, Zigzag.setoid, setoid
-/
def ConnectedComponents.functorToDiscrete (X : Type*)
    (f : ConnectedComponents J -> X) : J ⥤ Discrete X where
  obj Y := Discrete.mk (f (Quotient.mk (Zigzag.setoid _) Y))
  map g := Discrete.eqToHom (congrArg f (Quotient.sound (Zigzag.of_hom g)))

/--
Definition of `ConnectedComponents.liftFunctor` / `ConnectedComponents.liftFunctor` 的定义

English:
definition ConnectedComponents.liftFunctor
  signature: (J) [Category* J] {X : Type*} (F : J ⥤ Discrete X)
  body: Quotient.lift (fun c => (F.obj c).as)
    (fun _ _ h => eq_of_zigzag X (zigzag_obj_of_zigzag F h))

中文:
定义 ConnectedComponents.liftFunctor
  签名: (J) [范畴* J] {X : 类型} (F : J ⥤ 离散 X)
  定义体: Quotient.lift (fun c => (F.obj c).as)
    (fun _ _ h => eq_of_zigzag X (zigzag_obj_of_zigzag F h))

Depends on / 依赖: F.obj, Quotient, Quotient.lift, eq_of_zigzag, zigzag_obj_of_zigzag
-/
def ConnectedComponents.liftFunctor (J) [Category* J] {X : Type*} (F : J ⥤ Discrete X) :
    (ConnectedComponents J -> X) :=
  Quotient.lift (fun c => (F.obj c).as)
    (fun _ _ h => eq_of_zigzag X (zigzag_obj_of_zigzag F h))

/--
Definition of `ConnectedComponents.typeToCatHomEquiv` / `ConnectedComponents.typeToCatHomEquiv` 的定义

English:
definition ConnectedComponents.typeToCatHomEquiv
  signature: (J) [Category* J] (X : Type*)
  body: ConnectedComponents.functorToDiscrete _
  invFun := ConnectedComponents.liftFunctor _
  left_inv f := funext fun x => by
    obtain ⟨x, h⟩ := Quotient.exists_rep x
    rw [← h]
    rfl
  right_inv fctr :=
    Functor.hext (fun _ => rfl) (fun c d f =>
      have : Subsingleton (fctr.obj c ⟶ fctr.obj 

中文:
定义 ConnectedComponents.typeToCatHomEquiv
  签名: (J) [范畴* J] (X : 类型)
  定义体: ConnectedComponents.functorToDiscrete _
  invFun := ConnectedComponents.liftFunctor _
  left_inv f := funext fun x => by
    obtain ⟨x, h⟩ := Quotient.exists_rep x
    rw [← h]
    rfl
  right_inv fctr :=
    Functor.hext (fun _ => rfl) (fun c d f =>
      have : Subsingleton (fctr.obj c ⟶ fctr.obj 

Depends on / 依赖: ConnectedComponents, ConnectedComponents.functorToDiscrete, functorToDiscrete
-/
def ConnectedComponents.typeToCatHomEquiv (J) [Category* J] (X : Type*) :
    (ConnectedComponents J -> X) ≃ (J ⥤ Discrete X) where
  toFun := ConnectedComponents.functorToDiscrete _
  invFun := ConnectedComponents.liftFunctor _
  left_inv f := funext fun x => by
    obtain ⟨x, h⟩ := Quotient.exists_rep x
    rw [← h]
    rfl
  right_inv fctr :=
    Functor.hext (fun _ => rfl) (fun c d f =>
      have : Subsingleton (fctr.obj c ⟶ fctr.obj d) := Discrete.instSubsingletonDiscreteHom _ _
      (Subsingleton.elim (fctr.map f) _).symm.heq)

/--
Definition of `ConnectedComponents.objectProperty` / `ConnectedComponents.objectProperty` 的定义

English:
definition ConnectedComponents.objectProperty
  signature: (j : ConnectedComponents J)
  body: fun k => Quotient.mk'' k = j

中文:
定义 ConnectedComponents.objectProperty
  签名: (j : ConnectedComponents J)
  定义体: fun k => Quotient.mk'' k = j

Depends on / 依赖: Quotient, Quotient.mk
-/
def ConnectedComponents.objectProperty (j : ConnectedComponents J) :
    ObjectProperty J := fun k => Quotient.mk'' k = j

/--
Definition of `ConnectedComponents.Component` / `ConnectedComponents.Component` 的定义

English:
abbreviation ConnectedComponents.Component
  signature: (j : ConnectedComponents J)
  body: j.objectProperty.FullSubcategory

中文:
缩写 ConnectedComponents.Component
  签名: (j : ConnectedComponents J)
  定义体: j.objectProperty.FullSubcategory

Depends on / 依赖: FullSubcategory, j.objectProperty.FullSubcategory, objectProperty
-/
abbrev ConnectedComponents.Component (j : ConnectedComponents J) : Type u₁ :=
  j.objectProperty.FullSubcategory

/--
Definition of `ConnectedComponents.ι` / `ConnectedComponents.ι` 的定义

English:
abbreviation ConnectedComponents.ι
  signature: (j : ConnectedComponents J)
  body: j.objectProperty.ι

中文:
缩写 ConnectedComponents.ι
  签名: (j : ConnectedComponents J)
  定义体: j.objectProperty.ι

Depends on / 依赖: j.objectProperty, objectProperty
-/
abbrev ConnectedComponents.ι (j : ConnectedComponents J) : j.Component ⥤ J := j.objectProperty.ι

/--
Definition of `ConnectedComponents.mk` / `ConnectedComponents.mk` 的定义

English:
abbreviation ConnectedComponents.mk
  signature: (j : J)
  body: Quotient.mk'' j

中文:
缩写 ConnectedComponents.mk
  签名: (j : J)
  定义体: Quotient.mk'' j

Depends on / 依赖: Quotient, Quotient.mk
-/
abbrev ConnectedComponents.mk (j : J) : ConnectedComponents J :=
  Quotient.mk'' j

/-- Each connected component of the category is nonempty. -/
instance (j : ConnectedComponents J) : Nonempty j.Component := by
  induction j using Quotient.inductionOn'
  exact ⟨⟨_, rfl⟩⟩

instance (j : ConnectedComponents J) : Inhabited j.Component :=
  Classical.inhabited_of_nonempty'

/-- Each connected component of the category is connected. -/
instance (j : ConnectedComponents J) : IsConnected j.Component := by
  -- Show it's connected by constructing a zigzag (in `j.Component`) between any two objects
  apply isConnected_of_zigzag
  rintro ⟨j₁, hj₁⟩ ⟨j₂, rfl⟩
  -- We know that the underlying objects j₁ j₂ have some zigzag between them in `J`
  have h₁₂ : Zigzag j₁ j₂ := Quotient.exact' hj₁
  -- Get an explicit zigzag as a list
  rcases List.exists_isChain_cons_of_relationReflTransGen h₁₂ with ⟨l, hl₁, hl₂⟩
  -- Everything which has a zigzag to j₂ can be lifted to the same component as `j₂`.
  let f : forall x, Zigzag x j₂ -> (ConnectedComponents.mk j₂).Component :=
    fun x h => ⟨x, Quotient.sound' h⟩
  -- Everything in our chosen zigzag from `j₁` to `j₂` has a zigzag to `j₂`.
  have hf : forall a : J, a in l -> Zigzag a j₂ := by
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

/--
Definition of `Decomposed` / `Decomposed` 的定义

English:
abbreviation Decomposed
  signature: (J : Type u₁) [Category.{v₁} J]
  body: Σ j : ConnectedComponents J, j.Component

中文:
缩写 Decomposed
  签名: (J : 类型u₁) [范畴.{v₁} J]
  定义体: Σ j : ConnectedComponents J, j.Component

Depends on / 依赖: Component, ConnectedComponents, j.Component
-/
abbrev Decomposed (J : Type u₁) [Category.{v₁} J] :=
  Σ j : ConnectedComponents J, j.Component

-- This name may cause clashes further down the road, and so might need to be changed.
/--
Definition of `inclusion` / `inclusion` 的定义

English:
abbreviation inclusion
  signature: (j : ConnectedComponents J)
  body: Sigma.incl _

中文:
缩写 inclusion
  签名: (j : ConnectedComponents J)
  定义体: Sigma.incl _

Depends on / 依赖: Sigma.incl
-/
abbrev inclusion (j : ConnectedComponents J) : j.Component ⥤ Decomposed J :=
  Sigma.incl _

/-- The forward direction of the equivalence between the decomposed category and the original. -/
@[simps!]
/--
Definition of `decomposedTo` / `decomposedTo` 的定义

English:
definition decomposedTo
  signature: (J : Type u₁) [Category.{v₁} J]
  body: Sigma.desc ConnectedComponents.ι

@[simp]

中文:
定义 decomposedTo
  签名: (J : 类型u₁) [范畴.{v₁} J]
  定义体: Sigma.desc ConnectedComponents.ι

@[simp]

Depends on / 依赖: ConnectedComponents, Sigma.desc
-/
def decomposedTo (J : Type u₁) [Category.{v₁} J] : Decomposed J ⥤ J :=
  Sigma.desc ConnectedComponents.ι

@[simp]
/--
theorem `inclusion_comp_decomposedTo` / 定理 `inclusion_comp_decomposedTo`

English:
theorem inclusion_comp_decomposedTo
  given: (j : ConnectedComponents J)
  proof: rfl

中文:
定理 inclusion_comp_decomposedTo
  条件: (j : ConnectedComponents J)
  证明: rfl
-/
theorem inclusion_comp_decomposedTo (j : ConnectedComponents J) :
    inclusion j ⋙ decomposedTo J = ConnectedComponents.ι j :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (decomposedTo J).Full
  body: by
    rintro ⟨j', X, hX⟩ ⟨k', Y, hY⟩ f
    dsimp at f
    have : j' = k' := by
      rw [← hX]; rw [← hY]; rw [Quotient.eq'']
      exact Relation.ReflTransGen.single (Or.inl ⟨f⟩)
    subst this
    exact ⟨Sigma.SigmaHom.mk (ObjectProperty.homMk f), rfl⟩

中文:
实例 :
  签名: (decomposedTo J).满
  定义体: by
    rintro ⟨j', X, hX⟩ ⟨k', Y, hY⟩ f
    dsimp at f
    have : j' = k' := by
      rw [← hX]; rw [← hY]; rw [Quotient.eq'']
      exact Relation.ReflTransGen.single (Or.inl ⟨f⟩)
    subst this
    exact ⟨Sigma.SigmaHom.mk (ObjectProperty.homMk f), rfl⟩

Depends on / 依赖: ObjectProperty, ObjectProperty.homMk, Or.inl, Quotient, Quotient.eq, ReflTransGen, Relation, Relation.ReflTransGen.single, Sigma.SigmaHom.mk, SigmaHom, single
-/
instance : (decomposedTo J).Full where
  map_surjective := by
    rintro ⟨j', X, hX⟩ ⟨k', Y, hY⟩ f
    dsimp at f
    have : j' = k' := by
      rw [← hX]; rw [← hY]; rw [Quotient.eq'']
      exact Relation.ReflTransGen.single (Or.inl ⟨f⟩)
    subst this
    exact ⟨Sigma.SigmaHom.mk (ObjectProperty.homMk f), rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (decomposedTo J).Faithful
  body: by
    rintro ⟨_, j, rfl⟩ ⟨_, k, hY⟩ ⟨⟨f⟩⟩ ⟨⟨_⟩⟩ rfl
    rfl

中文:
实例 :
  签名: (decomposedTo J).忠实
  定义体: by
    rintro ⟨_, j, rfl⟩ ⟨_, k, hY⟩ ⟨⟨f⟩⟩ ⟨⟨_⟩⟩ rfl
    rfl
-/
instance : (decomposedTo J).Faithful where
  map_injective := by
    rintro ⟨_, j, rfl⟩ ⟨_, k, hY⟩ ⟨⟨f⟩⟩ ⟨⟨_⟩⟩ rfl
    rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (decomposedTo J).EssSurj
  body: ⟨⟨_, j, rfl⟩, ⟨Iso.refl _⟩⟩

中文:
实例 :
  签名: (decomposedTo J).本质满射
  定义体: ⟨⟨_, j, rfl⟩, ⟨Iso.refl _⟩⟩

Depends on / 依赖: Iso.refl
-/
instance : (decomposedTo J).EssSurj where mem_essImage j := ⟨⟨_, j, rfl⟩, ⟨Iso.refl _⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (decomposedTo J).IsEquivalence

中文:
实例 :
  签名: (decomposedTo J).是等价
-/
instance : (decomposedTo J).IsEquivalence where

/-- This gives that any category is equivalent to a disjoint union of connected categories. -/
@[simps! functor]
/--
Definition of `decomposedEquiv` / `decomposedEquiv` 的定义

English:
definition decomposedEquiv
  signature: : Decomposed J ≌ J
  body: (decomposedTo J).asEquivalence

中文:
定义 decomposedEquiv
  签名: : Decomposed J ≌ J
  定义体: (decomposedTo J).asEquivalence

Depends on / 依赖: asEquivalence, decomposedTo
-/
def decomposedEquiv : Decomposed J ≌ J :=
  (decomposedTo J).asEquivalence

end CategoryTheory
