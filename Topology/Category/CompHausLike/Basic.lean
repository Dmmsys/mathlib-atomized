/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
module

public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
/-!

# Categories of Compact Hausdorff Spaces

We construct the category of compact Hausdorff spaces satisfying an additional property `P`.

## Implementation

We define a structure `CompHausLike` which takes as an argument a predicate `P` on topological
spaces. It consists of the data of a topological space, satisfying the additional properties of
being compact and Hausdorff, and satisfying `P`. We give a category structure to `CompHausLike P`
induced by the forgetful functor to topological spaces.

It used to be the case (before https://github.com/leanprover-community/mathlib4/pull/12930 was merged) that several different categories of compact
Hausdorff spaces, possibly satisfying some extra property, were defined from scratch in this way.
For example, one would define a structure `CompHaus` as follows:

```lean
structure CompHaus where
  toTop : TopCat
  [is_compact : CompactSpace toTop]
  [is_hausdorff : T2Space toTop]
```

and give it the category structure induced from topological spaces. Then the category of profinite
spaces was defined as follows:

```lean
structure Profinite where
  toCompHaus : CompHaus
  [isTotallyDisconnected : TotallyDisconnectedSpace toCompHaus]
```

The categories `Stonean` consisting of extremally disconnected compact Hausdorff spaces and
`LightProfinite` consisting of totally disconnected, second countable compact Hausdorff spaces were
defined in a similar way. This resulted in code duplication, and reducing this duplication was part
of the motivation for introducing `CompHausLike`.

Using `CompHausLike`, we can now define
`CompHaus := CompHausLike (fun _ ↦ True)`
`Profinite := CompHausLike (fun X ↦ TotallyDisconnectedSpace X)`.
`Stonean := CompHausLike (fun X ↦ ExtremallyDisconnected X)`.
`LightProfinite := CompHausLike (fun X ↦ TotallyDisconnectedSpace X ∧ SecondCountableTopology X)`.

These four categories are important building blocks of condensed objects (see the files
`Condensed.Basic` and `Condensed.Light.Basic`). These categories share many properties and often,
one wants to argue about several of them simultaneously. This is the other part of the motivation
for introducing `CompHausLike`. On paper, one would say "let `C` be on of the categories `CompHaus`
or `Profinite`, then the following holds: ...". This was not possible in Lean using the old
definitions. Using the new definitions, this becomes a matter of identifying what common property
of `CompHaus` and `Profinite` is used in the proof in question, and then proving the theorem for
`CompHausLike P` satisfying that property, and it will automatically apply to both `CompHaus` and
`Profinite`.
-/

@[expose] public section

universe u

open CategoryTheory

variable (P : TopCat.{u} -> Prop)

/--
Definition of `CompHausLike` / `CompHausLike` 的定义

English:
structure CompHausLike
  parameters: where
  axioms and operations (4):
    - toTop : TopCat
    - [is_compact : CompactSpace toTop]
    - [is_hausdorff : T2Space toTop]
    - prop : P toTop

中文:
结构 余mpHausLike
  参数: where
  公理与运算 (4 个):
    - toTop : 顶元素范畴
    - [is_compact : 紧空间 toTop]
    - [is_hausdorff : T2空间 toTop]
    - prop : P toTop
-/
structure CompHausLike where
  /-- The underlying topological space of an object of `CompHausLike P`. -/
  toTop : TopCat
  /-- The underlying topological space is compact. -/
  [is_compact : CompactSpace toTop]
  /-- The underlying topological space is T2. -/
  [is_hausdorff : T2Space toTop]
  /-- The underlying topological space satisfies P. -/
  prop : P toTop

namespace CompHausLike

attribute [instance] is_compact is_hausdorff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (CompHausLike P) (Type u)
  body: ⟨fun X => X.toTop⟩

中文:
实例 :
  签名: CoeSort (余mpHausLike P) (类型u)
  定义体: ⟨fun X => X.toTop⟩

Depends on / 依赖: X.toTop
-/
instance : CoeSort (CompHausLike P) (Type u) :=
  ⟨fun X => X.toTop⟩

/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : Category (CompHausLike P)
  body: inferInstanceAs Category (InducedCategory _ toTop)

中文:
实例 category
  签名: : 范畴 (余mpHausLike P)
  定义体: inferInstanceAs Category (InducedCategory _ toTop)

Depends on / 依赖: Category, InducedCategory
-/
instance category : Category (CompHausLike P) :=
inferInstanceAs Category (InducedCategory _ toTop)

/--
Instance `concreteCategory` / 实例 `concreteCategory`

English:
instance concreteCategory
  signature: : ConcreteCategory (CompHausLike P) (C(·, ·))
  body: inferInstanceAs ConcreteCategory (InducedCategory _ toTop) _

中文:
实例 concreteCategory
  签名: : 余ncrete范畴 (余mpHausLike P) (C(·, ·))
  定义体: inferInstanceAs ConcreteCategory (InducedCategory _ toTop) _

Depends on / 依赖: ConcreteCategory, InducedCategory
-/
instance concreteCategory : ConcreteCategory (CompHausLike P) (C(·, ·)) :=
inferInstanceAs ConcreteCategory (InducedCategory _ toTop) _

/--
Instance `hasForget₂` / 实例 `hasForget₂`

English:
instance hasForget₂
  signature: : HasForget₂ (CompHausLike P) TopCat
  body: inferInstanceAs HasForget₂ (InducedCategory _ toTop) _

中文:
实例 hasForget₂
  签名: : 有Forget₂ (余mpHausLike P) 顶元素范畴
  定义体: inferInstanceAs HasForget₂ (InducedCategory _ toTop) _

Depends on / 依赖: InducedCategory
-/
instance hasForget₂ : HasForget₂ (CompHausLike P) TopCat :=
inferInstanceAs HasForget₂ (InducedCategory _ toTop) _

variable (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/--
Definition of `HasProp` / `HasProp` 的定义

English:
class HasProp
  parameters: : Prop where
  axioms and operations (1):
    - hasProp : P (TopCat.of X)

中文:
类 有命题
  参数: : 命题 where
  公理与运算 (1 个):
    - hasProp : P (顶元素范畴.of X)
-/
class HasProp : Prop where
  hasProp : P (TopCat.of X)

instance (X : CompHausLike P) : HasProp P X := ⟨X.4⟩

variable [HasProp P X]

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: : CompHausLike P where
  body: TopCat.of X
  is_compact := ‹_›
  is_hausdorff := ‹_›
  prop := HasProp.hasProp

中文:
缩写 of
  签名: : 余mpHausLike P where
  定义体: TopCat.of X
  is_compact := ‹_›
  is_hausdorff := ‹_›
  prop := HasProp.hasProp

Depends on / 依赖: TopCat, TopCat.of
-/
abbrev of : CompHausLike P where
  toTop := TopCat.of X
  is_compact := ‹_›
  is_hausdorff := ‹_›
  prop := HasProp.hasProp

/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  statement: (CompHausLike.of P X : Type _) = X
  proof: rfl

@[simp]

中文:
定理 coe_of
  结论: (余mpHausLike.of P X : 类型 _) = X
  证明: rfl

@[simp]
-/
theorem coe_of : (CompHausLike.of P X : Type _) = X := rfl

@[simp]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  given: (X : CompHausLike P)
  statement: (𝟙 X : X -> X) = id
  proof: rfl

@[simp]

中文:
定理 coe_id
  条件: (X : 余mpHausLike P)
  结论: (𝟙 X : X -> X) = id
  证明: rfl

@[simp]
-/
theorem coe_id (X : CompHausLike P) : (𝟙 X : X -> X) = id :=
  rfl

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: {X Y Z : CompHausLike P} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
定理 coe_comp
  条件: {X Y Z : 余mpHausLike P} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
theorem coe_comp {X Y Z : CompHausLike P} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : X -> Z) = (g ∘ f) :=
  rfl

section

variable {X} {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [HasProp P Y]
variable {Z : Type u} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] [HasProp P Z]

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: (f : C(X, Y))
  body: ConcreteCategory.ofHom f

中文:
缩写 ofHom
  签名: (f : C(X, Y))
  定义体: ConcreteCategory.ofHom f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom (f : C(X, Y)) : of P X ⟶ of P Y := ConcreteCategory.ofHom f

/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: (f : C(X, Y))
  statement: ConcreteCategory.hom (ofHom P f) = f
  proof: rfl

中文:
引理 hom_ofHom
  条件: (f : C(X, Y))
  结论: 余ncrete范畴.hom (ofHom P f) = f
  证明: rfl
-/
@[simp] lemma hom_ofHom (f : C(X, Y)) : ConcreteCategory.hom (ofHom P f) = f := rfl

/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  statement: ofHom P (ContinuousMap.id X) = 𝟙 (of _ X)
  proof: rfl

中文:
引理 ofHom_id
  结论: ofHom P (连续映射.id X) = 𝟙 (of _ X)
  证明: rfl
-/
@[simp] lemma ofHom_id : ofHom P (ContinuousMap.id X) = 𝟙 (of _ X) := rfl

/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  given: (f : C(X, Y)) (g : C(Y, Z))
  proof: rfl

中文:
引理 ofHom_comp
  条件: (f : C(X, Y)) (g : C(Y, Z))
  证明: rfl
-/
@[simp] lemma ofHom_comp (f : C(X, Y)) (g : C(Y, Z)) :
    ofHom P (g.comp f) = ofHom _ f ≫ ofHom _ g := rfl

end

variable {P}

/-- If `P` implies `P'`, then there is a functor from `CompHausLike P` to `CompHausLike P'`. -/
@[simps map]
/--
Definition of `toCompHausLike` / `toCompHausLike` 的定义

English:
definition toCompHausLike
  signature: {P P' : TopCat -> Prop} (h : forall (X : CompHausLike P), P X.toTop -> P' X.toTop)
  body: haveI : HasProp P' X := ⟨(h _ X.prop)⟩
    CompHausLike.of _ X
  map {X Y} f := ConcreteCategory.ofHom f.hom.hom

中文:
定义 toCompHausLike
  签名: {P P' : 顶元素范畴 -> 命题} (h : 对任意 (X : 余mpHausLike P), P X.toTop -> P' X.toTop)
  定义体: haveI : HasProp P' X := ⟨(h _ X.prop)⟩
    CompHausLike.of _ X
  map {X Y} f := ConcreteCategory.ofHom f.hom.hom

Depends on / 依赖: CompHausLike, CompHausLike.of, ConcreteCategory, ConcreteCategory.ofHom, HasProp, X.prop, f.hom.hom
-/
def toCompHausLike {P P' : TopCat -> Prop} (h : forall (X : CompHausLike P), P X.toTop -> P' X.toTop) :
    CompHausLike P ⥤ CompHausLike P' where
  obj X :=
    haveI : HasProp P' X := ⟨(h _ X.prop)⟩
    CompHausLike.of _ X
  map {X Y} f := ConcreteCategory.ofHom f.hom.hom

section

variable {P P' : TopCat -> Prop} (h : forall (X : CompHausLike P), P X.toTop -> P' X.toTop)

/--
Definition of `fullyFaithfulToCompHausLike` / `fullyFaithfulToCompHausLike` 的定义

English:
definition fullyFaithfulToCompHausLike
  signature: : (toCompHausLike h).FullyFaithful where
  body: ConcreteCategory.ofHom f.hom.hom

中文:
定义 fullyFaithfulToCompHausLike
  签名: : (toCompHausLike h).满忠实 where
  定义体: ConcreteCategory.ofHom f.hom.hom

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, f.hom.hom
-/
def fullyFaithfulToCompHausLike : (toCompHausLike h).FullyFaithful where
  preimage f := ConcreteCategory.ofHom f.hom.hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toCompHausLike h).Full
  body: (fullyFaithfulToCompHausLike h).full

中文:
实例 :
  签名: (toCompHausLike h).满
  定义体: (fullyFaithfulToCompHausLike h).full

Depends on / 依赖: fullyFaithfulToCompHausLike
-/
instance : (toCompHausLike h).Full := (fullyFaithfulToCompHausLike h).full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toCompHausLike h).Faithful
  body: (fullyFaithfulToCompHausLike h).faithful

中文:
实例 :
  签名: (toCompHausLike h).忠实
  定义体: (fullyFaithfulToCompHausLike h).faithful

Depends on / 依赖: faithful, fullyFaithfulToCompHausLike
-/
instance : (toCompHausLike h).Faithful := (fullyFaithfulToCompHausLike h).faithful

end

variable (P)

/-- The fully faithful embedding of `CompHausLike P` in `TopCat`. -/
@[simps! map]
/--
Definition of `compHausLikeToTop` / `compHausLikeToTop` 的定义

English:
definition compHausLikeToTop
  signature: : CompHausLike.{u} P ⥤ TopCat.{u}
  body: inducedFunctor _

中文:
定义 compHausLikeToTop
  签名: : 余mpHausLike.{u} P ⥤ 顶元素范畴.{u}
  定义体: inducedFunctor _

Depends on / 依赖: inducedFunctor
-/
def compHausLikeToTop : CompHausLike.{u} P ⥤ TopCat.{u} :=
  inducedFunctor _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

example {P P' : TopCat -> Prop} (h : forall (X : CompHausLike P), P X.toTop -> P' X.toTop) :
    toCompHausLike h ⋙ compHausLikeToTop P' = compHausLikeToTop P := rfl

/--
Definition of `fullyFaithfulCompHausLikeToTop` / `fullyFaithfulCompHausLikeToTop` 的定义

English:
definition fullyFaithfulCompHausLikeToTop
  signature: : (compHausLikeToTop P).FullyFaithful
  body: fullyFaithfulInducedFunctor _

中文:
定义 fullyFaithfulCompHausLikeToTop
  签名: : (compHausLikeToTop P).满忠实
  定义体: fullyFaithfulInducedFunctor _

Depends on / 依赖: fullyFaithfulInducedFunctor
-/
def fullyFaithfulCompHausLikeToTop : (compHausLikeToTop P).FullyFaithful :=
  fullyFaithfulInducedFunctor _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (compHausLikeToTop P).Full
  body: inferInstanceAs (inducedFunctor _).Full

中文:
实例 :
  签名: (compHausLikeToTop P).满
  定义体: inferInstanceAs (inducedFunctor _).Full

Depends on / 依赖: inducedFunctor
-/
instance : (compHausLikeToTop P).Full :=
  inferInstanceAs (inducedFunctor _).Full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (compHausLikeToTop P).Faithful
  body: inferInstanceAs (inducedFunctor _).Faithful

中文:
实例 :
  签名: (compHausLikeToTop P).忠实
  定义体: inferInstanceAs (inducedFunctor _).Faithful

Depends on / 依赖: Faithful, inducedFunctor
-/
instance : (compHausLikeToTop P).Faithful :=
  inferInstanceAs (inducedFunctor _).Faithful

instance (X : CompHausLike P) : CompactSpace ((compHausLikeToTop P).obj X) :=
  inferInstanceAs (CompactSpace X.toTop)

instance (X : CompHausLike P) : T2Space ((compHausLikeToTop P).obj X) :=
  inferInstanceAs (T2Space X.toTop)

variable {P}

/--
theorem `epi_of_surjective` / 定理 `epi_of_surjective`

English:
theorem epi_of_surjective
  given: {X Y : CompHausLike.{u} P} (f : X ⟶ Y) (hf : Function.Surjective f)
  proof: by
  rw [← CategoryTheory.ofHom_epi_iff_surjective] at hf
  exact (forget (CompHausLike P)).epi_of_epi_map hf

中文:
定理 epi_of_surjective
  条件: {X Y : 余mpHausLike.{u} P} (f : X ⟶ Y) (hf : 函数.满射 f)
  证明: by
  rw [← CategoryTheory.ofHom_epi_iff_surjective] at hf
  exact (forget (CompHausLike P)).epi_of_epi_map hf

Depends on / 依赖: CategoryTheory, CategoryTheory.ofHom_epi_iff_surjective, CompHausLike, epi_of_epi_map, forget, ofHom_epi_iff_surjective
-/
theorem epi_of_surjective {X Y : CompHausLike.{u} P} (f : X ⟶ Y) (hf : Function.Surjective f) :
    Epi f := by
  rw [← CategoryTheory.ofHom_epi_iff_surjective] at hf
  exact (forget (CompHausLike P)).epi_of_epi_map hf

/--
theorem `mono_iff_injective` / 定理 `mono_iff_injective`

English:
theorem mono_iff_injective
  given: {X Y : CompHausLike.{u} P} (f : X ⟶ Y)
  proof: by
  constructor
  · intro hf x₁ x₂ h
    let g₁ : X ⟶ X := ofHom _ ⟨fun _ => x₁, continuous_const⟩
    let g₂ : X ⟶ X := ofHom _ ⟨fun _ => x₂, continuous_const⟩
    have : g₁ ≫ f = g₂ ≫ f := by ext; exact h
    exact CategoryTheory.congr_fun ((cancel_mono _).mp this) x₁
  · rw [← CategoryTheory.ofHom_mono_iff_injective]
    apply (forget (CompHausLike P)).mono_of_mono_map

中文:
定理 mono_iff_injective
  条件: {X Y : 余mpHausLike.{u} P} (f : X ⟶ Y)
  证明: by
  constructor
  · intro hf x₁ x₂ h
    let g₁ : X ⟶ X := ofHom _ ⟨fun _ => x₁, continuous_const⟩
    let g₂ : X ⟶ X := ofHom _ ⟨fun _ => x₂, continuous_const⟩
    have : g₁ ≫ f = g₂ ≫ f := by ext; exact h
    exact CategoryTheory.congr_fun ((cancel_mono _).mp this) x₁
  · rw [← CategoryTheory.ofHom_mono_iff_injective]
    apply (forget (CompHausLike P)).mono_of_mono_map

Depends on / 依赖: CategoryTheory, CategoryTheory.congr_fun, CategoryTheory.ofHom_mono_iff_injective, CompHausLike, cancel_mono, congr_fun, continuous_const, forget, mono_of_mono_map, ofHom_mono_iff_injective
-/
theorem mono_iff_injective {X Y : CompHausLike.{u} P} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective f := by
  constructor
  · intro hf x₁ x₂ h
    let g₁ : X ⟶ X := ofHom _ ⟨fun _ => x₁, continuous_const⟩
    let g₂ : X ⟶ X := ofHom _ ⟨fun _ => x₂, continuous_const⟩
    have : g₁ ≫ f = g₂ ≫ f := by ext; exact h
    exact CategoryTheory.congr_fun ((cancel_mono _).mp this) x₁
  · rw [← CategoryTheory.ofHom_mono_iff_injective]
    apply (forget (CompHausLike P)).mono_of_mono_map

/--
theorem `isClosedMap` / 定理 `isClosedMap`

English:
theorem isClosedMap
  given: {X Y : CompHausLike.{u} P} (f : X ⟶ Y)
  statement: IsClosedMap f
  proof: fun _ hC =>
  (hC.isCompact.image f.hom.hom.continuous).isClosed

中文:
定理 isClosedMap
  条件: {X Y : 余mpHausLike.{u} P} (f : X ⟶ Y)
  结论: 是闭映射 f
  证明: fun _ hC =>
  (hC.isCompact.image f.hom.hom.continuous).isClosed
-/
theorem isClosedMap {X Y : CompHausLike.{u} P} (f : X ⟶ Y) : IsClosedMap f := fun _ hC =>
  (hC.isCompact.image f.hom.hom.continuous).isClosed

/--
theorem `isIso_of_bijective` / 定理 `isIso_of_bijective`

English:
theorem isIso_of_bijective
  given: {X Y : CompHausLike.{u} P} (f : X ⟶ Y) (bij : Function.Bijective f)
  proof: by
  let E := Equiv.ofBijective _ bij
  have hE : Continuous E.symm := by
    rw [continuous_iff_isClosed]
    intro S hS
    rw [← E.image_eq_preimage_symm]
    exact isClosedMap f S hS
  refine ⟨⟨ofHom _ ⟨E.symm, hE⟩, ?_, ?_⟩⟩
  · ext x
    apply E.symm_apply_apply
  · ext x
    apply E.apply_symm_apply

中文:
定理 isIso_of_bijective
  条件: {X Y : 余mpHausLike.{u} P} (f : X ⟶ Y) (bij : 函数.双射 f)
  证明: by
  let E := Equiv.ofBijective _ bij
  have hE : Continuous E.symm := by
    rw [continuous_iff_isClosed]
    intro S hS
    rw [← E.image_eq_preimage_symm]
    exact isClosedMap f S hS
  refine ⟨⟨ofHom _ ⟨E.symm, hE⟩, ?_, ?_⟩⟩
  · ext x
    apply E.symm_apply_apply
  · ext x
    apply E.apply_symm_apply

Depends on / 依赖: Continuous, E.apply_symm_apply, E.image_eq_preimage_symm, E.symm, E.symm_apply_apply, Equiv.ofBijective, apply_symm_apply, continuous_iff_isClosed, image_eq_preimage_symm, isClosedMap, ofBijective, symm_apply_apply
-/
theorem isIso_of_bijective {X Y : CompHausLike.{u} P} (f : X ⟶ Y) (bij : Function.Bijective f) :
    IsIso f := by
  let E := Equiv.ofBijective _ bij
  have hE : Continuous E.symm := by
    rw [continuous_iff_isClosed]
    intro S hS
    rw [← E.image_eq_preimage_symm]
    exact isClosedMap f S hS
  refine ⟨⟨ofHom _ ⟨E.symm, hE⟩, ?_, ?_⟩⟩
  · ext x
    apply E.symm_apply_apply
  · ext x
    apply E.apply_symm_apply

/--
Instance `forget_reflectsIsomorphisms` / 实例 `forget_reflectsIsomorphisms`

English:
instance forget_reflectsIsomorphisms
  signature: :
  body: ⟨by intro A B f hf; rw [isIso_iff_bijective] at hf; exact isIso_of_bijective _ hf⟩

中文:
实例 forget_reflectsIsomorphisms
  签名: :
  定义体: ⟨by intro A B f hf; rw [isIso_iff_bijective] at hf; exact isIso_of_bijective _ hf⟩

Depends on / 依赖: isIso_iff_bijective, isIso_of_bijective
-/
instance forget_reflectsIsomorphisms :
    (forget (CompHausLike.{u} P)).ReflectsIsomorphisms :=
  ⟨by intro A B f hf; rw [isIso_iff_bijective] at hf; exact isIso_of_bijective _ hf⟩

/--
Definition of `isoOfBijective` / `isoOfBijective` 的定义

English:
definition isoOfBijective
  signature: {X Y : CompHausLike.{u} P} (f : X ⟶ Y)
  body: letI := isIso_of_bijective _ bij
  asIso f

中文:
定义 isoOfBijective
  签名: {X Y : 余mpHausLike.{u} P} (f : X ⟶ Y)
  定义体: letI := isIso_of_bijective _ bij
  asIso f

Depends on / 依赖: isIso_of_bijective
-/
noncomputable def isoOfBijective {X Y : CompHausLike.{u} P} (f : X ⟶ Y)
    (bij : Function.Bijective f) : X ≅ Y :=
  letI := isIso_of_bijective _ bij
  asIso f

/-- Construct an isomorphism from a homeomorphism. -/
@[simps!]
/--
Definition of `isoOfHomeo` / `isoOfHomeo` 的定义

English:
definition isoOfHomeo
  signature: {X Y : CompHausLike.{u} P} (f : X ≃ₜ Y)
  body: (fullyFaithfulCompHausLikeToTop P).preimageIso (TopCat.isoOfHomeo f)

中文:
定义 isoOfHomeo
  签名: {X Y : 余mpHausLike.{u} P} (f : X ≃ₜ Y)
  定义体: (fullyFaithfulCompHausLikeToTop P).preimageIso (TopCat.isoOfHomeo f)

Depends on / 依赖: TopCat, TopCat.isoOfHomeo, fullyFaithfulCompHausLikeToTop, isoOfHomeo, preimageIso
-/
def isoOfHomeo {X Y : CompHausLike.{u} P} (f : X ≃ₜ Y) : X ≅ Y :=
  (fullyFaithfulCompHausLikeToTop P).preimageIso (TopCat.isoOfHomeo f)

/-- Construct a homeomorphism from an isomorphism. -/
@[simps!]
/--
Definition of `homeoOfIso` / `homeoOfIso` 的定义

English:
definition homeoOfIso
  signature: {X Y : CompHausLike.{u} P} (f : X ≅ Y)
  body: TopCat.homeoOfIso (compHausLikeToTop P).mapIso f

中文:
定义 homeoOfIso
  签名: {X Y : 余mpHausLike.{u} P} (f : X ≅ Y)
  定义体: TopCat.homeoOfIso (compHausLikeToTop P).mapIso f

Depends on / 依赖: TopCat, TopCat.homeoOfIso, compHausLikeToTop, homeoOfIso, mapIso
-/
def homeoOfIso {X Y : CompHausLike.{u} P} (f : X ≅ Y) : X ≃ₜ Y :=
TopCat.homeoOfIso (compHausLikeToTop P).mapIso f

/-- The equivalence between isomorphisms in `CompHaus` and homeomorphisms
of topological spaces. -/
@[simps]
/--
Definition of `isoEquivHomeo` / `isoEquivHomeo` 的定义

English:
definition isoEquivHomeo
  signature: {X Y : CompHausLike.{u} P}
  body: homeoOfIso
  invFun := isoOfHomeo

中文:
定义 isoEquivHomeo
  签名: {X Y : 余mpHausLike.{u} P}
  定义体: homeoOfIso
  invFun := isoOfHomeo

Depends on / 依赖: homeoOfIso
-/
def isoEquivHomeo {X Y : CompHausLike.{u} P} : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: {P : TopCat.{u} -> Prop}
  body: ofHom _ (ContinuousMap.const _ s)

中文:
定义 const
  签名: {P : 顶元素范畴.{u} -> 命题}
  定义体: ofHom _ (ContinuousMap.const _ s)

Depends on / 依赖: ContinuousMap, ContinuousMap.const
-/
def const {P : TopCat.{u} -> Prop}
    (T : CompHausLike.{u} P) {S : CompHausLike.{u} P} (s : S) : T ⟶ S :=
  ofHom _ (ContinuousMap.const _ s)

/--
lemma `const_comp` / 引理 `const_comp`

English:
lemma const_comp
  statement: {P : TopCat.{u} -> Prop} {S T U : CompHausLike.{u} P}
  proof: rfl

中文:
引理 const_comp
  结论: {P : 顶元素范畴.{u} -> 命题} {S T U : 余mpHausLike.{u} P}
  证明: rfl
-/
lemma const_comp {P : TopCat.{u} -> Prop} {S T U : CompHausLike.{u} P}
    (s : S) (g : S ⟶ U) : T.const s ≫ g = T.const (g s) :=
  rfl

end CompHausLike
