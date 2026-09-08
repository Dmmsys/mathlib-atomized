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
`LightProfinite := CompHausLike  (fun X ↦ TotallyDisconnectedSpace X ∧ SecondCountableTopology X)`.

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

variable (P : TopCat.{u} → Prop)

/-- The type of Compact Hausdorff topological spaces satisfying an additional property `P`. -/
/-
**CompHausLike** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(TopCat → Prop) → Type (u + 1)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of Compact Hausdorff topological spaces satisfying an additional proper
ty `P`.
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

/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (CompHausLike P) (Type u) :=
  ⟨fun X => X.toTop⟩
/-
**CompHausLike.category** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
形式化陈述：category : Category (CompHausLike P)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance category : Category (CompHausLike P) :=
  inferInstanceAs <| Category (InducedCategory _ toTop)
/-
**CompHausLike.concreteCategory** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
形式化陈述：concreteCategory : ConcreteCategory (CompHausLike P) (C(·, ·))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance concreteCategory : ConcreteCategory (CompHausLike P) (C(·, ·)) :=
  inferInstanceAs <| ConcreteCategory (InducedCategory _ toTop) _
/-
**CompHausLike.hasForget** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForget₂ : HasForget₂ (CompHausLike P) TopCat :=
  inferInstanceAs <| HasForget₂ (InducedCategory _ toTop) _

variable (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- This wraps the predicate `P : TopCat → Prop` in a typeclass. -/
/-
**CompHausLike.HasProp** 是 Mathlib 中的一个归纳类型，位于命名空间 `CompHausLike`。
形式化陈述：(TopCat → Prop) → (X : Type u) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This wraps the predicate `P : TopCat → Prop` in a typeclass.
-/
class HasProp : Prop where
  hasProp : P (TopCat.of X)
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : CompHausLike P) : HasProp P X := ⟨X.4⟩

variable [HasProp P X]

/-- A constructor for objects of the category `CompHausLike P`,
taking a type, and bundling the compact Hausdorff topology
found by typeclass inference. -/
/-
**CompHausLike.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `CompHausLike`。
形式化陈述：of : CompHausLike P where toTop
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.HasProp.hasProp`：∀ {P : TopCat → Prop} {X : Type u} {inst :
 TopologicalSpace X} [self : CompHausLike.HasProp P X], P (TopCat.of X)

--- 原说明 ---
A constructor for objects of the category `CompHausLike P`,
taking a type, and bundling the compact Hausdorff topology
found by typeclass inference.
-/
abbrev of : CompHausLike P where
  toTop := TopCat.of X
  is_compact := ‹_›
  is_hausdorff := ‹_›
  prop := HasProp.hasProp
/-
**CompHausLike.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `CompHausLike`。
形式化陈述：coe_of : (CompHausLike.of P X : Type _) = X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of : (CompHausLike.of P X : Type _) = X := rfl

@[simp]
/-
**CompHausLike.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `CompHausLike`。
形式化陈述：coe_id (X : CompHausLike P) : (𝟙 X : X -> X) = id
参数：X : CompHausLike P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id (X : CompHausLike P) : (𝟙 X : X → X) = id :=
  rfl

@[simp]
/-
**CompHausLike.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `CompHausLike`。
形式化陈述：coe_comp {X Y Z : CompHausLike P} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X -> 
Z) = (g ∘ f)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp {X Y Z : CompHausLike P} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : X → Z) = (g ∘ f) :=
  rfl

section

variable {X} {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [HasProp P Y]
variable {Z : Type u} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] [HasProp P Z]

/-- Typecheck a continuous map as a morphism in the category `CompHausLike P`. -/
/-
**CompHausLike.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CompHausLike`。
形式化陈述：ofHom (f : C(X, Y)) : of P X ⟶ of P Y
参数：f : C(X, Y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a continuous map as a morphism in the category `CompHausLike P`.
-/
abbrev ofHom (f : C(X, Y)) : of P X ⟶ of P Y := ConcreteCategory.ofHom f
/-
**CompHausLike.hom_ofHom** 是 Mathlib 中的一个定理，位于命名空间 `CompHausLike`。
形式化陈述：∀ (P : TopCat → Prop) {X : Type u} [inst : TopologicalSpace X] [inst_1 : C
ompactSpace X] [inst_2 : T2Space X]   [inst_3 : CompHausLike.HasProp P X] {Y : T
ype u} [inst_4 : TopologicalSpace Y] [inst_5 : CompactSpace Y]   [inst_6 : T2Spa
ce Y] [inst_7 : CompHausLike.HasProp P Y] (f : C(X, Y)),   CategoryTheory.Concre
teCategory.hom (CompHausLike.ofHom P f) = f
参数：P : TopCat → Prop；f : C(X, Y)；CompHausLike.ofHom P f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_ofHom (f : C(X, Y)) : ConcreteCategory.hom (ofHom P f) = f := rfl
/-
**CompHausLike.ofHom_id** 是 Mathlib 中的一个定理，位于命名空间 `CompHausLike`。
形式化陈述：∀ (P : TopCat → Prop) {X : Type u} [inst : TopologicalSpace X] [inst_1 : C
ompactSpace X] [inst_2 : T2Space X]   [inst_3 : CompHausLike.HasProp P X],   Com
pHausLike.ofHom P (ContinuousMap.id X) = CategoryTheory.CategoryStruct.id (CompH
ausLike.of P X)
参数：P : TopCat → Prop；ContinuousMap.id X；CompHausLike.of P X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofHom_id : ofHom P (ContinuousMap.id X) = 𝟙 (of _ X) := rfl
/-
**CompHausLike.ofHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `CompHausLike`。
形式化陈述：∀ (P : TopCat → Prop) {X : Type u} [inst : TopologicalSpace X] [inst_1 : C
ompactSpace X] [inst_2 : T2Space X]   [inst_3 : CompHausLike.HasProp P X] {Y : T
ype u} [inst_4 : TopologicalSpace Y] [inst_5 : CompactSpace Y]   [inst_6 : T2Spa
ce Y] [inst_7 : CompHausLike.HasProp P Y] {Z : Type u} [inst_8 : TopologicalSpac
e Z]   [inst_9 : CompactSpace Z] [inst_10 : T2Space Z] [inst_11 : CompHausLike.H
asProp P Z] (f : C(X, Y)) (g : C(Y, Z)),   CompHausLike.ofHom P (g.comp f) = Cat
egoryTheory.CategoryStruct.comp (CompHausLike.ofHom P f) (CompHausLike.ofHom P g
)
参数：P : TopCat → Prop；f : C(X, Y)；g : C(Y, Z)；g.comp f；CompHausLike.ofHom P f；Com
pHausLike.ofHom P g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofHom_comp (f : C(X, Y)) (g : C(Y, Z)) :
    ofHom P (g.comp f) = ofHom _ f ≫ ofHom _ g := rfl

end

variable {P}

/-- If `P` implies `P'`, then there is a functor from `CompHausLike P` to `CompHausLike P'`. -/
@[simps map]
/-
**CompHausLike.toCompHausLike** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike`。
形式化陈述：toCompHausLike {P P' : TopCat -> Prop} (h : forall (X : CompHausLike P), P
 X.toTop -> P' X.toTop) : CompHausLike P ⥤ CompHausLike P' where obj X
参数：h : forall (X : CompHausLike P), P X.toTop -> P' X.toTop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop

--- 原说明 ---
If `P` implies `P'`, then there is a functor from `CompHausLike P` to `CompHausL
ike P'`.
-/
def toCompHausLike {P P' : TopCat → Prop} (h : ∀ (X : CompHausLike P), P X.toTop → P' X.toTop) :
    CompHausLike P ⥤ CompHausLike P' where
  obj X :=
    haveI : HasProp P' X := ⟨(h _ X.prop)⟩
    CompHausLike.of _ X
  map {X Y} f := ConcreteCategory.ofHom f.hom.hom

section

variable {P P' : TopCat → Prop} (h : ∀ (X : CompHausLike P), P X.toTop → P' X.toTop)

/-- If `P` implies `P'`, then the functor from `CompHausLike P` to `CompHausLike P'` is fully
faithful. -/
/-
**CompHausLike.fullyFaithfulToCompHausLike** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLi
ke`。
形式化陈述：fullyFaithfulToCompHausLike : (toCompHausLike h).FullyFaithful where preim
age f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` implies `P'`, then the functor from `CompHausLike P` to `CompHausLike P'`
 is fully
faithful.
-/
def fullyFaithfulToCompHausLike : (toCompHausLike h).FullyFaithful where
  preimage f := ConcreteCategory.ofHom f.hom.hom
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toCompHausLike h).Full := (fullyFaithfulToCompHausLike h).full
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toCompHausLike h).Faithful := (fullyFaithfulToCompHausLike h).faithful

end

variable (P)

/-- The fully faithful embedding of `CompHausLike P` in `TopCat`. -/
@[simps! map]
/-
**CompHausLike.compHausLikeToTop** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike`。
形式化陈述：compHausLikeToTop : CompHausLike.{u} P ⥤ TopCat.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fully faithful embedding of `CompHausLike P` in `TopCat`.
-/
def compHausLikeToTop : CompHausLike.{u} P ⥤ TopCat.{u} :=
  inducedFunctor _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380
/-
**CompHausLike.** 是 Mathlib 中的一个示例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {P P' : TopCat → Prop} (h : ∀ (X : CompHausLike P), P X.toTop → P' X.toTop) :
    toCompHausLike h ⋙ compHausLikeToTop P' = compHausLikeToTop P := rfl

/-- The functor from `CompHausLike P` to `TopCat` is fully faithful. -/
/-
**CompHausLike.fullyFaithfulCompHausLikeToTop** 是 Mathlib 中的一个定义，位于命名空间 `CompHau
sLike`。
形式化陈述：fullyFaithfulCompHausLikeToTop : (compHausLikeToTop P).FullyFaithful
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from `CompHausLike P` to `TopCat` is fully faithful.
-/
def fullyFaithfulCompHausLikeToTop : (compHausLikeToTop P).FullyFaithful :=
  fullyFaithfulInducedFunctor _
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (compHausLikeToTop P).Full :=
  inferInstanceAs (inducedFunctor _).Full
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (compHausLikeToTop P).Faithful :=
  inferInstanceAs (inducedFunctor _).Faithful
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : CompHausLike P) : CompactSpace ((compHausLikeToTop P).obj X) :=
  inferInstanceAs (CompactSpace X.toTop)
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : CompHausLike P) : T2Space ((compHausLikeToTop P).obj X) :=
  inferInstanceAs (T2Space X.toTop)

variable {P}
/-
**CompHausLike.epi_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `CompHausLike`。
形式化陈述：epi_of_surjective {X Y : CompHausLike.{u} P} (f : X ⟶ Y) (hf : Function.Su
rjective f) : Epi f
参数：f : X ⟶ Y；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ofHom_epi_iff_surjective`：ofHom_epi_iff_surjective {X Y :
 Type u} (f : X -> Y) : Epi (ofHom f) ↔ Function.Surjective f
-/
theorem epi_of_surjective {X Y : CompHausLike.{u} P} (f : X ⟶ Y) (hf : Function.Surjective f) :
    Epi f := by
  rw [← CategoryTheory.ofHom_epi_iff_surjective] at hf
  exact (forget (CompHausLike P)).epi_of_epi_map hf
/-
**CompHausLike.mono_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 `CompHausLike`。
形式化陈述：mono_iff_injective {X Y : CompHausLike.{u} P} (f : X ⟶ Y) : Mono f ↔ Funct
ion.Injective f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `CompHausLike.instHasPropCarrierToTop`：∀ (P : TopCat → Prop) (X : CompHau
sLike P), CompHausLike.HasProp P ↑X.toTop
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `CategoryTheory.congr_fun`：∀ {C : Type u_1} [inst : CategoryTheory.Catego
ry.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C → Type w
)} [inst_1 : o…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ofHom_mono_iff_injective`：ofHom_mono_iff_injective {X Y :
 Type u} (f : X -> Y) : Mono (ofHom f) ↔ Function.Injective f
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
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

/-- Any continuous function on compact Hausdorff spaces is a closed map. -/
/-
**CompHausLike.isClosedMap** 是 Mathlib 中的一个定理，位于命名空间 `CompHausLike`。
形式化陈述：isClosedMap {X Y : CompHausLike.{u} P} (f : X ⟶ Y) : IsClosedMap f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f

--- 原说明 ---
Any continuous function on compact Hausdorff spaces is a closed map.
-/
theorem isClosedMap {X Y : CompHausLike.{u} P} (f : X ⟶ Y) : IsClosedMap f := fun _ hC =>
  (hC.isCompact.image f.hom.hom.continuous).isClosed

/-- Any continuous bijection of compact Hausdorff spaces is an isomorphism. -/
/-
**CompHausLike.isIso_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `CompHausLike`。
形式化陈述：isIso_of_bijective {X Y : CompHausLike.{u} P} (f : X ⟶ Y) (bij : Function.
Bijective f) : IsIso f
参数：f : X ⟶ Y；bij : Function.Bijective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_isClosed`：continuous_iff_isClosed : Continuous f ↔ forall
 s, IsClosed s -> IsClosed (f ⁻¹' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
· 使用定理 `CompHausLike.isClosedMap`：isClosedMap {X Y : CompHausLike.{u} P} (f : X 
⟶ Y) : IsClosedMap f
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `CompHausLike.instHasPropCarrierToTop`：∀ (P : TopCat → Prop) (X : CompHau
sLike P), CompHausLike.HasProp P ↑X.toTop
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x

--- 原说明 ---
Any continuous bijection of compact Hausdorff spaces is an isomorphism.
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
/-
**CompHausLike.forget_reflectsIsomorphisms** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLi
ke`。
形式化陈述：forget_reflectsIsomorphisms : (forget (CompHausLike.{u} P)).ReflectsIsomor
phisms
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.isIso_of_bijective`：isIso_of_bijective {X Y : CompHausLike.
{u} P} (f : X ⟶ Y) (bij : Function.Bijective f) : IsIso f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.isIso_iff_bijective`：isIso_iff_bijective {X Y : Type u} (
f : X ⟶ Y) : IsIso f ↔ Function.Bijective f
-/
instance forget_reflectsIsomorphisms :
    (forget (CompHausLike.{u} P)).ReflectsIsomorphisms :=
  ⟨by intro A B f hf; rw [isIso_iff_bijective] at hf; exact isIso_of_bijective _ hf⟩

/-- Any continuous bijection of compact Hausdorff spaces induces an isomorphism. -/
/-
**CompHausLike.isoOfBijective** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike`。
形式化陈述：isoOfBijective {X Y : CompHausLike.{u} P} (f : X ⟶ Y) (bij : Function.Bije
ctive f) : X ≅ Y
参数：f : X ⟶ Y；bij : Function.Bijective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.isIso_of_bijective`：isIso_of_bijective {X Y : CompHausLike.
{u} P} (f : X ⟶ Y) (bij : Function.Bijective f) : IsIso f

--- 原说明 ---
Any continuous bijection of compact Hausdorff spaces induces an isomorphism.
-/
noncomputable def isoOfBijective {X Y : CompHausLike.{u} P} (f : X ⟶ Y)
    (bij : Function.Bijective f) : X ≅ Y :=
  letI := isIso_of_bijective _ bij
  asIso f

/-- Construct an isomorphism from a homeomorphism. -/
@[simps!]
/-
**CompHausLike.isoOfHomeo** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike`。
形式化陈述：isoOfHomeo {X Y : CompHausLike.{u} P} (f : X ≃ₜ Y) : X ≅ Y
参数：f : X ≃ₜ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism from a homeomorphism.
-/
def isoOfHomeo {X Y : CompHausLike.{u} P} (f : X ≃ₜ Y) : X ≅ Y :=
  (fullyFaithfulCompHausLikeToTop P).preimageIso (TopCat.isoOfHomeo f)

/-- Construct a homeomorphism from an isomorphism. -/
@[simps!]
/-
**CompHausLike.homeoOfIso** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike`。
形式化陈述：homeoOfIso {X Y : CompHausLike.{u} P} (f : X ≅ Y) : X ≃ₜ Y
参数：f : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a homeomorphism from an isomorphism.
-/
def homeoOfIso {X Y : CompHausLike.{u} P} (f : X ≅ Y) : X ≃ₜ Y :=
  TopCat.homeoOfIso <| (compHausLikeToTop P).mapIso f

/-- The equivalence between isomorphisms in `CompHaus` and homeomorphisms
of topological spaces. -/
@[simps]
/-
**CompHausLike.isoEquivHomeo** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike`。
形式化陈述：isoEquivHomeo {X Y : CompHausLike.{u} P} : (X ≅ Y) ≃ (X ≃ₜ Y) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between isomorphisms in `CompHaus` and homeomorphisms
of topological spaces.
-/
def isoEquivHomeo {X Y : CompHausLike.{u} P} : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo

/-- A constant map as a morphism in `CompHausLike` -/
/-
**CompHausLike.const** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike`。
形式化陈述：const {P : TopCat.{u} -> Prop} (T : CompHausLike.{u} P) {S : CompHausLike.
{u} P} (s : S) : T ⟶ S
参数：T : CompHausLike.{u} P；s : S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `CompHausLike.instHasPropCarrierToTop`：∀ (P : TopCat → Prop) (X : CompHau
sLike P), CompHausLike.HasProp P ↑X.toTop

--- 原说明 ---
A constant map as a morphism in `CompHausLike`
-/
def const {P : TopCat.{u} → Prop}
    (T : CompHausLike.{u} P) {S : CompHausLike.{u} P} (s : S) : T ⟶ S :=
  ofHom _ (ContinuousMap.const _ s)
/-
**CompHausLike.const_comp** 是 Mathlib 中的一个引理，位于命名空间 `CompHausLike`。
形式化陈述：const_comp {P : TopCat.{u} -> Prop} {S T U : CompHausLike.{u} P} (s : S) (
g : S ⟶ U) : T.const s ≫ g = T.const (g s)
参数：s : S；g : S ⟶ U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma const_comp {P : TopCat.{u} → Prop} {S T U : CompHausLike.{u} P}
    (s : S) (g : S ⟶ U) : T.const s ≫ g = T.const (g s) :=
  rfl

end CompHausLike

