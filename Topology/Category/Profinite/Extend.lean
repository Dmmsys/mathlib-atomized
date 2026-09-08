/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import Mathlib.CategoryTheory.Filtered.Final
/-!

# Extending cones in `Profinite`

Let `(Sᵢ)_{i : I}` be a family of finite sets indexed by a cofiltered category `I` and let `S` be
its limit in `Profinite`. Let `G` be a functor from `Profinite` to a category `C` and suppose that
`G` preserves the limit described above. Suppose further that the projection maps `S ⟶ Sᵢ` are
epimorphic for all `i`. Then `G.obj S` is isomorphic to a limit indexed by
`StructuredArrow S toProfinite` (see `Profinite.Extend.isLimitCone`).

We also provide the dual result for a functor of the form `G : Profiniteᵒᵖ ⥤ C`.

We apply this to define `Profinite.diagram'`, `Profinite.asLimitCone'`, and `Profinite.asLimit'`,
analogues to their unprimed versions in `Mathlib/Topology/Category/Profinite/AsLimit.lean`, in which
the indexing category is `StructuredArrow S toProfinite` instead of `DiscreteQuotient S`.
-/

@[expose] public section

universe u w

open CategoryTheory Limits FintypeCat Functor

namespace Profinite

variable {I : Type u} [SmallCategory I] [IsCofiltered I]
    {F : I ⥤ FintypeCat.{max u w}} (c : Cone <| F ⋙ toProfinite)

/--
A continuous map from a profinite set to a finite set factors through one of the components of
the profinite set when written as a cofiltered limit of finite sets.
-/
/-
**Profinite.exists_hom** 是 Mathlib 中的一个引理，位于命名空间 `Profinite`。
形式化陈述：exists_hom (hc : IsLimit c) {X : FintypeCat} (f : c.pt ⟶ toProfinite.obj X
) : exists (i : I) (g : F.obj i ⟶ X), f = c.π.app i ≫ toProfinite.map g
参数：hc : IsLimit c；f : c.pt ⟶ toProfinite.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocallyConstant.iff_continuous`：iff_continuous {_ : TopologicalSpace Y
} [DiscreteTopology Y] (f : X -> Y) : IsLocallyConstant f ↔ Continuous f
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `Profinite.exists_locallyConstant`：exists_locallyConstant {α : Type*} (hC
 : IsLimit C) (f : LocallyConstant C.pt α) : exists (j : J) (g : LocallyConstant
 (F.obj j) α), f = g.c…
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `LocallyConstant.congr_fun`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topol
ogicalSpace X] {f g : LocallyConstant X Y}, f = g → ∀ (x : X), f x = g x

--- 原说明 ---
A continuous map from a profinite set to a finite set factors through one of the
 components of
the profinite set when written as a cofiltered limit of finite sets.
-/
lemma exists_hom (hc : IsLimit c) {X : FintypeCat} (f : c.pt ⟶ toProfinite.obj X) :
    ∃ (i : I) (g : F.obj i ⟶ X), f = c.π.app i ≫ toProfinite.map g := by
  have : DiscreteTopology (toProfinite.obj X) := ⟨rfl⟩
  let f' : LocallyConstant c.pt (toProfinite.obj X) :=
    ⟨f, (IsLocallyConstant.iff_continuous _).mpr f.hom.hom.continuous⟩
  obtain ⟨i, g, h⟩ := exists_locallyConstant.{_, u} c hc f'
  refine ⟨i, ⟨↾g⟩, ?_⟩
  ext x
  exact LocallyConstant.congr_fun h x

namespace Extend

/--
Given a cone in `Profinite`, consisting of finite sets and indexed by a cofiltered category,
we obtain a functor from the indexing category to `StructuredArrow c.pt toProfinite`.
-/
@[simps]
/-
**Profinite.Extend.functor** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Extend`。
形式化陈述：functor : I ⥤ StructuredArrow c.pt toProfinite where obj i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cone in `Profinite`, consisting of finite sets and indexed by a cofilter
ed category,
we obtain a functor from the indexing category to `StructuredArrow c.pt toProfin
ite`.
-/
def functor : I ⥤ StructuredArrow c.pt toProfinite where
  obj i := StructuredArrow.mk (c.π.app i)
  map f := StructuredArrow.homMk (F.map f) (c.w f)

-- We check that the original diagram factors through `Profinite.Extend.functor`.
/-
**Profinite.Extend.** 是 Mathlib 中的一个示例，位于命名空间 `Profinite.Extend`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : functor c ⋙ StructuredArrow.proj c.pt toProfinite ≅ F := Iso.refl _

/--
Given a cone in `Profinite`, consisting of finite sets and indexed by a cofiltered category,
we obtain a functor from the opposite of the indexing category to
`CostructuredArrow toProfinite.op ⟨c.pt⟩`.
-/
@[simps! obj map]
/-
**Profinite.Extend.functorOp** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Extend`。
形式化陈述：functorOp : Iᵒᵖ ⥤ CostructuredArrow toProfinite.op ⟨c.pt⟩
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cone in `Profinite`, consisting of finite sets and indexed by a cofilter
ed category,
we obtain a functor from the opposite of the indexing category to
`CostructuredArrow toProfinite.op ⟨c.pt⟩`.
-/
def functorOp : Iᵒᵖ ⥤ CostructuredArrow toProfinite.op ⟨c.pt⟩ :=
  (functor c).op ⋙ StructuredArrow.toCostructuredArrow _ _

-- We check that the opposite of the original diagram factors through `Profinite.Extend.functorOp`.
/-
**Profinite.Extend.** 是 Mathlib 中的一个示例，位于命名空间 `Profinite.Extend`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : functorOp c ⋙ CostructuredArrow.proj toProfinite.op ⟨c.pt⟩ ≅ F.op := Iso.refl _

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] uliftCategory in
/--
If the projection maps in the cone are epimorphic and the cone is limiting, then
`Profinite.Extend.functor` is initial.

TODO: investigate how to weaken the assumption `∀ i, Epi (c.π.app i)` to
`∀ i, ∃ j (_ : j ⟶ i), Epi (c.π.app j)`.
-/
/-
**Profinite.Extend.functor_initial** 是 Mathlib 中的一个引理，位于命名空间 `Profinite.Extend`。
形式化陈述：functor_initial (hc : IsLimit c) [forall i, Epi (c.π.app i)] : Initial (fu
nctor c)
参数：hc : IsLimit c；c.π.app i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.initial_iff_of_isCofiltered`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
· 使用定理 `CategoryTheory.instIsCofilteredULiftHom`：∀ (C : Type u) [inst : Category
Theory.Category.{v, u} C] [CategoryTheory.IsCofiltered C],   CategoryTheory.IsCo
filtered (CategoryTheory.ULif…
· 使用定理 `CategoryTheory.instIsCofilteredULift`：∀ (C : Type u) [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.IsCofiltered C],   CategoryTheory.IsCofil
tered (ULift.{u₂, u} C)
· 使用引理 `Profinite.exists_hom`：exists_hom (hc : IsLimit c) {X : FintypeCat} (f : 
c.pt ⟶ toProfinite.obj X) : exists (i : I) (g : F.obj i ⟶ X), f = c.π.app i ≫ to
Profinite.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `instFaithfulFintypeCatProfiniteToProfinite`：FintypeCat.toProfinite.Faith
ful
· 使用定理 `CategoryTheory.Epi.left_cancellation`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.Epi f] {Z : 
C}   (g h : Y ⟶ Z), Catego…
· 使用定理 `CategoryTheory.Functor.initial_of_equivalence_comp`：initial_of_equivalen
ce_comp [IsEquivalence F] [Initial (F ⋙ G)] : Initial G where out d
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…

--- 原说明 ---
If the projection maps in the cone are epimorphic and the cone is limiting, then
`Profinite.Extend.functor` is initial.

TODO: investigate how to weaken the assumption `∀ i, Epi (c.π.app i)` to
`∀ i, ∃ j (_ : j ⟶ i), Epi (c.π.app j)`.
-/
lemma functor_initial (hc : IsLimit c) [∀ i, Epi (c.π.app i)] : Initial (functor c) := by
  let e : I ≌ ULiftHom.{w} (ULift.{w} I) := ULiftHomULiftCategory.equiv _
  suffices (e.inverse ⋙ functor c).Initial from initial_of_equivalence_comp e.inverse (functor c)
  rw [initial_iff_of_isCofiltered (F := e.inverse ⋙ functor c)]
  constructor
  · intro ⟨_, X, (f : c.pt ⟶ _)⟩
    obtain ⟨i, g, h⟩ := exists_hom c hc f
    exact ⟨⟨i⟩, ⟨StructuredArrow.homMk g h.symm⟩⟩
  · intro ⟨_, X, (f : c.pt ⟶ _)⟩ ⟨i⟩ ⟨_, (s : F.obj i ⟶ X), (w : f = c.π.app i ≫ _)⟩
      ⟨_, (s' : F.obj i ⟶ X), (w' : f = c.π.app i ≫ _)⟩
    simp only [StructuredArrow.hom_eq_iff,
      StructuredArrow.comp_right]
    refine ⟨⟨i⟩, 𝟙 _, ?_⟩
    simp only [CategoryTheory.Functor.map_id]
    rw [w] at w'
    exact toProfinite.map_injective <| Epi.left_cancellation _ _ w'

/--
If the projection maps in the cone are epimorphic and the cone is limiting, then
`Profinite.Extend.functorOp` is final.
-/
/-
**Profinite.Extend.functorOp_final** 是 Mathlib 中的一个引理，位于命名空间 `Profinite.Extend`。
形式化陈述：functorOp_final (hc : IsLimit c) [forall i, Epi (c.π.app i)] : Final (func
torOp c)
参数：hc : IsLimit c；c.π.app i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Profinite.Extend.functor_initial`：functor_initial (hc : IsLimit c) [fora
ll i, Epi (c.π.app i)] : Initial (functor c)
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.Functor.final_of_isRightAdjoint`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
If the projection maps in the cone are epimorphic and the cone is limiting, then
`Profinite.Extend.functorOp` is final.
-/
lemma functorOp_final (hc : IsLimit c) [∀ i, Epi (c.π.app i)] : Final (functorOp c) := by
  have := functor_initial c hc
  have : ((StructuredArrow.toCostructuredArrow toProfinite c.pt)).IsEquivalence :=
    (inferInstance : (structuredArrowOpEquivalence _ _).functor.IsEquivalence)
  exact Functor.final_comp (functor c).op _

section Limit

variable {C : Type*} [Category* C] (G : Profinite ⥤ C)

set_option backward.defeqAttrib.useBackward true in
/--
Given a functor `G` from `Profinite` and `S : Profinite`, we obtain a cone on
`(StructuredArrow.proj S toProfinite ⋙ toProfinite ⋙ G)` with cone point `G.obj S`.

Whiskering this cone with `Profinite.Extend.functor c` gives `G.mapCone c` as we check in the
example below.
-/
@[simps]
/-
**Profinite.Extend.cone** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Extend`。
形式化陈述：cone (S : Profinite) : Cone (StructuredArrow.proj S toProfinite ⋙ toProfin
ite ⋙ G) where pt
参数：S : Profinite。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `G` from `Profinite` and `S : Profinite`, we obtain a cone on
`(StructuredArrow.proj S toProfinite ⋙ toProfinite ⋙ G)` with cone point `G.obj 
S`.

Whiskering this cone with `Profinite.Extend.functor c` gives `G.mapCone c` as we
 check in the
example below.
-/
def cone (S : Profinite) :
    Cone (StructuredArrow.proj S toProfinite ⋙ toProfinite ⋙ G) where
  pt := G.obj S
  π := {
    app := fun i ↦ G.map i.hom
    naturality := fun _ _ f ↦ (by simp [← map_comp]) }
/-
**Profinite.Extend.** 是 Mathlib 中的一个示例，位于命名空间 `Profinite.Extend`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : G.mapCone c = (cone G c.pt).whisker (functor c) := rfl

/--
If `c` and `G.mapCone c` are limit cones and the projection maps in `c` are epimorphic,
then `cone G c.pt` is a limit cone.
-/
noncomputable
/-
**Profinite.Extend.isLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Extend`。
形式化陈述：isLimitCone (hc : IsLimit c) [forall i, Epi (c.π.app i)] (hc' : IsLimit <|
 G.mapCone c) : IsLimit (cone G c.pt)
参数：hc : IsLimit c；c.π.app i；hc' : IsLimit <| G.mapCone c。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Profinite.Extend.functor_initial`：functor_initial (hc : IsLimit c) [fora
ll i, Epi (c.π.app i)] : Initial (functor c)
-/
def isLimitCone (hc : IsLimit c) [∀ i, Epi (c.π.app i)] (hc' : IsLimit <| G.mapCone c) :
    IsLimit (cone G c.pt) := (functor_initial c hc).isLimitWhiskerEquiv _ _ hc'

end Limit

section Colimit

variable {C : Type*} [Category* C] (G : Profiniteᵒᵖ ⥤ C)

set_option backward.defeqAttrib.useBackward true in
/--
Given a functor `G` from `Profiniteᵒᵖ` and `S : Profinite`, we obtain a cocone on
`(CostructuredArrow.proj toProfinite.op ⟨S⟩ ⋙ toProfinite.op ⋙ G)` with cocone point `G.obj ⟨S⟩`.

Whiskering this cocone with `Profinite.Extend.functorOp c` gives `G.mapCocone c.op` as we check in
the example below.
-/
@[simps]
/-
**Profinite.Extend.cocone** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Extend`。
形式化陈述：cocone (S : Profinite) : Cocone (CostructuredArrow.proj toProfinite.op ⟨S⟩
 ⋙ toProfinite.op ⋙ G) where pt
参数：S : Profinite。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `G` from `Profiniteᵒᵖ` and `S : Profinite`, we obtain a cocone o
n
`(CostructuredArrow.proj toProfinite.op ⟨S⟩ ⋙ toProfinite.op ⋙ G)` with cocone p
oint `G.obj ⟨S⟩`.

Whiskering this cocone with `Profinite.Extend.functorOp c` gives `G.mapCocone c.
op` as we check in
the example below.
-/
def cocone (S : Profinite) :
    Cocone (CostructuredArrow.proj toProfinite.op ⟨S⟩ ⋙ toProfinite.op ⋙ G) where
  pt := G.obj ⟨S⟩
  ι := {
    app := fun i ↦ G.map i.hom
    naturality := fun _ _ f ↦ (by
      have := f.w
      simp only [op_obj, const_obj_obj, op_map, CostructuredArrow.right_eq_id, const_obj_map,
        Category.comp_id] at this
      simp [← map_comp, this]) }
/-
**Profinite.Extend.** 是 Mathlib 中的一个示例，位于命名空间 `Profinite.Extend`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : G.mapCocone c.op = (cocone G c.pt).whisker (functorOp c) := rfl

/--
If `c` is a limit cone, `G.mapCocone c.op` is a colimit cone and the projection maps in `c`
are epimorphic, then `cocone G c.pt` is a colimit cone.
-/
noncomputable
/-
**Profinite.Extend.isColimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Extend`。
形式化陈述：isColimitCocone (hc : IsLimit c) [forall i, Epi (c.π.app i)] (hc' : IsColi
mit <| G.mapCocone c.op) : IsColimit (cocone G c.pt)
参数：hc : IsLimit c；c.π.app i；hc' : IsColimit <| G.mapCocone c.op。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Profinite.Extend.functorOp_final`：functorOp_final (hc : IsLimit c) [fora
ll i, Epi (c.π.app i)] : Final (functorOp c)
-/
def isColimitCocone (hc : IsLimit c) [∀ i, Epi (c.π.app i)] (hc' : IsColimit <| G.mapCocone c.op) :
    IsColimit (cocone G c.pt) := (functorOp_final c hc).isColimitWhiskerEquiv _ _ hc'

end Colimit

end Extend

open Extend

section ProfiniteAsLimit

variable (S : Profinite.{u})

/--
A functor `StructuredArrow S toProfinite ⥤ FintypeCat` whose limit in `Profinite` is isomorphic
to `S`.
-/
/-
**Profinite.fintypeDiagram'** 是 Mathlib 中的一个缩写定义，位于命名空间 `Profinite`。
形式化陈述：fintypeDiagram' : StructuredArrow S toProfinite ⥤ FintypeCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `StructuredArrow S toProfinite ⥤ FintypeCat` whose limit in `Profinite
` is isomorphic
to `S`.
-/
abbrev fintypeDiagram' : StructuredArrow S toProfinite ⥤ FintypeCat :=
  StructuredArrow.proj S toProfinite

/-- An abbreviation for `S.fintypeDiagram' ⋙ toProfinite`. -/
/-
**Profinite.diagram'** 是 Mathlib 中的一个缩写定义，位于命名空间 `Profinite`。
形式化陈述：diagram' : StructuredArrow S toProfinite ⥤ Profinite
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `S.fintypeDiagram' ⋙ toProfinite`.
-/
abbrev diagram' : StructuredArrow S toProfinite ⥤ Profinite :=
  S.fintypeDiagram' ⋙ toProfinite

/-- A cone over `S.diagram'` whose cone point is `S`. -/
/-
**Profinite.asLimitCone'** 是 Mathlib 中的一个缩写定义，位于命名空间 `Profinite`。
形式化陈述：asLimitCone' : Cone (S.diagram')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cone over `S.diagram'` whose cone point is `S`.
-/
abbrev asLimitCone' : Cone (S.diagram') := cone (𝟭 _) S
/-
**Profinite.** 是 Mathlib 中的一个实例，位于命名空间 `Profinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : DiscreteQuotient S) : Epi (S.asLimitCone.π.app i) :=
  (epi_iff_surjective _).mpr i.proj_surjective

/-- `S.asLimitCone'` is a limit cone. -/
/-
**Profinite.asLimit'** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：asLimit' : IsLimit S.asLimitCone'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Profinite.instEpiAppDiscreteQuotientCarrierToTopTotallyDisconnectedSpace
πAsLimitCone`：∀ (S : Profinite) (i : DiscreteQuotient ↑S.toTop), CategoryTheory.
Epi (S.asLimitCone.π.app i)

--- 原说明 ---
`S.asLimitCone'` is a limit cone.
-/
noncomputable def asLimit' : IsLimit S.asLimitCone' := isLimitCone _ (𝟭 _) S.asLimit S.asLimit

/-- A bundled version of `S.asLimitCone'` and `S.asLimit'`. -/
/-
**Profinite.lim'** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：lim' : LimitCone S.diagram'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bundled version of `S.asLimitCone'` and `S.asLimit'`.
-/
noncomputable def lim' : LimitCone S.diagram' := ⟨S.asLimitCone', S.asLimit'⟩

end ProfiniteAsLimit

end Profinite

