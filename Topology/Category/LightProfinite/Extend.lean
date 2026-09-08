/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.LightProfinite.AsLimit
public import Mathlib.Topology.Category.Profinite.Extend

/-!

# Extending cones in `LightProfinite`

Let `(Sₙ)_{n : ℕᵒᵖ}` be a sequential inverse system of finite sets and let `S` be
its limit in `Profinite`. Let `G` be a functor from `LightProfinite` to a category `C` and suppose
that `G` preserves the limit described above. Suppose further that the projection maps `S ⟶ Sₙ` are
epimorphic for all `n`. Then `G.obj S` is isomorphic to a limit indexed by
`StructuredArrow S toLightProfinite` (see `LightProfinite.Extend.isLimitCone`).

We also provide the dual result for a functor of the form `G : LightProfiniteᵒᵖ ⥤ C`.

We apply this to define `LightProfinite.diagram'`, `LightProfinite.asLimitCone'`, and
`LightProfinite.asLimit'`, analogues to their unprimed versions in
`Mathlib/Topology/Category/LightProfinite/AsLimit.lean`, in which the
indexing category is `StructuredArrow S toLightProfinite` instead of `ℕᵒᵖ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits FintypeCat Functor

attribute [local instance] FintypeCat.discreteTopology

namespace LightProfinite

variable {F : ℕᵒᵖ ⥤ FintypeCat.{u}} (c : Cone <| F ⋙ toLightProfinite)

namespace Extend

/--
Given a sequential cone in `LightProfinite` consisting of finite sets,
we obtain a functor from the indexing category to `StructuredArrow c.pt toLightProfinite`.
-/
@[simps]
/-
**LightProfinite.Extend.functor** 是 Mathlib 中的一个定义，位于命名空间 `LightProfinite.Extend
`。
形式化陈述：functor : Natᵒᵖ ⥤ StructuredArrow c.pt toLightProfinite where obj i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a sequential cone in `LightProfinite` consisting of finite sets,
we obtain a functor from the indexing category to `StructuredArrow c.pt toLightP
rofinite`.
-/
def functor : ℕᵒᵖ ⥤ StructuredArrow c.pt toLightProfinite where
  obj i := StructuredArrow.mk (c.π.app i)
  map f := StructuredArrow.homMk (F.map f) (c.w f)

-- We check that the original diagram factors through `LightProfinite.Extend.functor`.
/-
**LightProfinite.Extend.** 是 Mathlib 中的一个示例，位于命名空间 `LightProfinite.Extend`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : functor c ⋙ StructuredArrow.proj c.pt toLightProfinite ≅ F := Iso.refl _

/--
Given a sequential cone in `LightProfinite` consisting of finite sets,
we obtain a functor from the opposite of the indexing category to
`CostructuredArrow toProfinite.op ⟨c.pt⟩`.
-/
@[simps! obj map]
/-
**LightProfinite.Extend.functorOp** 是 Mathlib 中的一个定义，位于命名空间 `LightProfinite.Exte
nd`。
形式化陈述：functorOp : Nat ⥤ CostructuredArrow toLightProfinite.op ⟨c.pt⟩
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a sequential cone in `LightProfinite` consisting of finite sets,
we obtain a functor from the opposite of the indexing category to
`CostructuredArrow toProfinite.op ⟨c.pt⟩`.
-/
def functorOp : ℕ ⥤ CostructuredArrow toLightProfinite.op ⟨c.pt⟩ :=
  (functor c).rightOp ⋙ StructuredArrow.toCostructuredArrow _ _

-- We check that the opposite of the original diagram factors through `Profinite.Extend.functorOp`.
/-
**LightProfinite.Extend.** 是 Mathlib 中的一个示例，位于命名空间 `LightProfinite.Extend`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : functorOp c ⋙ CostructuredArrow.proj toLightProfinite.op ⟨c.pt⟩ ≅ F.rightOp := Iso.refl _

-- We check that `Profinite.Extend.functor` factors through `LightProfinite.Extend.functor`,
-- via the equivalence `StructuredArrow.post _ _ lightToProfinite`.
/-
**LightProfinite.Extend.** 是 Mathlib 中的一个示例，位于命名空间 `LightProfinite.Extend`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : functor c ⋙ (StructuredArrow.post _ _ lightToProfinite) =
    Profinite.Extend.functor (lightToProfinite.mapCone c) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
If the projection maps in the cone are epimorphic and the cone is limiting, then
`LightProfinite.Extend.functor` is initial.
-/
/-
**LightProfinite.Extend.functor_initial** 是 Mathlib 中的一个定理，位于命名空间 `LightProfinit
e.Extend`。
形式化陈述：functor_initial (hc : IsLimit c) [forall i, Epi (c.π.app i)] : Initial (fu
nctor c)
参数：hc : IsLimit c；c.π.app i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.initial_iff_comp_equivalence`：initial_iff_comp_eq
uivalence [IsEquivalence G] : Initial F ↔ Initial (F ⋙ G)
· 使用定理 `CategoryTheory.StructuredArrow.isEquivalence_post`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {B : Type u₄} [ins…
· 使用定理 `CompHausLike.instFullToCompHausLike`：∀ {P P' : TopCat → Prop} (h : ∀ (X 
: CompHausLike P), P X.toTop → P' X.toTop), (CompHausLike.toCompHausLike h).Full
· 使用定理 `CompHausLike.instFaithfulToCompHausLike`：∀ {P P' : TopCat → Prop} (h : ∀
 (X : CompHausLike P), P X.toTop → P' X.toTop), (CompHausLike.toCompHausLike h).
Faithful
· 使用引理 `Profinite.Extend.functor_initial`：functor_initial (hc : IsLimit c) [fora
ll i, Epi (c.π.app i)] : Initial (functor c)
· 使用定理 `CategoryTheory.isFiltered_of_directed_le_nonempty`：∀ (α : Type u) [inst 
: Preorder α] [IsDirectedOrder α] [Nonempty α], CategoryTheory.IsFiltered α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.instCountableCategoryNat`：CategoryTheory.CountableCategor
y ℕ
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasCountableLimitsOfCountabl
eCategory`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] (J : T
ype u_2)   [CategoryTheory.Limits.HasCountableLimits C] [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.hasCountableLimits_of_hasLimits`：∀ (C : Type u_1) 
[inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasLimits C
],   CategoryTheory.Limits.HasCountableLimi…

--- 原说明 ---
If the projection maps in the cone are epimorphic and the cone is limiting, then
`LightProfinite.Extend.functor` is initial.
-/
theorem functor_initial (hc : IsLimit c) [∀ i, Epi (c.π.app i)] : Initial (functor c) := by
  rw [initial_iff_comp_equivalence _ (StructuredArrow.post _ _ lightToProfinite)]
  have : ∀ i, Epi ((lightToProfinite.mapCone c).π.app i) :=
    fun i ↦ inferInstanceAs (Epi (lightToProfinite.map (c.π.app i)))
  exact Profinite.Extend.functor_initial _ (isLimitOfPreserves lightToProfinite hc)

/--
If the projection maps in the cone are epimorphic and the cone is limiting, then
`LightProfinite.Extend.functorOp` is final.
-/
/-
**LightProfinite.Extend.functorOp_final** 是 Mathlib 中的一个定理，位于命名空间 `LightProfinit
e.Extend`。
形式化陈述：functorOp_final (hc : IsLimit c) [forall i, Epi (c.π.app i)] : Final (func
torOp c)
参数：hc : IsLimit c；c.π.app i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LightProfinite.Extend.functor_initial`：functor_initial (hc : IsLimit c) 
[forall i, Epi (c.π.app i)] : Initial (functor c)
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
`LightProfinite.Extend.functorOp` is final.
-/
theorem functorOp_final (hc : IsLimit c) [∀ i, Epi (c.π.app i)] : Final (functorOp c) := by
  have := functor_initial c hc
  have : ((StructuredArrow.toCostructuredArrow toLightProfinite c.pt)).IsEquivalence :=
    (inferInstance : (structuredArrowOpEquivalence _ _).functor.IsEquivalence)
  have : (functor c).rightOp.Final :=
    inferInstanceAs ((opOpEquivalence ℕ).inverse ⋙ (functor c).op).Final
  exact Functor.final_comp (functor c).rightOp _

section Limit

variable {C : Type*} [Category* C] (G : LightProfinite ⥤ C)

set_option backward.defeqAttrib.useBackward true in
/--
Given a functor `G` from `LightProfinite` and `S : LightProfinite`, we obtain a cone on
`(StructuredArrow.proj S toLightProfinite ⋙ toLightProfinite ⋙ G)` with cone point `G.obj S`.

Whiskering this cone with `LightProfinite.Extend.functor c` gives `G.mapCone c` as we check in the
example below.
-/
/-
**LightProfinite.Extend.cone** 是 Mathlib 中的一个定义，位于命名空间 `LightProfinite.Extend`。
形式化陈述：cone (S : LightProfinite) : Cone (StructuredArrow.proj S toLightProfinite 
⋙ toLightProfinite ⋙ G) where pt
参数：S : LightProfinite。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `G` from `LightProfinite` and `S : LightProfinite`, we obtain a 
cone on
`(StructuredArrow.proj S toLightProfinite ⋙ toLightProfinite ⋙ G)` with cone poi
nt `G.obj S`.

Whiskering this cone with `LightProfinite.Extend.functor c` gives `G.mapCone c` 
as we check in the
example below.
-/
def cone (S : LightProfinite) :
    Cone (StructuredArrow.proj S toLightProfinite ⋙ toLightProfinite ⋙ G) where
  pt := G.obj S
  π :=
    { app i := G.map i.hom
      naturality _ _ f := by simp [← Functor.map_comp] }
/-
**LightProfinite.Extend.** 是 Mathlib 中的一个示例，位于命名空间 `LightProfinite.Extend`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : G.mapCone c = (cone G c.pt).whisker (functor c) := rfl

/--
If `c` and `G.mapCone c` are limit cones and the projection maps in `c` are epimorphic,
then `cone G c.pt` is a limit cone.
-/
noncomputable
/-
**LightProfinite.Extend.isLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `LightProfinite.Ex
tend`。
形式化陈述：isLimitCone (hc : IsLimit c) [forall i, Epi (c.π.app i)] (hc' : IsLimit <|
 G.mapCone c) : IsLimit (cone G c.pt)
参数：hc : IsLimit c；c.π.app i；hc' : IsLimit <| G.mapCone c。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LightProfinite.Extend.functor_initial`：functor_initial (hc : IsLimit c) 
[forall i, Epi (c.π.app i)] : Initial (functor c)
-/
def isLimitCone (hc : IsLimit c) [∀ i, Epi (c.π.app i)] (hc' : IsLimit <| G.mapCone c) :
    IsLimit (cone G c.pt) := (functor_initial c hc).isLimitWhiskerEquiv _ _ hc'

end Limit

section Colimit

variable {C : Type*} [Category* C] (G : LightProfiniteᵒᵖ ⥤ C)

set_option backward.defeqAttrib.useBackward true in
/--
Given a functor `G` from `LightProfiniteᵒᵖ` and `S : LightProfinite`, we obtain a cocone on
`(CostructuredArrow.proj toLightProfinite.op ⟨S⟩ ⋙ toLightProfinite.op ⋙ G)` with cocone point
`G.obj ⟨S⟩`.

Whiskering this cocone with `LightProfinite.Extend.functorOp c` gives `G.mapCocone c.op` as we
check in the example below.
-/
@[simps]
/-
**LightProfinite.Extend.cocone** 是 Mathlib 中的一个定义，位于命名空间 `LightProfinite.Extend`
。
形式化陈述：cocone (S : LightProfinite) : Cocone (CostructuredArrow.proj toLightProfin
ite.op ⟨S⟩ ⋙ toLightProfinite.op ⋙ G) where pt
参数：S : LightProfinite。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `G` from `LightProfiniteᵒᵖ` and `S : LightProfinite`, we obtain 
a cocone on
`(CostructuredArrow.proj toLightProfinite.op ⟨S⟩ ⋙ toLightProfinite.op ⋙ G)` wit
h cocone point
`G.obj ⟨S⟩`.

Whiskering this cocone with `LightProfinite.Extend.functorOp c` gives `G.mapCoco
ne c.op` as we
check in the example below.
-/
def cocone (S : LightProfinite) :
    Cocone (CostructuredArrow.proj toLightProfinite.op ⟨S⟩ ⋙ toLightProfinite.op ⋙ G) where
  pt := G.obj ⟨S⟩
  ι := {
    app := fun i ↦ G.map i.hom
    naturality := fun _ _ f ↦ (by
      have := f.w
      simp only [op_obj, const_obj_obj, op_map, CostructuredArrow.right_eq_id, const_obj_map,
        Category.comp_id] at this
      simp only [comp_obj, CostructuredArrow.proj_obj, op_obj, const_obj_obj, Functor.comp_map,
        CostructuredArrow.proj_map, op_map, ← map_comp, this, const_obj_map, Category.comp_id]) }
/-
**LightProfinite.Extend.** 是 Mathlib 中的一个示例，位于命名空间 `LightProfinite.Extend`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : G.mapCocone c.op = (cocone G c.pt).whisker
    ((opOpEquivalence ℕ).functor ⋙ functorOp c) := rfl

/--
If `c` is a limit cone, `G.mapCocone c.op` is a colimit cone and the projection maps in `c`
are epimorphic, then `cocone G c.pt` is a colimit cone.
-/
noncomputable
/-
**LightProfinite.Extend.isColimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `LightProfinit
e.Extend`。
形式化陈述：isColimitCocone (hc : IsLimit c) [forall i, Epi (c.π.app i)] (hc' : IsColi
mit <| G.mapCocone c.op) : IsColimit (cocone G c.pt)
参数：hc : IsLimit c；c.π.app i；hc' : IsColimit <| G.mapCocone c.op。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def isColimitCocone (hc : IsLimit c) [∀ i, Epi (c.π.app i)] (hc' : IsColimit <| G.mapCocone c.op) :
    IsColimit (cocone G c.pt) :=
  haveI := functorOp_final c hc
  (Functor.final_comp (opOpEquivalence ℕ).functor (functorOp c)).isColimitWhiskerEquiv _ _ hc'

end Colimit

end Extend

open Extend

section LightProfiniteAsLimit

variable (S : LightProfinite.{u})

/--
A functor `StructuredArrow S toLightProfinite ⥤ FintypeCat` whose limit in `LightProfinite` is
isomorphic to `S`.
-/
/-
**LightProfinite.fintypeDiagram'** 是 Mathlib 中的一个缩写定义，位于命名空间 `LightProfinite`。
形式化陈述：fintypeDiagram' : StructuredArrow S toLightProfinite ⥤ FintypeCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `StructuredArrow S toLightProfinite ⥤ FintypeCat` whose limit in `Ligh
tProfinite` is
isomorphic to `S`.
-/
abbrev fintypeDiagram' : StructuredArrow S toLightProfinite ⥤ FintypeCat :=
  StructuredArrow.proj S toLightProfinite

/-- An abbreviation for `S.fintypeDiagram' ⋙ toLightProfinite`. -/
/-
**LightProfinite.diagram'** 是 Mathlib 中的一个缩写定义，位于命名空间 `LightProfinite`。
形式化陈述：diagram' : StructuredArrow S toLightProfinite ⥤ LightProfinite
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `S.fintypeDiagram' ⋙ toLightProfinite`.
-/
abbrev diagram' : StructuredArrow S toLightProfinite ⥤ LightProfinite :=
  S.fintypeDiagram' ⋙ toLightProfinite

/-- A cone over `S.diagram'` whose cone point is `S`. -/
/-
**LightProfinite.asLimitCone'** 是 Mathlib 中的一个定义，位于命名空间 `LightProfinite`。
形式化陈述：asLimitCone' : Cone (S.diagram')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cone over `S.diagram'` whose cone point is `S`.
-/
def asLimitCone' : Cone (S.diagram') := cone (𝟭 _) S
/-
**LightProfinite.** 是 Mathlib 中的一个实例，位于命名空间 `LightProfinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : ℕᵒᵖ) : Epi (S.asLimitCone.π.app i) :=
  (epi_iff_surjective _).mpr (S.proj_surjective _)

/-- `S.asLimitCone'` is a limit cone. -/
/-
**LightProfinite.asLimit'** 是 Mathlib 中的一个定义，位于命名空间 `LightProfinite`。
形式化陈述：asLimit' : IsLimit S.asLimitCone'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LightProfinite.instEpiAppOppositeNatπAsLimitCone`：∀ (S : LightProfinite)
 (i : ℕᵒᵖ), CategoryTheory.Epi (S.asLimitCone.π.app i)

--- 原说明 ---
`S.asLimitCone'` is a limit cone.
-/
noncomputable def asLimit' : IsLimit S.asLimitCone' := isLimitCone _ (𝟭 _) S.asLimit S.asLimit

/-- A bundled version of `S.asLimitCone'` and `S.asLimit'`. -/
/-
**LightProfinite.lim'** 是 Mathlib 中的一个定义，位于命名空间 `LightProfinite`。
形式化陈述：lim' : LimitCone S.diagram'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bundled version of `S.asLimitCone'` and `S.asLimit'`.
-/
noncomputable def lim' : LimitCone S.diagram' := ⟨S.asLimitCone', S.asLimit'⟩

end LightProfiniteAsLimit

end LightProfinite

