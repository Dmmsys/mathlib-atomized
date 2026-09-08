/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Category.Pairwise
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.OpensLeCover

/-!
# Equivalent formulations of the sheaf condition

We give an equivalent formulation of the sheaf condition.

Given any indexed type `ι`, we define `overlap ι`,
a category with objects corresponding to
* individual open sets, `single i`, and
* intersections of pairs of open sets, `pair i j`,
  with morphisms from `pair i j` to both `single i` and `single j`.

Any open cover `U : ι → Opens X` provides a functor `diagram U : overlap ι ⥤ (Opens X)ᵒᵖ`.

There is a canonical cone over this functor, `cone U`, whose cone point is `isup U`,
and in fact this is a limit cone.

A presheaf `F : Presheaf C X` is a sheaf precisely if it preserves this limit.
We express this in two equivalent ways, as
* `isLimit (F.mapCone (cone U))`, or
* `preservesLimit (diagram U) F`

We show that this sheaf condition is equivalent to the `OpensLeCover` sheaf condition, and
thereby also equivalent to the default sheaf condition.
-/

@[expose] public section

assert_not_exists IsOrderedMonoid

noncomputable section

universe w

open TopologicalSpace TopCat Opposite CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category* C] {X : TopCat.{w}}

namespace TopCat.Presheaf

section

/-- An alternative formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`isSheaf_iff_isSheafPairwiseIntersections`).

A presheaf is a sheaf if `F` sends the cone `(Pairwise.cocone U).op` to a limit cone.
(Recall `Pairwise.cocone U` has cone point `iSup U`, mapping down to the `U i` and the `U i ⊓ U j`.)
-/
/-
**TopCat.Presheaf.IsSheafPairwiseIntersections** 是 Mathlib 中的一个定义，位于命名空间 `TopCat
.Presheaf`。
形式化陈述：IsSheafPairwiseIntersections (F : Presheaf C X) : Prop
参数：F : Presheaf C X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternative formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`isSheaf_iff_isSheafPairwiseIntersections`).

A presheaf is a sheaf if `F` sends the cone `(Pairwise.cocone U).op` to a limit 
cone.
(Recall `Pairwise.cocone U` has cone point `iSup U`, mapping down to the `U i` a
nd the `U i ⊓ U j`.)
-/
def IsSheafPairwiseIntersections (F : Presheaf C X) : Prop :=
  ∀ ⦃ι : Type w⦄ (U : ι → Opens X), Nonempty (IsLimit (F.mapCone (Pairwise.cocone U).op))

/-- An alternative formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`isSheaf_iff_isSheafPreservesLimitPairwiseIntersections`).

A presheaf is a sheaf if `F` preserves the limit of `Pairwise.diagram U`.
(Recall `Pairwise.diagram U` is the diagram consisting of the pairwise intersections
`U i ⊓ U j` mapping into the open sets `U i`. This diagram has limit `iSup U`.)
-/
/-
**TopCat.Presheaf.IsSheafPreservesLimitPairwiseIntersections** 是 Mathlib 中的一个定义，
位于命名空间 `TopCat.Presheaf`。
形式化陈述：IsSheafPreservesLimitPairwiseIntersections (F : Presheaf C X) : Prop
参数：F : Presheaf C X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternative formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`isSheaf_iff_isSheafPreservesLimitPairwiseIntersections`).

A presheaf is a sheaf if `F` preserves the limit of `Pairwise.diagram U`.
(Recall `Pairwise.diagram U` is the diagram consisting of the pairwise intersect
ions
`U i ⊓ U j` mapping into the open sets `U i`. This diagram has limit `iSup U`.)
-/
def IsSheafPreservesLimitPairwiseIntersections (F : Presheaf C X) : Prop :=
  ∀ ⦃ι : Type w⦄ (U : ι → Opens X), PreservesLimit (Pairwise.diagram U).op F

end

namespace SheafCondition

variable {ι : Type*} (U : ι → Opens X)

open CategoryTheory.Pairwise

/-- Implementation detail:
the object level of `pairwiseToOpensLeCover : Pairwise ι ⥤ OpensLeCover U`
-/
@[simp]
/-
**TopCat.Presheaf.SheafCondition.pairwiseToOpensLeCoverObj** 是 Mathlib 中的一个定义，位于
命名空间 `TopCat.Presheaf.SheafCondition`。
形式化陈述：{X : TopCat} →   {ι : Type u_2} →     (U : ι → TopologicalSpace.Opens ↑X) 
→ CategoryTheory.Pairwise ι → TopCat.Presheaf.SheafCondition.OpensLeCover U
参数：U : ι → TopologicalSpace.Opens ↑X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation detail:
the object level of `pairwiseToOpensLeCover : Pairwise ι ⥤ OpensLeCover U`
-/
def pairwiseToOpensLeCoverObj : Pairwise ι → OpensLeCover U
  | single i => ⟨U i, ⟨i, le_rfl⟩⟩
  | Pairwise.pair i j => ⟨U i ⊓ U j, ⟨i, inf_le_left⟩⟩

open CategoryTheory.Pairwise.Hom

/-- Implementation detail:
the morphism level of `pairwiseToOpensLeCover : Pairwise ι ⥤ OpensLeCover U`
-/
/-
**TopCat.Presheaf.SheafCondition.pairwiseToOpensLeCoverMap** 是 Mathlib 中的一个定义，位于
命名空间 `TopCat.Presheaf.SheafCondition`。
形式化陈述：{X : TopCat} →   {ι : Type u_2} →     (U : ι → TopologicalSpace.Opens ↑X) 
→       {V W : CategoryTheory.Pairwise ι} →         (V ⟶ W) →           (TopCat.
Presheaf.SheafCondition.pairwiseToOpensLeCoverObj U V ⟶             TopCat.Presh
eaf.SheafCondition.pairwiseToOpensLeCoverObj U W)
参数：U : ι → TopologicalSpace.Opens ↑X；V ⟶ W；TopCat.Presheaf.SheafCondition.pairwi
seToOpensLeCoverObj U V ⟶             TopCat.Presheaf.SheafCondition.pairwiseToO
pensLeCoverObj U W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation detail:
the morphism level of `pairwiseToOpensLeCover : Pairwise ι ⥤ OpensLeCover U`
-/
def pairwiseToOpensLeCoverMap :
    ∀ {V W : Pairwise ι}, (V ⟶ W) → (pairwiseToOpensLeCoverObj U V ⟶ pairwiseToOpensLeCoverObj U W)
  | _, _, id_single _ => 𝟙 _
  | _, _, id_pair _ _ => 𝟙 _
  | _, _, left _ _ => ObjectProperty.homMk (homOfLE inf_le_left)
  | _, _, right _ _ => ObjectProperty.homMk (homOfLE inf_le_right)

/-- The category of single and double intersections of the `U i` maps into the category
of open sets below some `U i`.
-/
@[simps]
/-
**TopCat.Presheaf.SheafCondition.pairwiseToOpensLeCover** 是 Mathlib 中的一个定义，位于命名空
间 `TopCat.Presheaf.SheafCondition`。
形式化陈述：pairwiseToOpensLeCover : Pairwise ι ⥤ OpensLeCover U where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of single and double intersections of the `U i` maps into the categ
ory
of open sets below some `U i`.
-/
def pairwiseToOpensLeCover : Pairwise ι ⥤ OpensLeCover U where
  obj := pairwiseToOpensLeCoverObj U
  map {_ _} i := pairwiseToOpensLeCoverMap U i
/-
**TopCat.Presheaf.SheafCondition.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.Presheaf.She
afCondition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V : OpensLeCover U) : Nonempty (StructuredArrow V (pairwiseToOpensLeCover U)) :=
  ⟨StructuredArrow.mk (Y := single V.index) (ObjectProperty.homMk V.homToIndex)⟩

-- This is a case bash: for each pair of types of objects in `Pairwise ι`,
-- we have to explicitly construct a zigzag.
/-- The diagram consisting of the `U i` and `U i ⊓ U j` is cofinal in the diagram
of all opens contained in some `U i`.
-/
/-
**TopCat.Presheaf.SheafCondition.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.Presheaf.She
afCondition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram consisting of the `U i` and `U i ⊓ U j` is cofinal in the diagram
of all opens contained in some `U i`.
-/
instance : Functor.Final (pairwiseToOpensLeCover U) :=
  ⟨fun V =>
    isConnected_of_zigzag fun A B => by
      rcases A with ⟨⟨⟨⟩⟩, ⟨i⟩ | ⟨i, j⟩, a⟩ <;> rcases B with ⟨⟨⟨⟩⟩, ⟨i'⟩ | ⟨i', j'⟩, b⟩
      · refine
          ⟨[{ left := ⟨⟨⟩⟩
              right := pair i i'
              hom := ObjectProperty.homMk (homOfLE
                (by simpa using le_inf a.hom.le b.hom.le)) }, _], ?_, rfl⟩
        exact
          List.IsChain.cons_cons
            (Or.inr
              ⟨{  left := 𝟙 _
                  right := left i i' }⟩)
            (List.IsChain.cons_cons
              (Or.inl
                ⟨{  left := 𝟙 _
                    right := right i i' }⟩)
              (List.IsChain.singleton _))
      · refine
          ⟨[{   left := ⟨⟨⟩⟩
                right := pair i' i
                hom := ObjectProperty.homMk (homOfLE
                  (le_inf (b.hom.le.trans (by simp)) a.hom.le)) },
              { left := ⟨⟨⟩⟩
                right := single i'
                hom := ObjectProperty.homMk (homOfLE (b.hom.le.trans (by simp))) }, _], ?_, rfl⟩
        exact
          List.IsChain.cons_cons
            (Or.inr
              ⟨{  left := 𝟙 _
                  right := right i' i }⟩)
            (List.IsChain.cons_cons
              (Or.inl
                ⟨{  left := 𝟙 _
                    right := left i' i }⟩)
              (List.IsChain.cons_cons
                (Or.inr
                  ⟨{  left := 𝟙 _
                      right := left i' j' }⟩)
                (List.IsChain.singleton _)))
      · refine
          ⟨[{   left := ⟨⟨⟩⟩
                right := single i
                hom := ObjectProperty.homMk (homOfLE (a.hom.le.trans (by simp))) },
              { left := ⟨⟨⟩⟩
                right := pair i i'
                hom := ObjectProperty.homMk (homOfLE
                  (le_inf ((a.hom.le).trans (by simp)) b.hom.le)) }, _],
                ?_, rfl⟩
        exact
          List.IsChain.cons_cons
            (Or.inl
              ⟨{  left := 𝟙 _
                  right := left i j }⟩)
            (List.IsChain.cons_cons
              (Or.inr
                ⟨{  left := 𝟙 _
                    right := left i i' }⟩)
              (List.IsChain.cons_cons
                (Or.inl
                  ⟨{  left := 𝟙 _
                      right := right i i' }⟩)
                (List.IsChain.singleton _)))
      · refine
          ⟨[{   left := ⟨⟨⟩⟩
                right := single i
                hom := ObjectProperty.homMk (homOfLE (a.hom.le.trans (by simp))) },
              { left := ⟨⟨⟩⟩
                right := pair i i'
                hom := ObjectProperty.homMk (homOfLE
                  (le_inf (a.hom.le.trans (by simp)) (b.hom.le.trans (by simp)))) },
              { left := ⟨⟨⟩⟩
                right := single i'
                hom := ObjectProperty.homMk (homOfLE (b.hom.le.trans (by simp))) }, _], ?_, rfl⟩
        exact
          List.IsChain.cons_cons
            (Or.inl
              ⟨{  left := 𝟙 _
                  right := left i j }⟩)
            (List.IsChain.cons_cons
              (Or.inr
                ⟨{  left := 𝟙 _
                    right := left i i' }⟩)
              (List.IsChain.cons_cons
                (Or.inl
                  ⟨{  left := 𝟙 _
                      right := right i i' }⟩)
                (List.IsChain.cons_cons
                  (Or.inr
                    ⟨{  left := 𝟙 _
                        right := left i' j' }⟩)
                  (List.IsChain.singleton _))))⟩

/-- The diagram in `Opens X` indexed by pairwise intersections from `U` is isomorphic
(in fact, equal) to the diagram factored through `OpensLeCover U`.
-/
/-
**TopCat.Presheaf.SheafCondition.pairwiseDiagramIso** 是 Mathlib 中的一个定义，位于命名空间 `T
opCat.Presheaf.SheafCondition`。
形式化陈述：pairwiseDiagramIso : Pairwise.diagram U ≅ pairwiseToOpensLeCover U ⋙ Objec
tProperty.ι _ where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram in `Opens X` indexed by pairwise intersections from `U` is isomorphi
c
(in fact, equal) to the diagram factored through `OpensLeCover U`.
-/
def pairwiseDiagramIso :
    Pairwise.diagram U ≅ pairwiseToOpensLeCover U ⋙ ObjectProperty.ι _ where
  hom := { app := by rintro (i | ⟨i, j⟩) <;> exact 𝟙 _ }
  inv := { app := by rintro (i | ⟨i, j⟩) <;> exact 𝟙 _ }

/--
The cocone `Pairwise.cocone U` with cocone point `iSup U` over `Pairwise.diagram U` is isomorphic
to the cocone `opensLeCoverCocone U` (with the same cocone point)
after appropriate whiskering and postcomposition.
-/
/-
**TopCat.Presheaf.SheafCondition.pairwiseCoconeIso** 是 Mathlib 中的一个定义，位于命名空间 `To
pCat.Presheaf.SheafCondition`。
形式化陈述：pairwiseCoconeIso : (Pairwise.cocone U).op ≅ (Cone.postcomposeEquivalence 
(NatIso.op (pairwiseDiagramIso U :) :)).functor.obj ((opensLeCoverCocone U).op.w
hisker (pairwiseToOpensLeCover U).op)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone `Pairwise.cocone U` with cocone point `iSup U` over `Pairwise.diagram
 U` is isomorphic
to the cocone `opensLeCoverCocone U` (with the same cocone point)
after appropriate whiskering and postcomposition.
-/
def pairwiseCoconeIso :
    (Pairwise.cocone U).op ≅
      (Cone.postcomposeEquivalence (NatIso.op (pairwiseDiagramIso U :) :)).functor.obj
        ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op) :=
  Cone.ext (Iso.refl _) (by cat_disch)

end SheafCondition

open SheafCondition

variable (F : Presheaf C X) {ι : Type*} (U : ι → Opens X)

/-- The diagram over all `{ V : Opens X // ∃ i, V ≤ U i }` is a limit iff the diagram
over `U i` and `U i ⊓ U j` is a limit. -/
/-
**TopCat.Presheaf.isLimitOpensLeCoverEquivPairwise** 是 Mathlib 中的一个定义，位于命名空间 `To
pCat.Presheaf`。
形式化陈述：isLimitOpensLeCoverEquivPairwise : IsLimit (F.mapCone (opensLeCoverCocone 
U).op) ≃ IsLimit (F.mapCone (Pairwise.cocone U).op)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The diagram over all `{ V : Opens X // ∃ i, V ≤ U i }` is a limit iff the diagra
m
over `U i` and `U i ⊓ U j` is a limit.
-/
def isLimitOpensLeCoverEquivPairwise :
    IsLimit (F.mapCone (opensLeCoverCocone U).op) ≃ IsLimit (F.mapCone (Pairwise.cocone U).op) :=
  calc
    IsLimit (F.mapCone (opensLeCoverCocone U).op) ≃
        IsLimit ((F.mapCone (opensLeCoverCocone U).op).whisker (pairwiseToOpensLeCover U).op) :=
      (Functor.Initial.isLimitWhiskerEquiv (pairwiseToOpensLeCover U).op _).symm
    _ ≃ IsLimit (F.mapCone ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op)) :=
      (IsLimit.equivIsoLimit F.mapConeWhisker.symm)
    _ ≃
        IsLimit
          ((Cone.postcomposeEquivalence _).functor.obj
            (F.mapCone ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op))) :=
      (IsLimit.postcomposeHomEquiv _ _).symm
    _ ≃
        IsLimit
          (F.mapCone
            ((Cone.postcomposeEquivalence _).functor.obj
              ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op))) :=
      (IsLimit.equivIsoLimit (Functor.mapConePostcomposeEquivalenceFunctor _).symm)
    _ ≃ IsLimit (F.mapCone (Pairwise.cocone U).op) :=
      IsLimit.equivIsoLimit ((Cone.functoriality _ _).mapIso (pairwiseCoconeIso U :).symm)

/-- The sheaf condition
in terms of a limit diagram over all `{ V : Opens X // ∃ i, V ≤ U i }`
is equivalent to the reformulation
in terms of a limit diagram over `U i` and `U i ⊓ U j`.
-/
/-
**TopCat.Presheaf.isSheafOpensLeCover_iff_isSheafPairwiseIntersections** 是 Mathl
ib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：isSheafOpensLeCover_iff_isSheafPairwiseIntersections : F.IsSheafOpensLeCov
er ↔ F.IsSheafPairwiseIntersections
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β

--- 原说明 ---
The sheaf condition
in terms of a limit diagram over all `{ V : Opens X // ∃ i, V ≤ U i }`
is equivalent to the reformulation
in terms of a limit diagram over `U i` and `U i ⊓ U j`.
-/
theorem isSheafOpensLeCover_iff_isSheafPairwiseIntersections :
    F.IsSheafOpensLeCover ↔ F.IsSheafPairwiseIntersections :=
  forall₂_congr fun _ U ↦ (F.isLimitOpensLeCoverEquivPairwise U).nonempty_congr

variable {F} in
/-
**TopCat.Presheaf.IsSheaf.isSheafPairwiseIntersections** 是 Mathlib 中的一个定理，位于命名空间
 `TopCat.Presheaf.IsSheaf`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : TopCat
} {F : TopCat.Presheaf C X} {ι : Type u_2}   (U : ι → TopologicalSpace.Opens ↑X)
,   F.IsSheaf →     Nonempty (CategoryTheory.Limits.IsLimit (CategoryTheory.Func
tor.mapCone F (CategoryTheory.Pairwise.cocone U).op))
参数：U : ι → TopologicalSpace.Opens ↑X；CategoryTheory.Limits.IsLimit (CategoryTheo
ry.Functor.mapCone F (CategoryTheory.Pairwise.cocone U).op)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `TopCat.Presheaf.IsSheaf.isSheafOpensLeCover`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] {X : TopCat} {F : TopCat.Presheaf C X} {ι : 
Type u_2}   (U : ι → TopologicalS…
-/
theorem IsSheaf.isSheafPairwiseIntersections (h : F.IsSheaf) :
    Nonempty (IsLimit (F.mapCone (Pairwise.cocone U).op)) :=
  (h.isSheafOpensLeCover U).map (F.isLimitOpensLeCoverEquivPairwise _)

/-- The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of a limit diagram over `U i` and `U i ⊓ U j`.
-/
/-
**TopCat.Presheaf.isSheaf_iff_isSheafPairwiseIntersections** 是 Mathlib 中的一个定理，位于
命名空间 `TopCat.Presheaf`。
形式化陈述：isSheaf_iff_isSheafPairwiseIntersections : F.IsSheaf ↔ F.IsSheafPairwiseIn
tersections
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover`：isSheaf_iff_isSheafOpen
sLeCover : F.IsSheaf ↔ F.IsSheafOpensLeCover
· 使用定理 `TopCat.Presheaf.isSheafOpensLeCover_iff_isSheafPairwiseIntersections`：is
SheafOpensLeCover_iff_isSheafPairwiseIntersections : F.IsSheafOpensLeCover ↔ F.I
sSheafPairwiseIntersections
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of a limit diagram over `U i` and `U i ⊓ U j`.
-/
theorem isSheaf_iff_isSheafPairwiseIntersections : F.IsSheaf ↔ F.IsSheafPairwiseIntersections := by
  rw [isSheaf_iff_isSheafOpensLeCover, isSheafOpensLeCover_iff_isSheafPairwiseIntersections]

variable {F} in
/-
**TopCat.Presheaf.IsSheaf.isSheafPreservesLimitPairwiseIntersections** 是 Mathlib
 中的一个定理，位于命名空间 `TopCat.Presheaf.IsSheaf`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : TopCat
} {F : TopCat.Presheaf C X} {ι : Type u_2}   (U : ι → TopologicalSpace.Opens ↑X)
,   F.IsSheaf → CategoryTheory.Limits.PreservesLimit (CategoryTheory.Pairwise.di
agram U).op F
参数：U : ι → TopologicalSpace.Opens ↑X；CategoryTheory.Pairwise.diagram U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `TopCat.Presheaf.IsSheaf.isSheafPairwiseIntersections`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] {X : TopCat} {F : TopCat.Presheaf C
 X} {ι : Type u_2}   (U : ι → TopologicalS…
-/
theorem IsSheaf.isSheafPreservesLimitPairwiseIntersections (h : F.IsSheaf) :
    PreservesLimit (Pairwise.diagram U).op F :=
  preservesLimit_of_preserves_limit_cone (Pairwise.coconeIsColimit U).op
    (h.isSheafPairwiseIntersections U).some

/-- The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of the presheaf preserving the limit of the diagram
consisting of the `U i` and `U i ⊓ U j`.
-/
/-
**TopCat.Presheaf.isSheaf_iff_isSheafPreservesLimitPairwiseIntersections** 是 Mat
hlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：isSheaf_iff_isSheafPreservesLimitPairwiseIntersections : F.IsSheaf ↔ F.IsS
heafPreservesLimitPairwiseIntersections
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.IsSheaf.isSheafPreservesLimitPairwiseIntersections`：∀ {C
 : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : TopCat} {F : Top
Cat.Presheaf C X} {ι : Type u_2}   (U : ι → TopologicalS…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopCat.Presheaf.isSheaf_iff_isSheafPairwiseIntersections`：isSheaf_iff_is
SheafPairwiseIntersections : F.IsSheaf ↔ F.IsSheafPairwiseIntersections

--- 原说明 ---
The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of the presheaf preserving the limit of the diagra
m
consisting of the `U i` and `U i ⊓ U j`.
-/
theorem isSheaf_iff_isSheafPreservesLimitPairwiseIntersections :
    F.IsSheaf ↔ F.IsSheafPreservesLimitPairwiseIntersections := by
  refine ⟨fun h U ↦ h.isSheafPreservesLimitPairwiseIntersections,
    fun h ↦ F.isSheaf_iff_isSheafPairwiseIntersections.mpr fun ι U ↦ ?_⟩
  have := h U
  exact ⟨isLimitOfPreserves _ (Pairwise.coconeIsColimit U).op⟩

end TopCat.Presheaf

namespace TopCat.Sheaf

variable (F : X.Sheaf C) (U V : Opens X)

open CategoryTheory.Limits

/-- For a sheaf `F`, `F(U ⊔ V)` is the pullback of `F(U) ⟶ F(U ⊓ V)` and `F(V) ⟶ F(U ⊓ V)`.
This is the pullback cone. -/
/-
**TopCat.Sheaf.interUnionPullbackCone** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Sheaf`。
形式化陈述：interUnionPullbackCone : PullbackCone (F.1.map (homOfLE inf_le_left : U ⊓ 
V ⟶ _).op) (F.1.map (homOfLE inf_le_right).op)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a sheaf `F`, `F(U ⊔ V)` is the pullback of `F(U) ⟶ F(U ⊓ V)` and `F(V) ⟶ F(U
 ⊓ V)`.
This is the pullback cone.
-/
def interUnionPullbackCone :
    PullbackCone (F.1.map (homOfLE inf_le_left : U ⊓ V ⟶ _).op)
      (F.1.map (homOfLE inf_le_right).op) :=
  PullbackCone.mk (F.1.map (homOfLE le_sup_left).op) (F.1.map (homOfLE le_sup_right).op) <| by
    rw [← F.1.map_comp, ← F.1.map_comp]
    congr 1

@[simp]
/-
**TopCat.Sheaf.interUnionPullbackCone_pt** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Sheaf
`。
形式化陈述：interUnionPullbackCone_pt : (interUnionPullbackCone F U V).pt = F.1.obj (o
p <| U ⊔ V)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem interUnionPullbackCone_pt : (interUnionPullbackCone F U V).pt = F.1.obj (op <| U ⊔ V) :=
  rfl

@[simp]
/-
**TopCat.Sheaf.interUnionPullbackCone_fst** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Shea
f`。
形式化陈述：interUnionPullbackCone_fst : (interUnionPullbackCone F U V).fst = F.1.map 
(homOfLE le_sup_left).op
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem interUnionPullbackCone_fst :
    (interUnionPullbackCone F U V).fst = F.1.map (homOfLE le_sup_left).op :=
  rfl

@[simp]
/-
**TopCat.Sheaf.interUnionPullbackCone_snd** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Shea
f`。
形式化陈述：interUnionPullbackCone_snd : (interUnionPullbackCone F U V).snd = F.1.map 
(homOfLE le_sup_right).op
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem interUnionPullbackCone_snd :
    (interUnionPullbackCone F U V).snd = F.1.map (homOfLE le_sup_right).op :=
  rfl

variable
  (s :
    PullbackCone (F.1.map (homOfLE inf_le_left : U ⊓ V ⟶ _).op) (F.1.map (homOfLE inf_le_right).op))

set_option backward.defeqAttrib.useBackward true in
/-- (Implementation).
Every cone over `F(U) ⟶ F(U ⊓ V)` and `F(V) ⟶ F(U ⊓ V)` factors through `F(U ⊔ V)`.
-/
/-
**TopCat.Sheaf.interUnionPullbackConeLift** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Shea
f`。
形式化陈述：interUnionPullbackConeLift : s.pt ⟶ F.1.obj (op (U ⊔ V))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation).
Every cone over `F(U) ⟶ F(U ⊓ V)` and `F(V) ⟶ F(U ⊓ V)` factors through `F(U ⊔ V
)`.
-/
def interUnionPullbackConeLift : s.pt ⟶ F.1.obj (op (U ⊔ V)) := by
  let ι : ULift.{w} WalkingPair → Opens X := fun j => WalkingPair.casesOn j.down U V
  have hι : U ⊔ V = iSup ι := by
    ext
    rw [Opens.coe_iSup, Set.mem_iUnion]
    constructor
    · rintro (h | h)
      exacts [⟨⟨WalkingPair.left⟩, h⟩, ⟨⟨WalkingPair.right⟩, h⟩]
    · rintro ⟨⟨_ | _⟩, h⟩
      exacts [Or.inl h, Or.inr h]
  refine
    (F.presheaf.isSheaf_iff_isSheafPairwiseIntersections.mp F.2 ι).some.lift
        ⟨s.pt,
          { app := ?_
            naturality := ?_ }⟩ ≫
      F.1.map (eqToHom hι).op
  · rintro ((_ | _) | (_ | _))
    exacts [s.fst, s.snd, s.fst ≫ F.1.map (homOfLE inf_le_left).op,
      s.snd ≫ F.1.map (homOfLE inf_le_left).op]
  rintro ⟨i⟩ ⟨j⟩ f
  let g : j ⟶ i := f.unop
  have : f = g.op := rfl
  clear_value g
  subst this
  rcases i with (⟨⟨_ | _⟩⟩ | ⟨⟨_ | _⟩, ⟨_⟩⟩) <;>
  rcases j with (⟨⟨_ | _⟩⟩ | ⟨⟨_ | _⟩, ⟨_⟩⟩) <;>
  rcases g with ⟨⟩ <;>
  dsimp [Pairwise.diagram] <;>
  simp only [ι, Category.id_comp, s.condition, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← cancel_mono (F.1.map (eqToHom <| inf_comm U V : U ⊓ V ⟶ _).op), Category.assoc,
    Category.assoc, ← F.1.map_comp, ← F.1.map_comp]
  exact s.condition.symm

set_option backward.isDefEq.respectTransparency false in
/-
**TopCat.Sheaf.interUnionPullbackConeLift_left** 是 Mathlib 中的一个定理，位于命名空间 `TopCat
.Sheaf`。
形式化陈述：interUnionPullbackConeLift_left : interUnionPullbackConeLift F U V s ≫ F.1
.map (homOfLE le_sup_left).op = s.fst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Sheaf.interUnionPullbackConeLift.eq_1`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] {X : TopCat} (F : TopCat.Sheaf C X)   (U V 
: TopologicalSpace.Opens ↑X)   (s …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopCat.Presheaf.isSheaf_iff_isSheafPairwiseIntersections`：isSheaf_iff_is
SheafPairwiseIntersections : F.IsSheaf ↔ F.IsSheafPairwiseIntersections
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
theorem interUnionPullbackConeLift_left :
    interUnionPullbackConeLift F U V s ≫ F.1.map (homOfLE le_sup_left).op = s.fst := by
  rw [interUnionPullbackConeLift, Category.assoc, ← F.1.map_comp]
  exact
    (F.presheaf.isSheaf_iff_isSheafPairwiseIntersections.mp F.2 _).some.fac _ <|
      op <| Pairwise.single <| ULift.up WalkingPair.left

set_option backward.isDefEq.respectTransparency false in
/-
**TopCat.Sheaf.interUnionPullbackConeLift_right** 是 Mathlib 中的一个定理，位于命名空间 `TopCa
t.Sheaf`。
形式化陈述：interUnionPullbackConeLift_right : interUnionPullbackConeLift F U V s ≫ F.
1.map (homOfLE le_sup_right).op = s.snd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Sheaf.interUnionPullbackConeLift.eq_1`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] {X : TopCat} (F : TopCat.Sheaf C X)   (U V 
: TopologicalSpace.Opens ↑X)   (s …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopCat.Presheaf.isSheaf_iff_isSheafPairwiseIntersections`：isSheaf_iff_is
SheafPairwiseIntersections : F.IsSheaf ↔ F.IsSheafPairwiseIntersections
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
theorem interUnionPullbackConeLift_right :
    interUnionPullbackConeLift F U V s ≫ F.1.map (homOfLE le_sup_right).op = s.snd := by
  rw [interUnionPullbackConeLift, Category.assoc, ← F.1.map_comp]
  exact
    (F.presheaf.isSheaf_iff_isSheafPairwiseIntersections.mp F.2 _).some.fac _ <|
      op <| Pairwise.single <| ULift.up WalkingPair.right

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For a sheaf `F`, `F(U ⊔ V)` is the pullback of `F(U) ⟶ F(U ⊓ V)` and `F(V) ⟶ F(U ⊓ V)`. -/
/-
**TopCat.Sheaf.isLimitPullbackCone** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Sheaf`。
形式化陈述：isLimitPullbackCone : IsLimit (interUnionPullbackCone F U V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a sheaf `F`, `F(U ⊔ V)` is the pullback of `F(U) ⟶ F(U ⊓ V)` and `F(V) ⟶ F(U
 ⊓ V)`.
-/
def isLimitPullbackCone : IsLimit (interUnionPullbackCone F U V) := by
  let ι : ULift.{w} WalkingPair → Opens X := fun ⟨j⟩ => WalkingPair.casesOn j U V
  have hι : U ⊔ V = iSup ι := by
    ext
    rw [Opens.coe_iSup, Set.mem_iUnion]
    constructor
    · rintro (h | h)
      exacts [⟨⟨WalkingPair.left⟩, h⟩, ⟨⟨WalkingPair.right⟩, h⟩]
    · rintro ⟨⟨_ | _⟩, h⟩
      exacts [Or.inl h, Or.inr h]
  apply PullbackCone.isLimitAux'
  intro s
  use interUnionPullbackConeLift F U V s
  refine ⟨?_, ?_, ?_⟩
  · apply interUnionPullbackConeLift_left
  · apply interUnionPullbackConeLift_right
  · intro m h₁ h₂
    rw [← cancel_mono (F.1.map (eqToHom hι.symm).op)]
    apply (F.presheaf.isSheaf_iff_isSheafPairwiseIntersections.mp F.2 ι).some.hom_ext
    rintro ((_ | _) | (_ | _)) <;>
    rw [Category.assoc, Category.assoc, Functor.mapCone_π_app, ← F.1.map_comp]
    · convert! h₁
      apply interUnionPullbackConeLift_left
    · convert! h₂
      apply interUnionPullbackConeLift_right
    all_goals
      dsimp only [Functor.op, Pairwise.cocone_ι_app, Functor.mapCone_π_app, Cocone.op,
        Pairwise.coconeιApp, unop_op, op_comp, NatTrans.op]
      simp_rw [F.1.map_comp, ← Category.assoc]
      congr 1
      simp_rw [Category.assoc, ← F.1.map_comp]
    · convert! h₁
      apply interUnionPullbackConeLift_left
    · convert! h₂
      apply interUnionPullbackConeLift_right

/-- If `U, V` are disjoint, then `F(U ⊔ V) = F(U) × F(V)`. -/
/-
**TopCat.Sheaf.isProductOfDisjoint** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Sheaf`。
形式化陈述：isProductOfDisjoint (h : U ⊓ V = ⊥) : IsLimit (BinaryFan.mk (F.1.map (homO
fLE le_sup_left : _ ⟶ U ⊔ V).op) (F.1.map (homOfLE le_sup_right : _ ⟶ U ⊔ V).op)
)
参数：h : U ⊓ V = ⊥。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `U, V` are disjoint, then `F(U ⊔ V) = F(U) × F(V)`.
-/
def isProductOfDisjoint (h : U ⊓ V = ⊥) :
    IsLimit
      (BinaryFan.mk (F.1.map (homOfLE le_sup_left : _ ⟶ U ⊔ V).op)
        (F.1.map (homOfLE le_sup_right : _ ⟶ U ⊔ V).op)) :=
  isProductOfIsTerminalIsPullback _ _ _ _ (F.isTerminalOfEqEmpty h) (isLimitPullbackCone F U V)

end TopCat.Sheaf

