/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.SmallObject.Construction
public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall
public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# Cardinals that are suitable for the small object argument

In this file, given a class of morphisms `I : MorphismProperty C` and
a regular cardinal `κ : Cardinal.{w}`, we define a typeclass
`IsCardinalForSmallObjectArgument I κ` which requires certain
smallness properties (`I` is `w`-small, `C` is locally `w`-small),
the existence of certain colimits (pushouts, coproducts of size `w`,
and the condition `HasIterationOfShape κ.ord.ToType C` about the
existence of colimits indexed by limit ordinal smaller than or equal
to `κ.ord`), and the technical assumption that if `A` is the
a morphism in `I`, then the functor `Hom(A, _)` should commute
with the filtering colimits corresponding to relative
`I`-cell complexes. (This last condition shall hold when `κ`
is the successor of an infinite cardinal `c` such that all these objects `A` are `c`-presentable,
see `Mathlib/CategoryTheory/Presentable/Basic.lean`.)

Given `I : MorphismProperty C`, we shall say that `I` permits
the small object argument if there exists `κ` such that
`IsCardinalForSmallObjectArgument I κ` holds. See the file
`Mathlib/CategoryTheory/SmallObject/Basic.lean` for the definition of this typeclass
`HasSmallObjectArgument` and an outline of the proof.

## Main results

Assuming `IsCardinalForSmallObjectArgument I κ`, any morphism `f : X ⟶ Y`
is factored as `ιObj I κ f ≫ πObj I κ f = f`. It is shown that `ιObj I κ f`
is a relative `I`-cell complex (see `SmallObject.relativeCellComplexιObj`)
and that `πObj I κ f` has the right lifting property with respect to `I`
(see `SmallObject.rlp_πObj`). This construction is obtained by
iterating to the power `κ.ord.ToType` the functor `Arrow C ⥤ Arrow C` defined
in the file `Mathlib/CategoryTheory/SmallObject/Construction.lean`.
This factorization is functorial in `f`
and gives the property `HasFunctorialFactorization I.rlp.llp I.rlp`.
Finally, the lemma `llp_rlp_of_isCardinalForSmallObjectArgument`
(and its primed version) shows that the morphisms in `I.rlp.llp` are exactly
the retracts of the transfinite compositions (of shape `κ.ord.ToType`) of
pushouts of coproducts of morphisms in `I`.

## References
- https://ncatlab.org/nlab/show/small+object+argument

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Category HomotopicalAlgebra Limits SmallObject

variable {C : Type u} [Category.{v} C] (I : MorphismProperty C)

namespace MorphismProperty

/-- Given `I : MorphismProperty C` and a regular cardinal `κ : Cardinal.{w}`,
this property asserts the technical conditions which allow to proceed
to the small object argument by doing a construction by transfinite
induction indexed by the well-ordered type `κ.ord.ToType`. -/
/-
**CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument** 是 Mathlib 中
的一个类，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：IsCardinalForSmallObjectArgument (κ : Cardinal.{w}) [Fact κ.IsRegular] [Or
derBot κ.ord.ToType] : Prop where isSmall : IsSmall.{w} I
参数：κ : Cardinal.{w}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `I : MorphismProperty C` and a regular cardinal `κ : Cardinal.{w}`,
this property asserts the technical conditions which allow to proceed
to the small object argument by doing a construction by transfinite
induction indexed by the well-ordered type `κ.ord.ToType`.
-/
class IsCardinalForSmallObjectArgument (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [OrderBot κ.ord.ToType] : Prop where
  isSmall : IsSmall.{w} I := by infer_instance
  locallySmall : LocallySmall.{w} C := by infer_instance
  hasPushouts : HasPushouts C := by infer_instance
  hasCoproducts : HasCoproducts.{w} C := by infer_instance
  hasIterationOfShape : HasIterationOfShape κ.ord.ToType C := by infer_instance
  preservesColimit {A B X Y : C} (i : A ⟶ B) (_ : I i) (f : X ⟶ Y)
    (hf : RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) ↦ I.homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op A))

end MorphismProperty

namespace SmallObject

open MorphismProperty

variable (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [I.IsCardinalForSmallObjectArgument κ]

include I κ

/-
**CategoryTheory.SmallObject.isSmall** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.S
mallObject`。
形式化陈述：isSmall : IsSmall.{w} I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument.isSmall
`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {I : CategoryTheory.M
orphismProperty C} (κ : Cardinal.{w})   {inst_1 : Fact κ.IsReg…
-/
lemma isSmall : IsSmall.{w} I :=
  IsCardinalForSmallObjectArgument.isSmall κ
/-
**CategoryTheory.SmallObject.locallySmall** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.SmallObject`。
形式化陈述：locallySmall : LocallySmall.{w} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument.locally
Small`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} (I : CategoryThe
ory.MorphismProperty C) (κ : Cardinal.{w})   {inst_1 : Fact κ.IsReg…
-/
lemma locallySmall : LocallySmall.{w} C :=
  IsCardinalForSmallObjectArgument.locallySmall I κ
/-
**CategoryTheory.SmallObject.hasIterationOfShape** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.SmallObject`。
形式化陈述：hasIterationOfShape : HasIterationOfShape κ.ord.ToType C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument.hasIter
ationOfShape`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} (I : Cate
goryTheory.MorphismProperty C) {κ : Cardinal.{w}}   {inst_1 : Fact κ.IsReg…
-/
lemma hasIterationOfShape : HasIterationOfShape κ.ord.ToType C :=
  IsCardinalForSmallObjectArgument.hasIterationOfShape I
/-
**CategoryTheory.SmallObject.hasPushouts** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.SmallObject`。
形式化陈述：hasPushouts : HasPushouts C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument.hasPush
outs`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} (I : CategoryTheo
ry.MorphismProperty C) (κ : Cardinal.{w})   {inst_1 : Fact κ.IsReg…
-/
lemma hasPushouts : HasPushouts C :=
  IsCardinalForSmallObjectArgument.hasPushouts I κ
/-
**CategoryTheory.SmallObject.hasCoproducts** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.SmallObject`。
形式化陈述：hasCoproducts : HasCoproducts.{w} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument.hasCopr
oducts`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} (I : CategoryTh
eory.MorphismProperty C) (κ : Cardinal.{w})   {inst_1 : Fact κ.IsReg…
-/
lemma hasCoproducts : HasCoproducts.{w} C :=
  IsCardinalForSmallObjectArgument.hasCoproducts I κ
/-
**CategoryTheory.SmallObject.preservesColimit** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.SmallObject`。
形式化陈述：preservesColimit {A B X Y : C} (i : A ⟶ B) (hi : I i) (f : X ⟶ Y) (hf : Re
lativeCellComplex.{w} (fun (_ : κ.ord.ToType) => I.homFamily) f) : PreservesColi
mit hf.F (coyoneda.obj (Opposite.op A))
参数：i : A ⟶ B；hi : I i；f : X ⟶ Y；hf : RelativeCellComplex.{w} (fun (_ : κ.ord.ToT
ype) => I.homFamily) f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument.preserv
esColimit`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {I : Categor
yTheory.MorphismProperty C} {κ : Cardinal.{w}}   {inst_1 : Fact κ.IsReg…
-/
lemma preservesColimit {A B X Y : C} (i : A ⟶ B) (hi : I i) (f : X ⟶ Y)
    (hf : RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) ↦ I.homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op A)) :=
  IsCardinalForSmallObjectArgument.preservesColimit i hi f hf
/-
**CategoryTheory.SmallObject.hasColimitsOfShape_discrete** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.SmallObject`。
形式化陈述：hasColimitsOfShape_discrete (X Y : C) (p : X ⟶ Y) : HasColimitsOfShape (Di
screte (FunctorObjIndex I.homFamily p)) C
参数：X Y : C；p : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SmallObject.locallySmall`：locallySmall : LocallySmall.{w}
 C
· 使用引理 `CategoryTheory.SmallObject.isSmall`：isSmall : IsSmall.{w} I
· 使用引理 `CategoryTheory.SmallObject.hasCoproducts`：hasCoproducts : HasCoproducts.
{w} C
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
· 使用定理 `CategoryTheory.SmallObject.instSmallFunctorObjIndex`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {I : Type w} {A B : I → C} (f : (i : I) → 
A i ⟶ B i) {S X : C}   (πX : X ⟶ S) [Cate…
· 使用定理 `CategoryTheory.MorphismProperty.IsSmall.small_toSet`：∀ {C : Type u} {ins
t : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.MorphismProperty C}   
[self : CategoryTheory.MorphismProperty.I…
-/
lemma hasColimitsOfShape_discrete (X Y : C) (p : X ⟶ Y) :
    HasColimitsOfShape
      (Discrete (FunctorObjIndex I.homFamily p)) C := by
  have := locallySmall I κ
  have := isSmall I κ
  have := hasCoproducts I κ
  exact hasColimitsOfShape_of_equivalence
    (Discrete.equivalence (equivShrink.{w} _)).symm

/-- The successor structure on `Arrow C ⥤ Arrow C` corresponding
to the iterations of the natural transformation
`ε : 𝟭 (Arrow C) ⟶ SmallObject.functor I.homFamily`
(see the file `SmallObject.Construction`). -/
/-
**CategoryTheory.SmallObject.succStruct** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.SmallObject`。
形式化陈述：succStruct : SuccStruct (Arrow C ⥤ Arrow C)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SmallObject.hasPushouts`：hasPushouts : HasPushouts C
· 使用引理 `CategoryTheory.SmallObject.hasColimitsOfShape_discrete`：hasColimitsOfSha
pe_discrete (X Y : C) (p : X ⟶ Y) : HasColimitsOfShape (Discrete (FunctorObjInde
x I.homFamily p)) C

--- 原说明 ---
The successor structure on `Arrow C ⥤ Arrow C` corresponding
to the iterations of the natural transformation
`ε : 𝟭 (Arrow C) ⟶ SmallObject.functor I.homFamily`
(see the file `SmallObject.Construction`).
-/
noncomputable def succStruct : SuccStruct (Arrow C ⥤ Arrow C) :=
  haveI := hasColimitsOfShape_discrete I κ
  haveI := hasPushouts I κ
  SuccStruct.ofNatTrans (ε I.homFamily)

set_option backward.isDefEq.respectTransparency.types false in
/-- For the successor structure `succStruct I κ` on `Arrow C ⥤ Arrow C`,
the morphism from an object to its successor induces
morphisms in `C` which consists in attaching `I`-cells. -/
/-
**CategoryTheory.SmallObject.attachCellsOfSuccStructProp** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.SmallObject`。
形式化陈述：attachCellsOfSuccStructProp {F G : Arrow C ⥤ Arrow C} {φ : F ⟶ G} (h : (su
ccStruct I κ).prop φ) (f : Arrow C) : AttachCells.{w} I.homFamily (φ.app f).left
参数：h : (succStruct I κ).prop φ；f : Arrow C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SmallObject.locallySmall`：locallySmall : LocallySmall.{w}
 C

--- 原说明 ---
For the successor structure `succStruct I κ` on `Arrow C ⥤ Arrow C`,
the morphism from an object to its successor induces
morphisms in `C` which consists in attaching `I`-cells.
-/
noncomputable def attachCellsOfSuccStructProp
    {F G : Arrow C ⥤ Arrow C} {φ : F ⟶ G}
    (h : (succStruct I κ).prop φ) (f : Arrow C) :
    AttachCells.{w} I.homFamily (φ.app f).left :=
  haveI := locallySmall I κ
  haveI := isSmall I κ
  haveI := hasColimitsOfShape_discrete I κ
  haveI := hasPushouts I κ
  AttachCells.ofArrowIso (attachCellsιFunctorObjOfSmall _ _)
    ((Functor.mapArrow ((evaluation _ _).obj f ⋙
      Arrow.leftFunc)).mapIso h.arrowIso.symm)

/-- The class of morphisms in `Arrow C` which on the left side are
pushouts of coproducts of morphisms in `I`, and which are
isomorphisms on the right side. -/
/-
**CategoryTheory.SmallObject.propArrow** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.SmallObject`。
形式化陈述：propArrow : MorphismProperty (Arrow C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of morphisms in `Arrow C` which on the left side are
pushouts of coproducts of morphisms in `I`, and which are
isomorphisms on the right side.
-/
def propArrow : MorphismProperty (Arrow C) := fun _ _ f ↦
  (coproducts.{w} I).pushouts f.left ∧ (isomorphisms C) f.right

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.SmallObject.succStruct_prop_le_propArrow** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.SmallObject`。
形式化陈述：succStruct_prop_le_propArrow : (succStruct I κ).prop <= (propArrow.{w} I).
functorCategory (Arrow C)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SmallObject.locallySmall`：locallySmall : LocallySmall.{w}
 C
· 使用引理 `CategoryTheory.SmallObject.isSmall`：isSmall : IsSmall.{w} I
· 使用引理 `CategoryTheory.SmallObject.hasColimitsOfShape_discrete`：hasColimitsOfSha
pe_discrete (X Y : C) (p : X ⟶ Y) : HasColimitsOfShape (Discrete (FunctorObjInde
x I.homFamily p)) C
· 使用引理 `CategoryTheory.SmallObject.hasPushouts`：hasPushouts : HasPushouts C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.ofHoms_homFamily`：ofHoms_homFamily (P : 
MorphismProperty C) : ofHoms P.homFamily = P
· 使用引理 `CategoryTheory.MorphismProperty.pushouts_mk`：pushouts_mk {A B X Y : C} {
f : A ⟶ X} {q : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} (sq : IsPushout f q p g) (hq : P 
q) : P.pushouts p
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `CategoryTheory.SmallObject.functorObj_isPushout`：functorObj_isPushout : 
IsPushout (functorObjTop f πX) (functorObjLeft f πX) (ιFunctorObj f πX) (ρFuncto
rObj f πX)
· 使用引理 `CategoryTheory.MorphismProperty.coproducts_of_small`：coproducts_of_small
 {X Y : C} (f : X ⟶ Y) {J : Type w'} (hf : W.colimitsOfShape (Discrete J) f) [Sm
all.{w} J] : coproducts.{w} W f
· 使用引理 `CategoryTheory.MorphismProperty.colimitsOfShape_colimMap`：colimitsOfShap
e_colimMap {X Y : J ⥤ C} (f : X ⟶ Y) [HasColimit X] [HasColimit Y] (hf : W.funct
orCategory _ f) : W.colimitsOfShape J (colimMa…
· 使用定理 `CategoryTheory.SmallObject.instSmallFunctorObjIndex`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {I : Type w} {A B : I → C} (f : (i : I) → 
A i ⟶ B i) {S X : C}   (πX : X ⟶ S) [Cate…
· 使用定理 `CategoryTheory.MorphismProperty.IsSmall.small_toSet`：∀ {C : Type u} {ins
t : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.MorphismProperty C}   
[self : CategoryTheory.MorphismProperty.I…
· 使用定理 `CategoryTheory.MorphismProperty.isomorphisms.iff`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Morph
ismProperty.isomorphisms C f ↔ Categor…
-/
lemma succStruct_prop_le_propArrow :
    (succStruct I κ).prop ≤ (propArrow.{w} I).functorCategory (Arrow C) := by
  have := locallySmall I κ
  have := isSmall I κ
  have := hasColimitsOfShape_discrete I κ
  have := hasPushouts I κ
  intro _ _ _ ⟨F⟩ f
  constructor
  · nth_rw 1 [← I.ofHoms_homFamily]
    apply pushouts_mk _ (functorObj_isPushout I.homFamily (F.obj f).hom)
    exact coproducts_of_small _ _ (colimitsOfShape_colimMap _ (by rintro ⟨j⟩; constructor))
  · rw [MorphismProperty.isomorphisms.iff]
    dsimp [succStruct]
    infer_instance

/-- The functor `κ.ord.ToType ⥤ Arrow C ⥤ Arrow C` corresponding to the
iterations of the successor structure `succStruct I κ`. -/
/-
**CategoryTheory.SmallObject.iterationFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.SmallObject`。
形式化陈述：iterationFunctor : κ.ord.ToType ⥤ Arrow C ⥤ Arrow C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `κ.ord.ToType ⥤ Arrow C ⥤ Arrow C` corresponding to the
iterations of the successor structure `succStruct I κ`.
-/
noncomputable def iterationFunctor : κ.ord.ToType ⥤ Arrow C ⥤ Arrow C :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).iterationFunctor κ.ord.ToType

/-- The colimit of `iterationFunctor I κ`. -/
/-
**CategoryTheory.SmallObject.iteration** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.SmallObject`。
形式化陈述：iteration : Arrow C ⥤ Arrow C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit of `iterationFunctor I κ`.
-/
noncomputable def iteration : Arrow C ⥤ Arrow C :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).iteration κ.ord.ToType

/-- The natural "inclusion" `𝟭 (Arrow C) ⟶ iteration I κ`. -/
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural "inclusion" `𝟭 (Arrow C) ⟶ iteration I κ`.
-/
noncomputable def ιIteration : 𝟭 _ ⟶ iteration I κ :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).ιIteration κ.ord.ToType

/-- The morphism `ιIteration I κ` is a transfinite composition of shape
`κ.ord.ToType` of morphisms satisfying `(succStruct I κ).prop`. -/
/-
**CategoryTheory.SmallObject.transfiniteCompositionOfShapeSuccStructProp** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.SmallObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `ιIteration I κ` is a transfinite composition of shape
`κ.ord.ToType` of morphisms satisfying `(succStruct I κ).prop`.
-/
noncomputable def transfiniteCompositionOfShapeSuccStructPropιIteration :
    (succStruct I κ).prop.TransfiniteCompositionOfShape κ.ord.ToType (ιIteration I κ) :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).transfiniteCompositionOfShapeιIteration κ.ord.ToType

@[simp]
/-
**CategoryTheory.SmallObject.transfiniteCompositionOfShapeSuccStructProp** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma transfiniteCompositionOfShapeSuccStructPropιIteration_F :
    (transfiniteCompositionOfShapeSuccStructPropιIteration I κ).F =
      iterationFunctor I κ :=
  rfl

/-- For any `f : Arrow C`, the map `((ιIteration I κ).app f).right` is
a transfinite composition of isomorphisms. -/
/-
**CategoryTheory.SmallObject.transfiniteCompositionOfShape** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.SmallObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any `f : Arrow C`, the map `((ιIteration I κ).app f).right` is
a transfinite composition of isomorphisms.
-/
noncomputable def transfiniteCompositionOfShapeιIterationAppRight (f : Arrow C) :
    (isomorphisms C).TransfiniteCompositionOfShape κ.ord.ToType
      ((ιIteration I κ).app f).right :=
  haveI := hasIterationOfShape I κ
  let h := transfiniteCompositionOfShapeSuccStructPropιIteration I κ
  { toTransfiniteCompositionOfShape :=
      h.toTransfiniteCompositionOfShape.map ((evaluation _ _).obj f ⋙ Arrow.rightFunc)
    map_mem j hj := ((succStruct_prop_le_propArrow I κ _ (h.map_mem j hj)) f).2 }
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : Arrow C) : IsIso ((ιIteration I κ).app f).right :=
  (transfiniteCompositionOfShapeιIterationAppRight I κ f).isIso
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {j₁ j₂ : κ.ord.ToType} (φ : j₁ ⟶ j₂) (f : Arrow C) :
    IsIso (((iterationFunctor I κ).map φ).app f).right :=
  inferInstanceAs (IsIso ((transfiniteCompositionOfShapeιIterationAppRight I κ f).F.map φ))

/-- For any `f : Arrow C`, the object `((iteration I κ).obj f).right`
identifies to `f.right`. -/
@[simps! hom]
/-
**CategoryTheory.SmallObject.iterationObjRightIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.SmallObject`。
形式化陈述：iterationObjRightIso (f : Arrow C) : f.right ≅ ((iteration I κ).obj f).rig
ht
参数：f : Arrow C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SmallObject.instIsIsoRightAppArrowιIteration`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] (I : CategoryTheory.MorphismProper
ty C) (κ : Cardinal.{w})   [inst_1 : Fact κ.IsReg…

--- 原说明 ---
For any `f : Arrow C`, the object `((iteration I κ).obj f).right`
identifies to `f.right`.
-/
noncomputable def iterationObjRightIso (f : Arrow C) :
    f.right ≅ ((iteration I κ).obj f).right :=
  asIso ((ιIteration I κ).app f).right

set_option backward.isDefEq.respectTransparency false in
/-- For any `f : Arrow C` and `j : κ.ord.ToType`, the object
`(((iterationFunctor I κ).obj j).obj f).right` identifies to `f.right`. -/
/-
**CategoryTheory.SmallObject.iterationFunctorObjObjRightIso** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.SmallObject`。
形式化陈述：iterationFunctorObjObjRightIso (f : Arrow C) (j : κ.ord.ToType) : (((itera
tionFunctor I κ).obj j).obj f).right ≅ f.right
参数：f : Arrow C；j : κ.ord.ToType。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any `f : Arrow C` and `j : κ.ord.ToType`, the object
`(((iterationFunctor I κ).obj j).obj f).right` identifies to `f.right`.
-/
noncomputable def iterationFunctorObjObjRightIso (f : Arrow C) (j : κ.ord.ToType) :
    (((iterationFunctor I κ).obj j).obj f).right ≅ f.right :=
  asIso ((transfiniteCompositionOfShapeιIterationAppRight I κ f).incl.app j) ≪≫
    (iterationObjRightIso I κ f).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SmallObject.iterationFunctorObjObjRightIso_** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.SmallObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iterationFunctorObjObjRightIso_ιIteration_app_right (f : Arrow C) (j : κ.ord.ToType) :
    (iterationFunctorObjObjRightIso I κ f j).hom ≫ ((ιIteration I κ).app f).right =
      (transfiniteCompositionOfShapeιIterationAppRight I κ f).incl.app j := by
  simp [iterationFunctorObjObjRightIso, iterationObjRightIso]
/-
**CategoryTheory.SmallObject.prop_iterationFunctor_map_succ** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.SmallObject`。
形式化陈述：prop_iterationFunctor_map_succ (j : κ.ord.ToType) : (succStruct I κ).prop 
((iterationFunctor I κ).map (homOfLE (Order.le_succ j)))
参数：j : κ.ord.ToType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SmallObject.hasIterationOfShape`：hasIterationOfShape : Ha
sIterationOfShape κ.ord.ToType C
· 使用定理 `Cardinal.noMaxOrder`：noMaxOrder {c} (h : ℵ₀ <= c) : NoMaxOrder c.ord.ToT
ype
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.prop_iterationFunctor_map_succ`：pr
op_iterationFunctor_map_succ (j : J) (hj : ¬ IsMax j) : Φ.prop ((Φ.iterationFunc
tor J).map (homOfLE (Order.le_succ j)))
· 使用定理 `CategoryTheory.Limits.instHasIterationOfShapeFunctor`：∀ (J : Type w) [in
st : LinearOrder J] (C : Type u) [inst_1 : CategoryTheory.Category.{v, u} C] (K 
: Type u')   [inst_2 : CategoryTheory.Cate…
· 使用定理 `CategoryTheory.Limits.instHasIterationOfShapeArrow`：∀ (J : Type w) [inst
 : LinearOrder J] (C : Type u) [inst_1 : CategoryTheory.Category.{v, u} C]   [Ca
tegoryTheory.Limits.HasIterationOfShape …
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
lemma prop_iterationFunctor_map_succ (j : κ.ord.ToType) :
    (succStruct I κ).prop ((iterationFunctor I κ).map (homOfLE (Order.le_succ j))) := by
  have := hasIterationOfShape I κ
  have := Cardinal.noMaxOrder (Fact.elim inferInstance : κ.IsRegular).aleph0_le
  exact (succStruct I κ).prop_iterationFunctor_map_succ j (not_isMax j)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For any `f : Arrow C` and `j : κ.ord.ToType`, the morphism
`((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f` identifies
to a morphism given by `SmallObject.ε I.homFamily`. -/
/-
**CategoryTheory.SmallObject.iterationFunctorMapSuccAppArrowIso** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.SmallObject`。
形式化陈述：iterationFunctorMapSuccAppArrowIso (f : Arrow C) (j : κ.ord.ToType) : letI
参数：f : Arrow C；j : κ.ord.ToType。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SmallObject.hasIterationOfShape`：hasIterationOfShape : Ha
sIterationOfShape κ.ord.ToType C
· 使用引理 `CategoryTheory.SmallObject.hasPushouts`：hasPushouts : HasPushouts C
· 使用引理 `CategoryTheory.SmallObject.hasColimitsOfShape_discrete`：hasColimitsOfSha
pe_discrete (X Y : C) (p : X ⟶ Y) : HasColimitsOfShape (Discrete (FunctorObjInde
x I.homFamily p)) C

--- 原说明 ---
For any `f : Arrow C` and `j : κ.ord.ToType`, the morphism
`((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f` identifies
to a morphism given by `SmallObject.ε I.homFamily`.
-/
noncomputable def iterationFunctorMapSuccAppArrowIso (f : Arrow C) (j : κ.ord.ToType) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    Arrow.mk (((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f) ≅
      (ε I.homFamily).app (((iterationFunctor I κ).obj j).obj f) :=
  have := hasIterationOfShape I κ
  have := Cardinal.noMaxOrder (Fact.elim inferInstance : κ.IsRegular).aleph0_le
  Arrow.isoMk (Iso.refl _)
    (((evaluation _ _).obj f).mapIso
      ((succStruct I κ).iterationFunctorObjSuccIso j (not_isMax j))) (by
    have := NatTrans.congr_app ((succStruct I κ).iterationFunctor_map_succ j (not_isMax j)) f
    dsimp at this
    dsimp [iterationFunctor]
    rw [id_comp, this, assoc, Iso.inv_hom_id_app, comp_id]
    dsimp [succStruct])

@[simp]
/-
**CategoryTheory.SmallObject.iterationFunctorMapSuccAppArrowIso_hom_left** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObject`。
形式化陈述：iterationFunctorMapSuccAppArrowIso_hom_left (f : Arrow C) (j : κ.ord.ToTyp
e) : (iterationFunctorMapSuccAppArrowIso I κ f j).hom.left = 𝟙 _
参数：f : Arrow C；j : κ.ord.ToType。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用引理 `CategoryTheory.SmallObject.hasPushouts`：hasPushouts : HasPushouts C
· 使用引理 `CategoryTheory.SmallObject.hasColimitsOfShape_discrete`：hasColimitsOfSha
pe_discrete (X Y : C) (p : X ⟶ Y) : HasColimitsOfShape (Discrete (FunctorObjInde
x I.homFamily p)) C
-/
lemma iterationFunctorMapSuccAppArrowIso_hom_left (f : Arrow C) (j : κ.ord.ToType) :
    (iterationFunctorMapSuccAppArrowIso I κ f j).hom.left = 𝟙 _ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in -- Needed below
@[reassoc (attr := simp)]
/-
**CategoryTheory.SmallObject.iterationFunctorMapSuccAppArrowIso_hom_right_right_
comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObject`。
形式化陈述：iterationFunctorMapSuccAppArrowIso_hom_right_right_comp (f : Arrow C) (j :
 κ.ord.ToType) : (iterationFunctorMapSuccAppArrowIso I κ f j).hom.right.right ≫ 
(((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f).right = 𝟙 _
参数：f : Arrow C；j : κ.ord.ToType。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用引理 `CategoryTheory.SmallObject.hasPushouts`：hasPushouts : HasPushouts C
· 使用引理 `CategoryTheory.SmallObject.hasColimitsOfShape_discrete`：hasColimitsOfSha
pe_discrete (X Y : C) (p : X ⟶ Y) : HasColimitsOfShape (Discrete (FunctorObjInde
x I.homFamily p)) C
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `CategoryTheory.Arrow.Hom.w`：∀ {T : Type u} [inst : CategoryTheory.Catego
ry.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : f ⟶ g),   CategoryTheory.Categ
oryStruct.comp (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.SmallObject.instIsIsoRightAppArrowMapToTypeOrdFunctorIter
ationFunctor`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (I : Cate
goryTheory.MorphismProperty C) (κ : Cardinal.{w})   [inst_1 : Fact κ.IsReg…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
-/
lemma iterationFunctorMapSuccAppArrowIso_hom_right_right_comp
    (f : Arrow C) (j : κ.ord.ToType) :
    (iterationFunctorMapSuccAppArrowIso I κ f j).hom.right.right ≫
      (((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f).right = 𝟙 _ := by
  have := Arrow.rightFunc.congr_map ((iterationFunctorMapSuccAppArrowIso I κ f j).hom.w)
  dsimp at this ⊢
  rw [← cancel_epi (((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f).right,
    ← reassoc_of% this, comp_id]

section

variable {X Y : C} (f : X ⟶ Y)

/-- The intermediate object in the factorization given by the
small object argument. -/
/-
**CategoryTheory.SmallObject.obj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Small
Object`。
形式化陈述：obj : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intermediate object in the factorization given by the
small object argument.
-/
noncomputable def obj : C := ((iteration I κ).obj (Arrow.mk f)).left

/-- The "inclusion" morphism in the factorization given by
the small object argument. -/
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "inclusion" morphism in the factorization given by
the small object argument.
-/
noncomputable def ιObj : X ⟶ obj I κ f := ((ιIteration I κ).app (Arrow.mk f)).left

set_option backward.isDefEq.respectTransparency false in
/-- The "projection" morphism in the factorization given by
the small object argument. -/
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "projection" morphism in the factorization given by
the small object argument.
-/
noncomputable def πObj : obj I κ f ⟶ Y :=
  ((iteration I κ).obj (Arrow.mk f)).hom ≫ inv ((ιIteration I κ).app f).right

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma πObj_ιIteration_app_right :
    πObj I κ f ≫ ((ιIteration I κ).app f).right =
      ((iteration I κ).obj (Arrow.mk f)).hom := by simp [πObj]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιObj_πObj : ιObj I κ f ≫ πObj I κ f = f := by
  simp [ιObj, πObj]

/-- The morphism `ιObj I κ f` is a relative `I`-cell complex. -/
/-
**CategoryTheory.SmallObject.relativeCellComplex** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.SmallObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `ιObj I κ f` is a relative `I`-cell complex.
-/
noncomputable def relativeCellComplexιObj :
    RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) ↦ I.homFamily)
      (ιObj I κ f) := by
  have := hasIterationOfShape I κ
  let h := transfiniteCompositionOfShapeSuccStructPropιIteration I κ
  exact
  { toTransfiniteCompositionOfShape :=
      h.toTransfiniteCompositionOfShape.map ((evaluation _ _).obj f ⋙ Arrow.leftFunc)
    attachCells j hj :=
      attachCellsOfSuccStructProp I κ (h.map_mem j hj) f }
/-
**CategoryTheory.SmallObject.transfiniteCompositionsOfShape_** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.SmallObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma transfiniteCompositionsOfShape_ιObj :
    (coproducts.{w} I).pushouts.transfiniteCompositionsOfShape κ.ord.ToType
      (ιObj I κ f) :=
  ⟨((relativeCellComplexιObj I κ f).transfiniteCompositionOfShape).ofLE
    (by simp)⟩
/-
**CategoryTheory.SmallObject.llp_rlp_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
SmallObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma llp_rlp_ιObj : I.rlp.llp (ιObj I κ f) := by
  apply I.transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp κ.ord.ToType
  apply transfiniteCompositionsOfShape_ιObj

/-- When `ιObj I κ f` is considered as a relative `I`-cell complex,
the object at the `j`th step is obtained by applying the construction
`SmallObject.functorObj`. -/
/-
**CategoryTheory.SmallObject.relativeCellComplex** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.SmallObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `ιObj I κ f` is considered as a relative `I`-cell complex,
the object at the `j`th step is obtained by applying the construction
`SmallObject.functorObj`.
-/
noncomputable def relativeCellComplexιObjFObjSuccIso (j : κ.ord.ToType) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    (relativeCellComplexιObj I κ f).F.obj (Order.succ j) ≅
      functorObj I.homFamily (((iterationFunctor I κ).obj j).obj (Arrow.mk f)).hom :=
  (Arrow.rightFunc ⋙ Arrow.leftFunc).mapIso
    (iterationFunctorMapSuccAppArrowIso I κ f j)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιFunctorObj_eq (j : κ.ord.ToType) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    ιFunctorObj I.homFamily (((iterationFunctor I κ).obj j).obj (Arrow.mk f)).hom =
      (relativeCellComplexιObj I κ f).F.map (homOfLE (Order.le_succ j)) ≫
        (relativeCellComplexιObjFObjSuccIso I κ f j).hom := by
  simpa using! Arrow.leftFunc.congr_map (iterationFunctorMapSuccAppArrowIso I κ f j).hom.w

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma πFunctorObj_eq (j : κ.ord.ToType) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    πFunctorObj I.homFamily (((iterationFunctor I κ).obj j).obj (Arrow.mk f)).hom =
      (relativeCellComplexιObjFObjSuccIso I κ f j).inv ≫
      (relativeCellComplexιObj I κ f).incl.app (Order.succ j) ≫
      πObj I κ f ≫ (iterationFunctorObjObjRightIso I κ (Arrow.mk f) j).inv := by
  have h₁ := (iterationFunctorMapSuccAppArrowIso I κ f j).hom.right.w
  have h₂ := (transfiniteCompositionOfShapeSuccStructPropιIteration I κ).incl.naturality
    (homOfLE (Order.le_succ j))
  dsimp at h₁ h₂
  rw [comp_id] at h₂
  rw [← cancel_mono (iterationFunctorObjObjRightIso I κ (Arrow.mk f) j).hom,
    ← cancel_mono ((ιIteration I κ).app f).right, assoc, assoc, assoc, assoc, assoc,
    Iso.inv_hom_id_assoc, πObj_ιIteration_app_right,
    iterationFunctorObjObjRightIso_ιIteration_app_right,
    ← cancel_epi (relativeCellComplexιObjFObjSuccIso I κ f j).hom, Iso.hom_inv_id_assoc]
  dsimp [relativeCellComplexιObjFObjSuccIso,
    relativeCellComplexιObj, transfiniteCompositionOfShapeιIterationAppRight]
  simp only [reassoc_of% h₁, comp_id, comp_id, Arrow.w_mk_right, ← h₂,
    NatTrans.comp_app, Arrow.comp_right,
    iterationFunctorMapSuccAppArrowIso_hom_right_right_comp_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.SmallObject.hasRightLiftingProperty_** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.SmallObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasRightLiftingProperty_πObj {A B : C} (i : A ⟶ B) (hi : I i) (f : X ⟶ Y) :
    HasLiftingProperty i (πObj I κ f) := ⟨by
  have := hasColimitsOfShape_discrete I κ
  have := hasPushouts I κ
  have := preservesColimit I κ i hi _ (relativeCellComplexιObj I κ f)
  intro g b sq
  obtain ⟨j, t, ht⟩ := Types.jointly_surjective _
    (isColimitOfPreserves (coyoneda.obj (Opposite.op A))
      (relativeCellComplexιObj I κ f).isColimit) g
  dsimp at g b sq t ht
  obtain ⟨l, hl₁, hl₂⟩ := ιFunctorObj_extension' I.homFamily
    ((relativeCellComplexιObj I κ f).incl.app j ≫ πObj I κ f)
    ((relativeCellComplexιObj I κ f).F.map (homOfLE (Order.le_succ j)))
    ((relativeCellComplexιObj I κ f).incl.app (Order.succ j) ≫ πObj I κ f) (by simp) (Iso.refl _)
    (iterationFunctorObjObjRightIso I κ (Arrow.mk f) j).symm
    (relativeCellComplexιObjFObjSuccIso I κ f j)
    (by dsimp; rw [ιFunctorObj_eq, id_comp])
    (by dsimp; rw [πFunctorObj_eq, assoc, Iso.hom_inv_id_assoc])
    (i := ⟨i, hi⟩) t b (by rw [reassoc_of% ht, sq.w]; dsimp)
  dsimp at hl₁
  exact ⟨⟨{
    l := l ≫ (relativeCellComplexιObj I κ f).incl.app (Order.succ j)
    fac_left := by simp [reassoc_of% hl₁, ← ht]
    fac_right := by rw [assoc, hl₂]
  }⟩⟩⟩
/-
**CategoryTheory.SmallObject.rlp_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Smal
lObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rlp_πObj : I.rlp (πObj I κ f) :=
  fun _ _ _ hi ↦ hasRightLiftingProperty_πObj _ _ _ hi _

end

/-- The functoriality of the intermediate object in the
factorization of the small object argument. -/
/-
**CategoryTheory.SmallObject.objMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sm
allObject`。
形式化陈述：objMap {f g : Arrow C} (φ : f ⟶ g) : obj I κ f.hom ⟶ obj I κ g.hom
参数：φ : f ⟶ g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functoriality of the intermediate object in the
factorization of the small object argument.
-/
noncomputable def objMap {f g : Arrow C} (φ : f ⟶ g) : obj I κ f.hom ⟶ obj I κ g.hom :=
  ((iteration I κ).map φ).left

@[simp]
/-
**CategoryTheory.SmallObject.objMap_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.SmallObject`。
形式化陈述：objMap_id (f : Arrow C) : objMap I κ (𝟙 f) = 𝟙 _
参数：f : Arrow C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
lemma objMap_id (f : Arrow C) : objMap I κ (𝟙 f) = 𝟙 _ := by
  simp only [objMap, Functor.map_id]
  rfl

@[reassoc, simp]
/-
**CategoryTheory.SmallObject.objMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.SmallObject`。
形式化陈述：objMap_comp {f g h : Arrow C} (φ : f ⟶ g) (ψ : g ⟶ h) : objMap I κ (φ ≫ ψ)
 = objMap I κ φ ≫ objMap I κ ψ
参数：φ : f ⟶ g；ψ : g ⟶ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
lemma objMap_comp {f g h : Arrow C} (φ : f ⟶ g) (ψ : g ⟶ h) :
    objMap I κ (φ ≫ ψ) = objMap I κ φ ≫ objMap I κ ψ := by
  simp only [objMap, Functor.map_comp]
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιObj_naturality {f g : Arrow C} (φ : f ⟶ g) :
    ιObj I κ f.hom ≫ objMap I κ φ = φ.left ≫ ιObj I κ g.hom :=
  Arrow.leftFunc.congr_map ((ιIteration I κ).naturality φ).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma πObj_naturality {f g : Arrow C} (φ : f ⟶ g) :
    objMap I κ φ ≫ πObj I κ g.hom = πObj I κ f.hom ≫ φ.right := by
  let e₁ := asIso ((ιIteration I κ).app (Arrow.mk f.hom)).right
  let e₂ := asIso ((ιIteration I κ).app (Arrow.mk g.hom)).right
  change _ ≫ _ ≫ e₂.inv = (_ ≫ e₁.inv) ≫ _
  have h₁ := ((iteration I κ).map φ).w =≫ e₂.inv
  have h₂ : φ.right ≫ e₂.hom = e₁.hom ≫ ((iteration I κ).map φ).right :=
    ((Functor.whiskerRight (ιIteration I κ) Arrow.rightFunc).naturality φ)
  dsimp at h₁
  rw [assoc] at h₁
  apply h₁.trans
  simp only [← cancel_mono e₂.hom, assoc, e₂.inv_hom_id, h₂, e₁.inv_hom_id_assoc]
  rw [← assoc]
  apply comp_id

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functorial factorization `ιObj I κ f ≫ πObj I κ f.hom = f`
with `ιObj I κ f` in `I.rlp.llp` and `πObj I κ f.hom` in `I.rlp`. -/
@[simps]
/-
**CategoryTheory.SmallObject.functorialFactorizationData** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.SmallObject`。
形式化陈述：functorialFactorizationData : FunctorialFactorizationData I.rlp.llp I.rlp 
where Z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functorial factorization `ιObj I κ f ≫ πObj I κ f.hom = f`
with `ιObj I κ f` in `I.rlp.llp` and `πObj I κ f.hom` in `I.rlp`.
-/
noncomputable def functorialFactorizationData :
    FunctorialFactorizationData I.rlp.llp I.rlp where
  Z :=
    { obj f := obj I κ f.hom
      map φ := objMap I κ φ }
  i := { app f := ιObj I κ f.hom }
  p := { app f := πObj I κ f.hom }
  hi f := llp_rlp_ιObj I κ f.hom
  hp f := rlp_πObj I κ f.hom
/-
**CategoryTheory.SmallObject.hasFunctorialFactorization** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.SmallObject`。
形式化陈述：hasFunctorialFactorization : HasFunctorialFactorization I.rlp.llp I.rlp wh
ere nonempty_functorialFactorizationData
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasFunctorialFactorization :
    HasFunctorialFactorization I.rlp.llp I.rlp where
  nonempty_functorialFactorizationData :=
    ⟨functorialFactorizationData I κ⟩

set_option backward.defeqAttrib.useBackward true in
/-- If `κ` is a suitable cardinal for the small object argument for `I : MorphismProperty C`,
then the class `I.rlp.llp` is exactly the class of morphisms that are retracts
of transfinite compositions (of shape `κ.ord.ToType`) of pushouts of coproducts
of maps in `I`. -/
/-
**CategoryTheory.SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument'** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObject`。
形式化陈述：llp_rlp_of_isCardinalForSmallObjectArgument' : I.rlp.llp = (transfiniteCom
positionsOfShape (coproducts.{w} I).pushouts κ.ord.ToType).retracts
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.SmallObject.ιObj_πObj`：ιObj_πObj : ιObj I κ f ≫ πObj I κ 
f = f
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.SmallObject.rlp_πObj`：rlp_πObj : I.rlp (πObj I κ f)
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.CommSq.fac_left`：fac_left [hsq : HasLift sq] : i ≫ sq.lif
t = f
· 使用引理 `CategoryTheory.Arrow.hom_ext`：hom_ext {X Y : Arrow T} (f g : X ⟶ Y) (h₁ 
: f.left = g.left) (h₂ : f.right = g.right) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.CommSq.fac_right`：∀ {C : Type u_1} [inst : CategoryTheory
.Category.{v_1, u_1} C] {A B X Y : C} {f : X ⟶ A} {i : B ⟶ A} {p : Y ⟶ X}   {g :
 Y ⟶ B} (sq : Categor…
· 使用引理 `CategoryTheory.SmallObject.transfiniteCompositionsOfShape_ιObj`：transfin
iteCompositionsOfShape_ιObj : (coproducts.{w} I).pushouts.transfiniteComposition
sOfShape κ.ord.ToType (ιObj I κ f)
· 使用引理 `CategoryTheory.MorphismProperty.retracts_transfiniteCompositionsOfShape_
pushouts_coproducts_le_llp_rlp`：retracts_transfiniteCompositionsOfShape_pushouts
_coproducts_le_llp_rlp : ((coproducts.{t} W).pushouts.transfiniteCompositionsOfS
hape J).retr…

--- 原说明 ---
If `κ` is a suitable cardinal for the small object argument for `I : MorphismPro
perty C`,
then the class `I.rlp.llp` is exactly the class of morphisms that are retracts
of transfinite compositions (of shape `κ.ord.ToType`) of pushouts of coproducts
of maps in `I`.
-/
lemma llp_rlp_of_isCardinalForSmallObjectArgument' :
    I.rlp.llp = (transfiniteCompositionsOfShape
      (coproducts.{w} I).pushouts κ.ord.ToType).retracts := by
  refine le_antisymm ?_
    (retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp I κ.ord.ToType)
  intro X Y f hf
  have sq : CommSq (ιObj I κ f) f (πObj I κ f) (𝟙 _) := ⟨by simp⟩
  have := hf _ (rlp_πObj I κ f)
  refine ⟨_, _, _, ?_, transfiniteCompositionsOfShape_ιObj I κ f⟩
  exact
    { i := Arrow.homMk (𝟙 _) sq.lift
      r := Arrow.homMk (𝟙 _) (πObj I κ f) }

omit κ in
attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType in
/-
**CategoryTheory.SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObject`。
形式化陈述：llp_rlp_of_isCardinalForSmallObjectArgument_aleph0 [I.IsCardinalForSmallOb
jectArgument Cardinal.aleph0.{w}] : I.rlp.llp = (transfiniteCompositionsOfShape 
(coproducts.{w} I).pushouts Nat).retracts
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.fact_isRegular_aleph0`：fact_isRegular_aleph0 : Fact (IsRegular 
ℵ₀) where out
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTULift`：∀ {α : Type u_1} [inst : LT α] [h : WellFoundedL
T α], WellFoundedLT (ULift.{u_4, u_1} α)
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.type_nat_lt`：type_nat_lt : typeLT Nat = ω
· 使用定理 `Ordinal.lift_omega0`：lift_omega0 : lift ω = ω
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `Cardinal.ord_aleph0`：ord_aleph0 : ord.{u} ℵ₀ = ω
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument'`
：llp_rlp_of_isCardinalForSmallObjectArgument' : I.rlp.llp = (transfiniteComposit
ionsOfShape (coproducts.{w} I).pushouts κ.ord.ToType).retract…
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_eq_of_ord
erIso`：transfiniteCompositionsOfShape_eq_of_orderIso (e : J ≃o J') : W.transfini
teCompositionsOfShape J = W.transfiniteCompositionsOfShape J'
-/
lemma llp_rlp_of_isCardinalForSmallObjectArgument_aleph0
    [I.IsCardinalForSmallObjectArgument Cardinal.aleph0.{w}] :
    I.rlp.llp = (transfiniteCompositionsOfShape (coproducts.{w} I).pushouts ℕ).retracts := by
  let e : ℕ ≃o Cardinal.aleph0.{w}.ord.ToType :=
    ULift.orderIso.{w}.symm.trans
      (OrderIso.ofRelIsoLT (Nonempty.some (by simp [← Ordinal.type_eq])))
  rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument' _ Cardinal.aleph0,
    MorphismProperty.transfiniteCompositionsOfShape_eq_of_orderIso _ e]

/-- If `κ` is a suitable cardinal for the small object argument for `I : MorphismProperty C`,
then the class `I.rlp.llp` is exactly the class of morphisms that are retracts
of transfinite compositions of pushouts of coproducts of maps in `I`. -/
/-
**CategoryTheory.SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObject`。
形式化陈述：llp_rlp_of_isCardinalForSmallObjectArgument : I.rlp.llp = (transfiniteComp
ositions.{w} (coproducts.{w} I).pushouts).retracts
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument'`
：llp_rlp_of_isCardinalForSmallObjectArgument' : I.rlp.llp = (transfiniteComposit
ionsOfShape (coproducts.{w} I).pushouts κ.ord.ToType).retract…
· 使用引理 `CategoryTheory.MorphismProperty.retracts_monotone`：retracts_monotone : M
onotone (retracts (C
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le_transf
initeCompositions`：transfiniteCompositionsOfShape_le_transfiniteCompositions (J 
: Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] : W.tran…
· 使用引理 `CategoryTheory.MorphismProperty.retracts_transfiniteComposition_pushouts
_coproducts_le_llp_rlp`：retracts_transfiniteComposition_pushouts_coproducts_le_l
lp_rlp : (transfiniteCompositions.{w} (coproducts.{w} W).pushouts).retracts <= W
.rlp…

--- 原说明 ---
If `κ` is a suitable cardinal for the small object argument for `I : MorphismPro
perty C`,
then the class `I.rlp.llp` is exactly the class of morphisms that are retracts
of transfinite compositions of pushouts of coproducts of maps in `I`.
-/
lemma llp_rlp_of_isCardinalForSmallObjectArgument :
    I.rlp.llp =
      (transfiniteCompositions.{w} (coproducts.{w} I).pushouts).retracts := by
  refine le_antisymm ?_
    (retracts_transfiniteComposition_pushouts_coproducts_le_llp_rlp I)
  rw [llp_rlp_of_isCardinalForSmallObjectArgument' I κ]
  apply retracts_monotone
  apply transfiniteCompositionsOfShape_le_transfiniteCompositions

end SmallObject

end CategoryTheory

