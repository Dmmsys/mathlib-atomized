/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Indization.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Indization.ParallelPair
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape

/-!
# Equalizers of ind-objects

We show that if a category `C` has equalizers, then ind-objects are closed under equalizers.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Section 6.1
-/

public section

universe v v' u u'

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section

variable {I : Type v} [SmallCategory I] [IsFiltered I]

variable {J : Type} [SmallCategory J] [FinCategory J]

variable (F : J ⥤ I ⥤ C)

/--
Suppose `F : J ⥤ I ⥤ C` is a finite diagram in the functor category `I ⥤ C`, where `I` is small
and filtered. If `i : I`, we can apply the Yoneda embedding to `F(·, i)` to obtain a
diagram of presheaves `J ⥤ Cᵒᵖ ⥤ Type v`. Suppose that the limits of this diagram is always an
ind-object.

For `j : J` we can apply the Yoneda embedding to `F(j, ·)` and take colimits to obtain a finite
diagram `J ⥤ Cᵒᵖ ⥤ Type v` (which is actually a diagram `J ⥤ Ind C`). The theorem states that
the limit of this diagram is an ind-object.

This theorem will be used to construct equalizers in the category of ind-objects. It can be
interpreted as saying that ind-objects are closed under finite limits as long as the diagram
we are taking the limit of comes from a diagram in a functor category `I ⥤ C`. We will show (TODO)
that this is the case for any parallel pair of morphisms in `Ind C` and deduce that ind-objects
are closed under equalizers.

This is Proposition 6.1.16(i) in [Kashiwara2006].
-/
/-
**CategoryTheory.Limits.isIndObject_limit_comp_yoneda_comp_colim** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isIndObject_limit_comp_yoneda_comp_colim (hF : forall i, IsIndObject (limi
t (F.flip.obj i ⋙ yoneda))) : IsIndObject (limit (F ⋙ (Functor.whiskeringRight _
 _ _).obj yoneda ⋙ colim))
参数：hF : forall i, IsIndObject (limit (F.flip.obj i ⋙ yoneda))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.IsIndObject.map`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {A B : CategoryTheory.Functor Cᵒᵖ (Type v)} (η : A ⟶ B) 
  [CategoryTheory.IsIso η],…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfShape`：∀ {J : Type v} [inst : Cat
egoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimi
tsOfShape J (Type u)
· 使用定理 `CategoryTheory.instPreservesLimitsOfShapeFunctorColim`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.C
ategory.{v₁, u₁} J]   {K : Type u₂} [inst_2…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.isIndObject_colimit`：isIndObject_colimit (I : Type
 v) [SmallCategory I] [IsFiltered I] (F : I ⥤ Cᵒᵖ ⥤ Type v) (hF : forall i, IsIn
dObject (F.obj i)) : IsIndObjec…
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv

--- 原说明 ---
Suppose `F : J ⥤ I ⥤ C` is a finite diagram in the functor category `I ⥤ C`, whe
re `I` is small
and filtered. If `i : I`, we can apply the Yoneda embedding to `F(·, i)` to obta
in a
diagram of presheaves `J ⥤ Cᵒᵖ ⥤ Type v`. Suppose that the limits of this diagra
m is always an
ind-object.

For `j : J` we can apply the Yoneda embedding to `F(j, ·)` and take colimits to 
obtain a finite
diagram `J ⥤ Cᵒᵖ ⥤ Type v` (which is actually a diagram `J ⥤ Ind C`). The theore
m states that
the limit of this diagram is an ind-object.

This theorem will be used to construct equalizers in the category of ind-objects
. It can be
interpreted as saying that ind-objects are closed under finite limits as long as
 the diagram
we are taking the limit of comes from a diagram in a functor category `I ⥤ C`. W
e will show (TODO)
that this is the case for any parallel pair of morphisms in `Ind C` and deduce t
hat ind-objects
are closed under equalizers.

This is Proposition 6.1.16(i) in [Kashiwara2006].
-/
theorem isIndObject_limit_comp_yoneda_comp_colim
    (hF : ∀ i, IsIndObject (limit (F.flip.obj i ⋙ yoneda))) :
    IsIndObject (limit (F ⋙ (Functor.whiskeringRight _ _ _).obj yoneda ⋙ colim)) := by
  let G : J ⥤ I ⥤ (Cᵒᵖ ⥤ Type v) := F ⋙ (Functor.whiskeringRight _ _ _).obj yoneda
  apply IsIndObject.map (HasLimit.isoOfNatIso (colimitFlipIsoCompColim G)).hom
  apply IsIndObject.map (colimitLimitIso G).hom
  apply isIndObject_colimit
  exact fun i => IsIndObject.map (limitObjIsoLimitCompEvaluation _ _).inv (hF i)

end

/-- If `C` has equalizers. then ind-objects are closed under equalizers.

This is Proposition 6.1.17(i) in [Kashiwara2006].
-/
/-
**CategoryTheory.Limits.isClosedUnderLimitsOfShape_isIndObject_walkingParallelPa
ir** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isClosedUnderLimitsOfShape_isIndObject_walkingParallelPair [HasEqualizers 
C] : ObjectProperty.IsClosedUnderLimitsOfShape (IsIndObject (C
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape.mk'`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectP
roperty C} {J : Type u'}   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsIndObject.instIsClosedUnderIsomorphismsFunctorOp
positeType`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C],   Category
Theory.ObjectProperty.IsClosedUnderIsomorphisms CategoryTheory.Limits.Is…
· 使用定理 `CategoryTheory.nonempty_indParallelPairPresentation`：nonempty_indParalle
lPairPresentation {A B : Cᵒᵖ ⥤ Type v₁} (hA : IsIndObject A) (hB : IsIndObject B
) (f g : A ⟶ B) : Nonempty (IndParallelPa…
· 使用定理 `CategoryTheory.Limits.IsIndObject.map`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {A B : CategoryTheory.Functor Cᵒᵖ (Type v)} (η : A ⟶ B) 
  [CategoryTheory.IsIso η],…
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.isIndObject_limit_comp_yoneda_comp_colim`：isIndObj
ect_limit_comp_yoneda_comp_colim (hF : forall i, IsIndObject (limit (F.flip.obj 
i ⋙ yoneda))) : IsIndObject (limit (F ⋙ (Functor.whi…
· 使用定理 `CategoryTheory.instIsFilteredI`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {A B : CategoryTheory.Functor Cᵒᵖ (Type v₁)} {f g : A ⟶ B}  
 (P : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.isIndObject_limit_comp_yoneda`：isIndObject_limit_c
omp_yoneda {J : Type u'} [Category.{v'} J] (F : J ⥤ C) [HasLimit F] : IsIndObjec
t (limit (F ⋙ yoneda))
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `C` has equalizers. then ind-objects are closed under equalizers.

This is Proposition 6.1.17(i) in [Kashiwara2006].
-/
instance isClosedUnderLimitsOfShape_isIndObject_walkingParallelPair [HasEqualizers C] :
    ObjectProperty.IsClosedUnderLimitsOfShape (IsIndObject (C := C)) WalkingParallelPair :=
  .mk' (by
    rintro _ ⟨F, h⟩
    obtain ⟨P⟩ := nonempty_indParallelPairPresentation (h WalkingParallelPair.zero)
      (h WalkingParallelPair.one) (F.map WalkingParallelPairHom.left)
      (F.map WalkingParallelPairHom.right)
    exact IsIndObject.map
      (HasLimit.isoOfNatIso (P.parallelPairIsoParallelPairCompYoneda.symm ≪≫
        (diagramIsoParallelPair _).symm)).hom
      (isIndObject_limit_comp_yoneda_comp_colim (parallelPair P.φ P.ψ)
        (fun i => isIndObject_limit_comp_yoneda _)))

end CategoryTheory.Limits

