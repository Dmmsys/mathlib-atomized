/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Preservation of finite (co)limits.

These functors are also known as left exact (flat) or right exact functors when the categories
involved are abelian, or more generally, finitely (co)complete.

## Related results
* `CategoryTheory.Limits.preservesFiniteLimitsOfPreservesEqualizersAndFiniteProducts` :
  see `Mathlib/CategoryTheory/Limits/Constructions/LimitsOfProductsAndEqualizers.lean`.
  Also provides the dual version.
* `CategoryTheory.Limits.preservesFiniteLimitsIffFlat` :
  see `Mathlib/CategoryTheory/Functor/Flat.lean`.

-/

public section


open CategoryTheory

namespace CategoryTheory.Limits

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe u w w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable {J : Type w} [SmallCategory J] {K : J ⥤ C}

/--
Definition of `PreservesFiniteLimits` / `PreservesFiniteLimits` 的定义

English:
class PreservesFiniteLimits
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - preservesFiniteLimits : forall (J : Type) [SmallCategory J] [FinCategory J], PreservesLimitsOfShape J F  [default: by infer_instance]

中文:
类 保持FiniteLimits
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - preservesFiniteLimits : 对任意 (J : 类型) [小范畴 J] [有限范畴 J], 保持形状极限 J F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class PreservesFiniteLimits (F : C ⥤ D) : Prop where
  preservesFiniteLimits :
    forall (J : Type) [SmallCategory J] [FinCategory J], PreservesLimitsOfShape J F := by infer_instance

attribute [instance] PreservesFiniteLimits.preservesFiniteLimits

/-- Preserving finite limits also implies preserving limits over finite shapes in higher universes,
though through a noncomputable instance. -/
instance (priority := 100) preservesLimitsOfShapeOfPreservesFiniteLimits (F : C ⥤ D)
    [PreservesFiniteLimits F] (J : Type w) [SmallCategory J] [FinCategory J] :
    PreservesLimitsOfShape J F := by
  apply preservesLimitsOfShape_of_equiv (FinCategory.equivAsType J)

-- This is a dangerous instance as it has unbound universe variables.
/--
lemma `PreservesLimitsOfSize.preservesFiniteLimits` / 引理 `PreservesLimitsOfSize.preservesFiniteLimits`

English:
lemma PreservesLimitsOfSize.preservesFiniteLimits
  statement: (F : C ⥤ D)
  proof: by
    have := preservesSmallestLimits_of_preservesLimits F
    exact preservesLimitsOfShape_of_equiv (FinCategory.equivAsType J) F

中文:
引理 保持LimitsOfSize.preservesFiniteLimits
  结论: (F : C ⥤ D)
  证明: by
    have := preservesSmallestLimits_of_preservesLimits F
    exact preservesLimitsOfShape_of_equiv (FinCategory.equivAsType J) F

Depends on / 依赖: FinCategory, FinCategory.equivAsType, equivAsType, preservesLimitsOfShape_of_equiv, preservesSmallestLimits_of_preservesLimits
-/
lemma PreservesLimitsOfSize.preservesFiniteLimits (F : C ⥤ D)
    [PreservesLimitsOfSize.{w, w₂} F] : PreservesFiniteLimits F where
  preservesFiniteLimits J (sJ : SmallCategory J) fJ := by
    have := preservesSmallestLimits_of_preservesLimits F
    exact preservesLimitsOfShape_of_equiv (FinCategory.equivAsType J) F

-- Added as a specialization of the dangerous instance above, for limits indexed in Type 0.
instance (priority := 120) PreservesLimitsOfSize0.preservesFiniteLimits
    (F : C ⥤ D) [PreservesLimitsOfSize.{0, 0} F] : PreservesFiniteLimits F :=
  PreservesLimitsOfSize.preservesFiniteLimits F

-- An alternative specialization of the dangerous instance for small limits.
instance (priority := 120) PreservesLimits.preservesFiniteLimits (F : C ⥤ D)
    [PreservesLimits F] : PreservesFiniteLimits F :=
  PreservesLimitsOfSize.preservesFiniteLimits F

attribute [local instance] uliftCategory in
/--
lemma `preservesFiniteLimits_of_preservesFiniteLimitsOfSize` / 引理 `preservesFiniteLimits_of_preservesFiniteLimitsOfSize`

English:
lemma preservesFiniteLimits_of_preservesFiniteLimitsOfSize
  statement: (F : C ⥤ D)
  proof: by
        have := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
        exact preservesLimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv J).symm F

中文:
引理 preservesFiniteLimits_of_preservesFiniteLimitsOfSize
  结论: (F : C ⥤ D)
  证明: by
        have := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
        exact preservesLimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv J).symm F

Depends on / 依赖: CategoryTheory, CategoryTheory.finCategoryUlift, ULiftHom, ULiftHomULiftCategory, ULiftHomULiftCategory.equiv, finCategoryUlift, preservesLimitsOfShape_of_equiv
-/
lemma preservesFiniteLimits_of_preservesFiniteLimitsOfSize (F : C ⥤ D)
    (h :
      forall (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), PreservesLimitsOfShape J F) :
    PreservesFiniteLimits F where
      preservesFiniteLimits J (_ : SmallCategory J) _ := by
        have := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
        exact preservesLimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv J).symm F

/--
lemma `comp_preservesFiniteLimits` / 引理 `comp_preservesFiniteLimits`

English:
lemma comp_preservesFiniteLimits
  statement: (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteLimits F]
  proof: ⟨fun _ _ _ => inferInstance⟩

中文:
引理 comp_preservesFiniteLimits
  结论: (F : C ⥤ D) (G : D ⥤ E) [保持FiniteLimits F]
  证明: ⟨fun _ _ _ => inferInstance⟩
-/
lemma comp_preservesFiniteLimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteLimits F]
    [PreservesFiniteLimits G] : PreservesFiniteLimits (F ⋙ G) :=
  ⟨fun _ _ _ => inferInstance⟩

/--
lemma `preservesFiniteLimits_of_natIso` / 引理 `preservesFiniteLimits_of_natIso`

English:
lemma preservesFiniteLimits_of_natIso
  given: {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteLimits F]
  proof: preservesLimitsOfShape_of_natIso h

中文:
引理 preservesFiniteLimits_of_natIso
  条件: {F G : C ⥤ D} (h : F ≅ G) [保持FiniteLimits F]
  证明: preservesLimitsOfShape_of_natIso h

Depends on / 依赖: preservesLimitsOfShape_of_natIso
-/
lemma preservesFiniteLimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteLimits F] :
    PreservesFiniteLimits G where
  preservesFiniteLimits _ _ _ := preservesLimitsOfShape_of_natIso h

/--
Definition of `PreservesFiniteProducts` / `PreservesFiniteProducts` 的定义

English:
class PreservesFiniteProducts
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - preserves : forall n, PreservesLimitsOfShape (Discrete (Fin n)) F

中文:
类 保持FiniteProducts
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - preserves : 对任意 n, 保持形状极限 (离散 (有限集 n)) F
-/
class PreservesFiniteProducts (F : C ⥤ D) : Prop where
  preserves : forall n, PreservesLimitsOfShape (Discrete (Fin n)) F

instance (priority := 100) (F : C ⥤ D) (J : Type u) [Finite J]
    [PreservesFiniteProducts F] : PreservesLimitsOfShape (Discrete J) F := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have := PreservesFiniteProducts.preserves (F := F) n
  exact preservesLimitsOfShape_of_equiv (Discrete.equivalence e.symm) F

/--
Instance `comp_preservesFiniteProducts` / 实例 `comp_preservesFiniteProducts`

English:
instance comp_preservesFiniteProducts
  signature: (F : C ⥤ D) (G : D ⥤ E)
  body: inferInstance

中文:
实例 comp_preservesFiniteProducts
  签名: (F : C ⥤ D) (G : D ⥤ E)
  定义体: inferInstance
-/
instance comp_preservesFiniteProducts (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteProducts F] [PreservesFiniteProducts G] :
    PreservesFiniteProducts (F ⋙ G) where
  preserves _ := inferInstance

instance (F : C ⥤ D) [PreservesFiniteLimits F] : PreservesFiniteProducts F where
  preserves _ := inferInstance

/--
Definition of `ReflectsFiniteLimits` / `ReflectsFiniteLimits` 的定义

English:
class ReflectsFiniteLimits
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - reflects : forall (J : Type) [SmallCategory J] [FinCategory J], ReflectsLimitsOfShape J F  [default: by infer_instance]

中文:
类 ReflectsFiniteLimits
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - reflects : 对任意 (J : 类型) [小范畴 J] [有限范畴 J], 反映形状极限 J F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class ReflectsFiniteLimits (F : C ⥤ D) : Prop where
  reflects : forall (J : Type) [SmallCategory J] [FinCategory J], ReflectsLimitsOfShape J F := by
    infer_instance

attribute [instance] ReflectsFiniteLimits.reflects

/- Similarly to preserving finite products, quantified classes don't behave well. -/
/--
Definition of `ReflectsFiniteProducts` / `ReflectsFiniteProducts` 的定义

English:
class ReflectsFiniteProducts
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - reflects : forall n, ReflectsLimitsOfShape (Discrete (Fin n)) F

中文:
类 ReflectsFiniteProducts
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - reflects : 对任意 n, 反映形状极限 (离散 (有限集 n)) F
-/
class ReflectsFiniteProducts (F : C ⥤ D) : Prop where
  reflects : forall n, ReflectsLimitsOfShape (Discrete (Fin n)) F

instance (priority := 100) (F : C ⥤ D) [ReflectsFiniteProducts F] (J : Type u) [Finite J] :
    ReflectsLimitsOfShape (Discrete J) F :=
  let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have := ReflectsFiniteProducts.reflects (F := F) n
  reflectsLimitsOfShape_of_equiv (Discrete.equivalence e.symm) _

-- This is a dangerous instance as it has unbound universe variables.
/--
lemma `ReflectsLimitsOfSize.reflectsFiniteLimits` / 引理 `ReflectsLimitsOfSize.reflectsFiniteLimits`

English:
lemma ReflectsLimitsOfSize.reflectsFiniteLimits
  proof: by
    have := reflectsSmallestLimits_of_reflectsLimits F
    exact reflectsLimitsOfShape_of_equiv (FinCategory.equivAsType J) F

中文:
引理 ReflectsLimitsOfSize.reflectsFiniteLimits
  证明: by
    have := reflectsSmallestLimits_of_reflectsLimits F
    exact reflectsLimitsOfShape_of_equiv (FinCategory.equivAsType J) F

Depends on / 依赖: FinCategory, FinCategory.equivAsType, equivAsType, reflectsLimitsOfShape_of_equiv, reflectsSmallestLimits_of_reflectsLimits
-/
lemma ReflectsLimitsOfSize.reflectsFiniteLimits
    (F : C ⥤ D) [ReflectsLimitsOfSize.{w, w₂} F] : ReflectsFiniteLimits F where
  reflects J (sJ : SmallCategory J) fJ := by
    have := reflectsSmallestLimits_of_reflectsLimits F
    exact reflectsLimitsOfShape_of_equiv (FinCategory.equivAsType J) F

-- Added as a specialization of the dangerous instance above, for colimits indexed in Type 0.
instance (priority := 120) (F : C ⥤ D) [ReflectsLimitsOfSize.{0, 0} F] :
    ReflectsFiniteLimits F :=
  ReflectsLimitsOfSize.reflectsFiniteLimits F

-- An alternative specialization of the dangerous instance for small colimits.
instance (priority := 120) (F : C ⥤ D)
    [ReflectsLimits F] : ReflectsFiniteLimits F :=
  ReflectsLimitsOfSize.reflectsFiniteLimits F

/--
lemma `preservesFiniteLimits_of_reflects_of_preserves` / 引理 `preservesFiniteLimits_of_reflects_of_preserves`

English:
lemma preservesFiniteLimits_of_reflects_of_preserves
  statement: (F : C ⥤ D) (G : D ⥤ E)
  proof: preservesLimitsOfShape_of_reflects_of_preserves F G

中文:
引理 preservesFiniteLimits_of_reflects_of_preserves
  结论: (F : C ⥤ D) (G : D ⥤ E)
  证明: preservesLimitsOfShape_of_reflects_of_preserves F G

Depends on / 依赖: preservesLimitsOfShape_of_reflects_of_preserves
-/
lemma preservesFiniteLimits_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteLimits (F ⋙ G)] [ReflectsFiniteLimits G] : PreservesFiniteLimits F where
  preservesFiniteLimits _ _ _ := preservesLimitsOfShape_of_reflects_of_preserves F G

/--
lemma `preservesFiniteProducts_of_reflects_of_preserves` / 引理 `preservesFiniteProducts_of_reflects_of_preserves`

English:
lemma preservesFiniteProducts_of_reflects_of_preserves
  statement: (F : C ⥤ D) (G : D ⥤ E)
  proof: preservesLimitsOfShape_of_reflects_of_preserves F G

中文:
引理 preservesFiniteProducts_of_reflects_of_preserves
  结论: (F : C ⥤ D) (G : D ⥤ E)
  证明: preservesLimitsOfShape_of_reflects_of_preserves F G

Depends on / 依赖: PreservesColimitOfIsSplitPair, PreservesColimitOfIsSplitPair.out, preservesLimitsOfShape_of_reflects_of_preserves
-/
lemma preservesFiniteProducts_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteProducts (F ⋙ G)] [ReflectsFiniteProducts G] : PreservesFiniteProducts F where
  preserves _ := preservesLimitsOfShape_of_reflects_of_preserves F G

/--
Instance `reflectsFiniteLimits_of_reflectsIsomorphisms` / 实例 `reflectsFiniteLimits_of_reflectsIsomorphisms`

English:
instance reflectsFiniteLimits_of_reflectsIsomorphisms
  signature: (F : C ⥤ D)
  body: reflectsLimitsOfShape_of_reflectsIsomorphisms

中文:
实例 reflectsFiniteLimits_of_reflectsIsomorphisms
  签名: (F : C ⥤ D)
  定义体: reflectsLimitsOfShape_of_reflectsIsomorphisms

Depends on / 依赖: reflectsLimitsOfShape_of_reflectsIsomorphisms
-/
instance reflectsFiniteLimits_of_reflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteLimits C] [PreservesFiniteLimits F] :
      ReflectsFiniteLimits F where
  reflects _ _ _ := reflectsLimitsOfShape_of_reflectsIsomorphisms

/--
Instance `reflectsFiniteProducts_of_reflectsIsomorphisms` / 实例 `reflectsFiniteProducts_of_reflectsIsomorphisms`

English:
instance reflectsFiniteProducts_of_reflectsIsomorphisms
  signature: (F : C ⥤ D)
  body: reflectsLimitsOfShape_of_reflectsIsomorphisms

中文:
实例 reflectsFiniteProducts_of_reflectsIsomorphisms
  签名: (F : C ⥤ D)
  定义体: reflectsLimitsOfShape_of_reflectsIsomorphisms

Depends on / 依赖: ReflectsColimitOfIsSplitPair, ReflectsColimitOfIsSplitPair.out, reflectsLimitsOfShape_of_reflectsIsomorphisms
-/
instance reflectsFiniteProducts_of_reflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteProducts C] [PreservesFiniteProducts F] :
      ReflectsFiniteProducts F where
  reflects _ := reflectsLimitsOfShape_of_reflectsIsomorphisms

/--
Instance `comp_reflectsFiniteProducts` / 实例 `comp_reflectsFiniteProducts`

English:
instance comp_reflectsFiniteProducts
  signature: (F : C ⥤ D) (G : D ⥤ E)
  body: inferInstance

中文:
实例 comp_reflectsFiniteProducts
  签名: (F : C ⥤ D) (G : D ⥤ E)
  定义体: inferInstance
-/
instance comp_reflectsFiniteProducts (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsFiniteProducts F] [ReflectsFiniteProducts G] :
    ReflectsFiniteProducts (F ⋙ G) where
  reflects _ := inferInstance

instance (F : C ⥤ D) [ReflectsFiniteLimits F] : ReflectsFiniteProducts F where
  reflects _ := inferInstance

/--
Definition of `PreservesFiniteColimits` / `PreservesFiniteColimits` 的定义

English:
class PreservesFiniteColimits
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - preservesFiniteColimits : forall (J : Type) [SmallCategory J] [FinCategory J], PreservesColimitsOfShape J F  [default: by infer_instance]

中文:
类 保持FiniteColimits
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - preservesFiniteColimits : 对任意 (J : 类型) [小范畴 J] [有限范畴 J], 保持形状余极限 J F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class PreservesFiniteColimits (F : C ⥤ D) : Prop where
  preservesFiniteColimits :
    forall (J : Type) [SmallCategory J] [FinCategory J], PreservesColimitsOfShape J F := by
      infer_instance

attribute [instance] PreservesFiniteColimits.preservesFiniteColimits

/--
Preserving finite colimits also implies preserving colimits over finite shapes in higher
universes.
-/
instance (priority := 100) preservesColimitsOfShapeOfPreservesFiniteColimits
    (F : C ⥤ D) [PreservesFiniteColimits F] (J : Type w) [SmallCategory J] [FinCategory J] :
    PreservesColimitsOfShape J F := by
  apply preservesColimitsOfShape_of_equiv (FinCategory.equivAsType J)

-- This is a dangerous instance as it has unbound universe variables.
/--
lemma `PreservesColimitsOfSize.preservesFiniteColimits` / 引理 `PreservesColimitsOfSize.preservesFiniteColimits`

English:
lemma PreservesColimitsOfSize.preservesFiniteColimits
  statement: (F : C ⥤ D)
  proof: by
    have := preservesSmallestColimits_of_preservesColimits F
    exact preservesColimitsOfShape_of_equiv (FinCategory.equivAsType J) F

中文:
引理 保持余limitsOfSize.preservesFiniteColimits
  结论: (F : C ⥤ D)
  证明: by
    have := preservesSmallestColimits_of_preservesColimits F
    exact preservesColimitsOfShape_of_equiv (FinCategory.equivAsType J) F

Depends on / 依赖: CreatesColimitOfIsSplitPair, CreatesColimitOfIsSplitPair.out, FinCategory, FinCategory.equivAsType, equivAsType, preservesColimitsOfShape_of_equiv, preservesSmallestColimits_of_preservesColimits
-/
lemma PreservesColimitsOfSize.preservesFiniteColimits (F : C ⥤ D)
    [PreservesColimitsOfSize.{w, w₂} F] : PreservesFiniteColimits F where
  preservesFiniteColimits J (sJ : SmallCategory J) fJ := by
    have := preservesSmallestColimits_of_preservesColimits F
    exact preservesColimitsOfShape_of_equiv (FinCategory.equivAsType J) F

-- Added as a specialization of the dangerous instance above, for colimits indexed in Type 0.
instance (priority := 120) PreservesColimitsOfSize0.preservesFiniteColimits
    (F : C ⥤ D) [PreservesColimitsOfSize.{0, 0} F] : PreservesFiniteColimits F :=
  PreservesColimitsOfSize.preservesFiniteColimits F

-- An alternative specialization of the dangerous instance for small colimits.
instance (priority := 120) PreservesColimits.preservesFiniteColimits (F : C ⥤ D)
    [PreservesColimits F] : PreservesFiniteColimits F :=
  PreservesColimitsOfSize.preservesFiniteColimits F

attribute [local instance] uliftCategory in
/--
lemma `preservesFiniteColimits_of_preservesFiniteColimitsOfSize` / 引理 `preservesFiniteColimits_of_preservesFiniteColimitsOfSize`

English:
lemma preservesFiniteColimits_of_preservesFiniteColimitsOfSize
  statement: (F : C ⥤ D)
  proof: by
        let : Category (ULiftHom (ULift J)) := ULiftHom.category
        have := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
        exact preservesColimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv J).symm F

中文:
引理 preservesFiniteColimits_of_preservesFiniteColimitsOfSize
  结论: (F : C ⥤ D)
  证明: by
        let : Category (ULiftHom (ULift J)) := ULiftHom.category
        have := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
        exact preservesColimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv J).symm F

Depends on / 依赖: Category, CategoryTheory, CategoryTheory.finCategoryUlift, ULiftHom, ULiftHom.category, ULiftHomULiftCategory, ULiftHomULiftCategory.equiv, category, finCategoryUlift, preservesColimitsOfShape_of_equiv
-/
lemma preservesFiniteColimits_of_preservesFiniteColimitsOfSize (F : C ⥤ D)
    (h :
      forall (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), PreservesColimitsOfShape J F) :
    PreservesFiniteColimits F where
      preservesFiniteColimits J (_ : SmallCategory J) _ := by
        let : Category (ULiftHom (ULift J)) := ULiftHom.category
        have := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
        exact preservesColimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv J).symm F

/--
lemma `comp_preservesFiniteColimits` / 引理 `comp_preservesFiniteColimits`

English:
lemma comp_preservesFiniteColimits
  statement: (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteColimits F]
  proof: ⟨fun _ _ _ => inferInstance⟩

中文:
引理 comp_preservesFiniteColimits
  结论: (F : C ⥤ D) (G : D ⥤ E) [保持FiniteColimits F]
  证明: ⟨fun _ _ _ => inferInstance⟩
-/
lemma comp_preservesFiniteColimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteColimits F]
    [PreservesFiniteColimits G] : PreservesFiniteColimits (F ⋙ G) :=
  ⟨fun _ _ _ => inferInstance⟩

/--
lemma `preservesFiniteColimits_of_natIso` / 引理 `preservesFiniteColimits_of_natIso`

English:
lemma preservesFiniteColimits_of_natIso
  given: {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteColimits F]
  proof: preservesColimitsOfShape_of_natIso h

中文:
引理 preservesFiniteColimits_of_natIso
  条件: {F G : C ⥤ D} (h : F ≅ G) [保持FiniteColimits F]
  证明: preservesColimitsOfShape_of_natIso h

Depends on / 依赖: preservesColimitsOfShape_of_natIso
-/
lemma preservesFiniteColimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteColimits F] :
    PreservesFiniteColimits G where
  preservesFiniteColimits _ _ _ := preservesColimitsOfShape_of_natIso h

/--
Definition of `PreservesFiniteCoproducts` / `PreservesFiniteCoproducts` 的定义

English:
class PreservesFiniteCoproducts
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - preserves : forall n, PreservesColimitsOfShape (Discrete (Fin n)) F

中文:
类 保持FiniteCoproducts
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - preserves : 对任意 n, 保持形状余极限 (离散 (有限集 n)) F

Depends on / 依赖: PreservesColimitOfIsReflexivePair, PreservesColimitOfIsReflexivePair.out
-/
class PreservesFiniteCoproducts (F : C ⥤ D) : Prop where
  /-- preservation of colimits indexed by `Discrete (Fin n)`. -/
  preserves : forall n, PreservesColimitsOfShape (Discrete (Fin n)) F

instance (priority := 100) (F : C ⥤ D) (J : Type u) [Finite J]
    [PreservesFiniteCoproducts F] : PreservesColimitsOfShape (Discrete J) F :=
  let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have := PreservesFiniteCoproducts.preserves (F := F) n
  preservesColimitsOfShape_of_equiv (Discrete.equivalence e.symm) F

/--
Instance `comp_preservesFiniteCoproducts` / 实例 `comp_preservesFiniteCoproducts`

English:
instance comp_preservesFiniteCoproducts
  signature: (F : C ⥤ D) (G : D ⥤ E)
  body: inferInstance

中文:
实例 comp_preservesFiniteCoproducts
  签名: (F : C ⥤ D) (G : D ⥤ E)
  定义体: inferInstance
-/
instance comp_preservesFiniteCoproducts (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteCoproducts F] [PreservesFiniteCoproducts G] :
    PreservesFiniteCoproducts (F ⋙ G) where
  preserves _ := inferInstance

instance (F : C ⥤ D) [PreservesFiniteColimits F] : PreservesFiniteCoproducts F where
  preserves _ := inferInstance

/--
Definition of `ReflectsFiniteColimits` / `ReflectsFiniteColimits` 的定义

English:
class ReflectsFiniteColimits
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - [reflects : forall (J : Type) [SmallCategory J] [FinCategory J], ReflectsColimitsOfShape J F]

中文:
类 ReflectsFiniteColimits
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - [reflects : 对任意 (J : 类型) [小范畴 J] [有限范畴 J], 反映形状余极限 J F]
-/
class ReflectsFiniteColimits (F : C ⥤ D) : Prop where
  [reflects : forall (J : Type) [SmallCategory J] [FinCategory J], ReflectsColimitsOfShape J F]

attribute [instance] ReflectsFiniteColimits.reflects

-- This is a dangerous instance as it has unbound universe variables.
/--
lemma `ReflectsColimitsOfSize.reflectsFiniteColimits` / 引理 `ReflectsColimitsOfSize.reflectsFiniteColimits`

English:
lemma ReflectsColimitsOfSize.reflectsFiniteColimits
  proof: by
    have := reflectsSmallestColimits_of_reflectsColimits F
    exact reflectsColimitsOfShape_of_equiv (FinCategory.equivAsType J) F

中文:
引理 ReflectsColimitsOfSize.reflectsFiniteColimits
  证明: by
    have := reflectsSmallestColimits_of_reflectsColimits F
    exact reflectsColimitsOfShape_of_equiv (FinCategory.equivAsType J) F

Depends on / 依赖: FinCategory, FinCategory.equivAsType, equivAsType, reflectsColimitsOfShape_of_equiv, reflectsSmallestColimits_of_reflectsColimits
-/
lemma ReflectsColimitsOfSize.reflectsFiniteColimits
    (F : C ⥤ D) [ReflectsColimitsOfSize.{w, w₂} F] : ReflectsFiniteColimits F where
  reflects J (sJ : SmallCategory J) fJ := by
    have := reflectsSmallestColimits_of_reflectsColimits F
    exact reflectsColimitsOfShape_of_equiv (FinCategory.equivAsType J) F

-- Added as a specialization of the dangerous instance above, for colimits indexed in Type 0.
instance (priority := 120) (F : C ⥤ D) [ReflectsColimitsOfSize.{0, 0} F] :
    ReflectsFiniteColimits F :=
  ReflectsColimitsOfSize.reflectsFiniteColimits F

-- An alternative specialization of the dangerous instance for small colimits.
instance (priority := 120) (F : C ⥤ D)
    [ReflectsColimits F] : ReflectsFiniteColimits F :=
  ReflectsColimitsOfSize.reflectsFiniteColimits F

/- Similarly to preserving finite coproducts, quantified classes don't behave well. -/
/--
Definition of `ReflectsFiniteCoproducts` / `ReflectsFiniteCoproducts` 的定义

English:
class ReflectsFiniteCoproducts
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - reflects : forall n, ReflectsColimitsOfShape (Discrete (Fin n)) F

中文:
类 ReflectsFiniteCoproducts
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - reflects : 对任意 n, 反映形状余极限 (离散 (有限集 n)) F
-/
class ReflectsFiniteCoproducts (F : C ⥤ D) : Prop where
  reflects : forall n, ReflectsColimitsOfShape (Discrete (Fin n)) F

instance (priority := 100) (F : C ⥤ D) [ReflectsFiniteCoproducts F] (J : Type u) [Finite J] :
    ReflectsColimitsOfShape (Discrete J) F :=
  let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have := ReflectsFiniteCoproducts.reflects (F := F) n
  reflectsColimitsOfShape_of_equiv (Discrete.equivalence e.symm) _

/--
lemma `preservesFiniteColimits_of_reflects_of_preserves` / 引理 `preservesFiniteColimits_of_reflects_of_preserves`

English:
lemma preservesFiniteColimits_of_reflects_of_preserves
  statement: (F : C ⥤ D) (G : D ⥤ E)
  proof: preservesColimitsOfShape_of_reflects_of_preserves F G

中文:
引理 preservesFiniteColimits_of_reflects_of_preserves
  结论: (F : C ⥤ D) (G : D ⥤ E)
  证明: preservesColimitsOfShape_of_reflects_of_preserves F G

Depends on / 依赖: preservesColimitsOfShape_of_reflects_of_preserves
-/
lemma preservesFiniteColimits_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteColimits (F ⋙ G)] [ReflectsFiniteColimits G] : PreservesFiniteColimits F where
  preservesFiniteColimits _ _ _ := preservesColimitsOfShape_of_reflects_of_preserves F G

/--
lemma `preservesFiniteCoproducts_of_reflects_of_preserves` / 引理 `preservesFiniteCoproducts_of_reflects_of_preserves`

English:
lemma preservesFiniteCoproducts_of_reflects_of_preserves
  statement: (F : C ⥤ D) (G : D ⥤ E)
  proof: preservesColimitsOfShape_of_reflects_of_preserves F G

中文:
引理 preservesFiniteCoproducts_of_reflects_of_preserves
  结论: (F : C ⥤ D) (G : D ⥤ E)
  证明: preservesColimitsOfShape_of_reflects_of_preserves F G

Depends on / 依赖: preservesColimitsOfShape_of_reflects_of_preserves
-/
lemma preservesFiniteCoproducts_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteCoproducts (F ⋙ G)] [ReflectsFiniteCoproducts G] :
    PreservesFiniteCoproducts F where
  preserves _ := preservesColimitsOfShape_of_reflects_of_preserves F G

/--
Instance `reflectsFiniteColimitsOfReflectsIsomorphisms` / 实例 `reflectsFiniteColimitsOfReflectsIsomorphisms`

English:
instance reflectsFiniteColimitsOfReflectsIsomorphisms
  signature: (F : C ⥤ D)
  body: reflectsColimitsOfShape_of_reflectsIsomorphisms

中文:
实例 reflectsFiniteColimitsOfReflectsIsomorphisms
  签名: (F : C ⥤ D)
  定义体: reflectsColimitsOfShape_of_reflectsIsomorphisms

Depends on / 依赖: reflectsColimitsOfShape_of_reflectsIsomorphisms
-/
instance reflectsFiniteColimitsOfReflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteColimits C] [PreservesFiniteColimits F] :
      ReflectsFiniteColimits F where
  reflects _ _ _ := reflectsColimitsOfShape_of_reflectsIsomorphisms

/--
Instance `reflectsFiniteCoproductsOfReflectsIsomorphisms` / 实例 `reflectsFiniteCoproductsOfReflectsIsomorphisms`

English:
instance reflectsFiniteCoproductsOfReflectsIsomorphisms
  signature: (F : C ⥤ D)
  body: reflectsColimitsOfShape_of_reflectsIsomorphisms

中文:
实例 reflectsFiniteCoproductsOfReflectsIsomorphisms
  签名: (F : C ⥤ D)
  定义体: reflectsColimitsOfShape_of_reflectsIsomorphisms

Depends on / 依赖: reflectsColimitsOfShape_of_reflectsIsomorphisms
-/
instance reflectsFiniteCoproductsOfReflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteCoproducts C] [PreservesFiniteCoproducts F] :
      ReflectsFiniteCoproducts F where
  reflects _ := reflectsColimitsOfShape_of_reflectsIsomorphisms

/--
Instance `comp_reflectsFiniteCoproducts` / 实例 `comp_reflectsFiniteCoproducts`

English:
instance comp_reflectsFiniteCoproducts
  signature: (F : C ⥤ D) (G : D ⥤ E)
  body: inferInstance

中文:
实例 comp_reflectsFiniteCoproducts
  签名: (F : C ⥤ D) (G : D ⥤ E)
  定义体: inferInstance
-/
instance comp_reflectsFiniteCoproducts (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsFiniteCoproducts F] [ReflectsFiniteCoproducts G] :
    ReflectsFiniteCoproducts (F ⋙ G) where
  reflects _ := inferInstance

instance (F : C ⥤ D) [ReflectsFiniteColimits F] : ReflectsFiniteCoproducts F where
  reflects _ := inferInstance

end CategoryTheory.Limits
