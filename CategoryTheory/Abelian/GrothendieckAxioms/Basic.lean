/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Isaac Hernando, Coleton Kotch, Adam Topaz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Logic.Equiv.List
/-!

# Grothendieck Axioms

This file defines some of the Grothendieck Axioms for abelian categories, and proves
basic facts about them.

## Definitions

- `HasExactColimitsOfShape J C` -- colimits of shape `J` in `C` are exact.
- The dual of the above definitions, called `HasExactLimitsOfShape`.
- `AB4` -- coproducts are exact (this is formulated in terms of `HasExactColimitsOfShape`).
- `AB5` -- filtered colimits are exact (this is formulated in terms of `HasExactColimitsOfShape`).

## Theorems

- The implication from `AB5` to `AB4` is established in `AB4.ofAB5`.
- That `HasExactColimitsOfShape J C` is invariant under equivalences in both parameters is shown
  in `HasExactColimitsOfShape.of_domain_equivalence` and
  `HasExactColimitsOfShape.of_codomain_equivalence`.

## Remarks

For `AB4` and `AB5`, we only require left exactness as right exactness is automatic.
A comparison with Grothendieck's original formulation of the properties can be found in the
comments of the linked Stacks page.
Exactness as the preservation of short exact sequences is introduced in
`Mathlib/CategoryTheory/Abelian/Exact.lean`.

We do not require `Abelian` in the definition of `AB4` and `AB5` because these classes represent
individual axioms. An `AB4` category is an _abelian_ category satisfying `AB4`, and similarly for
`AB5`.

## References
* [Stacks: Grothendieck's AB conditions](https://stacks.math.columbia.edu/tag/079A)

-/

public section

namespace CategoryTheory

open Limits CategoryTheory.Functor

attribute [instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe w w' w₂ w₂' v v' v'' u u' u''

variable (C : Type u) [Category.{v} C]

/--
A category `C` is said to have exact colimits of shape `J` provided that colimits of shape `J`
exist and are exact (in the sense that they preserve finite limits).
-/
/-
**CategoryTheory.HasExactColimitsOfShape** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheor
y`。
形式化陈述：HasExactColimitsOfShape (J : Type u') [Category.{v'} J] (C : Type u) [Cate
gory.{v} C] [HasColimitsOfShape J C] where /-- Exactness of `J`-shaped colimits 
stated as `colim : (J ⥤ C) ⥤ C` preserving finite limits. -/ preservesFiniteLimi
ts : PreservesFiniteLimits (colim (J
参数：J : Type u'；C : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` is said to have exact colimits of shape `J` provided that colimit
s of shape `J`
exist and are exact (in the sense that they preserve finite limits).
-/
class HasExactColimitsOfShape (J : Type u') [Category.{v'} J] (C : Type u) [Category.{v} C]
    [HasColimitsOfShape J C] where
  /-- Exactness of `J`-shaped colimits stated as `colim : (J ⥤ C) ⥤ C` preserving finite limits. -/
  preservesFiniteLimits : PreservesFiniteLimits (colim (J := J) (C := C))

/--
A category `C` is said to have exact limits of shape `J` provided that limits of shape `J`
exist and are exact (in the sense that they preserve finite colimits).
-/
/-
**CategoryTheory.HasExactLimitsOfShape** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`
。
形式化陈述：HasExactLimitsOfShape (J : Type u') [Category.{v'} J] (C : Type u) [Catego
ry.{v} C] [HasLimitsOfShape J C] where /-- Exactness of `J`-shaped limits stated
 as `lim : (J ⥤ C) ⥤ C` preserving finite colimits. -/ preservesFiniteColimits :
 PreservesFiniteColimits (lim (J
参数：J : Type u'；C : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` is said to have exact limits of shape `J` provided that limits of
 shape `J`
exist and are exact (in the sense that they preserve finite colimits).
-/
class HasExactLimitsOfShape (J : Type u') [Category.{v'} J] (C : Type u) [Category.{v} C]
    [HasLimitsOfShape J C] where
  /-- Exactness of `J`-shaped limits stated as `lim : (J ⥤ C) ⥤ C` preserving finite colimits. -/
  preservesFiniteColimits : PreservesFiniteColimits (lim (J := J) (C := C))

attribute [instance] HasExactColimitsOfShape.preservesFiniteLimits
  HasExactLimitsOfShape.preservesFiniteColimits

variable {C} in
/--
Pull back a `HasExactColimitsOfShape J` along a functor which preserves and reflects finite limits
and preserves colimits of shape `J`
-/
/-
**CategoryTheory.HasExactColimitsOfShape.domain_of_functor** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.HasExactColimitsOfShape`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} (J
 : Type u_2)   [inst_1 : CategoryTheory.Category.{v_1, u_2} J] [inst_2 : Categor
yTheory.Category.{v_2, u_1} D]   [inst_3 : CategoryTheory.Limits.HasColimitsOfSh
ape J C] [inst_4 : CategoryTheory.Limits.HasColimitsOfShape J D]   [CategoryTheo
ry.HasExactColimitsOfShape J D] (F : CategoryTheory.Functor C D)   [CategoryTheo
ry.Limits.PreservesFiniteLimits F] [CategoryTheory.Limits.ReflectsFiniteLimits F
]   [CategoryTheory.Limits.HasFiniteLimits C] [CategoryTheory.Limits.PreservesCo
limitsOfShape J F],   CategoryTheory.HasExactColimitsOfShape J C
参数：J : Type u_2；F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.HasExactColimitsOfShape.preservesFiniteLimits`：∀ {J : Typ
e u'} {inst : CategoryTheory.Category.{v', u'} J} {C : Type u} {inst_1 : Categor
yTheory.Category.{v, u} C}   {inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
Pull back a `HasExactColimitsOfShape J` along a functor which preserves and refl
ects finite limits
and preserves colimits of shape `J`
-/
lemma HasExactColimitsOfShape.domain_of_functor {D : Type*} (J : Type*) [Category* J] [Category* D]
    [HasColimitsOfShape J C] [HasColimitsOfShape J D] [HasExactColimitsOfShape J D]
    (F : C ⥤ D) [PreservesFiniteLimits F] [ReflectsFiniteLimits F] [HasFiniteLimits C]
    [PreservesColimitsOfShape J F] : HasExactColimitsOfShape J C where
  preservesFiniteLimits := { preservesFiniteLimits I := { preservesLimit {G} := {
    preserves {c} hc := by
      constructor
      apply isLimitOfReflects F
      refine (IsLimit.equivOfNatIsoOfIso (isoWhiskerLeft G (preservesColimitNatIso F).symm)
        ((_ ⋙ colim).mapCone c) _ ?_) (isLimitOfPreserves _ hc)
      exact Cone.ext ((preservesColimitNatIso F).symm.app _)
        fun i ↦ (preservesColimitNatIso F).inv.naturality _ } } }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {C} in
/--
Pull back a `HasExactLimitsOfShape J` along a functor which preserves and reflects finite colimits
and preserves limits of shape `J`
-/
/-
**CategoryTheory.HasExactLimitsOfShape.domain_of_functor** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.HasExactLimitsOfShape`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} (J
 : Type u_2)   [inst_1 : CategoryTheory.Category.{v_1, u_1} D] [inst_2 : Categor
yTheory.Category.{v_2, u_2} J]   [inst_3 : CategoryTheory.Limits.HasLimitsOfShap
e J C] [inst_4 : CategoryTheory.Limits.HasLimitsOfShape J D]   [CategoryTheory.H
asExactLimitsOfShape J D] (F : CategoryTheory.Functor C D)   [CategoryTheory.Lim
its.PreservesFiniteColimits F] [CategoryTheory.Limits.ReflectsFiniteColimits F] 
  [CategoryTheory.Limits.HasFiniteColimits C] [CategoryTheory.Limits.PreservesLi
mitsOfShape J F],   CategoryTheory.HasExactLimitsOfShape J C
参数：J : Type u_2；F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.eq_inv_comp`：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.HasExactLimitsOfShape.preservesFiniteColimits`：∀ {J : Typ
e u'} {inst : CategoryTheory.Category.{v', u'} J} {C : Type u} {inst_1 : Categor
yTheory.Category.{v, u} C}   {inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.Limits.reflectsColimit_of_reflectsColimitsOfShape`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteColimits.reflects`：∀ {C : Type u₁} {
inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheor
y.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
Pull back a `HasExactLimitsOfShape J` along a functor which preserves and reflec
ts finite colimits
and preserves limits of shape `J`
-/
lemma HasExactLimitsOfShape.domain_of_functor {D : Type*} (J : Type*) [Category* D] [Category* J]
    [HasLimitsOfShape J C] [HasLimitsOfShape J D] [HasExactLimitsOfShape J D]
    (F : C ⥤ D) [PreservesFiniteColimits F] [ReflectsFiniteColimits F] [HasFiniteColimits C]
    [PreservesLimitsOfShape J F] : HasExactLimitsOfShape J C where
  preservesFiniteColimits := { preservesFiniteColimits I := { preservesColimit {G} := {
    preserves {c} hc := by
      constructor
      apply isColimitOfReflects F
      refine (IsColimit.equivOfNatIsoOfIso (isoWhiskerLeft G (preservesLimitNatIso F).symm)
        ((_ ⋙ lim).mapCocone c) _ ?_) (isColimitOfPreserves _ hc)
      refine Cocone.ext ((preservesLimitNatIso F).symm.app _) fun i ↦ ?_
      simp only [Functor.comp_obj, lim_obj, Functor.mapCocone_pt, isoWhiskerLeft_inv, Iso.symm_inv,
        Cocone.precompose_obj_pt, whiskeringRight_obj_obj, Functor.const_obj_obj,
        Cocone.precompose_obj_ι, NatTrans.comp_app, whiskerLeft_app, preservesLimitNatIso_hom_app,
        Functor.mapCocone_ι_app, Functor.comp_map, whiskeringRight_obj_map, lim_map, Iso.app_hom,
        Iso.symm_hom, preservesLimitNatIso_inv_app, Category.assoc]
      rw [← Iso.eq_inv_comp]
      exact (preservesLimitNatIso F).inv.naturality _ } } }

/--
Transport a `HasExactColimitsOfShape` along an equivalence of the shape.

Note: When `C` has finite limits, this lemma holds with the equivalence replaced by a final
functor, see `hasExactColimitsOfShape_of_final` below.
-/
/-
**CategoryTheory.HasExactColimitsOfShape.of_domain_equivalence** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.HasExactColimitsOfShape`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] {J : Type u_1} {J
' : Type u_2}   [inst_1 : CategoryTheory.Category.{v_1, u_1} J] [inst_2 : Catego
ryTheory.Category.{v_2, u_2} J'] (e : J ≌ J')   [inst_3 : CategoryTheory.Limits.
HasColimitsOfShape J C] [CategoryTheory.HasExactColimitsOfShape J C],   Category
Theory.HasExactColimitsOfShape J' C
参数：C : Type u；e : J ≌ J'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_of_natIso`：preservesFiniteLi
mits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteLimits F] : PreservesFi
niteLimits G where preservesFiniteLimits _ …
· 使用定理 `CategoryTheory.Functor.final_of_isRightAdjoint`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用引理 `CategoryTheory.Limits.comp_preservesFiniteLimits`：comp_preservesFiniteLi
mits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteLimits F] [PreservesFiniteLimits G]
 : PreservesFiniteLimits (F ⋙ G)
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.instIsEquivalenceObjWhiskeringLeft`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.HasExactColimitsOfShape.preservesFiniteLimits`：∀ {J : Typ
e u'} {inst : CategoryTheory.Category.{v', u'} J} {C : Type u} {inst_1 : Categor
yTheory.Category.{v, u} C}   {inst_2 : CategoryThe…

--- 原说明 ---
Transport a `HasExactColimitsOfShape` along an equivalence of the shape.

Note: When `C` has finite limits, this lemma holds with the equivalence replaced
 by a final
functor, see `hasExactColimitsOfShape_of_final` below.
-/
lemma HasExactColimitsOfShape.of_domain_equivalence {J J' : Type*} [Category* J] [Category* J']
    (e : J ≌ J') [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    haveI : HasColimitsOfShape J' C := hasColimitsOfShape_of_equivalence e
    HasExactColimitsOfShape J' C :=
  haveI : HasColimitsOfShape J' C := hasColimitsOfShape_of_equivalence e
  ⟨preservesFiniteLimits_of_natIso (Functor.Final.colimIso e.functor)⟩

variable {C} in
/-
**CategoryTheory.HasExactColimitsOfShape.of_codomain_equivalence** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.HasExactColimitsOfShape`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : Type u_1) [i
nst_1 : CategoryTheory.Category.{v_1, u_1} J]   {D : Type u_2} [inst_2 : Categor
yTheory.Category.{v_2, u_2} D] (e : C ≌ D)   [inst_3 : CategoryTheory.Limits.Has
ColimitsOfShape J C] [CategoryTheory.HasExactColimitsOfShape J C],   CategoryThe
ory.HasExactColimitsOfShape J D
参数：J : Type u_1；e : C ≌ D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence`：hasColimits
OfShape_of_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimitsOfShape J D] : 
HasColimitsOfShape J C
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_natIso`：preservesLimit_of_natIso
 (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesLimit K F] : PreservesLimit K G
 where preserves t
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.comp_preservesLimitsOfShape`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.HasExactColimitsOfShape.preservesFiniteLimits`：∀ {J : Typ
e u'} {inst : CategoryTheory.Category.{v', u'} J} {C : Type u} {inst_1 : Categor
yTheory.Category.{v, u} C}   {inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
lemma HasExactColimitsOfShape.of_codomain_equivalence (J : Type*) [Category* J] {D : Type*}
    [Category* D] (e : C ≌ D) [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    haveI : HasColimitsOfShape J D := Adjunction.hasColimitsOfShape_of_equivalence e.inverse
    HasExactColimitsOfShape J D := by
  have : HasColimitsOfShape J D := Adjunction.hasColimitsOfShape_of_equivalence e.inverse
  refine ⟨⟨fun _ _ _ => ⟨@fun K => ?_⟩⟩⟩
  refine preservesLimit_of_natIso K (?_ : e.congrRight.inverse ⋙ colim ⋙ e.functor ≅ colim)
  apply e.symm.congrRight.fullyFaithfulFunctor.preimageIso
  exact isoWhiskerLeft (_ ⋙ colim) e.unitIso.symm ≪≫ (preservesColimitNatIso e.inverse).symm

/--
Transport a `HasExactLimitsOfShape` along an equivalence of the shape.

Note: When `C` has finite colimits, this lemma holds with the equivalence replaced by an initial
functor, see `hasExactLimitsOfShape_of_initial` below.
-/
/-
**CategoryTheory.HasExactLimitsOfShape.of_domain_equivalence** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.HasExactLimitsOfShape`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] {J : Type u_1} {J
' : Type u_2}   [inst_1 : CategoryTheory.Category.{v_1, u_1} J] [inst_2 : Catego
ryTheory.Category.{v_2, u_2} J'] (e : J ≌ J')   [inst_3 : CategoryTheory.Limits.
HasLimitsOfShape J C] [CategoryTheory.HasExactLimitsOfShape J C],   CategoryTheo
ry.HasExactLimitsOfShape J' C
参数：C : Type u；e : J ≌ J'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C
· 使用引理 `CategoryTheory.Limits.preservesFiniteColimits_of_natIso`：preservesFinite
Colimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteColimits F] : Prese
rvesFiniteColimits G where preservesFiniteCol…
· 使用定理 `CategoryTheory.Functor.initial_of_isLeftAdjoint`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用引理 `CategoryTheory.Limits.comp_preservesFiniteColimits`：comp_preservesFinite
Colimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteColimits F] [PreservesFiniteCol
imits G] : PreservesFiniteColimits (F ⋙ …
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint`：∀ {C 
: Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.instIsEquivalenceObjWhiskeringLeft`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.HasExactLimitsOfShape.preservesFiniteColimits`：∀ {J : Typ
e u'} {inst : CategoryTheory.Category.{v', u'} J} {C : Type u} {inst_1 : Categor
yTheory.Category.{v, u} C}   {inst_2 : CategoryThe…

--- 原说明 ---
Transport a `HasExactLimitsOfShape` along an equivalence of the shape.

Note: When `C` has finite colimits, this lemma holds with the equivalence replac
ed by an initial
functor, see `hasExactLimitsOfShape_of_initial` below.
-/
lemma HasExactLimitsOfShape.of_domain_equivalence {J J' : Type*} [Category* J] [Category* J']
    (e : J ≌ J') [HasLimitsOfShape J C] [HasExactLimitsOfShape J C] :
    haveI : HasLimitsOfShape J' C := hasLimitsOfShape_of_equivalence e
    HasExactLimitsOfShape J' C :=
  haveI : HasLimitsOfShape J' C := hasLimitsOfShape_of_equivalence e
  ⟨preservesFiniteColimits_of_natIso (Functor.Initial.limIso e.functor)⟩

variable {C} in
/-
**CategoryTheory.HasExactLimitsOfShape.of_codomain_equivalence** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.HasExactLimitsOfShape`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : Type u_1) [i
nst_1 : CategoryTheory.Category.{v_1, u_1} J]   {D : Type u_2} [inst_2 : Categor
yTheory.Category.{v_2, u_2} D] (e : C ≌ D)   [inst_3 : CategoryTheory.Limits.Has
LimitsOfShape J C] [CategoryTheory.HasExactLimitsOfShape J C],   CategoryTheory.
HasExactLimitsOfShape J D
参数：J : Type u_1；e : C ≌ D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence`：hasLimitsOfSh
ape_of_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOfShape J C] : HasLim
itsOfShape J D
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_natIso`：preservesColimit_of_na
tIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesColimit K F] : PreservesCol
imit K G where preserves t
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.comp_preservesColimitsOfShape`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.HasExactLimitsOfShape.preservesFiniteColimits`：∀ {J : Typ
e u'} {inst : CategoryTheory.Category.{v', u'} J} {C : Type u} {inst_1 : Categor
yTheory.Category.{v, u} C}   {inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
lemma HasExactLimitsOfShape.of_codomain_equivalence (J : Type*) [Category* J] {D : Type*}
    [Category* D] (e : C ≌ D) [HasLimitsOfShape J C] [HasExactLimitsOfShape J C] :
    haveI : HasLimitsOfShape J D := Adjunction.hasLimitsOfShape_of_equivalence e.inverse
    HasExactLimitsOfShape J D := by
  have : HasLimitsOfShape J D := Adjunction.hasLimitsOfShape_of_equivalence e.inverse
  refine ⟨⟨fun _ _ _ => ⟨@fun K => ?_⟩⟩⟩
  refine preservesColimit_of_natIso K (?_ : e.congrRight.inverse ⋙ lim ⋙ e.functor ≅ lim)
  apply e.symm.congrRight.fullyFaithfulFunctor.preimageIso
  exact isoWhiskerLeft (_ ⋙ lim) e.unitIso.symm ≪≫ (preservesLimitNatIso e.inverse).symm

namespace Adjunction

variable {C} {D : Type u''} [Category.{v''} D] {F : C ⥤ D} {G : D ⥤ C}

/-- Let `adj : F ⊣ G` be an adjunction, with `G : D ⥤ C` reflective.
Assume that `D` has finite limits and `F` commutes with them.
If `C` has exact colimits of shape `J`, then `D` also has exact colimits of shape `J`. -/
/-
**CategoryTheory.Adjunction.hasExactColimitsOfShape** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Adjunction`。
形式化陈述：hasExactColimitsOfShape (adj : F ⊣ G) [G.Full] [G.Faithful] (J : Type u') 
[Category.{v'} J] [HasColimitsOfShape J C] [HasColimitsOfShape J D] [HasExactCol
imitsOfShape J C] [HasFiniteLimits D] [PreservesFiniteLimits F] : HasExactColimi
tsOfShape J D where preservesFiniteLimits
参数：adj : F ⊣ G；J : Type u'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.rightAdjoint_preservesLimits`：rightAdjoint_pre
servesLimits : PreservesLimitsOfSize.{v, u} G where preservesLimitsOfShape
· 使用引理 `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`：leftAdjoint_pre
servesColimits : PreservesColimitsOfSize.{v, u} F where preservesColimitsOfShape
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_natIso`：preservesLimit_of_natIso
 (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesLimit K F] : PreservesLimit K G
 where preserves t
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize0.preservesFiniteLimits`：∀ {C
 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : 
CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.HasExactColimitsOfShape.preservesFiniteLimits`：∀ {J : Typ
e u'} {inst : CategoryTheory.Category.{v', u'} J} {C : Type u} {inst_1 : Categor
yTheory.Category.{v, u} C}   {inst_2 : CategoryThe…

--- 原说明 ---
Let `adj : F ⊣ G` be an adjunction, with `G : D ⥤ C` reflective.
Assume that `D` has finite limits and `F` commutes with them.
If `C` has exact colimits of shape `J`, then `D` also has exact colimits of shap
e `J`.
-/
lemma hasExactColimitsOfShape (adj : F ⊣ G) [G.Full] [G.Faithful]
    (J : Type u') [Category.{v'} J] [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    [HasExactColimitsOfShape J C] [HasFiniteLimits D] [PreservesFiniteLimits F] :
    HasExactColimitsOfShape J D where
  preservesFiniteLimits := ⟨fun K _ _ ↦ ⟨fun {H} ↦ by
    have : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits
    have : PreservesColimitsOfSize.{v', u'} F := adj.leftAdjoint_preservesColimits
    let e : (whiskeringRight J D C).obj G ⋙ colim ⋙ F ≅ colim :=
      isoWhiskerLeft _ (preservesColimitNatIso F) ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (whiskeringRightObjCompIso G F) _ ≪≫
        isoWhiskerRight ((whiskeringRight J D D).mapIso (asIso adj.counit)) _ ≪≫
        isoWhiskerRight whiskeringRightObjIdIso _ ≪≫ colim.leftUnitor
    exact preservesLimit_of_natIso _ e⟩⟩

/-- Let `adj : F ⊣ G` be an adjunction, with `F : C ⥤ D` coreflective.
Assume that `C` has finite colimits and `G` commutes with them.
If `D` has exact limits of shape `J`, then `C` also has exact limits of shape `J`. -/
/-
**CategoryTheory.Adjunction.hasExactLimitsOfShape** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Adjunction`。
形式化陈述：hasExactLimitsOfShape (adj : F ⊣ G) [F.Full] [F.Faithful] (J : Type u') [C
ategory.{v'} J] [HasLimitsOfShape J C] [HasLimitsOfShape J D] [HasExactLimitsOfS
hape J D] [HasFiniteColimits C] [PreservesFiniteColimits G] : HasExactLimitsOfSh
ape J C where preservesFiniteColimits
参数：adj : F ⊣ G；J : Type u'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.rightAdjoint_preservesLimits`：rightAdjoint_pre
servesLimits : PreservesLimitsOfSize.{v, u} G where preservesLimitsOfShape
· 使用引理 `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`：leftAdjoint_pre
servesColimits : PreservesColimitsOfSize.{v, u} F where preservesColimitsOfShape
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_natIso`：preservesColimit_of_na
tIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesColimit K F] : PreservesCol
imit K G where preserves t
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize0.preservesFiniteColimits`：
∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_
1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.HasExactLimitsOfShape.preservesFiniteColimits`：∀ {J : Typ
e u'} {inst : CategoryTheory.Category.{v', u'} J} {C : Type u} {inst_1 : Categor
yTheory.Category.{v, u} C}   {inst_2 : CategoryThe…

--- 原说明 ---
Let `adj : F ⊣ G` be an adjunction, with `F : C ⥤ D` coreflective.
Assume that `C` has finite colimits and `G` commutes with them.
If `D` has exact limits of shape `J`, then `C` also has exact limits of shape `J
`.
-/
lemma hasExactLimitsOfShape (adj : F ⊣ G) [F.Full] [F.Faithful]
    (J : Type u') [Category.{v'} J] [HasLimitsOfShape J C] [HasLimitsOfShape J D]
    [HasExactLimitsOfShape J D] [HasFiniteColimits C] [PreservesFiniteColimits G] :
    HasExactLimitsOfShape J C where
  preservesFiniteColimits := ⟨fun K _ _ ↦ ⟨fun {H} ↦ by
    have : PreservesLimitsOfSize.{v', u'} G := adj.rightAdjoint_preservesLimits
    have : PreservesColimitsOfSize.{0, 0} F := adj.leftAdjoint_preservesColimits
    let e : (whiskeringRight J _ _).obj F ⋙ lim ⋙ G ≅ lim :=
      isoWhiskerLeft _ (preservesLimitNatIso G) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (whiskeringRightObjCompIso F G) _ ≪≫
        isoWhiskerRight ((whiskeringRight J C C).mapIso (asIso adj.unit).symm) _ ≪≫
        isoWhiskerRight whiskeringRightObjIdIso _ ≪≫ lim.leftUnitor
    exact preservesColimit_of_natIso _ e⟩⟩

end Adjunction

/--
A category `C` which has coproducts is said to have `AB4` of size `w` provided that
coproducts of size `w` are exact.
-/
@[pp_with_univ]
/-
**CategoryTheory.AB4OfSize** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheory
.Limits.HasCoproducts C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` which has coproducts is said to have `AB4` of size `w` provided t
hat
coproducts of size `w` are exact.
-/
class AB4OfSize [HasCoproducts.{w} C] where
  ofShape (α : Type w) : HasExactColimitsOfShape (Discrete α) C

attribute [instance] AB4OfSize.ofShape

/--
A category `C` which has coproducts is said to have `AB4` provided that
coproducts are exact.
-/
@[stacks 079B]
/-
**CategoryTheory.AB4** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：AB4 [HasCoproducts C]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` which has coproducts is said to have `AB4` provided that
coproducts are exact.
-/
abbrev AB4 [HasCoproducts C] := AB4OfSize.{v} C
/-
**CategoryTheory.AB4OfSize_shrink** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：AB4OfSize_shrink [HasCoproducts.{max w w'} C] [AB4OfSize.{max w w'} C] : h
aveI : HasCoproducts.{w} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.hasCoproducts_shrink`：hasCoproducts_shrink [HasCop
roducts.{max w w'} C] : HasCoproducts.{w} C
· 使用定理 `CategoryTheory.HasExactColimitsOfShape.of_domain_equivalence`：∀ (C : Typ
e u) [inst : CategoryTheory.Category.{v, u} C] {J : Type u_1} {J' : Type u_2}   
[inst_1 : CategoryTheory.Category.{v_1, u_1} J] [i…
· 使用定理 `CategoryTheory.AB4OfSize.ofShape`：∀ {C : Type u} {inst : CategoryTheory.
Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasCoproducts C}   [self : Ca
tegoryTheory.AB4OfSize…
-/
lemma AB4OfSize_shrink [HasCoproducts.{max w w'} C] [AB4OfSize.{max w w'} C] :
    haveI : HasCoproducts.{w} C := hasCoproducts_shrink.{w, w'}
    AB4OfSize.{w} C :=
  haveI := hasCoproducts_shrink.{w, w'} (C := C)
  ⟨fun J ↦ HasExactColimitsOfShape.of_domain_equivalence C
    (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [HasCoproducts.{w} C] [AB4OfSize.{w} C] :
    haveI : HasCoproducts.{0} C := hasCoproducts_shrink
    AB4OfSize.{0} C := AB4OfSize_shrink C

/-- A category `C` which has products is said to have `AB4Star` (in literature AB4\*)
provided that products are exact. -/
@[pp_with_univ, stacks 079B]
/-
**CategoryTheory.AB4StarOfSize** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheory
.Limits.HasProducts C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` which has products is said to have `AB4Star` (in literature AB4\*
)
provided that products are exact.
-/
class AB4StarOfSize [HasProducts.{w} C] where
  ofShape (α : Type w) : HasExactLimitsOfShape (Discrete α) C

attribute [instance] AB4StarOfSize.ofShape

/-- A category `C` which has products is said to have `AB4Star` (in literature AB4\*)
provided that products are exact. -/
/-
**CategoryTheory.AB4Star** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：AB4Star [HasProducts C]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` which has products is said to have `AB4Star` (in literature AB4\*
)
provided that products are exact.
-/
abbrev AB4Star [HasProducts C] := AB4StarOfSize.{v} C
/-
**CategoryTheory.AB4StarOfSize_shrink** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`
。
形式化陈述：AB4StarOfSize_shrink [HasProducts.{max w w'} C] [AB4StarOfSize.{max w w'} 
C] : haveI : HasProducts.{w} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.hasProducts_shrink`：hasProducts_shrink [HasProduct
s.{max w w'} C] : HasProducts.{w} C
· 使用定理 `CategoryTheory.HasExactLimitsOfShape.of_domain_equivalence`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] {J : Type u_1} {J' : Type u_2}   [i
nst_1 : CategoryTheory.Category.{v_1, u_1} J] [i…
· 使用定理 `CategoryTheory.AB4StarOfSize.ofShape`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasProducts C}   [self : 
CategoryTheory.AB4StarOfSi…
-/
lemma AB4StarOfSize_shrink [HasProducts.{max w w'} C] [AB4StarOfSize.{max w w'} C] :
    haveI : HasProducts.{w} C := hasProducts_shrink.{w, w'}
    AB4StarOfSize.{w} C :=
  haveI := hasProducts_shrink.{w, w'} (C := C)
  ⟨fun J ↦ HasExactLimitsOfShape.of_domain_equivalence C
    (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [HasProducts.{w} C] [AB4StarOfSize.{w} C] :
    haveI : HasProducts.{0} C := hasProducts_shrink
    AB4StarOfSize.{0} C := AB4StarOfSize_shrink C

/--
A category `C` which has countable coproducts is said to have countable `AB4` provided that
countable coproducts are exact.
-/
/-
**CategoryTheory.CountableAB4** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheory
.Limits.HasCountableCoproducts C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` which has countable coproducts is said to have countable `AB4` pr
ovided that
countable coproducts are exact.
-/
class CountableAB4 [HasCountableCoproducts C] where
  ofShape (α : Type) [Countable α] : HasExactColimitsOfShape (Discrete α) C
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [HasCoproducts.{0} C] [AB4OfSize.{0} C] : CountableAB4 C :=
  ⟨inferInstance⟩

/--
A category `C` which has countable coproducts is said to have countable `AB4Star` provided that
countable products are exact.
-/
/-
**CategoryTheory.CountableAB4Star** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheory
.Limits.HasCountableProducts C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` which has countable coproducts is said to have countable `AB4Star
` provided that
countable products are exact.
-/
class CountableAB4Star [HasCountableProducts C] where
  ofShape (α : Type) [Countable α] : HasExactLimitsOfShape (Discrete α) C
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [HasProducts.{0} C] [AB4StarOfSize.{0} C] : CountableAB4Star C :=
  ⟨inferInstance⟩

attribute [instance] CountableAB4.ofShape CountableAB4Star.ofShape

/--
A category `C` which has filtered colimits of a given size is said to have `AB5` of that size
provided that these filtered colimits are exact.

`AB5OfSize.{w, w'} C` means that `C` has exact colimits of shape `J : Type w'` with
`Category.{w} J` such that `J` is filtered.
-/
@[pp_with_univ]
/-
**CategoryTheory.AB5OfSize** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheo
ry.Limits.HasFilteredColimitsOfSize.{w, w', v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` which has filtered colimits of a given size is said to have `AB5`
 of that size
provided that these filtered colimits are exact.

`AB5OfSize.{w, w'} C` means that `C` has exact colimits of shape `J : Type w'` w
ith
`Category.{w} J` such that `J` is filtered.
-/
class AB5OfSize [HasFilteredColimitsOfSize.{w, w'} C] where
  ofShape (J : Type w') [Category.{w} J] [IsFiltered J] : HasExactColimitsOfShape J C

attribute [instance] AB5OfSize.ofShape

/--
A category `C` which has filtered colimits is said to have `AB5` provided that
filtered colimits are exact.
-/
@[stacks 079B]
/-
**CategoryTheory.AB5** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：AB5 [HasFilteredColimits C]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` which has filtered colimits is said to have `AB5` provided that
filtered colimits are exact.
-/
abbrev AB5 [HasFilteredColimits C] := AB5OfSize.{v, v} C
/-
**CategoryTheory.AB5OfSize_of_univLE** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：AB5OfSize_of_univLE [HasFilteredColimitsOfSize.{w₂, w₂'} C] [UnivLE.{w, w₂
}] [UnivLE.{w', w₂'}] [AB5OfSize.{w₂, w₂'} C] : haveI : HasFilteredColimitsOfSiz
e.{w, w'} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.hasFilteredColimitsOfSize_of_univLE`：hasFilteredCo
limitsOfSize_of_univLE [UnivLE.{w, w₂}] [UnivLE.{w', w₂'}] [HasFilteredColimitsO
fSize.{w₂', w₂} C] : HasFilteredColimitsOfSize.…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.IsFiltered.of_equivalence`：of_equivalence (h : C ≌ D) : I
sFiltered D
· 使用定理 `CategoryTheory.HasExactColimitsOfShape.of_domain_equivalence`：∀ (C : Typ
e u) [inst : CategoryTheory.Category.{v, u} C] {J : Type u_1} {J' : Type u_2}   
[inst_1 : CategoryTheory.Category.{v_1, u_1} J] [i…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.Has
FilteredColimitsOfSize.{w', w, v, u} C] (I : Type w)   …
· 使用定理 `CategoryTheory.AB5OfSize.ofShape`：∀ {C : Type u} {inst : CategoryTheory.
Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasFilteredColimitsOfSize.{
w, w', v, u} C}   [sel…
-/
lemma AB5OfSize_of_univLE [HasFilteredColimitsOfSize.{w₂, w₂'} C] [UnivLE.{w, w₂}]
    [UnivLE.{w', w₂'}] [AB5OfSize.{w₂, w₂'} C] :
    haveI : HasFilteredColimitsOfSize.{w, w'} C := hasFilteredColimitsOfSize_of_univLE.{w}
    AB5OfSize.{w, w'} C := by
  have : HasFilteredColimitsOfSize.{w, w'} C := hasFilteredColimitsOfSize_of_univLE.{w}
  constructor
  intro J _ _
  have := IsFiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J))
  exact HasExactColimitsOfShape.of_domain_equivalence _ ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J)).symm
/-
**CategoryTheory.AB5OfSize_shrink** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：AB5OfSize_shrink [HasFilteredColimitsOfSize.{max w w₂, max w' w₂'} C] [AB5
OfSize.{max w w₂, max w' w₂'} C] : haveI : HasFilteredColimitsOfSize.{w, w'} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.AB5OfSize_of_univLE`：AB5OfSize_of_univLE [HasFilteredColi
mitsOfSize.{w₂, w₂'} C] [UnivLE.{w, w₂}] [UnivLE.{w', w₂'}] [AB5OfSize.{w₂, w₂'}
 C] : haveI : HasFiltere…
-/
lemma AB5OfSize_shrink [HasFilteredColimitsOfSize.{max w w₂, max w' w₂'} C]
    [AB5OfSize.{max w w₂, max w' w₂'} C] :
    haveI : HasFilteredColimitsOfSize.{w, w'} C := hasFilteredColimitsOfSize_shrink
    AB5OfSize.{w, w'} C :=
  AB5OfSize_of_univLE C

/--
A category `C` which has cofiltered limits is said to have `AB5Star` (in literature `AB5*`)
provided that cofiltered limits are exact.
-/
@[pp_with_univ, stacks 079B]
/-
**CategoryTheory.AB5StarOfSize** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheo
ry.Limits.HasCofilteredLimitsOfSize.{w, w', v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` which has cofiltered limits is said to have `AB5Star` (in literat
ure `AB5*`)
provided that cofiltered limits are exact.
-/
class AB5StarOfSize [HasCofilteredLimitsOfSize.{w, w'} C] where
  ofShape (J : Type w') [Category.{w} J] [IsCofiltered J] : HasExactLimitsOfShape J C

attribute [instance] AB5StarOfSize.ofShape

/--
A category `C` which has cofiltered limits is said to have `AB5Star` (in literature `AB5*`)
provided that cofiltered limits are exact.
-/
/-
**CategoryTheory.AB5Star** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：AB5Star [HasCofilteredLimits C]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` which has cofiltered limits is said to have `AB5Star` (in literat
ure `AB5*`)
provided that cofiltered limits are exact.
-/
abbrev AB5Star [HasCofilteredLimits C] := AB5StarOfSize.{v, v} C
/-
**CategoryTheory.AB5StarOfSize_of_univLE** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：AB5StarOfSize_of_univLE [HasCofilteredLimitsOfSize.{w₂, w₂'} C] [UnivLE.{w
, w₂}] [UnivLE.{w', w₂'}] [AB5StarOfSize.{w₂, w₂'} C] : haveI : HasCofilteredLim
itsOfSize.{w, w'} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.hasCofilteredLimitsOfSize_of_univLE`：hasCofiltered
LimitsOfSize_of_univLE [UnivLE.{w, w₂}] [UnivLE.{w', w₂'}] [HasCofilteredLimitsO
fSize.{w₂', w₂} C] : HasCofilteredLimitsOfSize.…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.IsCofiltered.of_equivalence`：of_equivalence (h : C ≌ D) :
 IsCofiltered D
· 使用定理 `CategoryTheory.HasExactLimitsOfShape.of_domain_equivalence`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] {J : Type u_1} {J' : Type u_2}   [i
nst_1 : CategoryTheory.Category.{v_1, u_1} J] [i…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_has_cofiltered_limits`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.HasCo
filteredLimitsOfSize.{w', w, v, u} C] (I : Type w)   …
· 使用定理 `CategoryTheory.AB5StarOfSize.ofShape`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasCofilteredLimitsOfSi
ze.{w, w', v, u} C}   [sel…
-/
lemma AB5StarOfSize_of_univLE [HasCofilteredLimitsOfSize.{w₂, w₂'} C] [UnivLE.{w, w₂}]
    [UnivLE.{w', w₂'}] [AB5StarOfSize.{w₂, w₂'} C] :
    haveI : HasCofilteredLimitsOfSize.{w, w'} C := hasCofilteredLimitsOfSize_of_univLE.{w}
    AB5StarOfSize.{w, w'} C := by
  have : HasCofilteredLimitsOfSize.{w, w'} C := hasCofilteredLimitsOfSize_of_univLE.{w}
  constructor
  intro J _ _
  have := IsCofiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J))
  exact HasExactLimitsOfShape.of_domain_equivalence _ ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J)).symm
/-
**CategoryTheory.AB5StarOfSize_shrink** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`
。
形式化陈述：AB5StarOfSize_shrink [HasCofilteredLimitsOfSize.{max w w₂, max w' w₂'} C] 
[AB5StarOfSize.{max w w₂, max w' w₂'} C] : haveI : HasCofilteredLimitsOfSize.{w,
 w'} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.AB5StarOfSize_of_univLE`：AB5StarOfSize_of_univLE [HasCofi
lteredLimitsOfSize.{w₂, w₂'} C] [UnivLE.{w, w₂}] [UnivLE.{w', w₂'}] [AB5StarOfSi
ze.{w₂, w₂'} C] : haveI : Ha…
-/
lemma AB5StarOfSize_shrink [HasCofilteredLimitsOfSize.{max w w₂, max w' w₂'} C]
    [AB5StarOfSize.{max w w₂, max w' w₂'} C] :
    haveI : HasCofilteredLimitsOfSize.{w, w'} C := hasCofilteredLimitsOfSize_shrink
    AB5StarOfSize.{w, w'} C :=
  AB5StarOfSize_of_univLE C

/-- `HasExactColimitsOfShape` can be "pushed forward" along final functors -/
/-
**CategoryTheory.hasExactColimitsOfShape_of_final** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：hasExactColimitsOfShape_of_final [HasFiniteLimits C] {J J' : Type*} [Categ
ory* J] [Category* J'] (F : J ⥤ J') [F.Final] [HasColimitsOfShape J' C] [HasColi
mitsOfShape J C] [HasExactColimitsOfShape J C] : HasExactColimitsOfShape J' C wh
ere preservesFiniteLimits
参数：F : J ⥤ J'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_of_natIso`：preservesFiniteLi
mits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteLimits F] : PreservesFi
niteLimits G where preservesFiniteLimits _ …
· 使用引理 `CategoryTheory.Limits.comp_preservesFiniteLimits`：comp_preservesFiniteLi
mits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteLimits F] [PreservesFiniteLimits G]
 : PreservesFiniteLimits (F ⋙ G)
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `CategoryTheory.HasExactColimitsOfShape.preservesFiniteLimits`：∀ {J : Typ
e u'} {inst : CategoryTheory.Category.{v', u'} J} {C : Type u} {inst_1 : Categor
yTheory.Category.{v, u} C}   {inst_2 : CategoryThe…

--- 原说明 ---
`HasExactColimitsOfShape` can be "pushed forward" along final functors
-/
lemma hasExactColimitsOfShape_of_final [HasFiniteLimits C]
    {J J' : Type*} [Category* J] [Category* J']
    (F : J ⥤ J') [F.Final] [HasColimitsOfShape J' C] [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C] : HasExactColimitsOfShape J' C where
  preservesFiniteLimits :=
    letI : PreservesFiniteLimits ((whiskeringLeft J J' C).obj F) := ⟨fun _ ↦ inferInstance⟩
    letI := comp_preservesFiniteLimits ((whiskeringLeft J J' C).obj F) colim
    preservesFiniteLimits_of_natIso (Functor.Final.colimIso F)

/-- `HasExactLimitsOfShape` can be "pushed forward" along initial functors -/
/-
**CategoryTheory.hasExactLimitsOfShape_of_initial** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：hasExactLimitsOfShape_of_initial [HasFiniteColimits C] {J J' : Type*} [Cat
egory* J] [Category* J'] (F : J ⥤ J') [F.Initial] [HasLimitsOfShape J' C] [HasLi
mitsOfShape J C] [HasExactLimitsOfShape J C] : HasExactLimitsOfShape J' C where 
preservesFiniteColimits
参数：F : J ⥤ J'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesFiniteColimits_of_natIso`：preservesFinite
Colimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteColimits F] : Prese
rvesFiniteColimits G where preservesFiniteCol…
· 使用引理 `CategoryTheory.Limits.comp_preservesFiniteColimits`：comp_preservesFinite
Colimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteColimits F] [PreservesFiniteCol
imits G] : PreservesFiniteColimits (F ⋙ …
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.HasExactLimitsOfShape.preservesFiniteColimits`：∀ {J : Typ
e u'} {inst : CategoryTheory.Category.{v', u'} J} {C : Type u} {inst_1 : Categor
yTheory.Category.{v, u} C}   {inst_2 : CategoryThe…

--- 原说明 ---
`HasExactLimitsOfShape` can be "pushed forward" along initial functors
-/
lemma hasExactLimitsOfShape_of_initial [HasFiniteColimits C] {J J' : Type*} [Category* J]
    [Category* J'] (F : J ⥤ J') [F.Initial] [HasLimitsOfShape J' C] [HasLimitsOfShape J C]
    [HasExactLimitsOfShape J C] : HasExactLimitsOfShape J' C where
  preservesFiniteColimits :=
    letI : PreservesFiniteColimits ((whiskeringLeft J J' C).obj F) := ⟨fun _ ↦ inferInstance⟩
    letI := comp_preservesFiniteColimits ((whiskeringLeft J J' C).obj F) lim
    preservesFiniteColimits_of_natIso (Functor.Initial.limIso F)

section AB4OfAB5

variable {α : Type w} [HasZeroMorphisms C] [HasFiniteBiproducts C] [HasFiniteLimits C]

open CoproductsFromFiniteFiltered

/-
**CategoryTheory.preservesFiniteLimits_liftToFinset** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory`。
形式化陈述：preservesFiniteLimits_liftToFinset : PreservesFiniteLimits (liftToFinset C
 α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.preservesFiniteLimits_of_evaluation`：preservesFiniteLimit
s_of_evaluation {D : Type*} [Category* D] {E : Type*} [Category* E] (F : C ⥤ D ⥤
 E) (h : forall d : D, PreservesFiniteLi…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteBiproducts`：∀ (C :
 Type uC) [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C]   [CategoryTheory.Limits.Ha…
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_of_natIso`：preservesFiniteLi
mits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteLimits F] : PreservesFi
niteLimits G where preservesFiniteLimits _ …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `CategoryTheory.Limits.comp_preservesFiniteLimits`：comp_preservesFiniteLi
mits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteLimits F] [PreservesFiniteLimits G]
 : PreservesFiniteLimits (F ⋙ G)
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `CategoryTheory.Limits.hasProductsOfShape_of_hasBiproductsOfShape`：∀ {J :
 Type w} (C : Type uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : 
CategoryTheory.Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `CategoryTheory.Limits.hasCoproductsOfShape_of_hasBiproductsOfShape`：∀ {J
 : Type w} (C : Type uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 
: CategoryTheory.Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
instance preservesFiniteLimits_liftToFinset : PreservesFiniteLimits (liftToFinset C α) :=
  preservesFiniteLimits_of_evaluation _ fun I =>
    letI : PreservesFiniteLimits (colim (J := Discrete I) (C := C)) :=
      preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm
    letI : PreservesFiniteLimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor fun x ↦ ↑x)) :=
      ⟨fun J _ _ => whiskeringLeft_preservesLimitsOfShape J _⟩
    letI : PreservesFiniteLimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor (·.val)) ⋙ colim) :=
      comp_preservesFiniteLimits _ _
    preservesFiniteLimits_of_natIso (liftToFinsetEvaluationIso I).symm

variable (J : Type*)

/--
`HasExactColimitsOfShape (Finset (Discrete J)) C` implies `HasExactColimitsOfShape (Discrete J) C`
-/
/-
**CategoryTheory.hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_fin
set_discrete** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discret
e [HasColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Finset (Discrete J)) 
C] [HasExactColimitsOfShape (Finset (Discrete J)) C] : HasExactColimitsOfShape (
Discrete J) C where preservesFiniteLimits
参数：Discrete J；Finset (Discrete J)；Finset (Discrete J)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_of_natIso`：preservesFiniteLi
mits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteLimits F] : PreservesFi
niteLimits G where preservesFiniteLimits _ …
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteBiproducts`：∀ (C :
 Type uC) [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C]   [CategoryTheory.Limits.Ha…
· 使用引理 `CategoryTheory.Limits.comp_preservesFiniteLimits`：comp_preservesFiniteLi
mits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteLimits F] [PreservesFiniteLimits G]
 : PreservesFiniteLimits (F ⋙ G)
· 使用定理 `CategoryTheory.HasExactColimitsOfShape.preservesFiniteLimits`：∀ {J : Typ
e u'} {inst : CategoryTheory.Category.{v', u'} J} {C : Type u} {inst_1 : Categor
yTheory.Category.{v, u} C}   {inst_2 : CategoryThe…

--- 原说明 ---
`HasExactColimitsOfShape (Finset (Discrete J)) C` implies `HasExactColimitsOfSha
pe (Discrete J) C`
-/
lemma hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete
    [HasColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Finset (Discrete J)) C]
    [HasExactColimitsOfShape (Finset (Discrete J)) C] : HasExactColimitsOfShape (Discrete J) C where
  preservesFiniteLimits :=
    letI : PreservesFiniteLimits (liftToFinset C J ⋙ colim) :=
      comp_preservesFiniteLimits _ _
    preservesFiniteLimits_of_natIso (liftToFinsetColimIso)

attribute [local instance] hasCoproducts_of_finite_and_filtered in
/-- A category with finite biproducts and finite limits is AB4 if it is AB5. -/
/-
**CategoryTheory.AB4.of_AB5** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.AB4`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   [inst_2 : CategoryTheory.Limits.HasFiniteBi
products C] [CategoryTheory.Limits.HasFiniteLimits C]   [inst_4 : CategoryTheory
.Limits.HasFilteredColimitsOfSize.{w, w, v, u} C] [CategoryTheory.AB5OfSize.{w, 
w, v, u} C],   CategoryTheory.AB4OfSize.{w, v, u} C
参数：C : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasCoproducts_of_finite_and_filtered`：hasCoproduct
s_of_finite_and_filtered [HasFiniteCoproducts C] [HasFilteredColimitsOfSize.{w, 
w} C] : HasCoproducts.{w} C
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteBiproducts`：∀ (C :
 Type uC) [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C]   [CategoryTheory.Limits.Ha…
· 使用引理 `CategoryTheory.hasExactColimitsOfShape_discrete_of_hasExactColimitsOfSha
pe_finset_discrete`：hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_
finset_discrete [HasColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Finset 
…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.Has
FilteredColimitsOfSize.{w', w, v, u} C] (I : Type w)   …
· 使用定理 `CategoryTheory.isFiltered_of_directed_le_nonempty`：∀ (α : Type u) [inst 
: Preorder α] [IsDirectedOrder α] [Nonempty α], CategoryTheory.IsFiltered α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CategoryTheory.AB5OfSize.ofShape`：∀ {C : Type u} {inst : CategoryTheory.
Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasFilteredColimitsOfSize.{
w, w', v, u} C}   [sel…

--- 原说明 ---
A category with finite biproducts and finite limits is AB4 if it is AB5.
-/
lemma AB4.of_AB5 [HasFilteredColimitsOfSize.{w, w} C]
    [AB5OfSize.{w, w} C] : AB4OfSize.{w} C where
  ofShape _ := hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete _ _

/--
A category with finite biproducts and finite limits has countable AB4 if sequential colimits are
exact.
-/
/-
**CategoryTheory.CountableAB4.of_countableAB5** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.CountableAB4`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   [CategoryTheory.Limits.HasFiniteBiproducts 
C] [CategoryTheory.Limits.HasFiniteLimits C]   [inst_4 : CategoryTheory.Limits.H
asColimitsOfShape ℕ C] [CategoryTheory.HasExactColimitsOfShape ℕ C]   [inst_6 : 
CategoryTheory.Limits.HasCountableCoproducts C], CategoryTheory.CountableAB4 C
参数：C : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Final.hasColimitsOfShape_of_final`：hasColimitsOfS
hape_of_final [HasColimitsOfShape C E] : HasColimitsOfShape D E where has_colimi
t
· 使用定理 `Finset.countable`：∀ {α : Type u_1} [Countable α], Countable (Finset α)
· 使用定理 `CategoryTheory.isFiltered_of_directed_le_nonempty`：∀ (α : Type u) [inst 
: Preorder α] [IsDirectedOrder α] [Nonempty α], CategoryTheory.IsFiltered α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `CategoryTheory.hasExactColimitsOfShape_of_final`：hasExactColimitsOfShape
_of_final [HasFiniteLimits C] {J J' : Type*} [Category* J] [Category* J'] (F : J
 ⥤ J') [F.Final] [HasColimitsOfShape …
· 使用引理 `CategoryTheory.hasExactColimitsOfShape_discrete_of_hasExactColimitsOfSha
pe_finset_discrete`：hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_
finset_discrete [HasColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Finset 
…
· 使用定理 `CategoryTheory.Limits.instHasCoproductsOfShapeOfHasCountableCoproductsOf
Countable`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [Categ
oryTheory.Limits.HasCountableCoproducts C]   (J : Type u_3) [Countable …

--- 原说明 ---
A category with finite biproducts and finite limits has countable AB4 if sequent
ial colimits are
exact.
-/
lemma CountableAB4.of_countableAB5 [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [HasCountableCoproducts C] : CountableAB4 C where
  ofShape J :=
    have : HasColimitsOfShape (Finset (Discrete J)) C :=
      Functor.Final.hasColimitsOfShape_of_final
        (IsFiltered.sequentialFunctor (Finset (Discrete J)))
    have := hasExactColimitsOfShape_of_final C (IsFiltered.sequentialFunctor (Finset (Discrete J)))
    hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete _ _

end AB4OfAB5

section AB4StarOfAB5Star

variable {α : Type w} [HasZeroMorphisms C] [HasFiniteBiproducts C] [HasFiniteColimits C]

open ProductsFromFiniteCofiltered

/-
**CategoryTheory.preservesFiniteColimits_liftToFinset** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory`。
形式化陈述：preservesFiniteColimits_liftToFinset : PreservesFiniteColimits (liftToFins
et C α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.preservesFiniteColimits_of_evaluation`：preservesFiniteCol
imits_of_evaluation {D : Type*} [Category* D] {E : Type*} [Category* E] (F : C ⥤
 D ⥤ E) (h : forall d : D, PreservesFinite…
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteBiproducts`：∀ (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C]   [CategoryTheory.Limits.Ha…
· 使用引理 `CategoryTheory.Limits.preservesFiniteColimits_of_natIso`：preservesFinite
Colimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteColimits F] : Prese
rvesFiniteColimits G where preservesFiniteCol…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `CategoryTheory.Limits.comp_preservesFiniteColimits`：comp_preservesFinite
Colimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteColimits F] [PreservesFiniteCol
imits G] : PreservesFiniteColimits (F ⋙ …
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.hasCoproductsOfShape_of_hasBiproductsOfShape`：∀ {J
 : Type w} (C : Type uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 
: CategoryTheory.Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
instance preservesFiniteColimits_liftToFinset : PreservesFiniteColimits (liftToFinset C α) :=
  preservesFiniteColimits_of_evaluation _ fun ⟨I⟩ =>
    letI : PreservesFiniteColimits (lim (J := Discrete I) (C := C)) :=
      preservesFiniteColimits_of_natIso HasBiproductsOfShape.colimIsoLim
    letI : PreservesFiniteColimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor fun x ↦ ↑x)) := ⟨fun _ _ _ => inferInstance⟩
    letI : PreservesFiniteColimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor (·.val)) ⋙ lim) :=
      comp_preservesFiniteColimits _ _
    preservesFiniteColimits_of_natIso (liftToFinsetEvaluationIso _ _ I).symm

variable (J : Type*)

/--
`HasExactLimitsOfShape (Finset (Discrete J))ᵒᵖ C` implies  `HasExactLimitsOfShape (Discrete J) C`
-/
/-
**CategoryTheory.hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_
discrete_op** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op
 [HasLimitsOfShape (Discrete J) C] [HasLimitsOfShape (Finset (Discrete J))ᵒᵖ C] 
[HasExactLimitsOfShape (Finset (Discrete J))ᵒᵖ C] : HasExactLimitsOfShape (Discr
ete J) C where preservesFiniteColimits
参数：Discrete J；Finset (Discrete J)；Finset (Discrete J)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesFiniteColimits_of_natIso`：preservesFinite
Colimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteColimits F] : Prese
rvesFiniteColimits G where preservesFiniteCol…
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteBiproducts`：∀ (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C]   [CategoryTheory.Limits.Ha…
· 使用引理 `CategoryTheory.Limits.comp_preservesFiniteColimits`：comp_preservesFinite
Colimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteColimits F] [PreservesFiniteCol
imits G] : PreservesFiniteColimits (F ⋙ …
· 使用定理 `CategoryTheory.HasExactLimitsOfShape.preservesFiniteColimits`：∀ {J : Typ
e u'} {inst : CategoryTheory.Category.{v', u'} J} {C : Type u} {inst_1 : Categor
yTheory.Category.{v, u} C}   {inst_2 : CategoryThe…

--- 原说明 ---
`HasExactLimitsOfShape (Finset (Discrete J))ᵒᵖ C` implies  `HasExactLimitsOfShap
e (Discrete J) C`
-/
lemma hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op
    [HasLimitsOfShape (Discrete J) C] [HasLimitsOfShape (Finset (Discrete J))ᵒᵖ C]
    [HasExactLimitsOfShape (Finset (Discrete J))ᵒᵖ C] :
    HasExactLimitsOfShape (Discrete J) C where
  preservesFiniteColimits :=
    letI : PreservesFiniteColimits (ProductsFromFiniteCofiltered.liftToFinset C J ⋙ lim) :=
      comp_preservesFiniteColimits _ _
    preservesFiniteColimits_of_natIso (ProductsFromFiniteCofiltered.liftToFinsetLimIso _ _)

attribute [local instance] hasProducts_of_finite_and_cofiltered in
/-- A category with finite biproducts and finite limits is AB4 if it is AB5. -/
/-
**CategoryTheory.AB4Star.of_AB5Star** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.AB
4Star`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   [inst_2 : CategoryTheory.Limits.HasFiniteBi
products C] [CategoryTheory.Limits.HasFiniteColimits C]   [inst_4 : CategoryTheo
ry.Limits.HasCofilteredLimitsOfSize.{w, w, v, u} C]   [CategoryTheory.AB5StarOfS
ize.{w, w, v, u} C], CategoryTheory.AB4StarOfSize.{w, v, u} C
参数：C : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasProducts_of_finite_and_cofiltered`：hasProducts_
of_finite_and_cofiltered [HasFiniteProducts C] [HasCofilteredLimitsOfSize.{w, w}
 C] : HasProducts.{w} C
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteBiproducts`：∀ (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C]   [CategoryTheory.Limits.Ha…
· 使用引理 `CategoryTheory.hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_f
inset_discrete_op`：hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finse
t_discrete_op [HasLimitsOfShape (Discrete J) C] [HasLimitsOfShape (Finset (Disc…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_has_cofiltered_limits`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.HasCo
filteredLimitsOfSize.{w', w, v, u} C] (I : Type w)   …
· 使用定理 `CategoryTheory.isFiltered_of_directed_le_nonempty`：∀ (α : Type u) [inst 
: Preorder α] [IsDirectedOrder α] [Nonempty α], CategoryTheory.IsFiltered α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CategoryTheory.AB5StarOfSize.ofShape`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasCofilteredLimitsOfSi
ze.{w, w', v, u} C}   [sel…

--- 原说明 ---
A category with finite biproducts and finite limits is AB4 if it is AB5.
-/
lemma AB4Star.of_AB5Star [HasCofilteredLimitsOfSize.{w, w} C] [AB5StarOfSize.{w, w} C] :
    AB4StarOfSize.{w} C where
  ofShape _ := hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op _ _

/--
A category with finite biproducts and finite limits has countable AB4\* if sequential limits are
exact.
-/
/-
**CategoryTheory.CountableAB4Star.of_countableAB5Star** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.CountableAB4Star`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   [CategoryTheory.Limits.HasFiniteBiproducts 
C] [CategoryTheory.Limits.HasFiniteColimits C]   [inst_4 : CategoryTheory.Limits
.HasLimitsOfShape ℕᵒᵖ C] [CategoryTheory.HasExactLimitsOfShape ℕᵒᵖ C]   [inst_6 
: CategoryTheory.Limits.HasCountableProducts C], CategoryTheory.CountableAB4Star
 C
参数：C : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Initial.hasLimitsOfShape_of_initial`：hasLimitsOfS
hape_of_initial [HasLimitsOfShape C E] : HasLimitsOfShape D E where has_limit
· 使用定理 `Finset.countable`：∀ {α : Type u_1} [Countable α], Countable (Finset α)
· 使用定理 `CategoryTheory.isFiltered_of_directed_le_nonempty`：∀ (α : Type u) [inst 
: Preorder α] [IsDirectedOrder α] [Nonempty α], CategoryTheory.IsFiltered α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `CategoryTheory.hasExactLimitsOfShape_of_initial`：hasExactLimitsOfShape_o
f_initial [HasFiniteColimits C] {J J' : Type*} [Category* J] [Category* J'] (F :
 J ⥤ J') [F.Initial] [HasLimitsOfShap…
· 使用引理 `CategoryTheory.hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_f
inset_discrete_op`：hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finse
t_discrete_op [HasLimitsOfShape (Discrete J) C] [HasLimitsOfShape (Finset (Disc…
· 使用定理 `CategoryTheory.Limits.instHasProductsOfShapeOfHasCountableProductsOfCoun
table`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryT
heory.Limits.HasCountableProducts C]   (J : Type u_3) [Countable J]…

--- 原说明 ---
A category with finite biproducts and finite limits has countable AB4\* if seque
ntial limits are
exact.
-/
lemma CountableAB4Star.of_countableAB5Star [HasLimitsOfShape ℕᵒᵖ C] [HasExactLimitsOfShape ℕᵒᵖ C]
    [HasCountableProducts C] : CountableAB4Star C where
  ofShape J :=
    have : HasLimitsOfShape (Finset (Discrete J))ᵒᵖ C :=
      Functor.Initial.hasLimitsOfShape_of_initial
        (IsFiltered.sequentialFunctor (Finset (Discrete J))).op
    have := hasExactLimitsOfShape_of_initial C
      (IsFiltered.sequentialFunctor (Finset (Discrete J))).op
    hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op _ _

end AB4StarOfAB5Star

/--
Checking exactness of colimits of shape `Discrete ℕ` and `Discrete J` for finite `J` is enough for
countable AB4.
-/
/-
**CategoryTheory.CountableAB4.of_hasExactColimitsOfShape_nat_and_finite** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.CountableAB4`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasCountableCoproducts C]   [CategoryTheory.Limits.HasFiniteLimit
s C]   [∀ (J : Type) [inst_3 : Finite J], CategoryTheory.HasExactColimitsOfShape
 (CategoryTheory.Discrete J) C]   [CategoryTheory.HasExactColimitsOfShape (Categ
oryTheory.Discrete ℕ) C], CategoryTheory.CountableAB4 C
参数：C : Type u；J : Type；CategoryTheory.Discrete J；CategoryTheory.Discrete ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasCoproductsOfShapeOfHasCountableCoproductsOf
Countable`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [Categ
oryTheory.Limits.HasCountableCoproducts C]   (J : Type u_3) [Countable …
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instCountableNat`：Countable ℕ
· 使用引理 `CategoryTheory.hasExactColimitsOfShape_of_final`：hasExactColimitsOfShape
_of_final [HasFiniteLimits C] {J J' : Type*} [Category* J] [Category* J'] (F : J
 ⥤ J') [F.Final] [HasColimitsOfShape …
· 使用定理 `CategoryTheory.Functor.final_of_isRightAdjoint`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…

--- 原说明 ---
Checking exactness of colimits of shape `Discrete ℕ` and `Discrete J` for finite
 `J` is enough for
countable AB4.
-/
lemma CountableAB4.of_hasExactColimitsOfShape_nat_and_finite [HasCountableCoproducts C]
    [HasFiniteLimits C] [∀ (J : Type) [Finite J], HasExactColimitsOfShape (Discrete J) C]
    [HasExactColimitsOfShape (Discrete ℕ) C] :
    CountableAB4 C where
  ofShape J := by
    by_cases h : Finite J
    · infer_instance
    · have : Infinite J := ⟨h⟩
      let _ := Encodable.ofCountable J
      let _ := Denumerable.ofEncodableOfInfinite J
      exact hasExactColimitsOfShape_of_final C (Discrete.equivalence (Denumerable.eqv J)).inverse

/--
Checking exactness of limits of shape `Discrete ℕ` and `Discrete J` for finite `J` is enough for
countable AB4\*.
-/
/-
**CategoryTheory.CountableAB4Star.of_hasExactLimitsOfShape_nat_and_finite** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.CountableAB4Star`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasCountableProducts C]   [CategoryTheory.Limits.HasFiniteColimit
s C]   [∀ (J : Type) [inst_3 : Finite J], CategoryTheory.HasExactLimitsOfShape (
CategoryTheory.Discrete J) C]   [CategoryTheory.HasExactLimitsOfShape (CategoryT
heory.Discrete ℕ) C], CategoryTheory.CountableAB4Star C
参数：C : Type u；J : Type；CategoryTheory.Discrete J；CategoryTheory.Discrete ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasProductsOfShapeOfHasCountableProductsOfCoun
table`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryT
heory.Limits.HasCountableProducts C]   (J : Type u_3) [Countable J]…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instCountableNat`：Countable ℕ
· 使用引理 `CategoryTheory.hasExactLimitsOfShape_of_initial`：hasExactLimitsOfShape_o
f_initial [HasFiniteColimits C] {J J' : Type*} [Category* J] [Category* J'] (F :
 J ⥤ J') [F.Initial] [HasLimitsOfShap…
· 使用定理 `CategoryTheory.Functor.initial_of_isLeftAdjoint`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…

--- 原说明 ---
Checking exactness of limits of shape `Discrete ℕ` and `Discrete J` for finite `
J` is enough for
countable AB4\*.
-/
lemma CountableAB4Star.of_hasExactLimitsOfShape_nat_and_finite [HasCountableProducts C]
    [HasFiniteColimits C] [∀ (J : Type) [Finite J], HasExactLimitsOfShape (Discrete J) C]
    [HasExactLimitsOfShape (Discrete ℕ) C] :
    CountableAB4Star C where
  ofShape J := by
    by_cases h : Finite J
    · infer_instance
    · have : Infinite J := ⟨h⟩
      let _ := Encodable.ofCountable J
      let _ := Denumerable.ofEncodableOfInfinite J
      exact hasExactLimitsOfShape_of_initial C (Discrete.equivalence (Denumerable.eqv J)).inverse

section EpiMono


section

variable [HasZeroMorphisms C] [HasFiniteBiproducts C]

/-
**CategoryTheory.hasExactColimitsOfShape_discrete_finite** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory`。
形式化陈述：hasExactColimitsOfShape_discrete_finite (J : Type*) [Finite J] : HasExactC
olimitsOfShape (Discrete J) C where preservesFiniteLimits
参数：J : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteBiproducts`：∀ (C :
 Type uC) [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C]   [CategoryTheory.Limits.Ha…
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_of_natIso`：preservesFiniteLi
mits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteLimits F] : PreservesFi
niteLimits G where preservesFiniteLimits _ …
· 使用定理 `CategoryTheory.Limits.hasProductsOfShape_of_hasBiproductsOfShape`：∀ {J :
 Type w} (C : Type uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : 
CategoryTheory.Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `CategoryTheory.Limits.hasCoproductsOfShape_of_hasBiproductsOfShape`：∀ {J
 : Type w} (C : Type uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 
: CategoryTheory.Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
noncomputable instance hasExactColimitsOfShape_discrete_finite (J : Type*) [Finite J] :
    HasExactColimitsOfShape (Discrete J) C where
  preservesFiniteLimits := preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm
/-
**CategoryTheory.hasExactLimitsOfShape_discrete_finite** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory`。
形式化陈述：hasExactLimitsOfShape_discrete_finite {J : Type*} [Finite J] : HasExactLim
itsOfShape (Discrete J) C where preservesFiniteColimits
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteBiproducts`：∀ (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C]   [CategoryTheory.Limits.Ha…
· 使用引理 `CategoryTheory.Limits.preservesFiniteColimits_of_natIso`：preservesFinite
Colimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteColimits F] : Prese
rvesFiniteColimits G where preservesFiniteCol…
· 使用定理 `CategoryTheory.Limits.hasCoproductsOfShape_of_hasBiproductsOfShape`：∀ {J
 : Type w} (C : Type uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 
: CategoryTheory.Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
noncomputable instance hasExactLimitsOfShape_discrete_finite {J : Type*} [Finite J] :
    HasExactLimitsOfShape (Discrete J) C where
  preservesFiniteColimits := preservesFiniteColimits_of_natIso HasBiproductsOfShape.colimIsoLim

/--
Checking exact colimits of shape `Discrete ℕ` is enough for countable AB4, provided that the
category has finite biproducts and finite limits.
-/
/-
**CategoryTheory.CountableAB4.of_hasExactColimitsOfShape_nat** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.CountableAB4`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   [CategoryTheory.Limits.HasFiniteBiproducts 
C] [CategoryTheory.Limits.HasFiniteLimits C]   [inst_4 : CategoryTheory.Limits.H
asCountableCoproducts C]   [CategoryTheory.HasExactColimitsOfShape (CategoryTheo
ry.Discrete ℕ) C], CategoryTheory.CountableAB4 C
参数：C : Type u；CategoryTheory.Discrete ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasCoproductsOfShapeOfHasCountableCoproductsOf
Countable`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [Categ
oryTheory.Limits.HasCountableCoproducts C]   (J : Type u_3) [Countable …
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `CategoryTheory.CountableAB4.of_hasExactColimitsOfShape_nat_and_finite`：∀
 (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.Limits.HasCountableCoproducts C]   [CategoryTheory.Limits.…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α

--- 原说明 ---
Checking exact colimits of shape `Discrete ℕ` is enough for countable AB4, provi
ded that the
category has finite biproducts and finite limits.
-/
lemma CountableAB4.of_hasExactColimitsOfShape_nat [HasFiniteLimits C] [HasCountableCoproducts C]
    [HasExactColimitsOfShape (Discrete ℕ) C] : CountableAB4 C := by
  apply +allowSynthFailures CountableAB4.of_hasExactColimitsOfShape_nat_and_finite
  exact fun _ ↦ inferInstance

/--
Checking exact limits of shape `Discrete ℕ` is enough for countable AB4\*, provided that the
category has finite biproducts and finite colimits.
-/
/-
**CategoryTheory.CountableAB4Star.of_hasExactLimitsOfShape_nat** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.CountableAB4Star`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   [CategoryTheory.Limits.HasFiniteBiproducts 
C] [CategoryTheory.Limits.HasFiniteColimits C]   [inst_4 : CategoryTheory.Limits
.HasCountableProducts C]   [CategoryTheory.HasExactLimitsOfShape (CategoryTheory
.Discrete ℕ) C], CategoryTheory.CountableAB4Star C
参数：C : Type u；CategoryTheory.Discrete ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasProductsOfShapeOfHasCountableProductsOfCoun
table`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryT
heory.Limits.HasCountableProducts C]   (J : Type u_3) [Countable J]…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `CategoryTheory.CountableAB4Star.of_hasExactLimitsOfShape_nat_and_finite`
：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheo
ry.Limits.HasCountableProducts C]   [CategoryTheory.Limits.Ha…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α

--- 原说明 ---
Checking exact limits of shape `Discrete ℕ` is enough for countable AB4\*, provi
ded that the
category has finite biproducts and finite colimits.
-/
lemma CountableAB4Star.of_hasExactLimitsOfShape_nat [HasFiniteColimits C]
    [HasCountableProducts C] [HasExactLimitsOfShape (Discrete ℕ) C] : CountableAB4Star C := by
  apply +allowSynthFailures CountableAB4Star.of_hasExactLimitsOfShape_nat_and_finite
  exact fun _ ↦ inferInstance

end

variable [Abelian C] (J : Type u') [Category.{v'} J]

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts
  preservesBinaryBiproducts_of_preservesBinaryProducts

/--
If `colim` of shape `J` into an abelian category `C` preserves monomorphisms, then `C` has exact
colimits of shape `J`.
-/
/-
**CategoryTheory.hasExactColimitsOfShape_of_preservesMono** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory`。
形式化陈述：hasExactColimitsOfShape_of_preservesMono [HasColimitsOfShape J C] [Preserv
esMonomorphisms (colim (J
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.preservesFiniteLimits_of_preservesHomology`：prese
rvesFiniteLimits_of_preservesHomology [HasFiniteProducts C] [HasKernels C] : Pre
servesFiniteLimits F
· 使用定理 `CategoryTheory.Functor.additive_of_preservesBinaryBiproducts`：additive_o
f_preservesBinaryBiproducts [HasBinaryBiproducts C] [PreservesZeroMorphisms F] [
PreservesBinaryBiproducts F] : Additive F where ma…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_initial_objec
t`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [in
st_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Limits.instIsLeftAdjointFunctorColim`：∀ {J : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.C
ategory.{v, u} C]   [inst_2 : CategoryThe…
· 使用引理 `CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoprod
ucts`：preservesBinaryBiproducts_of_preservesBinaryCoproducts [PreservesColimitsO
fShape (Discrete WalkingPair) F] : PreservesBinaryBiproducts F whe…
· 使用引理 `CategoryTheory.Functor.preservesHomology_of_preservesMonos_and_cokernels
`：preservesHomology_of_preservesMonos_and_cokernels [PreservesZeroMorphisms L] [
PreservesMonomorphisms L] [forall {X Y} (f : X ⟶ Y), Preserves…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.instHasFiniteProductsFunctor`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] {K : Type u_2}   [inst_1 : CategoryTh
eory.Category.{v_2, u_2} K] [CategoryThe…
· 使用定理 `CategoryTheory.Abelian.has_finite_products`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory
.Limits.HasFiniteProducts C
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C

--- 原说明 ---
If `colim` of shape `J` into an abelian category `C` preserves monomorphisms, th
en `C` has exact
colimits of shape `J`.
-/
lemma hasExactColimitsOfShape_of_preservesMono [HasColimitsOfShape J C]
    [PreservesMonomorphisms (colim (J := J) (C := C))] : HasExactColimitsOfShape J C where
  preservesFiniteLimits := by
    apply +allowSynthFailures preservesFiniteLimits_of_preservesHomology
    · exact preservesHomology_of_preservesMonos_and_cokernels _
    · exact additive_of_preservesBinaryBiproducts _

/--
If `lim` of shape `J` into an abelian category `C` preserves epimorphisms, then `C` has exact
limits of shape `J`.
-/
/-
**CategoryTheory.hasExactLimitsOfShape_of_preservesEpi** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory`。
形式化陈述：hasExactLimitsOfShape_of_preservesEpi [HasLimitsOfShape J C] [PreservesEpi
morphisms (lim (J
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology`：pre
servesFiniteColimits_of_preservesHomology [HasFiniteCoproducts C] [HasCokernels 
C] : PreservesFiniteColimits F
· 使用定理 `CategoryTheory.Functor.additive_of_preservesBinaryBiproducts`：additive_o
f_preservesBinaryBiproducts [HasBinaryBiproducts C] [PreservesZeroMorphisms F] [
PreservesBinaryBiproducts F] : Additive F where ma…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_terminal_obje
ct`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [i
nst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Limits.instIsRightAdjointFunctorLim`：∀ {J : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Ca
tegory.{v, u} C]   [inst_2 : CategoryThe…
· 使用引理 `CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProduc
ts`：preservesBinaryBiproducts_of_preservesBinaryProducts [PreservesLimitsOfShape
 (Discrete WalkingPair) F] : PreservesBinaryBiproducts F where p…
· 使用引理 `CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels`：p
reservesHomology_of_preservesEpis_and_kernels [PreservesZeroMorphisms L] [Preser
vesEpimorphisms L] [forall {X Y} (f : X ⟶ Y), PreservesLimi…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.instHasFiniteCoproductsFunctor`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] {K : Type u_2}   [inst_1 : Category
Theory.Category.{v_2, u_2} K] [CategoryThe…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `CategoryTheory.Abelian.hasFiniteColimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.H
asFiniteColimits C
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C

--- 原说明 ---
If `lim` of shape `J` into an abelian category `C` preserves epimorphisms, then 
`C` has exact
limits of shape `J`.
-/
lemma hasExactLimitsOfShape_of_preservesEpi [HasLimitsOfShape J C]
    [PreservesEpimorphisms (lim (J := J) (C := C))] : HasExactLimitsOfShape J C where
  preservesFiniteColimits := by
    apply +allowSynthFailures preservesFiniteColimits_of_preservesHomology
    · exact preservesHomology_of_preservesEpis_and_kernels _
    · exact additive_of_preservesBinaryBiproducts _

end EpiMono

end CategoryTheory

