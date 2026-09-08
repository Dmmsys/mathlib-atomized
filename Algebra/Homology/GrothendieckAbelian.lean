/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Generator.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Homological complexes in a Grothendieck abelian category

Let `c : ComplexShape ι` be a complex shape with no loop, and
such that `Small.{w} ι`. Then, if `C` is a Grothendieck abelian
category (with `IsGrothendieckAbelian.{w} C`), the category
`HomologicalComplex C c` is Grothendieck abelian.

-/

public section

universe w w' t v u

open CategoryTheory Limits

namespace HomologicalComplex

variable (C : Type u) [Category.{v} C] {ι : Type t} (c : ComplexShape ι)

section HasZeroMorphisms

variable [HasZeroMorphisms C]

/-
**HomologicalComplex.locallySmall** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`
。
形式化陈述：locallySmall [LocallySmall.{w} C] [Small.{w} ι] : LocallySmall.{w} (Homolo
gicalComplex C c) where hom_small K L
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.instSmallHomOfLocallySmall`：∀ (C : Type u) [inst : Catego
ryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C] (X Y : C),
   Small.{w, v} (X ⟶ Y)
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance locallySmall [LocallySmall.{w} C] [Small.{w} ι] :
    LocallySmall.{w} (HomologicalComplex C c) where
  hom_small K L := by
    let emb (f : K ⟶ L) (i : Shrink.{w} ι) := (equivShrink.{w} _) (f.f ((equivShrink _).symm i))
    have hemb : Function.Injective emb := fun f g h ↦ by
      ext i
      obtain ⟨i, rfl⟩ := (equivShrink.{w} _).symm.surjective i
      simpa [emb] using congr_fun h i
    apply small_of_injective hemb
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFilteredColimitsOfSize.{w, w'} C] :
    HasFilteredColimitsOfSize.{w, w'} (HomologicalComplex C c) where
  HasColimitsOfShape J _ _ := by infer_instance
/-
**HomologicalComplex.hasExactColimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间 `Homologi
calComplex`。
形式化陈述：hasExactColimitsOfShape (J : Type w) [Category.{w'} J] [HasFiniteLimits C]
 [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] : HasExactColimitsOfShap
e J (HomologicalComplex C c) where preservesFiniteLimits
参数：J : Type w。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasColimitsOfShape`：∀ {C : Type u_1} {ι : Type u_
2} {J : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cate
goryTheory.Category.{v_2, u_3} …
· 使用定理 `HomologicalComplex.instPreservesColimitsOfShapeEvalOfHasColimitsOfShape`
：∀ {C : Type u_1} {ι : Type u_2} {J : Type u_3} [inst : CategoryTheory.Category.
{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_3} …
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `HomologicalComplex.instHasLimitsOfShape`：∀ {C : Type u_1} {ι : Type u_2}
 {J : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_3} …
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `HomologicalComplex.instPreservesLimitsOfShapeEvalOfHasLimitsOfShape`：∀ {
C : Type u_1} {ι : Type u_2} {J : Type u_3} [inst : CategoryTheory.Category.{v_1
, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_3} …
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.HasExactColimitsOfShape.preservesFiniteLimits`：∀ {J : Typ
e u'} {inst : CategoryTheory.Category.{v', u'} J} {C : Type u} {inst_1 : Categor
yTheory.Category.{v, u} C}   {inst_2 : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatIso.naturality_2`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
instance hasExactColimitsOfShape (J : Type w) [Category.{w'} J] [HasFiniteLimits C]
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    HasExactColimitsOfShape J (HomologicalComplex C c) where
  preservesFiniteLimits :=
    ⟨fun K _ _ ↦ ⟨fun {F} ↦ ⟨fun hc ↦ ⟨isLimitOfEval _ _ (fun i ↦ by
      let e := preservesColimitNatIso (J := J) (eval C c i)
      exact (IsLimit.postcomposeHomEquiv (Functor.isoWhiskerLeft F e) _).1
        (IsLimit.ofIsoLimit
          (isLimitOfPreserves ((Functor.whiskeringRight J _ _).obj (eval C c i) ⋙ colim) hc)
          (Cone.ext (e.symm.app _) (fun k ↦ (NatIso.naturality_2 e.symm _).symm))))⟩⟩⟩⟩
/-
**HomologicalComplex.ab5OfSize** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
形式化陈述：ab5OfSize [HasFilteredColimitsOfSize.{w', w} C] [HasFiniteLimits C] [AB5Of
Size.{w', w} C] : AB5OfSize.{w', w} (HomologicalComplex C c) where ofShape J _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasFilteredColimitsOfSize`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] {ι : Type t} (c : ComplexShape ι)   [inst_1 :
 CategoryTheory.Limits.HasZeroMorphism…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.Has
FilteredColimitsOfSize.{w', w, v, u} C] (I : Type w)   …
· 使用定理 `CategoryTheory.AB5OfSize.ofShape`：∀ {C : Type u} {inst : CategoryTheory.
Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasFilteredColimitsOfSize.{
w, w', v, u} C}   [sel…
-/
instance ab5OfSize [HasFilteredColimitsOfSize.{w', w} C] [HasFiniteLimits C]
    [AB5OfSize.{w', w} C] :
    AB5OfSize.{w', w} (HomologicalComplex C c) where
  ofShape J _ _ := by infer_instance

end HasZeroMorphisms

/-
**HomologicalComplex.isGrothendieckAbelian** 是 Mathlib 中的一个实例，位于命名空间 `Homologica
lComplex`。
形式化陈述：isGrothendieckAbelian [Abelian C] [IsGrothendieckAbelian.{w} C] [c.HasNoLo
op] [Small.{w} ι] : IsGrothendieckAbelian.{w} (HomologicalComplex C c) where has
Separator
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.locallySmall`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self 
: CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `HomologicalComplex.instHasFilteredColimitsOfSize`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] {ι : Type t} (c : ComplexShape ι)   [inst_1 :
 CategoryTheory.Limits.HasZeroMorphism…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasFilteredColimitsOfSize`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelia
n C}   [self : CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.ab5OfSize`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self : C
ategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
· 使用定理 `CategoryTheory.Limits.hasCoproductsOfShape_of_hasCoproducts`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproduc
ts C] (J : Type w),   CategoryTheory.Limits.HasCo…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasColimits`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Catego
ryTheory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `HomologicalComplex.instHasSeparator`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {ι : Type w} (c : ComplexShape ι) [c.HasNoLoop]   [Categor
yTheory.Limits.HasCoprodu…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasSeparator`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self 
: CategoryTheory.IsGrothendieckAbelian.…
-/
instance isGrothendieckAbelian [Abelian C] [IsGrothendieckAbelian.{w} C]
    [c.HasNoLoop] [Small.{w} ι] :
    IsGrothendieckAbelian.{w} (HomologicalComplex C c) where
  hasSeparator := by
    have : HasCoproductsOfShape ι C :=
      hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{w} ι)).symm
    infer_instance

end HomologicalComplex

