/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!
# (Co)limits in over categories

We show that if `P` is a morphism property in `Scheme` that is local at the source, then
colimits in `P.Over ⊤ X` for `X : Scheme` of locally directed diagrams of open immersions
exist and agree with the colimit in `Scheme`.
-/

public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (X : Scheme.{u})

variable (P : MorphismProperty Scheme.{u})

section Over

variable {S : Scheme.{u}} {J : Type*} [Category* J] (F : J ⥤ Over S)
  [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f).left]
  [(F ⋙ Over.forget S ⋙ Scheme.forget).IsLocallyDirected]
  [Quiver.IsThin J] [Small.{u} J]

/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : HasColimit F :=
  have {i j} (f : i ⟶ j) : IsOpenImmersion ((F ⋙ Over.forget S).map f) :=
    inferInstanceAs <| IsOpenImmersion (F.map f).left
  have : ((F ⋙ Over.forget S) ⋙ Scheme.forget).IsLocallyDirected := ‹_›
  hasColimit_of_created _ (Over.forget S)

end Over

section OverProp

/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Scheme.{u}} {U X Y : P.Over ⊤ S} (f : U ⟶ X) (g : U ⟶ Y)
    [IsOpenImmersion f.left] [IsOpenImmersion g.left] (i : WalkingPair) :
    Mono ((span f g ⋙ MorphismProperty.Over.forget P ⊤ S ⋙ Over.forget S ⋙ Scheme.forget).map
      (WidePushoutShape.Hom.init i)) := by
  rw [mono_iff_injective]
  cases i
  · simpa using! f.left.isOpenEmbedding.injective
  · simpa using! g.left.isOpenEmbedding.injective
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Scheme.{u}} {U X Y : P.Over ⊤ S} (f : U ⟶ X) (g : U ⟶ Y)
    [IsOpenImmersion f.left] [IsOpenImmersion g.left]
    {i j : WalkingSpan} (t : i ⟶ j) :
      IsOpenImmersion ((span f g).map t).left := by
  obtain (a | (a | a)) := t
  · simp only [WidePushoutShape.hom_id, CategoryTheory.Functor.map_id]
    infer_instance
  · simpa
  · simpa

variable [IsZariskiLocalAtSource P] {S : Scheme.{u}} {J : Type*} [Category* J] (F : J ⥤ P.Over ⊤ S)
  [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f).left]
  [(F ⋙ MorphismProperty.Over.forget P ⊤ S ⋙ Over.forget S ⋙ Scheme.forget).IsLocallyDirected]
  [Quiver.IsThin J] [Small.{u} J]

local instance :
    (((F ⋙ MorphismProperty.Over.forget P ⊤ S) ⋙ Over.forget S) ⋙
      Scheme.forget).IsLocallyDirected :=
  ‹_›

local instance {i j} (f : i ⟶ j) :
    IsOpenImmersion <|
      ((F ⋙ MorphismProperty.Over.forget P ⊤ S) ⋙ Over.forget S).map f :=
  inferInstanceAs <| IsOpenImmersion (F.map f).left

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CreatesColimit F (MorphismProperty.Over.forget P ⊤ S) := by
  have : HasColimit (F ⋙ MorphismProperty.Over.forget P ⊤ S) :=
    hasColimit_of_created _ (Over.forget S)
  refine createsColimitOfFullyFaithfulOfIso
      { toComma := colimit (F ⋙ MorphismProperty.Over.forget P ⊤ S)
        prop := ?_ } (Iso.refl _)
  let e : (colimit (F ⋙ MorphismProperty.Over.forget P ⊤ S)).left ≅
      colimit ((F ⋙ MorphismProperty.Over.forget P ⊤ S) ⋙ Over.forget S) :=
    preservesColimitIso (Over.forget S) _
  let 𝒰 : (colimit (F ⋙ MorphismProperty.Over.forget P ⊤ S)).left.OpenCover :=
    (Scheme.IsLocallyDirected.openCover _).pushforwardIso e.inv
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) 𝒰]
  intro i
  simpa [𝒰, e] using! (F.obj i).prop
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasColimit F := hasColimit_of_created _ (MorphismProperty.Over.forget P ⊤ S)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesColimit F (MorphismProperty.Over.forget P ⊤ S) :=
  -- this is only `inferInstance` with the local instances above
  inferInstance

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (j : J) : IsOpenImmersion (colimit.ι F j).left := by
  rw [← MorphismProperty.Over.forget_comp_forget_map]
  let e : (colimit F).left ≅ colimit (F ⋙ _) :=
    preservesColimitIso (MorphismProperty.Over.forget P ⊤ S ⋙ Over.forget S) F
  rw [← MorphismProperty.cancel_right_of_respectsIso (P := @IsOpenImmersion) _ e.hom]
  simp only [e, CategoryTheory.ι_preservesColimitIso_hom]
  exact inferInstanceAs <| IsOpenImmersion
    (colimit.ι ((F ⋙ MorphismProperty.Over.forget P ⊤ S) ⋙ Over.forget S) j)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} [Small.{u} ι] : HasCoproductsOfShape ι (P.Over ⊤ S) where
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasFiniteCoproducts (P.Over ⊤ S) where
  out := inferInstance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (J : Type*) [Small.{u} J] :
    CreatesColimitsOfShape (Discrete J) (MorphismProperty.Over.forget P ⊤ S) where

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P]
/-
**AlgebraicGeometry.IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete
** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.IsZariskiLocalAtSource`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} [Algebrai
cGeometry.IsZariskiLocalAtSource P]   {ι : Type u_2} [Small.{u, u_2} ι] {C : Typ
e u_3} [inst : CategoryTheory.Category.{v_2, u_3} C]   [CategoryTheory.Limits.Ha
sColimitsOfShape (CategoryTheory.Discrete ι) C]   (L : CategoryTheory.Functor C 
AlgebraicGeometry.Scheme)   [CategoryTheory.Limits.PreservesColimitsOfShape (Cat
egoryTheory.Discrete ι) L] (X : AlgebraicGeometry.Scheme),   (CategoryTheory.Mor
phismProperty.costructuredArrowObj L P).IsClosedUnderColimitsOfShape (CategoryTh
eory.Discrete ι)
参数：CategoryTheory.Discrete ι；L : CategoryTheory.Functor C AlgebraicGeometry.Sche
me；CategoryTheory.Discrete ι；X : AlgebraicGeometry.Scheme；CategoryTheory.Morphis
mProperty.costructuredArrowObj L P；CategoryTheory.Discrete ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CostructuredArrow.isClosedUnderColimitsOfShape`：∀ {T : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] {A : Type u_2}   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} A] {L : Categor…
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.sigmaDesc`：sigmaDesc {X : Schem
e.{u}} {ι : Type v} [Small.{u} ι] {Y : ι -> Scheme.{u}} {f : forall i, Y i ⟶ X} 
(hf : forall i, P (f i)) : P (Sigma.desc…
-/
instance IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete {ι : Type*} [Small.{u} ι]
    {C : Type*} [Category* C] [HasColimitsOfShape (Discrete ι) C] (L : C ⥤ Scheme.{u})
    [PreservesColimitsOfShape (Discrete ι) L] (X : Scheme.{u}) :
    (P.costructuredArrowObj L (X := X)).IsClosedUnderColimitsOfShape (Discrete ι) :=
  CostructuredArrow.isClosedUnderColimitsOfShape _ (fun _ ↦ coproductIsCoproduct' _)
    (fun _ _ _ _ h ↦ IsZariskiLocalAtSource.sigmaDesc (h ⟨·⟩)) _

variable [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] [P.IsMultiplicative]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasFiniteCoproducts (P.CostructuredArrow ⊤ Scheme.Spec S) where
  out n := by
    have : (MorphismProperty.commaObj Scheme.Spec (.fromPUnit S) P).IsClosedUnderColimitsOfShape
        (Discrete (Fin n)) :=
      IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete _ _
    apply MorphismProperty.Comma.hasColimitsOfShape_of_closedUnderColimitsOfShape

end OverProp

end AlgebraicGeometry

