/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!

# Colimits in `P.Over ⊤ S`

Let `P` be a morphism property in the category of schemes and `S` be a scheme. Let
`D : J ⥤ P.Over ⊤ S` be a diagram and `𝒰` a locally directed open cover of `S`
(e.g., the cover of all affine opens of `S`).
Suppose the restrictions of `D` to `Dᵢ : J ⥤ P.Over ⊤ (𝒰.X i)` have a colimit for every `i`,
then we show that also `D` has a colimit under the following assumptions:

- `P` is local on the source.
- For `i ⟶ j`, the transition map `𝒰.X i ⟶ 𝒰.X j` satisfies `P`.
- For `i ⟶ j`, the base change functor `P.Over ⊤ (𝒰.X j) ⥤ P.Over ⊤ (𝒰.X i)` preserves
  colimits of shape `J`.

This can be used to reduce existence of certain colimits in `P.Over ⊤ S` to the case where
`S` is affine.

-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.Scheme.Cover

variable {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange] [P.IsMultiplicative]
  {S : Scheme.{u}} {J : Type*} [Category* J] (D : J ⥤ P.Over ⊤ S)
  (𝒰 : S.OpenCover) [Category* 𝒰.I₀] [𝒰.LocallyDirected]

/-- The data required for gluing the colimits of the `Dᵢ : J ⥤ P.Over ⊤ (𝒰.X i)`. -/
/-
**AlgebraicGeometry.Scheme.Cover.ColimitGluingData** 是 Mathlib 中的一个归纳类型，位于命名空间 `
AlgebraicGeometry.Scheme.Cover`。
形式化陈述：{P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} →   [P.IsSt
ableUnderBaseChange] →     {S : AlgebraicGeometry.Scheme} →       {J : Type u_1}
 →         [inst : CategoryTheory.Category.{v_1, u_1} J] →           CategoryThe
ory.Functor J (P.Over ⊤ S) →             (𝒰 : S.OpenCover) →               [inst
 : CategoryTheory.Category.{v_3, u_2} 𝒰.I₀] →                 [AlgebraicGeometry
.Scheme.Cover.LocallyDirected 𝒰] → Type (max (max (u + 1) u_1) u_2)
参数：P.Over ⊤ S；𝒰 : S.OpenCover；max (max (u + 1) u_1) u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data required for gluing the colimits of the `Dᵢ : J ⥤ P.Over ⊤ (𝒰.X i)`.
-/
structure ColimitGluingData (D : J ⥤ P.Over ⊤ S) (𝒰 : S.OpenCover)
    [Category* 𝒰.I₀] [𝒰.LocallyDirected] where
  /-- The cocones on the `Dᵢ`. -/
  cocone (i : 𝒰.I₀) : Cocone (D ⋙ MorphismProperty.Over.pullback P ⊤ (𝒰.f i))
  /-- The cocones on the `Dᵢ` are colimiting. -/
  isColimit (i : 𝒰.I₀) : IsColimit (cocone i)
  prop_trans {i j : 𝒰.I₀} (hij : i ⟶ j) : P (𝒰.trans hij)

namespace ColimitGluingData

variable {D} {𝒰} (d : ColimitGluingData D 𝒰)

/-- (Implementation) Auxiliary natural transformation for construction of
`AlgebraicGeometry.Scheme.Cover.ColimitGluingData.functor`. -/
@[simps!]
noncomputable
/-
**AlgebraicGeometry.Scheme.Cover.ColimitGluingData.trans** 是 Mathlib 中的一个定义，位于命名
空间 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData`。
形式化陈述：trans {i j : 𝒰.I₀} (hij : i ⟶ j) : D ⋙ Over.pullback P ⊤ (𝒰.f i) ⋙ Over.ma
p _ (d.prop_trans hij) ⟶ D ⋙ Over.pullback P ⊤ (𝒰.f j)
参数：hij : i ⟶ j。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderBaseChange
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData.prop_trans`：∀ {P : Cate
goryTheory.MorphismProperty AlgebraicGeometry.Scheme} [inst : P.IsStableUnderBas
eChange]   {S : AlgebraicGeometry.Scheme} {J : Ty…
· 使用定理 `trivial`：True
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
-/
def trans {i j : 𝒰.I₀} (hij : i ⟶ j) :
    D ⋙ Over.pullback P ⊤ (𝒰.f i) ⋙ Over.map _ (d.prop_trans hij) ⟶
      D ⋙ Over.pullback P ⊤ (𝒰.f j) :=
  D.whiskerLeft <| Over.pullbackMapHomPullback (P := P) (Q := ⊤) _ _ trivial _ _

/-- (Implementation) Cocone for transition map for construction of
`AlgebraicGeometry.Scheme.Cover.ColimitGluingData.functor`. -/
@[simps! pt ι_app]
noncomputable
/-
**AlgebraicGeometry.Scheme.Cover.ColimitGluingData.transitionCocone** 是 Mathlib 
中的一个定义，位于命名空间 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData`。
形式化陈述：transitionCocone {i j : 𝒰.I₀} (hij : i ⟶ j) : Cocone (D ⋙ Over.pullback P 
⊤ (𝒰.f i) ⋙ Over.map _ (d.prop_trans hij))
参数：hij : i ⟶ j。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderBaseChange
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData.prop_trans`：∀ {P : Cate
goryTheory.MorphismProperty AlgebraicGeometry.Scheme} [inst : P.IsStableUnderBas
eChange]   {S : AlgebraicGeometry.Scheme} {J : Ty…
-/
def transitionCocone {i j : 𝒰.I₀} (hij : i ⟶ j) :
    Cocone (D ⋙ Over.pullback P ⊤ (𝒰.f i) ⋙ Over.map _ (d.prop_trans hij)) :=
  (Cocone.precompose (d.trans hij)).obj (d.cocone j)

/-- (Implementation) Transition map for construction of
`AlgebraicGeometry.Scheme.Cover.ColimitGluingData.functor`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.Cover.ColimitGluingData.transitionMap** 是 Mathlib 中的一
个定义，位于命名空间 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData`。
形式化陈述：transitionMap {i j : 𝒰.I₀} (hij : i ⟶ j) : (Over.map ⊤ (d.prop_trans hij))
.obj (d.cocone i).pt ⟶ (d.cocone j).pt
参数：hij : i ⟶ j。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderBaseChange
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData.prop_trans`：∀ {P : Cate
goryTheory.MorphismProperty AlgebraicGeometry.Scheme} [inst : P.IsStableUnderBas
eChange]   {S : AlgebraicGeometry.Scheme} {J : Ty…
-/
def transitionMap {i j : 𝒰.I₀} (hij : i ⟶ j) :
    (Over.map ⊤ (d.prop_trans hij)).obj (d.cocone i).pt ⟶ (d.cocone j).pt :=
  (isColimitOfPreserves (Over.map ⊤ (d.prop_trans hij)) (d.isColimit i)).desc
    (d.transitionCocone hij)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicGeometry.Scheme.Cover.ColimitGluingData.cocone_** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cocone_ι_transitionMap {i j : 𝒰.I₀} (hij : i ⟶ j) (a : J) :
    (Over.map ⊤ (d.prop_trans hij)).map ((d.cocone i).ι.app a) ≫
      d.transitionMap hij = (d.trans hij).app a ≫ (d.cocone j).ι.app a := by
  simp [transitionMap, ← Functor.mapCocone_ι_app, transitionCocone]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.Scheme.Cover.ColimitGluingData.transitionMap_id** 是 Mathlib 
中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData`。
形式化陈述：transitionMap_id (i : 𝒰.I₀) : d.transitionMap (𝟙 i) = ((Over.mapId _ _ _).
hom.app <| (d.cocone i).pt)
参数：i : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksAlongOfHasPullbacks`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Morphi
smProperty C) [P.HasPullbacks]   {X Y : C} {f : X ⟶ Y}, P…
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksOfHasPullbacks`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismPro
perty C)   [CategoryTheory.Limits.HasPullbacks C], P…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderBaseChange
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData.prop_trans`：∀ {P : Cate
goryTheory.MorphismProperty AlgebraicGeometry.Scheme} [inst : P.IsStableUnderBas
eChange]   {S : AlgebraicGeometry.Scheme} {J : Ty…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.MorphismProperty.instIsLeftAdjointOverTopMapOfHasPullback
sAlongOfIsStableUnderBaseChangeAlong`：∀ {T : Type u_1} [inst : CategoryTheory.Ca
tegory.{v_1, u_1} T] (P : CategoryTheory.MorphismProperty T) {X Y : T}   [inst_1
 : P.IsStableUnder…
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsIsoTop`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C], ⊤.RespectsIso
· 使用定理 `CategoryTheory.MorphismProperty.Over.Hom.ext`：∀ {T : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} T] {P Q : CategoryTheory.MorphismProperty T} {
X : T}   [inst_1 : Q.IsMultiplicat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbackHomDiscretePUnitOfHasPull
backsAlong`：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q 
: CategoryTheory.MorphismProperty T) {X Y : T}   (f : X ⟶ Y) [P.HasPullb…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData.cocone_ι_transitionMap`
：cocone_ι_transitionMap {i j : 𝒰.I₀} (hij : i ⟶ j) (a : J) : (Over.map ⊤ (d.prop
_trans hij)).map ((d.cocone i).ι.app a) ≫ d.transitionMap hij…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.Scheme.Cover.trans_id`：trans_id (i : 𝒰.I₀) : 𝒰.trans (
𝟙 i) = 𝟙 (𝒰.X i)
· 使用定理 `CategoryTheory.Limits.pullback.map.congr_simp`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S)   [i
nst_1 : CategoryTheory.Limits.HasPu…
· 使用定理 `CategoryTheory.Limits.pullback.map_id`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma transitionMap_id (i : 𝒰.I₀) :
    d.transitionMap (𝟙 i) = ((Over.mapId _ _ _).hom.app <| (d.cocone i).pt) := by
  apply (isColimitOfPreserves (Over.map ⊤ (d.prop_trans <| 𝟙 i)) (d.isColimit i)).hom_ext
  intro
  ext
  simp [cocone_ι_transitionMap]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.Scheme.Cover.ColimitGluingData.transitionMap_comp** 是 Mathli
b 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData`。
形式化陈述：transitionMap_comp {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k) : d.transiti
onMap (hij ≫ hjk) = (Over.mapComp ⊤ (d.prop_trans hij) (d.prop_trans hjk) (𝒰.tra
ns (hij ≫ hjk))).hom.app _ ≫ (Over.map ⊤ (d.prop_trans hjk)).map (d.transitionMa
p hij) ≫ d.transitionMap hjk
参数：hij : i ⟶ j；hjk : j ⟶ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksAlongOfHasPullbacks`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Morphi
smProperty C) [P.HasPullbacks]   {X Y : C} {f : X ⟶ Y}, P…
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksOfHasPullbacks`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismPro
perty C)   [CategoryTheory.Limits.HasPullbacks C], P…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderBaseChange
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData.prop_trans`：∀ {P : Cate
goryTheory.MorphismProperty AlgebraicGeometry.Scheme} [inst : P.IsStableUnderBas
eChange]   {S : AlgebraicGeometry.Scheme} {J : Ty…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.MorphismProperty.instIsLeftAdjointOverTopMapOfHasPullback
sAlongOfIsStableUnderBaseChangeAlong`：∀ {T : Type u_1} [inst : CategoryTheory.Ca
tegory.{v_1, u_1} T] (P : CategoryTheory.MorphismProperty T) {X Y : T}   [inst_1
 : P.IsStableUnder…
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsIsoTop`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C], ⊤.RespectsIso
· 使用定理 `CategoryTheory.MorphismProperty.Over.Hom.ext`：∀ {T : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} T] {P Q : CategoryTheory.MorphismProperty T} {
X : T}   [inst_1 : Q.IsMultiplicat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbackHomDiscretePUnitOfHasPull
backsAlong`：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q 
: CategoryTheory.MorphismProperty T) {X Y : T}   (f : X ⟶ Y) [P.HasPullb…
· 使用引理 `AlgebraicGeometry.Scheme.Cover.trans_comp`：trans_comp {i j k : 𝒰.I₀} (hi
j : i ⟶ j) (hjk : j ⟶ k) : 𝒰.trans (hij ≫ hjk) = 𝒰.trans hij ≫ 𝒰.trans hjk
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData.cocone_ι_transitionMap`
：cocone_ι_transitionMap {i j : 𝒰.I₀} (hij : i ⟶ j) (a : J) : (Over.map ⊤ (d.prop
_trans hij)).map ((d.cocone i).ι.app a) ≫ d.transitionMap hij…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.pullback.map.congr_simp`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S)   [i
nst_1 : CategoryTheory.Limits.HasPu…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.map_comp_assoc`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {X Y Z X' Y' Z' X'' Y'' Z'' : C} {f : X ⟶ Z} {g 
: Y ⟶ Z}   {f' : X' ⟶ Z'} {g' : Y' …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma transitionMap_comp {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k) :
    d.transitionMap (hij ≫ hjk) =
      (Over.mapComp ⊤ (d.prop_trans hij) (d.prop_trans hjk) (𝒰.trans (hij ≫ hjk))).hom.app _ ≫
      (Over.map ⊤ (d.prop_trans hjk)).map (d.transitionMap hij) ≫
        d.transitionMap hjk := by
  apply (isColimitOfPreserves (Over.map ⊤ <| d.prop_trans _) (d.isColimit i)).hom_ext
  intro
  ext
  simp [← Functor.map_comp_assoc, cocone_ι_transitionMap, pullback.map_comp_assoc]

/-- (Implementation): Underlying functor of associated relative gluing datum. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.Cover.ColimitGluingData.functor** 是 Mathlib 中的一个定义，位于
命名空间 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData`。
形式化陈述：functor : 𝒰.I₀ ⥤ Scheme where obj i
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderBaseChange
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData.prop_trans`：∀ {P : Cate
goryTheory.MorphismProperty AlgebraicGeometry.Scheme} [inst : P.IsStableUnderBas
eChange]   {S : AlgebraicGeometry.Scheme} {J : Ty…

--- 原说明 ---
(Implementation): Underlying functor of associated relative gluing datum.
-/
noncomputable def functor : 𝒰.I₀ ⥤ Scheme where
  obj i := (d.cocone i).pt.left
  map {i j} hij := (d.transitionMap hij).left

variable [∀ {i j} (hij : i ⟶ j), PreservesColimitsOfShape J (Over.pullback P ⊤ (𝒰.trans hij))]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Cover.ColimitGluingData.isPullback** 是 Mathlib 中的一个引理
，位于命名空间 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData`。
形式化陈述：isPullback {i j : 𝒰.I₀} (hij : i ⟶ j) : IsPullback (d.transitionMap hij).l
eft (d.cocone i).pt.hom (d.cocone j).pt.hom (𝒰.trans hij)
参数：hij : i ⟶ j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksAlongOfHasPullbacks`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Morphi
smProperty C) [P.HasPullbacks]   {X Y : C} {f : X ⟶ Y}, P…
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksOfHasPullbacks`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismPro
perty C)   [CategoryTheory.Limits.HasPullbacks C], P…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderBaseChange
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsIsoTop`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C], ⊤.RespectsIso
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Cover.trans_map`：trans_map {i j : 𝒰.I₀} (hij : 
i ⟶ j) : 𝒰.trans hij ≫ 𝒰.f j = 𝒰.f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData.prop_trans`：∀ {P : Cate
goryTheory.MorphismProperty AlgebraicGeometry.Scheme} [inst : P.IsStableUnderBas
eChange]   {S : AlgebraicGeometry.Scheme} {J : Ty…
· 使用定理 `CategoryTheory.MorphismProperty.instHasOfPostcompPropertyTop`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.MorphismPrope
rty C),   ⊤.HasOfPostcompProperty W
· 使用定理 `trivial`：True
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.MorphismProperty.instIsLeftAdjointOverTopMapOfHasPullback
sAlongOfIsStableUnderBaseChangeAlong`：∀ {T : Type u_1} [inst : CategoryTheory.Ca
tegory.{v_1, u_1} T] (P : CategoryTheory.MorphismProperty T) {X Y : T}   [inst_1
 : P.IsStableUnder…
· 使用定理 `CategoryTheory.Limits.IsColimit.coconePointsIsoOfNatIso_hom`：∀ {J : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : Categor
yTheory.Category.{v₃, u₃} C]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.Limits.IsColimit.ι_map`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, 
u₃} C]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.mapCocone_ι_app`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃,
 u₃} C]   {D : Type u₄} [ins…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用引理 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData.cocone_ι_transitionMap`
：cocone_ι_transitionMap {i j : 𝒰.I₀} (hij : i ⟶ j) (a : J) : (Over.map ⊤ (d.prop
_trans hij)).map ((d.cocone i).ι.app a) ≫ d.transitionMap hij…
· 使用定理 `CategoryTheory.MorphismProperty.Over.Hom.ext`：∀ {T : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} T] {P Q : CategoryTheory.MorphismProperty T} {
X : T}   [inst_1 : Q.IsMultiplicat…
（共 49 条，此处仅展示前 30 条）
-/
lemma isPullback {i j : 𝒰.I₀} (hij : i ⟶ j) :
    IsPullback (d.transitionMap hij).left (d.cocone i).pt.hom
      (d.cocone j).pt.hom (𝒰.trans hij) := by
  let iso1 : (d.cocone i).pt ≅ _ :=
    (d.isColimit i).coconePointsIsoOfNatIso
      (isColimitOfPreserves (Over.pullback P ⊤ (𝒰.trans hij)) (d.isColimit j)) <|
      D.isoWhiskerLeft (Over.pullbackComp _ _ _) ≪≫ (Functor.associator _ _ _).symm
  have heq : (Over.map _ (d.prop_trans hij)).map iso1.hom ≫
        (Over.mapPullbackAdj _ _ _ (d.prop_trans hij) trivial).counit.app _ =
      d.transitionMap hij := by
    apply (isColimitOfPreserves (Over.map _ (d.prop_trans hij)) (d.isColimit i)).hom_ext
    intro a
    dsimp only [Functor.comp_obj, Functor.id_obj, Functor.mapCocone_pt, Functor.const_obj_obj,
      Functor.mapCocone_ι_app, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom]
    rw [IsColimit.coconePointsIsoOfNatIso_hom, ← Functor.map_comp_assoc, IsColimit.ι_map,
      Functor.mapCocone_ι_app, Functor.map_comp, Category.assoc,
      Adjunction.counit_naturality, cocone_ι_transitionMap]
    ext
    dsimp
    rw [Category.comp_id, ← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp
  let iso2 : (d.cocone i).pt.left ≅ pullback (d.cocone j).pt.hom (𝒰.trans hij) :=
    (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).mapIso iso1
  refine .of_iso (IsPullback.of_hasPullback _ _) iso2.symm (.refl _) (.refl _) (.refl _) ?_ ?_
      (by simp) (by simp)
  · simpa [← cancel_epi iso2.hom] using! congr($(heq).left)
  · exact (Over.w iso1.inv).symm

set_option backward.isDefEq.respectTransparency false in
/-- The relative gluing datum associated to the family of the `colim Dᵢ`. -/
@[simps natTrans_app, simps -isSimp functor]
noncomputable
/-
**AlgebraicGeometry.Scheme.Cover.ColimitGluingData.relativeGluingData** 是 Mathli
b 中的一个定义，位于命名空间 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData`。
形式化陈述：relativeGluingData : 𝒰.RelativeGluingData where functor
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderBaseChange
· 使用引理 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData.isPullback`：isPullback 
{i j : 𝒰.I₀} (hij : i ⟶ j) : IsPullback (d.transitionMap hij).left (d.cocone i).
pt.hom (d.cocone j).pt.hom (𝒰.trans hij)
-/
def relativeGluingData : 𝒰.RelativeGluingData where
  functor := d.functor
  natTrans.app i := (d.cocone i).pt.hom
  equifibered {i j} hij := d.isPullback hij

variable [Quiver.IsThin 𝒰.I₀] [Small.{u} 𝒰.I₀] [IsZariskiLocalAtTarget P]

set_option backward.isDefEq.respectTransparency false in
/-- The result of gluing the `colim Dᵢ`. -/
/-
**AlgebraicGeometry.Scheme.Cover.ColimitGluingData.glued** 是 Mathlib 中的一个定义，位于命名
空间 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData`。
形式化陈述：glued : P.Over ⊤ S
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderBaseChange

--- 原说明 ---
The result of gluing the `colim Dᵢ`.
-/
noncomputable def glued : P.Over ⊤ S :=
  Over.mk _ d.relativeGluingData.toBase <| by
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) 𝒰]
    intro i
    rw [Scheme.Cover.pullbackHom,
      ← (d.relativeGluingData.isPullback_natTrans_ι_toBase i).flip.isoPullback_inv_snd,
      P.cancel_left_of_respectsIso]
    exact (d.cocone i).pt.prop

set_option backward.isDefEq.respectTransparency false in
/-- `colim Dᵢ` is the pullback of the glued object over `S` along the inclusion `𝒰ᵢ ⟶ S`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.Cover.ColimitGluingData.pullbackGluedIso** 是 Mathlib 
中的一个定义，位于命名空间 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData`。
形式化陈述：pullbackGluedIso (i : 𝒰.I₀) : (MorphismProperty.Over.pullback P ⊤ (𝒰.f i))
.obj d.glued ≅ (d.cocone i).pt
参数：i : 𝒰.I₀。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderBaseChange
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsIsoTop`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C], ⊤.RespectsIso
-/
def pullbackGluedIso (i : 𝒰.I₀) :
    (MorphismProperty.Over.pullback P ⊤ (𝒰.f i)).obj d.glued ≅ (d.cocone i).pt :=
  Over.isoMk (d.relativeGluingData.isPullback_natTrans_ι_toBase i).flip.isoPullback.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Cover.ColimitGluingData.pullbackGluedIso_inv_fst** 是 
Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData`。
形式化陈述：pullbackGluedIso_inv_fst (i : 𝒰.I₀) : (d.pullbackGluedIso i).inv.left ≫ pu
llback.fst _ _ = colimit.ι d.relativeGluingData.functor i
参数：i : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksAlongOfHasPullbacks`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Morphi
smProperty C) [P.HasPullbacks]   {X Y : C} {f : X ⟶ Y}, P…
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksOfHasPullbacks`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismPro
perty C)   [CategoryTheory.Limits.HasPullbacks C], P…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderBaseChange
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbackHomDiscretePUnitOfHasPull
backsAlong`：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q 
: CategoryTheory.MorphismProperty T) {X Y : T}   (f : X ⟶ Y) [P.HasPullb…
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.instIsOpenImmersionMap
I₀Functor`：∀ {S : AlgebraicGeometry.Scheme} {𝒰 : S.OpenCover} [inst : CategoryTh
eory.Category.{u_2, u_1} 𝒰.I₀]   [inst_1 : AlgebraicGeometry.Scheme.Cov…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI
₀CompFunctorForgetOfIsThin`：∀ {S : AlgebraicGeometry.Scheme} {𝒰 : S.OpenCover} [
inst : CategoryTheory.Category.{u_2, u_1} 𝒰.I₀]   [inst_1 : AlgebraicGeometry.Sc
heme.Cov…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPullback.isoPullback_hom_fst`：isoPullback_hom_fst (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.hom ≫ pullback.fst _ _
 = fst
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullbackGluedIso_inv_fst (i : 𝒰.I₀) : (d.pullbackGluedIso i).inv.left ≫ pullback.fst _ _ =
    colimit.ι d.relativeGluingData.functor i := by
  simp [pullbackGluedIso, glued]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Cover.ColimitGluingData.pullbackGluedIso_inv_snd** 是 
Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData`。
形式化陈述：pullbackGluedIso_inv_snd (i : 𝒰.I₀) : (d.pullbackGluedIso i).inv.left ≫ pu
llback.snd _ _ = (d.cocone i).pt.hom
参数：i : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksAlongOfHasPullbacks`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Morphi
smProperty C) [P.HasPullbacks]   {X Y : C} {f : X ⟶ Y}, P…
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksOfHasPullbacks`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismPro
perty C)   [CategoryTheory.Limits.HasPullbacks C], P…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderBaseChange
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbackHomDiscretePUnitOfHasPull
backsAlong`：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q 
: CategoryTheory.MorphismProperty T) {X Y : T}   (f : X ⟶ Y) [P.HasPullb…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPullback.isoPullback_hom_snd`：isoPullback_hom_snd (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.hom ≫ pullback.snd _ _
 = snd
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullbackGluedIso_inv_snd (i : 𝒰.I₀) :
    (d.pullbackGluedIso i).inv.left ≫ pullback.snd _ _ = (d.cocone i).pt.hom := by
  simp [pullbackGluedIso, glued]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cocone glued from the `colim Dᵢ`. -/
@[simps pt]
/-
**AlgebraicGeometry.Scheme.Cover.ColimitGluingData.gluedCocone** 是 Mathlib 中的一个定
义，位于命名空间 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData`。
形式化陈述：gluedCocone : Cocone D
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderBaseChange
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `trivial`：True

--- 原说明 ---
The cocone glued from the `colim Dᵢ`.
-/
noncomputable def gluedCocone : Cocone D := by
  letI 𝒱 (a : J) : (D.obj a).left.OpenCover := 𝒰.pullback₁ (D.obj a).hom
  refine { pt := d.glued, ι.app a := ?_, ι.naturality {a b} f := ?_ }
  · refine ⟨(𝒱 a).glueMorphismsOverOfLocallyDirected ?_ ?_ ?_, trivial, trivial⟩
    · intro i
      exact ((d.cocone i).ι.app a).left ≫ colimit.ι d.relativeGluingData.functor i
    · intro i j hij
      conv_rhs => rw [← colimit.w d.relativeGluingData.functor hij]
      simp only [← Category.assoc]
      congr 1
      exact congr($(d.cocone_ι_transitionMap hij a).left).symm
    · intro
      simp [𝒱, pullback.condition, glued]
  · ext
    apply (𝒱 a).hom_ext
    intro i
    have : (𝒱 a).f i ≫ (D.map f).left =
        ((D ⋙ Over.pullback _ _ (𝒰.f i)).map f).left ≫ (𝒱 b).f i := by
      simp [𝒱]
    dsimp
    rw [Category.comp_id, Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left,
      reassoc_of% this, Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left,
      ← Over.comp_left_assoc, ← Comma.comp_hom, ← Functor.comp_map, Cocone.w]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicGeometry.Scheme.Cover.ColimitGluingData.fst_gluedCocone_** 是 Mathlib 
中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fst_gluedCocone_ι (a : J) (i : 𝒰.I₀) :
    pullback.fst (D.obj a).hom (𝒰.f i) ≫
      (d.gluedCocone.ι.app a).left =
      ((d.cocone i).ι.app a).left ≫ colimit.ι d.relativeGluingData.functor i := by
  simp only [gluedCocone]
  generalize_proofs _ _ _ _ _ _ _ _ _ _ _ _ h1 h2
  let 𝒱 : (D.obj a).left.OpenCover := 𝒰.pullback₁ (D.obj a).hom
  apply 𝒱.map_glueMorphismsOverOfLocallyDirected_left _ h1 h2

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The glued cocone is colimiting. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.Cover.ColimitGluingData.isColimitGluedCocone** 是 Math
lib 中的一个定义，位于命名空间 `AlgebraicGeometry.Scheme.Cover.ColimitGluingData`。
形式化陈述：isColimitGluedCocone : IsColimit d.gluedCocone
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderBaseChange
· 使用定理 `trivial`：True
-/
def isColimitGluedCocone : IsColimit d.gluedCocone := by
  letI 𝒱 : d.glued.left.OpenCover := d.relativeGluingData.cover
  refine { desc s := ?_, fac := ?_, uniq := ?_ }
  · refine ⟨𝒱.glueMorphismsOverOfLocallyDirected ?_ ?_ ?_, trivial, trivial⟩
    · intro i
      exact ((d.isColimit i).desc (Functor.mapCocone _ s)).left ≫ pullback.fst _ _
    · intro i j hij
      simp only [Functor.mapCocone_pt, MorphismProperty.Over.pullback_obj_left,
        Functor.id_obj, Functor.const_obj_obj]
      change (d.transitionMap hij).left ≫ _ ≫ _ = _
      have : d.transitionMap hij ≫ (d.isColimit j).desc ((Over.pullback P ⊤ (𝒰.f j)).mapCocone s) =
          (Over.map ⊤ (d.prop_trans hij)).map
            ((d.isColimit i).desc ((MorphismProperty.Over.pullback P ⊤ (𝒰.f i)).mapCocone s)) ≫
          (Over.pullbackMapHomPullback _ (d.prop_trans hij) trivial _ _).app _ := by
        apply (isColimitOfPreserves (Over.map ⊤ <| d.prop_trans _) (d.isColimit i)).hom_ext
        intro
        ext
        apply pullback.hom_ext <;> simp [cocone_ι_transitionMap_assoc, ← Functor.map_comp_assoc]
      rw [← Over.comp_left_assoc, ← Comma.comp_hom, this]
      simp
    · intro i
      have : _ ≫ pullback.snd _ _ = _ := Over.w ((d.isColimit i).desc (Functor.mapCocone _ s))
      simp only [glued, Category.assoc, 𝒱, pullback.condition]
      rw [reassoc_of% this]
      simp
  · intro s a
    let 𝒲 (a : J) : (D.obj a).left.OpenCover := 𝒰.pullback₁ (D.obj a).hom
    ext
    refine (𝒲 a).hom_ext _ _ fun i ↦ ?_
    dsimp
    simp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
      PreZeroHypercover.pullback₁_f, 𝒲, fst_gluedCocone_ι_assoc]
    change _ ≫ 𝒱.f _ ≫ _ = _
    rw [Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left, ← Over.comp_left_assoc,
      ← Comma.comp_hom]
    simp
  · intro s m hm
    ext
    refine 𝒱.hom_ext _ _ fun i ↦ ?_
    have : (d.pullbackGluedIso i).inv ≫ (Over.pullback P ⊤ (𝒰.f i)).map m =
        (d.isColimit i).desc ((Over.pullback P ⊤ (𝒰.f i)).mapCocone s) := by
      refine (d.isColimit i).hom_ext fun a ↦ ?_
      rw [IsColimit.fac]
      ext
      apply pullback.hom_ext
      · dsimp
        simp only [Category.assoc, limit.lift_π, PullbackCone.mk_π_app,
          pullbackGluedIso_inv_fst_assoc]
        rw [← congr($(hm a).left)]
        simp [fst_gluedCocone_ι_assoc]
      · simp
    rw [Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left]
    simp [𝒱, ← this]

end ColimitGluingData

/-
**AlgebraicGeometry.Scheme.Cover.hasColimit_of_locallyDirected** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry.Scheme.Cover`。
形式化陈述：hasColimit_of_locallyDirected (H : forall {i j} (hij : i ⟶ j), P (𝒰.trans 
hij)) [forall {i j : 𝒰.I₀} (hij : i ⟶ j), PreservesColimitsOfShape J (Over.pullb
ack P ⊤ (𝒰.trans hij))] [forall i, HasColimit (D ⋙ Over.pullback _ _ (𝒰.f i))] [
Quiver.IsThin 𝒰.I₀] [Small.{u} 𝒰.I₀] [IsZariskiLocalAtTarget P] : HasColimit D
参数：H : forall {i j} (hij : i ⟶ j), P (𝒰.trans hij)；hij : i ⟶ j；Over.pullback P ⊤
 (𝒰.trans hij)；D ⋙ Over.pullback _ _ (𝒰.f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksAlongOfHasPullbacks`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Morphi
smProperty C) [P.HasPullbacks]   {X Y : C} {f : X ⟶ Y}, P…
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksOfHasPullbacks`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismPro
perty C)   [CategoryTheory.Limits.HasPullbacks C], P…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderBaseChange
-/
lemma hasColimit_of_locallyDirected
    (H : ∀ {i j} (hij : i ⟶ j), P (𝒰.trans hij))
    [∀ {i j : 𝒰.I₀} (hij : i ⟶ j), PreservesColimitsOfShape J (Over.pullback P ⊤ (𝒰.trans hij))]
    [∀ i, HasColimit (D ⋙ Over.pullback _ _ (𝒰.f i))]
    [Quiver.IsThin 𝒰.I₀] [Small.{u} 𝒰.I₀] [IsZariskiLocalAtTarget P] :
    HasColimit D :=
  let d : ColimitGluingData D 𝒰 :=
    { cocone _ := colimit.cocone _
      isColimit _ := colimit.isColimit _
      prop_trans := H }
  ⟨d.gluedCocone, d.isColimitGluedCocone⟩

end AlgebraicGeometry.Scheme.Cover

