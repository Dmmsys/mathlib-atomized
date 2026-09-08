/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!

# Topological subcategories of `Action V G`

For a concrete category `V`, where the forgetful functor factors via `TopCat`,
and a monoid `G`, equipped with a topological space instance,
we define the full subcategory `ContAction V G` of all objects of `Action V G`
where the induced action is continuous.

We also define a category `DiscreteContAction V G` as the full subcategory of `ContAction V G`,
where the underlying topological space is discrete.

Finally we define inclusion functors into `Action V G` and `TopCat` in terms
of `HasForget₂` instances.

-/

@[expose] public section

open CategoryTheory Limits

variable (V : Type*) [Category* V] {FV : V → V → Type*} {CV : V → Type*}
    [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)] [ConcreteCategory V FV] [HasForget₂ V TopCat]
variable (G : Type*) [Monoid G] [TopologicalSpace G]

namespace Action

/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasForget₂ (Action V G) TopCat :=
  HasForget₂.trans (Action V G) V TopCat

set_option backward.isDefEq.respectTransparency.types false in
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Action V G) : MulAction G ((CategoryTheory.forget₂ _ TopCat).obj X) where
  smul g x := ((CategoryTheory.forget₂ _ TopCat).map (X.ρ g)) x
  one_smul x := by
    change ((CategoryTheory.forget₂ _ TopCat).map (X.ρ 1)) x = x
    simp
  mul_smul g h x := by
    change (CategoryTheory.forget₂ _ TopCat).map (X.ρ (g * h)) x =
      ((CategoryTheory.forget₂ _ TopCat).map (X.ρ h) ≫
        (CategoryTheory.forget₂ _ TopCat).map (X.ρ g)) x
    rw [← Functor.map_comp, map_mul]
    rfl

variable {V G}

/-- For `HasForget₂ V TopCat` a predicate on an `X : Action V G` saying that the induced action on
the underlying topological space is continuous. -/
/-
**Action.IsContinuous** 是 Mathlib 中的一个缩写定义，位于命名空间 `Action`。
形式化陈述：IsContinuous (X : Action V G) : Prop
参数：X : Action V G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `HasForget₂ V TopCat` a predicate on an `X : Action V G` saying that the ind
uced action on
the underlying topological space is continuous.
-/
abbrev IsContinuous (X : Action V G) : Prop :=
  ContinuousSMul G ((CategoryTheory.forget₂ _ TopCat).obj X)
/-
**Action.isContinuous_def** 是 Mathlib 中的一个引理，位于命名空间 `Action`。
形式化陈述：isContinuous_def (X : Action V G) : X.IsContinuous ↔ Continuous (fun p : G
 × (forget₂ _ TopCat).obj X => (forget₂ _ TopCat).map (X.ρ p.1) p.2)
参数：X : Action V G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
-/
lemma isContinuous_def (X : Action V G) :
    X.IsContinuous ↔ Continuous (fun p : G × (forget₂ _ TopCat).obj X ↦
      (forget₂ _ TopCat).map (X.ρ p.1) p.2) :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

end Action

open Action

/-- For `HasForget₂ V TopCat`, this is the full subcategory of `Action V G` where the induced
action is continuous. -/
/-
**ContAction** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：ContAction : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `HasForget₂ V TopCat`, this is the full subcategory of `Action V G` where th
e induced
action is continuous.
-/
abbrev ContAction : Type _ := ObjectProperty.FullSubcategory (IsContinuous (V := V) (G := G))

namespace ContAction

/-
**ContAction.** 是 Mathlib 中的一个实例，位于命名空间 `ContAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasForget₂ (ContAction V G) V :=
  HasForget₂.trans (ContAction V G) (Action V G) V
/-
**ContAction.** 是 Mathlib 中的一个实例，位于命名空间 `ContAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasForget₂ (ContAction V G) TopCat :=
  HasForget₂.trans (ContAction V G) (Action V G) TopCat
/-
**ContAction.** 是 Mathlib 中的一个实例，位于命名空间 `ContAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (ContAction V G) (Action V G) where
  coe X := X.obj

variable {V G}

/-- A predicate on an `X : ContAction V G` saying that the topology on the underlying type of `X`
is discrete. -/
/-
**ContAction.IsDiscrete** 是 Mathlib 中的一个缩写定义，位于命名空间 `ContAction`。
形式化陈述：IsDiscrete (X : ContAction V G) : Prop
参数：X : ContAction V G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate on an `X : ContAction V G` saying that the topology on the underlyin
g type of `X`
is discrete.
-/
abbrev IsDiscrete (X : ContAction V G) : Prop :=
  DiscreteTopology ((CategoryTheory.forget₂ _ TopCat).obj X)

variable (V) {H : Type*} [Monoid H] [TopologicalSpace H]

/-- The "restriction" functor along a monoid homomorphism `f : G →* H`,
taking actions of `H` to actions of `G`. This is the analogue of
`Action.res` in the continuous setting. -/
@[simps! obj_obj map]
/-
**ContAction.res** 是 Mathlib 中的一个定义，位于命名空间 `ContAction`。
形式化陈述：res (f : G ->ₜ* H) : ContAction V H ⥤ ContAction V G
参数：f : G ->ₜ* H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "restriction" functor along a monoid homomorphism `f : G →* H`,
taking actions of `H` to actions of `G`. This is the analogue of
`Action.res` in the continuous setting.
-/
def res (f : G →ₜ* H) : ContAction V H ⥤ ContAction V G :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Action.res _ f) fun X ↦ by
    constructor
    let v : G × (forget₂ _ TopCat).obj X → H × (forget₂ _ TopCat).obj X := fun p ↦ (f p.1, p.2)
    have : Continuous v := by fun_prop
    let u : H × (forget₂ _ TopCat).obj X → (forget₂ _ TopCat).obj X :=
      fun p ↦ (forget₂ _ TopCat).map (X.obj.ρ p.1) p.2
    have : Continuous u := X.2.1
    change Continuous (u ∘ v)
    fun_prop

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Restricting scalars along a composition is naturally isomorphic to restricting scalars twice. -/
@[simps! hom inv]
/-
**ContAction.resComp** 是 Mathlib 中的一个定义，位于命名空间 `ContAction`。
形式化陈述：resComp {K : Type*} [Monoid K] [TopologicalSpace K] (f : G ->ₜ* H) (h : H 
->ₜ* K) : ContAction.res V (h.comp f) ≅ ContAction.res V h ⋙ ContAction.res V f
参数：f : G ->ₜ* H；h : H ->ₜ* K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restricting scalars along a composition is naturally isomorphic to restricting s
calars twice.
-/
def resComp {K : Type*} [Monoid K] [TopologicalSpace K]
    (f : G →ₜ* H) (h : H →ₜ* K) :
    ContAction.res V (h.comp f) ≅ ContAction.res V h ⋙ ContAction.res V f :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `f = f'`, restriction of scalars along `f` and `f'` is the same. -/
@[simps! hom inv]
/-
**ContAction.resCongr** 是 Mathlib 中的一个定义，位于命名空间 `ContAction`。
形式化陈述：resCongr (f f' : G ->ₜ* H) (h : f = f') : ContAction.res V f ≅ ContAction.
res V f'
参数：f f' : G ->ₜ* H；h : f = f'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f = f'`, restriction of scalars along `f` and `f'` is the same.
-/
def resCongr (f f' : G →ₜ* H) (h : f = f') : ContAction.res V f ≅ ContAction.res V f' :=
  NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _ (Action.mkIso (Iso.refl _)
    (by subst h; simp))) fun f ↦ ObjectProperty.hom_ext _ (Action.Hom.ext (by simp))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction of scalars along a topological monoid isomorphism induces an equivalence of
categories. -/
@[simps! functor inverse]
/-
**ContAction.resEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContAction`。
形式化陈述：resEquiv (f : G ≃ₜ* H) : ContAction V H ≌ ContAction V G where functor
参数：f : G ≃ₜ* H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of scalars along a topological monoid isomorphism induces an equival
ence of
categories.
-/
def resEquiv (f : G ≃ₜ* H) : ContAction V H ≌ ContAction V G where
  functor := res _ f
  inverse := res _ f.symm
  unitIso := resCongr V (ContinuousMonoidHom.id H) _ (by ext; simp) ≪≫
    ContAction.resComp _ _ _
  counitIso := (ContAction.resComp _ _ _).symm ≪≫
    ContAction.resCongr V _ (ContinuousMonoidHom.id G) (by ext; simp)

end ContAction

open ContAction

set_option backward.isDefEq.respectTransparency.types false in
/-- The subcategory of `ContAction V G` where the topology is discrete. -/
/-
**DiscreteContAction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DiscreteContAction : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subcategory of `ContAction V G` where the topology is discrete.
-/
def DiscreteContAction : Type _ := ObjectProperty.FullSubcategory (IsDiscrete (V := V) (G := G))
deriving Category, ConcreteCategory

namespace DiscreteContAction


set_option backward.isDefEq.respectTransparency.types false in
/-
**DiscreteContAction.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteContAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasForget₂ (DiscreteContAction V G) (ContAction V G) :=
  inferInstanceAs <| HasForget₂ (ObjectProperty.FullSubcategory _) _

set_option backward.isDefEq.respectTransparency.types false in
/-
**DiscreteContAction.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteContAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasForget₂ (DiscreteContAction V G) TopCat :=
  HasForget₂.trans (DiscreteContAction V G) (ContAction V G) TopCat

variable {V G}

set_option backward.isDefEq.respectTransparency.types false in
/-
**DiscreteContAction.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteContAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : DiscreteContAction V G) :
    DiscreteTopology ((CategoryTheory.forget₂ _ TopCat).obj X) :=
  X.property

end DiscreteContAction

namespace CategoryTheory

variable {V W : Type*} [Category* V] {FV : V → V → Type*} {CV : V → Type*}
    [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)]
    [ConcreteCategory V FV] [HasForget₂ V TopCat]
    [Category* W] {FW : W → W → Type*} {CW : W → Type*} [∀ X Y, FunLike (FW X Y) (CW X) (CW Y)]
    [ConcreteCategory W FW] [HasForget₂ W TopCat]
    (G : Type*) [Monoid G] [TopologicalSpace G]

namespace Functor

/-- Continuous version of `Functor.mapAction`. -/
@[simps! obj_obj map]
/-
**CategoryTheory.Functor.mapContAction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：mapContAction (F : V ⥤ W) (H : forall X : ContAction V G, ((F.mapAction G)
.obj X.obj).IsContinuous) : ContAction V G ⥤ ContAction W G
参数：F : V ⥤ W；H : forall X : ContAction V G, ((F.mapAction G).obj X.obj).IsContin
uous。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous version of `Functor.mapAction`.
-/
def mapContAction (F : V ⥤ W) (H : ∀ X : ContAction V G, ((F.mapAction G).obj X.obj).IsContinuous) :
    ContAction V G ⥤ ContAction W G :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ F.mapAction G) H

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Continuous version of `Functor.mapActionComp`. -/
@[simps! hom inv]
/-
**CategoryTheory.Functor.mapContActionComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：mapContActionComp {T : Type*} [Category* T] {FT : T -> T -> Type*} {CT : T
 -> Type*} [forall X Y, FunLike (FT X Y) (CT X) (CT Y)] [ConcreteCategory T FT] 
[HasForget₂ T TopCat] (F : V ⥤ W) (H : forall X : ContAction V G, ((F.mapAction 
G).obj X.obj).IsContinuous) (F' : W ⥤ T) (H' : forall X : ContAction W G, ((F'.m
apAction G).obj X.obj).IsContinuous) : Functor.mapContAction G (F ⋙ F') (fun X =
> H' ((F.mapContAction G H).obj X)) ≅ Functor.mapContAction G F H ⋙ Functor.mapC
ontAction G F' H'
参数：FT X Y；CT X；CT Y；F : V ⥤ W；H : forall X : ContAction V G, ((F.mapAction G).ob
j X.obj).IsContinuous；F' : W ⥤ T；H' : forall X : ContAction W G, ((F'.mapAction 
G).obj X.obj).IsContinuous。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous version of `Functor.mapActionComp`.
-/
def mapContActionComp {T : Type*} [Category* T]
    {FT : T → T → Type*} {CT : T → Type*} [∀ X Y, FunLike (FT X Y) (CT X) (CT Y)]
    [ConcreteCategory T FT] [HasForget₂ T TopCat]
    (F : V ⥤ W) (H : ∀ X : ContAction V G, ((F.mapAction G).obj X.obj).IsContinuous)
    (F' : W ⥤ T) (H' : ∀ X : ContAction W G, ((F'.mapAction G).obj X.obj).IsContinuous) :
    Functor.mapContAction G (F ⋙ F') (fun X ↦ H' ((F.mapContAction G H).obj X)) ≅
      Functor.mapContAction G F H ⋙ Functor.mapContAction G F' H' :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Continuous version of `Functor.mapActionCongr`. -/
@[simps! hom inv]
/-
**CategoryTheory.Functor.mapContActionCongr** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：mapContActionCongr {F : V ⥤ W} {F' : V ⥤ W} (e : F ≅ F') (H : forall X : C
ontAction V G, ((F.mapAction G).obj X.obj).IsContinuous) (H' : forall X : ContAc
tion V G, ((F'.mapAction G).obj X.obj).IsContinuous) : Functor.mapContAction G F
 H ≅ Functor.mapContAction G F' H'
参数：e : F ≅ F'；H : forall X : ContAction V G, ((F.mapAction G).obj X.obj).IsConti
nuous；H' : forall X : ContAction V G, ((F'.mapAction G).obj X.obj).IsContinuous。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous version of `Functor.mapActionCongr`.
-/
def mapContActionCongr
    {F : V ⥤ W} {F' : V ⥤ W} (e : F ≅ F')
    (H : ∀ X : ContAction V G, ((F.mapAction G).obj X.obj).IsContinuous)
    (H' : ∀ X : ContAction V G, ((F'.mapAction G).obj X.obj).IsContinuous) :
    Functor.mapContAction G F H ≅ Functor.mapContAction G F' H' :=
  NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _ (Action.mkIso (e.app X.obj.V) (by simp)))

end Functor

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Continuous version of `Equivalence.mapAction`. -/
@[simps functor inverse]
/-
**CategoryTheory.Equivalence.mapContAction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Equivalence`。
形式化陈述：{V : Type u_5} →   {W : Type u_6} →     [inst : CategoryTheory.Category.{v
_2, u_5} V] →       {FV : V → V → Type u_7} →         {CV : V → Type u_8} →     
      [inst_1 : (X Y : V) → FunLike (FV X Y) (CV X) (CV Y)] →             [inst_
2 : CategoryTheory.ConcreteCategory V FV] →               [inst_3 : CategoryTheo
ry.HasForget₂ V TopCat] →                 [inst_4 : CategoryTheory.Category.{v_3
, u_6} W] →                   {FW : W → W → Type u_9} →                     {CW 
: W → Type u_10} →                       [inst_5 : (X Y : W) → FunLike (FW X Y) 
(CW X) (CW Y)] →                         [inst_6 : CategoryTheory.ConcreteCatego
ry W FW] →                           [inst_7 : CategoryTheory.HasForget₂ W TopCa
t] →                             (G : Type u_11) →                              
 [inst_8 : Monoid G] →                                 [inst_9 : TopologicalSpac
e G] →                                   (E : V ≌ W) →                          
           (∀ (X : ContAction V G), ((E.functor.mapAction G).obj X.obj).IsContin
uous) →                                       (∀ (X : ContAction W G), ((E.inver
se.mapAction G).obj X.obj).IsContinuous) →                                      
   (ContAction V G ≌ ContAction W G)
参数：X Y : V；FV X Y；CV X；CV Y；X Y : W；FW X Y；CW X；CW Y；G : Type u_11；E : V ≌ W；∀ (
X : ContAction V G), ((E.functor.mapAction G).obj X.obj).IsContinuous；∀ (X : Con
tAction W G), ((E.inverse.mapAction G).obj X.obj).IsContinuous；ContAction V G ≌ 
ContAction W G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous version of `Equivalence.mapAction`.
-/
def Equivalence.mapContAction (E : V ≌ W)
    (H₁ : ∀ X : ContAction V G, ((E.functor.mapAction G).obj X.obj).IsContinuous)
    (H₂ : ∀ X : ContAction W G, ((E.inverse.mapAction G).obj X.obj).IsContinuous) :
    ContAction V G ≌ ContAction W G where
  functor := E.functor.mapContAction G H₁
  inverse := E.inverse.mapContAction G H₂
  unitIso := Functor.mapContActionCongr G E.unitIso
      (fun X ↦ X.2) (fun X ↦ H₂ ((E.functor.mapContAction G H₁).obj X)) ≪≫
    Functor.mapContActionComp G _ _ _ _
  counitIso := (Functor.mapContActionComp G _ _ _ _).symm ≪≫
    Functor.mapContActionCongr G E.counitIso _ (fun X ↦ X.2)

end CategoryTheory

