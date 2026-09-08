/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Andrew Yang
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# functors between categories of sheaves

Show that the pushforward of a sheaf is a sheaf, and define
the pushforward functor from the category of C-valued sheaves
on X to that of sheaves on Y, given a continuous map between
topological spaces X and Y.

## Main definitions
- `TopCat.Sheaf.pushforward`:
    The pushforward functor between sheaf categories over topological spaces.
- `TopCat.Sheaf.pullback`: The pullback functor between sheaf categories over topological spaces.
- `TopCat.Sheaf.pullbackPushforwardAdjunction`:
  The adjunction between pullback and pushforward for sheaves on topological spaces.

-/

@[expose] public section


noncomputable section

universe w v u

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

open scoped AlgebraicGeometry

variable {C : Type u} [Category.{v} C]
variable {X Y : TopCat.{w}} (f : X ⟶ Y)
variable ⦃ι : Type w⦄ {U : ι → Opens Y}

namespace TopCat

namespace Sheaf

open Presheaf

/-- The pushforward of a sheaf (by a continuous map) is a sheaf.
-/
/-
**TopCat.Sheaf.pushforward_sheaf_of_sheaf** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Shea
f`。
形式化陈述：pushforward_sheaf_of_sheaf {F : X.Presheaf C} (h : F.IsSheaf) : (f _* F).I
sSheaf
参数：h : F.IsSheaf。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.op_comp_isSheaf`：op_comp_isSheaf [Functor.IsConti
nuous F J K] (G : Sheaf K A) : Presheaf.IsSheaf J (F.op ⋙ G.obj)
· 使用定理 `instIsContinuousOpensCarrierMapGrothendieckTopology`：∀ {X Y : TopCat} (f
 : X ⟶ Y),   (TopologicalSpace.Opens.map f).IsContinuous (Opens.grothendieckTopo
logy ↑Y) (Opens.grothendieckTopology ↑X)

--- 原说明 ---
The pushforward of a sheaf (by a continuous map) is a sheaf.
-/
theorem pushforward_sheaf_of_sheaf {F : X.Presheaf C} (h : F.IsSheaf) : (f _* F).IsSheaf :=
  (Opens.map f).op_comp_isSheaf _ _ ⟨_, h⟩

variable (C)

/-- The pushforward functor.
-/
/-
**TopCat.Sheaf.pushforward** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Sheaf`。
形式化陈述：pushforward (f : X ⟶ Y) : X.Sheaf C ⥤ Y.Sheaf C
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsContinuousOpensCarrierMapGrothendieckTopology`：∀ {X Y : TopCat} (f
 : X ⟶ Y),   (TopologicalSpace.Opens.map f).IsContinuous (Opens.grothendieckTopo
logy ↑Y) (Opens.grothendieckTopology ↑X)

--- 原说明 ---
The pushforward functor.
-/
def pushforward (f : X ⟶ Y) : X.Sheaf C ⥤ Y.Sheaf C :=
  (Opens.map f).sheafPushforwardContinuous _ _ _
/-
**TopCat.Sheaf.pushforward_forget** 是 Mathlib 中的一个引理，位于命名空间 `TopCat.Sheaf`。
形式化陈述：pushforward_forget (f : X ⟶ Y) : pushforward C f ⋙ forget C Y = forget C X
 ⋙ Presheaf.pushforward C f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pushforward_forget (f : X ⟶ Y) :
    pushforward C f ⋙ forget C Y = forget C X ⋙ Presheaf.pushforward C f := rfl

/--
Pushforward of sheaves is isomorphic (actually definitionally equal) to pushforward of presheaves.
-/
/-
**TopCat.Sheaf.pushforwardForgetIso** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Sheaf`。
形式化陈述：pushforwardForgetIso (f : X ⟶ Y) : pushforward C f ⋙ forget C Y ≅ forget C
 X ⋙ Presheaf.pushforward C f
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pushforward of sheaves is isomorphic (actually definitionally equal) to pushforw
ard of presheaves.
-/
def pushforwardForgetIso (f : X ⟶ Y) :
    pushforward C f ⋙ forget C Y ≅ forget C X ⋙ Presheaf.pushforward C f := Iso.refl _

variable {C}
/-
**TopCat.Sheaf.pushforward_obj_val** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Sheaf`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : TopCat} (f
 : X ⟶ Y) (F : TopCat.Sheaf C X),   ((TopCat.Sheaf.pushforward C f).obj F).obj =
 (TopCat.Presheaf.pushforward C f).obj F.obj
参数：f : X ⟶ Y；F : TopCat.Sheaf C X；(TopCat.Sheaf.pushforward C f).obj F；TopCat.Pr
esheaf.pushforward C f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pushforward_obj_val (f : X ⟶ Y) (F : X.Sheaf C) :
    ((pushforward C f).obj F).1 = f _* F.1 := rfl
/-
**TopCat.Sheaf.pushforward_map** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Sheaf`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : TopCat} (f
 : X ⟶ Y) {F F' : TopCat.Sheaf C X}   (α : F ⟶ F'), ((TopCat.Sheaf.pushforward C
 f).map α).hom = (TopCat.Presheaf.pushforward C f).map α.hom
参数：f : X ⟶ Y；α : F ⟶ F'；(TopCat.Sheaf.pushforward C f).map α；TopCat.Presheaf.pus
hforward C f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pushforward_map (f : X ⟶ Y) {F F' : X.Sheaf C} (α : F ⟶ F') :
    ((pushforward C f).map α).1 = (Presheaf.pushforward C f).map α.1 := rfl

variable (A : Type*) [Category.{w} A] {FA : A → A → Type*} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA] [HasColimits A]
variable [HasLimits A] [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

/--
The pullback functor.
-/
/-
**TopCat.Sheaf.pullback** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Sheaf`。
形式化陈述：pullback (f : X ⟶ Y) : Y.Sheaf A ⥤ X.Sheaf A
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsContinuousOpensCarrierMapGrothendieckTopology`：∀ {X Y : TopCat} (f
 : X ⟶ Y),   (TopologicalSpace.Opens.map f).IsContinuous (Opens.grothendieckTopo
logy ↑Y) (Opens.grothendieckTopology ↑X)

--- 原说明 ---
The pullback functor.
-/
def pullback (f : X ⟶ Y) : Y.Sheaf A ⥤ X.Sheaf A :=
  (Opens.map f).sheafPullback _ _ _

/--
The pullback of a sheaf is isomorphic (actually definitionally equal) to the sheafification
of the pullback as a presheaf.
-/
/-
**TopCat.Sheaf.pullbackIso** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Sheaf`。
形式化陈述：pullbackIso (f : X ⟶ Y) : pullback A f ≅ forget A Y ⋙ Presheaf.pullback A 
f ⋙ presheafToSheaf _ _
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsContinuousOpensCarrierMapGrothendieckTopology`：∀ {X Y : TopCat} (f
 : X ⟶ Y),   (TopologicalSpace.Opens.map f).IsContinuous (Opens.grothendieckTopo
logy ↑Y) (Opens.grothendieckTopology ↑X)

--- 原说明 ---
The pullback of a sheaf is isomorphic (actually definitionally equal) to the she
afification
of the pullback as a presheaf.
-/
def pullbackIso (f : X ⟶ Y) :
    pullback A f ≅ forget A Y ⋙ Presheaf.pullback A f ⋙ presheafToSheaf _ _ :=
  Functor.sheafPullbackConstruction.sheafPullbackIso _ _ _ _

/-- The adjunction between pullback and pushforward for sheaves on topological spaces. -/
/-
**TopCat.Sheaf.pullbackPushforwardAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.S
heaf`。
形式化陈述：pullbackPushforwardAdjunction (f : X ⟶ Y) : pullback A f ⊣ pushforward A f
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsContinuousOpensCarrierMapGrothendieckTopology`：∀ {X Y : TopCat} (f
 : X ⟶ Y),   (TopologicalSpace.Opens.map f).IsContinuous (Opens.grothendieckTopo
logy ↑Y) (Opens.grothendieckTopology ↑X)

--- 原说明 ---
The adjunction between pullback and pushforward for sheaves on topological space
s.
-/
def pullbackPushforwardAdjunction (f : X ⟶ Y) :
    pullback A f ⊣ pushforward A f :=
  (Opens.map f).sheafAdjunctionContinuous _ _ _
/-
**TopCat.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (pullback A f).IsLeftAdjoint := (pullbackPushforwardAdjunction A f).isLeftAdjoint
/-
**TopCat.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (pushforward A f).IsRightAdjoint := (pullbackPushforwardAdjunction A f).isRightAdjoint

end Sheaf

end TopCat

namespace Topology.IsOpenEmbedding

open TopCat Sheaf

variable (A : Type*) [Category.{w} A]
variable {f : X ⟶ Y} (hf : IsOpenEmbedding f)

/--
The "naive" sheaf pullback by an open embedding `f`: on the underlying presheaf, this is just
composition by the functor `IsOpenMap.functor f` (sending an open `U` to `f '' U`).
-/
/-
**Topology.IsOpenEmbedding.sheafPullback** 是 Mathlib 中的一个定义，位于命名空间 `Topology.IsO
penEmbedding`。
形式化陈述：sheafPullback : Y.Sheaf A ⥤ X.Sheaf A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsOpenEmbedding.functor_isContinuous`：Topology.IsOpenEmbedding.
functor_isContinuous (h : IsOpenEmbedding f) : h.functor.IsContinuous (Opens.gro
thendieckTopology X) (Opens.grothen…

--- 原说明 ---
The "naive" sheaf pullback by an open embedding `f`: on the underlying presheaf,
 this is just
composition by the functor `IsOpenMap.functor f` (sending an open `U` to `f '' U
`).
-/
def sheafPullback : Y.Sheaf A ⥤ X.Sheaf A :=
  haveI := Topology.IsOpenEmbedding.functor_isContinuous hf
  hf.functor.sheafPushforwardContinuous _ _ _

variable {FA : A → A → Type*} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA] [HasColimits A]
variable [HasLimits A] [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
The pullback of a sheaf by an open embedding `f` is isomorphic to its naive pullback
`IsOpenEmbedding.sheafPullback`, i.e. to the composition by the functor `IsOpenMap.functor f`.
Also, this is an isomorphism of functors.
-/
/-
**Topology.IsOpenEmbedding.sheafPullbackIso** 是 Mathlib 中的一个定义，位于命名空间 `Topology.
IsOpenEmbedding`。
形式化陈述：sheafPullbackIso : Sheaf.pullback A f ≅ hf.sheafPullback A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a sheaf by an open embedding `f` is isomorphic to its naive pull
back
`IsOpenEmbedding.sheafPullback`, i.e. to the composition by the functor `IsOpenM
ap.functor f`.
Also, this is an isomorphism of functors.
-/
def sheafPullbackIso : Sheaf.pullback A f ≅ hf.sheafPullback A := by
  refine Sheaf.pullbackIso A f ≪≫ NatIso.ofComponents (fun F ↦ ?_) (fun u ↦ ?_)
  · exact (presheafToSheaf (Opens.grothendieckTopology ↑X) A).mapIso
      (hf.isOpenMap.pullbackIso.app _) ≪≫
      (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) A).preimageIso
      (isoSheafify (Opens.grothendieckTopology X)
      (TopCat.Presheaf.isSheaf_of_isOpenEmbedding hf F.2)).symm
  · dsimp
    rw [← Functor.map_comp_assoc, hf.isOpenMap.pullbackIso.hom.naturality, Sheaf.hom_ext_iff]
    simp only [Functor.whiskeringLeft_obj_obj, Functor.whiskeringLeft_obj_map, Functor.map_comp,
      isoSheafify_inv, Category.assoc]
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom]
    dsimp [sheafPullback, Functor.sheafPushforwardContinuous, Sheaf.forget]
    simp only [sheafifyMap_sheafifyLift, Category.comp_id, sheafifyMap_sheafifyLift_assoc]
    rw [CategoryTheory.sheafifyLift_comp]

end Topology.IsOpenEmbedding

