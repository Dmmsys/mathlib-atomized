/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
/-!

# The constant sheaf

We define the constant sheaf functor (the sheafification of the constant presheaf)
`constantSheaf : D ⥤ Sheaf J D` and prove that it is left adjoint to evaluation at a terminal
object (see `constantSheafAdj`).

We also define a predicate on sheaves, `Sheaf.IsConstant`, saying that a sheaf is in the
essential image of the constant sheaf functor.

## Main results

* `Sheaf.isConstant_iff_isIso_counit_app`: Provided that the constant sheaf functor is fully
  faithful, a sheaf is constant if and only if the counit of the constant sheaf adjunction applied
  to it is an isomorphism.

* `Sheaf.isConstant_iff_of_equivalence` : The property of a sheaf of being constant is invariant
  under equivalence of sheaf categories.

* `Sheaf.isConstant_iff_forget` : Given a "forgetful" functor `U : D ⥤ B` a sheaf `F : Sheaf J D` is
  constant if and only if the sheaf given by postcomposition with `U` is constant.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite Category CategoryTheory.Functor Sheaf Adjunction

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
variable (D : Type*) [Category* D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The constant presheaf functor is left adjoint to evaluation at a terminal object. -/
@[simps! unit_app counit_app_app]
/-
**CategoryTheory.constantPresheafAdj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：constantPresheafAdj {T : C} (hT : IsTerminal T) : Functor.const Cᵒᵖ ⊣ (eva
luation Cᵒᵖ D).obj (op T) where unit
参数：hT : IsTerminal T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant presheaf functor is left adjoint to evaluation at a terminal object
.
-/
noncomputable def constantPresheafAdj {T : C} (hT : IsTerminal T) :
    Functor.const Cᵒᵖ ⊣ (evaluation Cᵒᵖ D).obj (op T) where
  unit := (Functor.constCompEvaluationObj D (op T)).hom
  counit := {
    app := fun F => {
      app := fun ⟨X⟩ => F.map (IsTerminal.from hT X).op
      naturality := fun _ _ _ => by
        simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.id_obj, Functor.const_obj_map,
          Category.id_comp, ← Functor.map_comp]
        congr
        simp }
    naturality := by intros; ext; simp /- Note: `aesop` works but is kind of slow -/ }

variable [HasWeakSheafify J D]

/--
The functor which maps an object of `D` to the constant sheaf at that object, i.e. the
sheafification of the constant presheaf.
-/
/-
**CategoryTheory.constantSheaf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：constantSheaf : D ⥤ Sheaf J D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor which maps an object of `D` to the constant sheaf at that object, i.
e. the
sheafification of the constant presheaf.
-/
noncomputable def constantSheaf : D ⥤ Sheaf J D := Functor.const Cᵒᵖ ⋙ (presheafToSheaf J D)

/-- The constant sheaf functor is left adjoint to evaluation at a terminal object. -/
@[simps! counit_app]
/-
**CategoryTheory.constantSheafAdj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：constantSheafAdj {T : C} (hT : IsTerminal T) : constantSheaf J D ⊣ (sheafS
ections J D).obj (op T)
参数：hT : IsTerminal T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant sheaf functor is left adjoint to evaluation at a terminal object.
-/
noncomputable def constantSheafAdj {T : C} (hT : IsTerminal T) :
    constantSheaf J D ⊣ (sheafSections J D).obj (op T) :=
  (constantPresheafAdj D hT).comp (sheafificationAdjunction J D)

variable {D}

namespace Sheaf

/--
A sheaf is constant if it is in the essential image of the constant sheaf functor.
-/
/-
**CategoryTheory.Sheaf.IsConstant** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Sh
eaf`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     (J 
: CategoryTheory.GrothendieckTopology C) →       {D : Type u_2} →         [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] →           [CategoryTheory.HasWeakShe
afify J D] → CategoryTheory.Sheaf J D → Prop
参数：J : CategoryTheory.GrothendieckTopology C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sheaf is constant if it is in the essential image of the constant sheaf functo
r.
-/
class IsConstant (F : Sheaf J D) : Prop where
  mem_essImage : (constantSheaf J D).essImage F
/-
**CategoryTheory.Sheaf.mem_essImage_of_isConstant** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Sheaf`。
形式化陈述：mem_essImage_of_isConstant (F : Sheaf J D) [IsConstant J F] : (constantShe
af J D).essImage F
参数：F : Sheaf J D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.IsConstant.mem_essImage`：∀ {C : Type u_1} {inst : C
ategoryTheory.Category.{v_1, u_1} C} {J : CategoryTheory.GrothendieckTopology C}
   {D : Type u_2} {inst_1 : Catego…
-/
lemma mem_essImage_of_isConstant (F : Sheaf J D) [IsConstant J F] :
    (constantSheaf J D).essImage F :=
  IsConstant.mem_essImage
/-
**CategoryTheory.Sheaf.isConstant_congr** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Sheaf`。
形式化陈述：isConstant_congr {F G : Sheaf J D} (i : F ≅ G) [IsConstant J F] : IsConsta
nt J G where mem_essImage
参数：i : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.essImage.ofIso`：∀ {C : Type u₁} {D : Type u₂} [in
st : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {F : CategoryTheor…
· 使用引理 `CategoryTheory.Sheaf.mem_essImage_of_isConstant`：mem_essImage_of_isConst
ant (F : Sheaf J D) [IsConstant J F] : (constantSheaf J D).essImage F
-/
lemma isConstant_congr {F G : Sheaf J D} (i : F ≅ G) [IsConstant J F] : IsConstant J G where
  mem_essImage := essImage.ofIso i F.mem_essImage_of_isConstant
/-
**CategoryTheory.Sheaf.isConstant_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Sheaf`。
形式化陈述：isConstant_of_iso {F : Sheaf J D} {X : D} (i : F ≅ (constantSheaf J D).obj
 X) : IsConstant J F
参数：i : F ≅ (constantSheaf J D).obj X。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isConstant_of_iso {F : Sheaf J D} {X : D} (i : F ≅ (constantSheaf J D).obj X) :
    IsConstant J F := ⟨_, ⟨i.symm⟩⟩
/-
**CategoryTheory.Sheaf.isConstant_iff_mem_essImage** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Sheaf`。
形式化陈述：isConstant_iff_mem_essImage {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T
) (adj : L ⊣ (sheafSections J D).obj ⟨T⟩) (F : Sheaf J D) : IsConstant J F ↔ L.e
ssImage F
参数：hT : IsTerminal T；adj : L ⊣ (sheafSections J D).obj ⟨T⟩；F : Sheaf J D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.essImage_eq_of_natIso`：essImage_eq_of_natIso {F' 
: C ⥤ D} (h : F ≅ F') : essImage F = essImage F'
-/
lemma isConstant_iff_mem_essImage {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T)
    (adj : L ⊣ (sheafSections J D).obj ⟨T⟩)
    (F : Sheaf J D) : IsConstant J F ↔ L.essImage F := by
  rw [essImage_eq_of_natIso (adj.leftAdjointUniq (constantSheafAdj J D hT))]
  exact ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩
/-
**CategoryTheory.Sheaf.isConstant_of_isIso_counit_app** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Sheaf`。
形式化陈述：isConstant_of_isIso_counit_app (F : Sheaf J D) [HasTerminal C] [IsIso <| (
constantSheafAdj J D terminalIsTerminal).counit.app F] : IsConstant J F where me
m_essImage
参数：F : Sheaf J D；constantSheafAdj J D terminalIsTerminal。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isConstant_of_isIso_counit_app (F : Sheaf J D) [HasTerminal C]
    [IsIso <| (constantSheafAdj J D terminalIsTerminal).counit.app F] : IsConstant J F where
  mem_essImage := ⟨_, ⟨asIso <| (constantSheafAdj J D terminalIsTerminal).counit.app F⟩⟩
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(constantSheaf J D).Faithful] [(constantSheaf J D).Full] (F : Sheaf J D)
    [IsConstant J F] {T : C} (hT : IsTerminal T) :
    IsIso ((constantSheafAdj J D hT).counit.app F) := by
  rw [isIso_counit_app_iff_mem_essImage]
  exact F.mem_essImage_of_isConstant

/--
If the constant sheaf functor is fully faithful, then a sheaf is constant if and only if the
counit of the constant sheaf adjunction applied to it is an isomorphism.
-/
/-
**CategoryTheory.Sheaf.isConstant_iff_isIso_counit_app** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Sheaf`。
形式化陈述：isConstant_iff_isIso_counit_app [(constantSheaf J D).Faithful] [(constantS
heaf J D).Full] (F : Sheaf J D) {T : C} (hT : IsTerminal T) : IsConstant J F ↔ (
IsIso <| (constantSheafAdj J D hT).counit.app F)
参数：constantSheaf J D；constantSheaf J D；F : Sheaf J D；hT : IsTerminal T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.instIsIsoAppCounitConstantSheafAdjOfFaithfulOfFullC
onstantSheafOfIsConstant`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1,
 u_1} C] (J : CategoryTheory.GrothendieckTopology C)   {D : Type u_2} [inst_1 : 
Catego…

--- 原说明 ---
If the constant sheaf functor is fully faithful, then a sheaf is constant if and
 only if the
counit of the constant sheaf adjunction applied to it is an isomorphism.
-/
lemma isConstant_iff_isIso_counit_app [(constantSheaf J D).Faithful] [(constantSheaf J D).Full]
    (F : Sheaf J D) {T : C} (hT : IsTerminal T) :
      IsConstant J F ↔ (IsIso <| (constantSheafAdj J D hT).counit.app F) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨_, ⟨asIso <| (constantSheafAdj J D hT).counit.app F⟩⟩⟩

/--
A variant of `isConstant_iff_isIso_counit_app` for a general left adjoint to evaluation at a
terminal object.
-/
/-
**CategoryTheory.Sheaf.isConstant_iff_isIso_counit_app'** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Sheaf`。
形式化陈述：isConstant_iff_isIso_counit_app' {L : D ⥤ Sheaf J D} {T : C} (hT : IsTermi
nal T) (adj : L ⊣ (sheafSections J D).obj ⟨T⟩) [L.Faithful] [L.Full] (F : Sheaf 
J D) : IsConstant J F ↔ IsIso (adj.counit.app F)
参数：hT : IsTerminal T；adj : L ⊣ (sheafSections J D).obj ⟨T⟩；F : Sheaf J D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `CategoryTheory.Sheaf.isConstant_iff_mem_essImage`：isConstant_iff_mem_ess
Image {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T) (adj : L ⊣ (sheafSections 
J D).obj ⟨T⟩) (F : Sheaf J D) : IsCons…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.Adjunction.isIso_counit_app_iff_mem_essImage`：isIso_couni
t_app_iff_mem_essImage [L.Faithful] [L.Full] {X : D} : IsIso (h.counit.app X) ↔ 
L.essImage X

--- 原说明 ---
A variant of `isConstant_iff_isIso_counit_app` for a general left adjoint to eva
luation at a
terminal object.
-/
lemma isConstant_iff_isIso_counit_app' {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T)
    (adj : L ⊣ (sheafSections J D).obj ⟨T⟩)
    [L.Faithful] [L.Full] (F : Sheaf J D) : IsConstant J F ↔ IsIso (adj.counit.app F) :=
  (isConstant_iff_mem_essImage J hT adj F).trans (isIso_counit_app_iff_mem_essImage adj).symm

end Sheaf

section Equivalence
variable {C' : Type*} [Category* C'] (K : GrothendieckTopology C') [HasWeakSheafify K D]
variable (G : C ⥤ C') [∀ (X : (C')ᵒᵖ), HasLimitsOfShape (StructuredArrow X G.op) D]
  [G.IsDenseSubsite J K] {T : C} (hT : IsTerminal T) (hT' : IsTerminal (G.obj T))

open IsDenseSubsite

variable (D) in
/--
The constant sheaf functor commutes up to isomorphism the equivalence of sheaf categories induced
by a dense subsite.
-/
/-
**CategoryTheory.equivCommuteConstant** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：equivCommuteConstant : constantSheaf J D ⋙ (sheafEquiv J K G D).functor ≅ 
constantSheaf K D
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsEquivalenceSheafSheafPushfor
wardContinuous`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.
{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (G : Categor…

--- 原说明 ---
The constant sheaf functor commutes up to isomorphism the equivalence of sheaf c
ategories induced
by a dense subsite.
-/
noncomputable def equivCommuteConstant :
    constantSheaf J D ⋙ (sheafEquiv J K G D).functor ≅ constantSheaf K D :=
  ((constantSheafAdj J D hT).comp (sheafEquiv J K G D).toAdjunction).leftAdjointUniq
    (constantSheafAdj K D hT')

variable (D) in
/--
The constant sheaf functor commutes up to isomorphism the inverse equivalence of sheaf categories
induced by a dense subsite.
-/
/-
**CategoryTheory.equivCommuteConstant'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
`。
形式化陈述：equivCommuteConstant' : constantSheaf J D ≅ constantSheaf K D ⋙ (sheafEqui
v J K G D).inverse
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsEquivalenceSheafSheafPushfor
wardContinuous`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.
{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (G : Categor…

--- 原说明 ---
The constant sheaf functor commutes up to isomorphism the inverse equivalence of
 sheaf categories
induced by a dense subsite.
-/
noncomputable def equivCommuteConstant' :
    constantSheaf J D ≅ constantSheaf K D ⋙ (sheafEquiv J K G D).inverse :=
  isoWhiskerLeft (constantSheaf J D) (sheafEquiv J K G D).unitIso ≪≫
    isoWhiskerRight (equivCommuteConstant J D K G hT hT') (sheafEquiv J K G D).inverse

/- TODO: find suitable assumptions for proving generalizations of `equivCommuteConstant` and
`equivCommuteConstant'` above, to commute `constantSheaf` with pullback/pushforward of sheaves. -/

include hT hT' in
/--
The property of a sheaf of being constant is invariant under equivalence of sheaf
categories.
-/
/-
**CategoryTheory.Sheaf.isConstant_iff_of_equivalence** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Sheaf`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (J : Catego
ryTheory.GrothendieckTopology C)   {D : Type u_2} [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} D] [inst_2 : CategoryTheory.HasWeakSheafify J D]   {C' : Type u_3
} [inst_3 : CategoryTheory.Category.{v_3, u_3} C'] (K : CategoryTheory.Grothendi
eckTopology C')   [inst_4 : CategoryTheory.HasWeakSheafify K D] (G : CategoryThe
ory.Functor C C')   [inst_5 : ∀ (X : C'ᵒᵖ), CategoryTheory.Limits.HasLimitsOfSha
pe (CategoryTheory.StructuredArrow X G.op) D]   [inst_6 : CategoryTheory.Functor
.IsDenseSubsite J K G] {T : C} (hT : CategoryTheory.Limits.IsTerminal T)   (hT' 
: CategoryTheory.Limits.IsTerminal (G.obj T)) (F : CategoryTheory.Sheaf K D),   
CategoryTheory.Sheaf.IsConstant J ((CategoryTheory.Functor.IsDenseSubsite.sheafE
quiv J K G D).inverse.obj F) ↔     CategoryTheory.Sheaf.IsConstant K F
参数：J : CategoryTheory.GrothendieckTopology C；K : CategoryTheory.GrothendieckTopo
logy C'；G : CategoryTheory.Functor C C'；X : C'ᵒᵖ；CategoryTheory.StructuredArrow 
X G.op；hT : CategoryTheory.Limits.IsTerminal T；hT' : CategoryTheory.Limits.IsTer
minal (G.obj T)；F : CategoryTheory.Sheaf K D；(CategoryTheory.Functor.IsDenseSubs
ite.sheafEquiv J K G D).inverse.obj F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsEquivalenceSheafSheafPushfor
wardContinuous`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.
{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (G : Categor…

--- 原说明 ---
The property of a sheaf of being constant is invariant under equivalence of shea
f
categories.
-/
lemma Sheaf.isConstant_iff_of_equivalence (F : Sheaf K D) :
    ((sheafEquiv J K G D).inverse.obj F).IsConstant J ↔ IsConstant K F := by
  constructor
  · exact fun ⟨Y, ⟨i⟩⟩ ↦ ⟨_, ⟨(equivCommuteConstant J D K G hT hT').symm.app _ ≪≫
      (sheafEquiv J K G D).functor.mapIso i ≪≫ (sheafEquiv J K G D).counitIso.app _⟩⟩
  · exact fun ⟨Y, ⟨i⟩⟩ ↦ ⟨_, ⟨(equivCommuteConstant' J D K G hT hT').app _ ≪≫
      (sheafEquiv J K G D).inverse.mapIso i⟩⟩

end Equivalence

section Forget

variable {B : Type*} [Category* B] (U : D ⥤ B) [HasWeakSheafify J B]
  [J.PreservesSheafification U] [J.HasSheafCompose U] (F : Sheaf J D)

/--
The constant sheaf functor commutes with `sheafCompose J U` up to isomorphism, provided that `U`
preserves sheafification.
-/
/-
**CategoryTheory.constantCommuteCompose** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y`。
形式化陈述：constantCommuteCompose : constantSheaf J D ⋙ sheafCompose J U ≅ U ⋙ consta
ntSheaf J B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant sheaf functor commutes with `sheafCompose J U` up to isomorphism, p
rovided that `U`
preserves sheafification.
-/
noncomputable def constantCommuteCompose :
    constantSheaf J D ⋙ sheafCompose J U ≅ U ⋙ constantSheaf J B :=
  (isoWhiskerLeft (const Cᵒᵖ)
    (sheafComposeNatIso J U (sheafificationAdjunction J D) (sheafificationAdjunction J B)).symm) ≪≫
      isoWhiskerRight (compConstIso _ _).symm _
/-
**CategoryTheory.constantCommuteCompose_hom_app_hom** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory`。
形式化陈述：constantCommuteCompose_hom_app_hom (X : D) : ((constantCommuteCompose J U)
.hom.app X).hom = (sheafifyComposeIso J U ((const Cᵒᵖ).obj X)).inv ≫ sheafifyMap
 J (constComp Cᵒᵖ X U).hom
参数：X : D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma constantCommuteCompose_hom_app_hom (X : D) : ((constantCommuteCompose J U).hom.app X).hom =
    (sheafifyComposeIso J U ((const Cᵒᵖ).obj X)).inv ≫ sheafifyMap J (constComp Cᵒᵖ X U).hom := rfl

@[deprecated (since := "2026-03-05")]
alias constantCommuteCompose_hom_app_val := constantCommuteCompose_hom_app_hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The counit of `constantSheafAdj` factors through the isomorphism `constantCommuteCompose`. -/
/-
**CategoryTheory.constantSheafAdj_counit_w** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory`。
形式化陈述：constantSheafAdj_counit_w {T : C} (hT : IsTerminal T) : ((constantCommuteC
ompose J U).hom.app (F.obj.obj ⟨T⟩)) ≫ ((constantSheafAdj J B hT).counit.app ((s
heafCompose J U).obj F)) = ((sheafCompose J U).map ((constantSheafAdj J D hT).co
unit.app F))
参数：hT : IsTerminal T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.hom_ext`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Type u₂}   [i
nst_1 : CategoryTh…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.constantCommuteCompose_hom_app_hom`：constantCommuteCompos
e_hom_app_hom (X : D) : ((constantCommuteCompose J U).hom.app X).hom = (sheafify
ComposeIso J U ((const Cᵒᵖ).obj X)).inv…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `CategoryTheory.sheafify_hom_ext`：sheafify_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ :
 sheafify J P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) (h : toSheafify J P ≫ η = toSheaf
ify J P ≫ γ) : η = γ
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.constantSheafAdj_counit_app`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] (J : CategoryTheory.GrothendieckTopology C)  
 (D : Type u_2) [inst_1 : Catego…
· 使用定理 `CategoryTheory.sheafificationAdjunction_counit_app_val`：sheafificationAd
junction_counit_app_val (P : Sheaf J D) : ((sheafificationAdjunction J D).counit
.app P).hom = sheafifyLift J (𝟙 P.obj) P.pro…
· 使用定理 `CategoryTheory.sheafifyMap_sheafifyLift`：sheafifyMap_sheafifyLift {P Q R
 : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (hR : Presheaf.IsSheaf J R) : sheafifyMap J 
η ≫ sheafifyLift J γ hR = she…
· 使用定理 `CategoryTheory.sheafifyLift.congr_simp`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C) {D : Typ
e u_1}   [inst_1 : CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.toSheafify_sheafifyLift`：toSheafify_sheafifyLift {P Q : C
ᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) : toSheafify J P ≫ sheafifyLift 
J η hQ = η
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.sheafComposeIso_hom_fac_assoc`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology C) {A : 
Type u_1}   {B : Type u_2} [inst_1…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The counit of `constantSheafAdj` factors through the isomorphism `constantCommut
eCompose`.
-/
lemma constantSheafAdj_counit_w {T : C} (hT : IsTerminal T) :
    ((constantCommuteCompose J U).hom.app (F.obj.obj ⟨T⟩)) ≫
      ((constantSheafAdj J B hT).counit.app ((sheafCompose J U).obj F)) =
        ((sheafCompose J U).map ((constantSheafAdj J D hT).counit.app F)) := by
  apply Sheaf.hom_ext
  dsimp
  rw [constantCommuteCompose_hom_app_hom, assoc, Iso.inv_comp_eq]
  apply sheafify_hom_ext _ _ _ ((sheafCompose J U).obj F).property
  ext x
  simp [NatTrans.comp_app] -- simp [NatTrans.comp_app] to unfold some definitions
  simp [← map_comp, ← NatTrans.comp_app] -- simp [← NatTrans.comp_app] to simplify some compositions

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Sheaf.isConstant_of_forget** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Sheaf`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (J : Catego
ryTheory.GrothendieckTopology C)   {D : Type u_2} [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} D] [inst_2 : CategoryTheory.HasWeakSheafify J D]   {B : Type u_3}
 [inst_3 : CategoryTheory.Category.{v_3, u_3} B] (U : CategoryTheory.Functor D B
)   [inst_4 : CategoryTheory.HasWeakSheafify J B] [J.PreservesSheafification U] 
[inst_6 : J.HasSheafCompose U]   (F : CategoryTheory.Sheaf J D) [(CategoryTheory
.constantSheaf J D).Faithful] [(CategoryTheory.constantSheaf J D).Full]   [(Cate
goryTheory.constantSheaf J B).Faithful] [(CategoryTheory.constantSheaf J B).Full
]   [(CategoryTheory.sheafCompose J U).ReflectsIsomorphisms]   [CategoryTheory.S
heaf.IsConstant J ((CategoryTheory.sheafCompose J U).obj F)] {T : C}   (hT : Cat
egoryTheory.Limits.IsTerminal T), CategoryTheory.Sheaf.IsConstant J F
参数：J : CategoryTheory.GrothendieckTopology C；U : CategoryTheory.Functor D B；F : 
CategoryTheory.Sheaf J D；CategoryTheory.constantSheaf J D；CategoryTheory.constan
tSheaf J D；CategoryTheory.constantSheaf J B；CategoryTheory.constantSheaf J B；Cat
egoryTheory.sheafCompose J U；(CategoryTheory.sheafCompose J U).obj F；hT : Catego
ryTheory.Limits.IsTerminal T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.constantSheafAdj_counit_w`：constantSheafAdj_counit_w {T :
 C} (hT : IsTerminal T) : ((constantCommuteCompose J U).hom.app (F.obj.obj ⟨T⟩))
 ≫ ((constantSheafAdj J B hT).…
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Sheaf.instIsIsoAppCounitConstantSheafAdjOfFaithfulOfFullC
onstantSheafOfIsConstant`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1,
 u_1} C] (J : CategoryTheory.GrothendieckTopology C)   {D : Type u_2} [inst_1 : 
Catego…
· 使用引理 `CategoryTheory.Sheaf.isConstant_iff_isIso_counit_app`：isConstant_iff_isI
so_counit_app [(constantSheaf J D).Faithful] [(constantSheaf J D).Full] (F : She
af J D) {T : C} (hT : IsTerminal T) : IsCo…
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
-/
lemma Sheaf.isConstant_of_forget [constantSheaf J D |>.Faithful] [constantSheaf J D |>.Full]
    [constantSheaf J B |>.Faithful] [constantSheaf J B |>.Full]
    [(sheafCompose J U).ReflectsIsomorphisms] [((sheafCompose J U).obj F).IsConstant J]
    {T : C} (hT : IsTerminal T) : F.IsConstant J := by
  have : IsIso ((sheafCompose J U).map ((constantSheafAdj J D hT).counit.app F)) := by
    rw [← constantSheafAdj_counit_w]
    infer_instance
  rw [F.isConstant_iff_isIso_counit_app (hT := hT)]
  exact isIso_of_reflects_iso _ (sheafCompose J U)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : F.IsConstant J] : ((sheafCompose J U).obj F).IsConstant J := by
  obtain ⟨Y, ⟨i⟩⟩ := h
  exact ⟨U.obj Y, ⟨(fullyFaithfulSheafToPresheaf _ _).preimageIso
    (((sheafifyComposeIso J U ((const Cᵒᵖ).obj Y)).symm ≪≫
      (presheafToSheaf J B ⋙ sheafToPresheaf J B).mapIso (constComp Cᵒᵖ Y U)).symm ≪≫
        (sheafToPresheaf _ _).mapIso ((sheafCompose J U).mapIso i))⟩⟩
/-
**CategoryTheory.Sheaf.isConstant_iff_forget** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Sheaf`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (J : Catego
ryTheory.GrothendieckTopology C)   {D : Type u_2} [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} D] [inst_2 : CategoryTheory.HasWeakSheafify J D]   {B : Type u_3}
 [inst_3 : CategoryTheory.Category.{v_3, u_3} B] (U : CategoryTheory.Functor D B
)   [inst_4 : CategoryTheory.HasWeakSheafify J B] [J.PreservesSheafification U] 
[inst_6 : J.HasSheafCompose U]   (F : CategoryTheory.Sheaf J D) [(CategoryTheory
.constantSheaf J D).Faithful] [(CategoryTheory.constantSheaf J D).Full]   [(Cate
goryTheory.constantSheaf J B).Faithful] [(CategoryTheory.constantSheaf J B).Full
]   [(CategoryTheory.sheafCompose J U).ReflectsIsomorphisms] {T : C} (hT : Categ
oryTheory.Limits.IsTerminal T),   CategoryTheory.Sheaf.IsConstant J F ↔ Category
Theory.Sheaf.IsConstant J ((CategoryTheory.sheafCompose J U).obj F)
参数：J : CategoryTheory.GrothendieckTopology C；U : CategoryTheory.Functor D B；F : 
CategoryTheory.Sheaf J D；CategoryTheory.constantSheaf J D；CategoryTheory.constan
tSheaf J D；CategoryTheory.constantSheaf J B；CategoryTheory.constantSheaf J B；Cat
egoryTheory.sheafCompose J U；hT : CategoryTheory.Limits.IsTerminal T；(CategoryTh
eory.sheafCompose J U).obj F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instIsConstantObjSheafSheafCompose`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] (J : CategoryTheory.GrothendieckTopolo
gy C)   {D : Type u_2} [inst_1 : Catego…
· 使用定理 `CategoryTheory.Sheaf.isConstant_of_forget`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] (J : CategoryTheory.GrothendieckTopology C)   
{D : Type u_2} [inst_1 : Catego…
-/
lemma Sheaf.isConstant_iff_forget [constantSheaf J D |>.Faithful] [constantSheaf J D |>.Full]
    [constantSheaf J B |>.Faithful] [constantSheaf J B |>.Full]
      [(sheafCompose J U).ReflectsIsomorphisms] {T : C} (hT : IsTerminal T) :
        F.IsConstant J ↔ ((sheafCompose J U).obj F).IsConstant J :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ Sheaf.isConstant_of_forget _ U F hT⟩

end Forget

end CategoryTheory

