/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.CatCommSq
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Opposites

/-!
# Localization of adjunctions

In this file, we show that if we have an adjunction `adj : G ⊣ F` such that both
functors `G : C₁ ⥤ C₂` and `F : C₂ ⥤ C₁` induce functors
`G' : D₁ ⥤ D₂` and `F' : D₂ ⥤ D₁` on localized categories, i.e. that we
have localization functors `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` with respect
to morphism properties `W₁` and `W₂` respectively, and 2-commutative diagrams
`[CatCommSq G L₁ L₂ G']` and `[CatCommSq F L₂ L₁ F']`, then we have an
induced adjunction `Adjunction.localization L₁ W₁ L₂ W₂ G' F' : G' ⊣ F'`.

-/

@[expose] public section

namespace CategoryTheory

open Localization Category CategoryTheory.Functor

namespace Adjunction

variable {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} (adj : G ⊣ F)

section

variable (L₁ : C₁ ⥤ D₁) (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂) (W₂ : MorphismProperty C₂) [L₂.IsLocalization W₂]
  (G' : D₁ ⥤ D₂) (F' : D₂ ⥤ D₁)
  [CatCommSq G L₁ L₂ G'] [CatCommSq F L₂ L₁ F']


namespace Localization

/-- Auxiliary definition of the unit morphism for the adjunction `Adjunction.localization` -/
/-
**CategoryTheory.Adjunction.Localization.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Adjunction.Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition of the unit morphism for the adjunction `Adjunction.localiz
ation`
-/
noncomputable def ε : 𝟭 D₁ ⟶ G' ⋙ F' := by
  letI : Lifting L₁ W₁ ((G ⋙ F) ⋙ L₁) (G' ⋙ F') :=
    Lifting.mk (CatCommSq.hComp G F L₁ L₂ L₁ G' F').iso.symm
  exact Localization.liftNatTrans L₁ W₁ L₁ ((G ⋙ F) ⋙ L₁) (𝟭 D₁) (G' ⋙ F')
    (whiskerRight adj.unit L₁)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Adjunction.Localization.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Adjunction.Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ε_app (X₁ : C₁) :
    (ε adj L₁ W₁ L₂ G' F').app (L₁.obj X₁) =
      L₁.map (adj.unit.app X₁) ≫ (CatCommSq.iso F L₂ L₁ F').hom.app (G.obj X₁) ≫
        F'.map ((CatCommSq.iso G L₁ L₂ G').hom.app X₁) := by
  let : Lifting L₁ W₁ ((G ⋙ F) ⋙ L₁) (G' ⋙ F') :=
    Lifting.mk (CatCommSq.hComp G F L₁ L₂ L₁ G' F').iso.symm
  simp only [ε, liftNatTrans_app, Lifting.iso, Iso.symm,
    Functor.id_obj, Functor.comp_obj, Functor.rightUnitor_hom_app,
      whiskerRight_app, CatCommSq.hComp_iso_hom_app, id_comp]

/-- Auxiliary definition of the counit morphism for the adjunction `Adjunction.localization` -/
/-
**CategoryTheory.Adjunction.Localization.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Adjunction.Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition of the counit morphism for the adjunction `Adjunction.local
ization`
-/
noncomputable def η : F' ⋙ G' ⟶ 𝟭 D₂ := by
  letI : Lifting L₂ W₂ ((F ⋙ G) ⋙ L₂) (F' ⋙ G') :=
    Lifting.mk (CatCommSq.hComp F G L₂ L₁ L₂ F' G').iso.symm
  exact liftNatTrans L₂ W₂ ((F ⋙ G) ⋙ L₂) L₂ (F' ⋙ G') (𝟭 D₂) (whiskerRight adj.counit L₂)
/-
**CategoryTheory.Adjunction.Localization.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Adjunction.Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma η_app (X₂ : C₂) :
    (η adj L₁ L₂ W₂ G' F').app (L₂.obj X₂) =
      G'.map ((CatCommSq.iso F L₂ L₁ F').inv.app X₂) ≫
        (CatCommSq.iso G L₁ L₂ G').inv.app (F.obj X₂) ≫
        L₂.map (adj.counit.app X₂) := by
  let : Lifting L₂ W₂ ((F ⋙ G) ⋙ L₂) (F' ⋙ G') :=
    Lifting.mk (CatCommSq.hComp F G L₂ L₁ L₂ F' G').iso.symm
  simp only [η, liftNatTrans_app, Lifting.iso, Iso.symm, CatCommSq.hComp_iso_inv_app,
    whiskerRight_app, Functor.rightUnitor_inv_app, comp_id, assoc]

end Localization

/-- If `adj : G ⊣ F` is an adjunction between two categories `C₁` and `C₂` that
are equipped with localization functors `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` with
respect to `W₁ : MorphismProperty C₁` and `W₂ : MorphismProperty C₂`, and that
the functors `F : C₂ ⥤ C₁` and `G : C₁ ⥤ C₂` induce functors `F' : D₂ ⥤ D₁`
and `G' : D₁ ⥤ D₂` on the localized categories, then the adjunction `adj`
induces an adjunction `G' ⊣ F'`. -/
/-
**CategoryTheory.Adjunction.localization** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Adjunction`。
形式化陈述：localization : G' ⊣ F'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `adj : G ⊣ F` is an adjunction between two categories `C₁` and `C₂` that
are equipped with localization functors `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` with
respect to `W₁ : MorphismProperty C₁` and `W₂ : MorphismProperty C₂`, and that
the functors `F : C₂ ⥤ C₁` and `G : C₁ ⥤ C₂` induce functors `F' : D₂ ⥤ D₁`
and `G' : D₁ ⥤ D₂` on the localized categories, then the adjunction `adj`
induces an adjunction `G' ⊣ F'`.
-/
noncomputable def localization : G' ⊣ F' :=
  Adjunction.mkOfUnitCounit
    { unit := Localization.ε adj L₁ W₁ L₂ G' F'
      counit := Localization.η adj L₁ L₂ W₂ G' F'
      left_triangle := by
        apply natTrans_ext L₁ W₁
        intro X₁
        have eq := adj.left_triangle_components X₁
        rw [NatTrans.comp_app, NatTrans.comp_app, whiskerRight_app, Localization.ε_app,
          Functor.associator_hom_app, id_comp, whiskerLeft_app, G'.map_comp, G'.map_comp,
          assoc, assoc]
        erw [(Localization.η adj L₁ L₂ W₂ G' F').naturality, Localization.η_app,
          assoc, assoc, ← G'.map_comp_assoc, ← G'.map_comp_assoc, assoc, Iso.hom_inv_id_app,
          comp_id, (CatCommSq.iso G L₁ L₂ G').inv.naturality_assoc, ← L₂.map_comp_assoc, eq,
          L₂.map_id, id_comp, Iso.inv_hom_id_app]
        rfl
      right_triangle := by
        apply natTrans_ext L₂ W₂
        intro X₂
        have eq := adj.right_triangle_components X₂
        rw [NatTrans.comp_app, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
          Localization.η_app, Functor.associator_inv_app, id_comp, F'.map_comp, F'.map_comp]
        erw [← (Localization.ε _ _ _ _ _ _).naturality_assoc, Localization.ε_app,
          assoc, assoc, ← F'.map_comp_assoc, Iso.hom_inv_id_app, F'.map_id, id_comp,
          ← NatTrans.naturality, ← L₁.map_comp_assoc, eq, L₁.map_id, id_comp,
          Iso.inv_hom_id_app]
        rfl }

@[simp]
/-
**CategoryTheory.Adjunction.localization_unit_app** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Adjunction`。
形式化陈述：localization_unit_app (X₁ : C₁) : (adj.localization L₁ W₁ L₂ W₂ G' F').uni
t.app (L₁.obj X₁) = L₁.map (adj.unit.app X₁) ≫ (CatCommSq.iso F L₂ L₁ F').hom.ap
p (G.obj X₁) ≫ F'.map ((CatCommSq.iso G L₁ L₂ G').hom.app X₁)
参数：X₁ : C₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.Localization.ε_app`：ε_app (X₁ : C₁) : (ε adj L
₁ W₁ L₂ G' F').app (L₁.obj X₁) = L₁.map (adj.unit.app X₁) ≫ (CatCommSq.iso F L₂ 
L₁ F').hom.app (G.obj X₁) ≫ F'.map…
-/
lemma localization_unit_app (X₁ : C₁) :
    (adj.localization L₁ W₁ L₂ W₂ G' F').unit.app (L₁.obj X₁) =
    L₁.map (adj.unit.app X₁) ≫ (CatCommSq.iso F L₂ L₁ F').hom.app (G.obj X₁) ≫
      F'.map ((CatCommSq.iso G L₁ L₂ G').hom.app X₁) := by
  apply Localization.ε_app

@[simp]
/-
**CategoryTheory.Adjunction.localization_counit_app** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Adjunction`。
形式化陈述：localization_counit_app (X₂ : C₂) : (adj.localization L₁ W₁ L₂ W₂ G' F').c
ounit.app (L₂.obj X₂) = G'.map ((CatCommSq.iso F L₂ L₁ F').inv.app X₂) ≫ (CatCom
mSq.iso G L₁ L₂ G').inv.app (F.obj X₂) ≫ L₂.map (adj.counit.app X₂)
参数：X₂ : C₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.Localization.η_app`：η_app (X₂ : C₂) : (η adj L
₁ L₂ W₂ G' F').app (L₂.obj X₂) = G'.map ((CatCommSq.iso F L₂ L₁ F').inv.app X₂) 
≫ (CatCommSq.iso G L₁ L₂ G').inv.a…
-/
lemma localization_counit_app (X₂ : C₂) :
    (adj.localization L₁ W₁ L₂ W₂ G' F').counit.app (L₂.obj X₂) =
    G'.map ((CatCommSq.iso F L₂ L₁ F').inv.app X₂) ≫
      (CatCommSq.iso G L₁ L₂ G').inv.app (F.obj X₂) ≫
      L₂.map (adj.counit.app X₂) := by
  apply Localization.η_app

end

include adj in
/-
**CategoryTheory.Adjunction.isLocalization** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Adjunction`。
形式化陈述：isLocalization [F.Full] [F.Faithful] : G.IsLocalization ((MorphismProperty
.isomorphisms C₂).inverseImage G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Adjunction.instIsIsoMapAppUnitOfFaithfulOfFull`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.IsLocalization.of_equivalence_target`：of_equivale
nce_target {E : Type*} [Category* E] (L' : C ⥤ E) (eq : D ≌ E) [L.IsLocalization
 W] (e : L ⋙ eq.functor ≅ L') : L'.IsLocalization…
-/
lemma isLocalization [F.Full] [F.Faithful] :
    G.IsLocalization ((MorphismProperty.isomorphisms C₂).inverseImage G) := by
  let W := ((MorphismProperty.isomorphisms C₂).inverseImage G)
  have hG : W.IsInvertedBy G := fun _ _ _ hf => hf
  have : ∀ (X : C₁), IsIso ((whiskerRight adj.unit W.Q).app X) := fun X =>
    Localization.inverts W.Q W _ (by
      change IsIso _
      infer_instance)
  have : IsIso (whiskerRight adj.unit W.Q) := NatIso.isIso_of_isIso_app _
  let e : W.Localization ≌ C₂ := Equivalence.mk (Localization.lift G hG W.Q) (F ⋙ W.Q)
    (liftNatIso W.Q W W.Q (G ⋙ F ⋙ W.Q) _ _
    (W.Q.leftUnitor.symm ≪≫ asIso (whiskerRight adj.unit W.Q)))
    (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Localization.fac G hG W.Q) ≪≫
      asIso adj.counit)
  apply Functor.IsLocalization.of_equivalence_target W.Q W G e
    (Localization.fac G hG W.Q)

include adj in
/-- This is the dual statement to `Adjunction.isLocalization`. -/
/-
**CategoryTheory.Adjunction.isLocalization'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Adjunction`。
形式化陈述：isLocalization' [G.Full] [G.Faithful] : F.IsLocalization ((MorphismPropert
y.isomorphisms C₁).inverseImage F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.IsLocalization.op_iff`：∀ {C : Type u_1} {D : Type
 u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_2} D] (L : Categor…
· 使用引理 `CategoryTheory.MorphismProperty.op_inverseImage`：op_inverseImage (P : Mo
rphismProperty D) (F : C ⥤ D) : (P.inverseImage F).op = P.op.inverseImage F.op
· 使用引理 `CategoryTheory.MorphismProperty.op_isomorphisms`：op_isomorphisms : (isom
orphisms C).op = isomorphisms Cᵒᵖ
· 使用引理 `CategoryTheory.Adjunction.isLocalization`：isLocalization [F.Full] [F.Fai
thful] : G.IsLocalization ((MorphismProperty.isomorphisms C₂).inverseImage G)
· 使用定理 `CategoryTheory.Functor.instFullOppositeOp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instFaithfulOppositeOp`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
This is the dual statement to `Adjunction.isLocalization`.
-/
lemma isLocalization' [G.Full] [G.Faithful] :
    F.IsLocalization ((MorphismProperty.isomorphisms C₁).inverseImage F) := by
  rw [← Functor.IsLocalization.op_iff, MorphismProperty.op_inverseImage,
    MorphismProperty.op_isomorphisms]
  exact adj.op.isLocalization

end Adjunction

end CategoryTheory

