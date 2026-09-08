/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Equivalence

/-!

# Localization of the opposite category

If a functor `L : C ⥤ D` is a localization functor for `W : MorphismProperty C`, it
is shown in this file that `L.op : Cᵒᵖ ⥤ Dᵒᵖ` is also a localization functor.

-/

@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Category

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {W : MorphismProperty C}

namespace Localization

/-- If `L : C ⥤ D` satisfies the universal property of the localisation
for `W : MorphismProperty C`, then `L.op` also does. -/
/-
**CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.op** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Localization.StrictUniversalPropertyFixedTarget`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {L
 : CategoryTheory.Functor C D} →           {W : CategoryTheory.MorphismProperty 
C} →             {E : Type u_3} →               [inst_2 : CategoryTheory.Categor
y.{v_3, u_3} E] →                 CategoryTheory.Localization.StrictUniversalPro
pertyFixedTarget L W Eᵒᵖ →                   CategoryTheory.Localization.StrictU
niversalPropertyFixedTarget L.op W.op E
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsInvertedBy.rightOp`：rightOp {W : Morph
ismProperty C} {L : Cᵒᵖ ⥤ D} (h : W.op.IsInvertedBy L) : W.IsInvertedBy L.rightO
p

--- 原说明 ---
If `L : C ⥤ D` satisfies the universal property of the localisation
for `W : MorphismProperty C`, then `L.op` also does.
-/
def StrictUniversalPropertyFixedTarget.op {E : Type*} [Category* E]
    (h : StrictUniversalPropertyFixedTarget L W Eᵒᵖ) :
    StrictUniversalPropertyFixedTarget L.op W.op E where
  inverts := h.inverts.op
  lift F hF := (h.lift F.rightOp hF.rightOp).leftOp
  fac F hF := by
    convert! congr_arg Functor.leftOp (h.fac F.rightOp hF.rightOp)
  uniq F₁ F₂ eq := by
    suffices F₁.rightOp = F₂.rightOp by
      rw [← F₁.rightOp_leftOp_eq, ← F₂.rightOp_leftOp_eq, this]
    have eq' := congr_arg Functor.rightOp eq
    exact h.uniq _ _ eq'
/-
**CategoryTheory.Localization.isLocalization_op** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.Localization`。
形式化陈述：isLocalization_op : W.Q.op.IsLocalization W.op
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLocalization.mk'`：∀ {C : Type u_1} {D : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cate
gory.{v_2, u_2} D] (L : Categor…
-/
instance isLocalization_op : W.Q.op.IsLocalization W.op :=
  Functor.IsLocalization.mk' W.Q.op W.op (strictUniversalPropertyFixedTargetQ W _).op
    (strictUniversalPropertyFixedTargetQ W _).op

end Localization

variable (L W)
variable [L.IsLocalization W]

namespace Functor

/-
**CategoryTheory.Functor.IsLocalization.op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor.IsLocalization`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : CategoryTheory.Functo
r C D)   (W : CategoryTheory.MorphismProperty C) [L.IsLocalization W], L.op.IsLo
calization W.op
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLocalization.of_equivalence_target`：of_equivale
nce_target {E : Type*} [Category* E] (L' : C ⥤ E) (eq : D ≌ E) [L.IsLocalization
 W] (e : L ⋙ eq.functor ≅ L') : L'.IsLocalization…
-/
instance IsLocalization.op : L.op.IsLocalization W.op :=
  IsLocalization.of_equivalence_target W.Q.op W.op L.op (Localization.equivalenceFromModel L W).op
    (NatIso.op (Localization.qCompEquivalenceFromModelFunctorIso L W).symm)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.IsLocalization.unop** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor.IsLocalization`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : CategoryTheory.Functo
r Cᵒᵖ Dᵒᵖ)   (W : CategoryTheory.MorphismProperty Cᵒᵖ) [L.IsLocalization W], L.u
nop.IsLocalization W.unop
参数：L : CategoryTheory.Functor Cᵒᵖ Dᵒᵖ；W : CategoryTheory.MorphismProperty Cᵒᵖ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.IsLocalization.of_equivalences`：of_equivalences (
L₁ : C₁ ⥤ D₁) (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁] (L₂ : C₂ ⥤ D₂) (
W₂ : MorphismProperty C₂) (E : C₁ ≌ C₂) (E'…
· 使用定理 `CategoryTheory.Functor.IsLocalization.op`：∀ {C : Type u_1} {D : Type u_2
} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} D] (L : Categor…
· 使用引理 `CategoryTheory.MorphismProperty.le_isoClosure`：le_isoClosure (P : Morphi
smProperty C) : P <= P.isoClosure
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
-/
instance IsLocalization.unop (L : Cᵒᵖ ⥤ Dᵒᵖ) (W : MorphismProperty Cᵒᵖ)
    [L.IsLocalization W] : L.unop.IsLocalization W.unop :=
  have : CatCommSq (opOpEquivalence C).functor L.op L.unop
    (opOpEquivalence D).functor := ⟨Iso.refl _⟩
  of_equivalences L.op W.op L.unop W.unop
    (opOpEquivalence C) (opOpEquivalence D)
    (fun _ _ _ hf ↦ MorphismProperty.le_isoClosure _ _ hf)
    (fun _ _ _ hf ↦ by
      have := Localization.inverts L W _ hf
      dsimp
      infer_instance)

@[simp]
/-
**CategoryTheory.Functor.IsLocalization.op_iff** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor.IsLocalization`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : CategoryTheory.Functo
r C D)   (W : CategoryTheory.MorphismProperty C), L.op.IsLocalization W.op ↔ L.I
sLocalization W
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLocalization.op`：∀ {C : Type u_1} {D : Type u_2
} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} D] (L : Categor…
-/
lemma IsLocalization.op_iff (L : C ⥤ D) (W : MorphismProperty C) :
    L.op.IsLocalization W.op ↔ L.IsLocalization W :=
  ⟨fun _ ↦ inferInstanceAs (L.op.unop.IsLocalization W.op.unop),
    fun _ ↦ inferInstance⟩

end Functor

namespace Localization

/-
**CategoryTheory.Localization.isoOfHom_unop** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Localization`。
形式化陈述：isoOfHom_unop {X Y : Cᵒᵖ} (w : X ⟶ Y) (hw : W.op w) : (isoOfHom L.op W.op 
w hw).unop = (isoOfHom L W w.unop hw)
参数：w : X ⟶ Y；hw : W.op w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.Functor.IsLocalization.op`：∀ {C : Type u_1} {D : Type u_2
} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} D] (L : Categor…
-/
lemma isoOfHom_unop {X Y : Cᵒᵖ} (w : X ⟶ Y) (hw : W.op w) :
    (isoOfHom L.op W.op w hw).unop = (isoOfHom L W w.unop hw) := by ext; rfl
/-
**CategoryTheory.Localization.isoOfHom_op_inv** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Localization`。
形式化陈述：isoOfHom_op_inv {X Y : Cᵒᵖ} (w : X ⟶ Y) (hw : W.op w) : (isoOfHom L.op W.o
p w hw).inv = (isoOfHom L W w.unop hw).inv.op
参数：w : X ⟶ Y；hw : W.op w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Functor.IsLocalization.op`：∀ {C : Type u_1} {D : Type u_2
} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} D] (L : Categor…
· 使用引理 `CategoryTheory.Localization.isoOfHom_unop`：isoOfHom_unop {X Y : Cᵒᵖ} (w 
: X ⟶ Y) (hw : W.op w) : (isoOfHom L.op W.op w hw).unop = (isoOfHom L W w.unop h
w)
-/
lemma isoOfHom_op_inv {X Y : Cᵒᵖ} (w : X ⟶ Y) (hw : W.op w) :
    (isoOfHom L.op W.op w hw).inv = (isoOfHom L W w.unop hw).inv.op :=
  congr_arg Quiver.Hom.op (congr_arg Iso.inv (isoOfHom_unop L W w hw))

end Localization

end CategoryTheory

