/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.HomEquiv
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Induction principles for structured and costructured arrows

Assume that `L : C ⥤ D` is a localization functor for `W : MorphismProperty C`.
Given `X : C` and a predicate `P` on `StructuredArrow (L.obj X) L`, we obtain
the lemma `Localization.induction_structuredArrow` which shows that `P` holds for
all structured arrows if `P` holds for the identity map `𝟙 (L.obj X)`,
if `P` is stable by post-composition with `L.map f` for any `f`
and if `P` is stable by post-composition with the inverse of `L.map w` when `W w`.

We obtain a similar lemma `Localization.induction_costructuredArrow` for
costructured arrows.

-/

@[expose] public section

namespace CategoryTheory

open Opposite

variable {C D D' : Type*} [Category* C] [Category* D] [Category* D']

namespace Localization

section

variable (W : MorphismProperty C) (L : C ⥤ D) (L' : C ⥤ D')
  [L.IsLocalization W] [L'.IsLocalization W] {X : C}

set_option backward.isDefEq.respectTransparency false in
/-- The bijection `StructuredArrow (L.obj X) L ≃ StructuredArrow (L'.obj X) L'`
when `L` and `L'` are two localization functors for the same class of morphisms. -/
@[simps]
/-
**CategoryTheory.Localization.structuredArrowEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Localization`。
形式化陈述：structuredArrowEquiv : StructuredArrow (L.obj X) L ≃ StructuredArrow (L'.o
bj X) L' where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `StructuredArrow (L.obj X) L ≃ StructuredArrow (L'.obj X) L'`
when `L` and `L'` are two localization functors for the same class of morphisms.
-/
noncomputable def structuredArrowEquiv :
    StructuredArrow (L.obj X) L ≃ StructuredArrow (L'.obj X) L' where
  toFun f := StructuredArrow.mk (homEquiv W L L' f.hom)
  invFun f := StructuredArrow.mk (homEquiv W L' L f.hom)
  left_inv f := by
    obtain ⟨Y, f, rfl⟩ := f.mk_surjective
    dsimp
    rw [← homEquiv_symm_apply, Equiv.symm_apply_apply]
  right_inv f := by
    obtain ⟨Y, f, rfl⟩ := f.mk_surjective
    dsimp
    rw [← homEquiv_symm_apply, Equiv.symm_apply_apply]

end

section

variable (W : MorphismProperty C) {X : C}
  (P : StructuredArrow (W.Q.obj X) W.Q → Prop)

open Construction in
/-
**CategoryTheory.Localization.induction_structuredArrow'** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma induction_structuredArrow'
    (hP₀ : P (StructuredArrow.mk (𝟙 (W.Q.obj X))))
    (hP₁ : ∀ ⦃Y₁ Y₂ : C⦄ (f : Y₁ ⟶ Y₂) (φ : W.Q.obj X ⟶ W.Q.obj Y₁),
      P (StructuredArrow.mk φ) → P (StructuredArrow.mk (φ ≫ W.Q.map f)))
    (hP₂ : ∀ ⦃Y₁ Y₂ : C⦄ (w : Y₁ ⟶ Y₂) (hw : W w) (φ : W.Q.obj X ⟶ W.Q.obj Y₂),
      P (StructuredArrow.mk φ) → P (StructuredArrow.mk (φ ≫ (isoOfHom W.Q W w hw).inv)))
    (g : StructuredArrow (W.Q.obj X) W.Q) : P g := by
  let X₀ : Paths (LocQuiver W) := ⟨X⟩
  suffices ∀ ⦃Y₀ : Paths (LocQuiver W)⦄ (f : X₀ ⟶ Y₀),
      P (StructuredArrow.mk ((Quotient.functor (relations W)).map f)) by
    obtain ⟨Y, g, rfl⟩ := g.mk_surjective
    obtain ⟨g, rfl⟩ := (Quotient.functor (relations W)).map_surjective g
    exact this g
  intro Y₀ f
  induction f with
  | nil => exact hP₀
  | cons f g hf =>
      obtain (g | ⟨w, hw⟩) := g
      · exact hP₁ g _ hf
      · simpa only [← Construction.wInv_eq_isoOfHom_inv w hw] using! hP₂ w hw _ hf

end

section

variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] {X : C}
  (P : StructuredArrow (L.obj X) L → Prop)


set_option backward.isDefEq.respectTransparency false in
@[elab_as_elim]
/-
**CategoryTheory.Localization.induction_structuredArrow** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Localization`。
形式化陈述：induction_structuredArrow (hP₀ : P (StructuredArrow.mk (𝟙 (L.obj X)))) (hP
₁ : forall ⦃Y₁ Y₂ : C⦄ (f : Y₁ ⟶ Y₂) (φ : L.obj X ⟶ L.obj Y₁), P (StructuredArro
w.mk φ) -> P (StructuredArrow.mk (φ ≫ L.map f))) (hP₂ : forall ⦃Y₁ Y₂ : C⦄ (w : 
Y₁ ⟶ Y₂) (hw : W w) (φ : L.obj X ⟶ L.obj Y₂), P (StructuredArrow.mk φ) -> P (Str
ucturedArrow.mk (φ ≫ (isoOfHom L W w hw).inv))) (g : StructuredArrow (L.obj X) L
) : P g
参数：hP₀ : P (StructuredArrow.mk (𝟙 (L.obj X)))；hP₁ : forall ⦃Y₁ Y₂ : C⦄ (f : Y₁ ⟶
 Y₂) (φ : L.obj X ⟶ L.obj Y₁), P (StructuredArrow.mk φ) -> P (StructuredArrow.mk
 (φ ≫ L.map f))；hP₂ : forall ⦃Y₁ Y₂ : C⦄ (w : Y₁ ⟶ Y₂) (hw : W w) (φ : L.obj X ⟶
 L.obj Y₂), P (StructuredArrow.mk φ) -> P (StructuredArrow.mk (φ ≫ (isoOfHom L W
 w hw).inv))；g : StructuredArrow (L.obj X) L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `_private.Mathlib.CategoryTheory.Localization.StructuredArrow.0.CategoryT
heory.Localization.induction_structuredArrow'`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] (W : CategoryTheory.MorphismProperty C) {X : C}   
(P : CategoryTheory.Structu…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Localization.structuredArrowEquiv_apply`：∀ {C : Type u_1}
 {D : Type u_2} {D' : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   
[inst_1 : CategoryTheory.Category.{v_2, u_2}…
· 使用引理 `CategoryTheory.Localization.homEquiv_id`：homEquiv_id : homEquiv W L₁ L₂ 
(𝟙 (L₁.obj X)) = 𝟙 (L₂.obj X)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Localization.homEquiv_comp`：homEquiv_comp (f : L₁.obj X ⟶
 L₁.obj Y) (g : L₁.obj Y ⟶ L₁.obj Z) : homEquiv W L₁ L₂ (f ≫ g) = homEquiv W L₁ 
L₂ f ≫ homEquiv W L₁ L₂ g
· 使用引理 `CategoryTheory.Localization.homEquiv_map`：homEquiv_map (f : X ⟶ Y) : hom
Equiv W L₁ L₂ (L₁.map f) = L₂.map f
· 使用引理 `CategoryTheory.Localization.homEquiv_isoOfHom_inv`：homEquiv_isoOfHom_inv
 (f : Y ⟶ X) (hf : W f) : homEquiv W L₁ L₂ (isoOfHom L₁ W f hf).inv = (isoOfHom 
L₂ W f hf).inv
-/
lemma induction_structuredArrow
    (hP₀ : P (StructuredArrow.mk (𝟙 (L.obj X))))
    (hP₁ : ∀ ⦃Y₁ Y₂ : C⦄ (f : Y₁ ⟶ Y₂) (φ : L.obj X ⟶ L.obj Y₁),
      P (StructuredArrow.mk φ) → P (StructuredArrow.mk (φ ≫ L.map f)))
    (hP₂ : ∀ ⦃Y₁ Y₂ : C⦄ (w : Y₁ ⟶ Y₂) (hw : W w) (φ : L.obj X ⟶ L.obj Y₂),
      P (StructuredArrow.mk φ) → P (StructuredArrow.mk (φ ≫ (isoOfHom L W w hw).inv)))
    (g : StructuredArrow (L.obj X) L) : P g := by
  let P' : StructuredArrow (W.Q.obj X) W.Q → Prop :=
    fun g ↦ P (structuredArrowEquiv W W.Q L g)
  rw [← (structuredArrowEquiv W W.Q L).apply_symm_apply g]
  apply induction_structuredArrow' W P'
  · convert! hP₀
    simp
  · intro Y₁ Y₂ f φ hφ
    convert! hP₁ f (homEquiv W W.Q L φ) hφ
    simp [homEquiv_comp]
  · intro Y₁ Y₂ w hw φ hφ
    convert! hP₂ w hw (homEquiv W W.Q L φ) hφ
    simp [homEquiv_comp, homEquiv_isoOfHom_inv]

end

section

variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] {Y : C}
  (P : CostructuredArrow L (L.obj Y) → Prop)

@[elab_as_elim]
/-
**CategoryTheory.Localization.induction_costructuredArrow** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Localization`。
形式化陈述：induction_costructuredArrow (hP₀ : P (CostructuredArrow.mk (𝟙 (L.obj Y))))
 (hP₁ : forall ⦃X₁ X₂ : C⦄ (f : X₁ ⟶ X₂) (φ : L.obj X₂ ⟶ L.obj Y), P (Costructur
edArrow.mk φ) -> P (CostructuredArrow.mk (L.map f ≫ φ))) (hP₂ : forall ⦃X₁ X₂ : 
C⦄ (w : X₁ ⟶ X₂) (hw : W w) (φ : L.obj X₁ ⟶ L.obj Y), P (CostructuredArrow.mk φ)
 -> P (CostructuredArrow.mk ((isoOfHom L W w hw).inv ≫ φ))) (g : CostructuredArr
ow L (L.obj Y)) : P g
参数：hP₀ : P (CostructuredArrow.mk (𝟙 (L.obj Y)))；hP₁ : forall ⦃X₁ X₂ : C⦄ (f : X₁
 ⟶ X₂) (φ : L.obj X₂ ⟶ L.obj Y), P (CostructuredArrow.mk φ) -> P (CostructuredAr
row.mk (L.map f ≫ φ))；hP₂ : forall ⦃X₁ X₂ : C⦄ (w : X₁ ⟶ X₂) (hw : W w) (φ : L.o
bj X₁ ⟶ L.obj Y), P (CostructuredArrow.mk φ) -> P (CostructuredArrow.mk ((isoOfH
om L W w hw).inv ≫ φ))；g : CostructuredArrow L (L.obj Y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.induction_structuredArrow`：induction_structu
redArrow (hP₀ : P (StructuredArrow.mk (𝟙 (L.obj X)))) (hP₁ : forall ⦃Y₁ Y₂ : C⦄ 
(f : Y₁ ⟶ Y₂) (φ : L.obj X ⟶ L.obj Y₁), P (…
· 使用定理 `CategoryTheory.Functor.IsLocalization.op`：∀ {C : Type u_1} {D : Type u_2
} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} D] (L : Categor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Localization.isoOfHom_op_inv`：isoOfHom_op_inv {X Y : Cᵒᵖ}
 (w : X ⟶ Y) (hw : W.op w) : (isoOfHom L.op W.op w hw).inv = (isoOfHom L W w.uno
p hw).inv.op
-/
lemma induction_costructuredArrow
    (hP₀ : P (CostructuredArrow.mk (𝟙 (L.obj Y))))
    (hP₁ : ∀ ⦃X₁ X₂ : C⦄ (f : X₁ ⟶ X₂) (φ : L.obj X₂ ⟶ L.obj Y),
      P (CostructuredArrow.mk φ) → P (CostructuredArrow.mk (L.map f ≫ φ)))
    (hP₂ : ∀ ⦃X₁ X₂ : C⦄ (w : X₁ ⟶ X₂) (hw : W w) (φ : L.obj X₁ ⟶ L.obj Y),
      P (CostructuredArrow.mk φ) → P (CostructuredArrow.mk ((isoOfHom L W w hw).inv ≫ φ)))
    (g : CostructuredArrow L (L.obj Y)) : P g := by
  let g' := StructuredArrow.mk (T := L.op) (Y := op g.left) g.hom.op
  change P (CostructuredArrow.mk g'.hom.unop)
  induction g' using induction_structuredArrow L.op W.op with
  | hP₀ => exact hP₀
  | hP₁ f φ hφ => exact hP₁ f.unop φ.unop hφ
  | hP₂ w hw φ hφ => simpa [isoOfHom_op_inv L W w hw] using! hP₂ w.unop hw φ.unop hφ

end

end Localization

end CategoryTheory

