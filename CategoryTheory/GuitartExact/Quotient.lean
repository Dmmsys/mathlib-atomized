/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.RightHomotopy
public import Mathlib.CategoryTheory.GuitartExact.Opposite

/-!
# Guitart exact squares and quotient categories

Consider a commutative square of categories given by a natural isomorphism
`e : T ⋙ R ≅ L ⋙ B`:
```
      T
 C₀ ----> H₀
 |        |
L|        |R
 v        v
 C  ----> H
      B
```

If both `T` and `B` are full and `T` is essentially surjective, we show
that the `2`-square above is Guitart exact if, whenever two morphisms
`f₀` and `f₁` in `L.obj X₀ ⟶ Y` (for `X₀ : C₀` and `Y : C`) become equal
after applying `B`, there exists a precylinder object `P` of `X₀`
such that `T.map P.i₀ = T.map i₁` and there exists a left homotopy
between `f₀` and `f₁` for `P.map L`. The dual result is also obtained.

This result shall be applied in the situation where `C₀` is a suitable
full subcategory of a category `C` of homological complexes, and `H₀` and `H`
are the corresponding homotopy categories (TODO @joelriou).

-/

public section

namespace CategoryTheory.TwoSquare.GuitartExact

open HomotopicalAlgebra Opposite

variable {C₀ C H₀ H : Type*} [Category* C₀] [Category* C] [Category* H₀] [Category* H]
  {T : C₀ ⥤ H₀} {L : C₀ ⥤ C} {R : H₀ ⥤ H} {B : C ⥤ H}
  [T.EssSurj] [T.Full] [B.Full]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.TwoSquare.GuitartExact.quotient_of_nonempty_leftHomotopy** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.TwoSquare.GuitartExact`。
形式化陈述：quotient_of_nonempty_leftHomotopy (e : T ⋙ R ≅ L ⋙ B) (he : forall ⦃X₀ : C
₀⦄ ⦃Y : C⦄ (f₀ f₁ : L.obj X₀ ⟶ Y) (_ : B.map f₀ = B.map f₁), exists (P : Precyli
nder X₀), T.map P.i₀ = T.map P.i₁ ∧ Nonempty ((P.map L).LeftHomotopy f₀ f₁)) : G
uitartExact e.hom
参数：e : T ⋙ R ≅ L ⋙ B；he : forall ⦃X₀ : C₀⦄ ⦃Y : C⦄ (f₀ f₁ : L.obj X₀ ⟶ Y) (_ : B
.map f₀ = B.map f₁), exists (P : Precylinder X₀), T.map P.i₀ = T.map P.i₁ ∧ None
mpty ((P.map L).LeftHomotopy f₀ f₁)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.TwoSquare.guitartExact_iff_isConnected_downwards`：guitart
Exact_iff_isConnected_downwards : w.GuitartExact ↔ forall {X₂ : C₂} {X₃ : C₃} (g
 : R.obj X₂ ⟶ B.obj X₃), IsConnected (w.CostructuredA…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.map_inv_hom_id_assoc`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1,
 u_1} D]   {X Y : C} (e : X ≅…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.zigzag_isConnected`：zigzag_isConnected [Nonempty J] (h : 
forall j₁ j₂ : J, Zigzag j₁ j₂) : IsConnected J
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatIso.naturality_1`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.StructuredArrow.Hom.w`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   {S : D} {T : Categ…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `HomotopicalAlgebra.Precylinder.LeftHomotopy.h₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X : C} {P : HomotopicalAlgebra.Precylinder X} 
{Y : C}   {f g : X ⟶ Y} (self : P.Le…
· 使用定理 `CategoryTheory.Zigzag.of_inv`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J} (f : j₂ ⟶ j₁), CategoryTheory.Zigzag j₁ j₂
· 使用定理 `CategoryTheory.Zigzag.of_hom`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J} (f : j₁ ⟶ j₂), CategoryTheory.Zigzag j₁ j₂
· 使用定理 `HomotopicalAlgebra.Precylinder.LeftHomotopy.h₁`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X : C} {P : HomotopicalAlgebra.Precylinder X} 
{Y : C}   {f g : X ⟶ Y} (self : P.Le…
-/
lemma quotient_of_nonempty_leftHomotopy (e : T ⋙ R ≅ L ⋙ B)
    (he : ∀ ⦃X₀ : C₀⦄ ⦃Y : C⦄ (f₀ f₁ : L.obj X₀ ⟶ Y) (_ : B.map f₀ = B.map f₁),
      ∃ (P : Precylinder X₀), T.map P.i₀ = T.map P.i₁ ∧
        Nonempty ((P.map L).LeftHomotopy f₀ f₁)) :
    GuitartExact e.hom := by
  rw [guitartExact_iff_isConnected_downwards]
  intro Y₀ X g
  let X₀ := T.objPreimage Y₀
  let e₀ : T.obj X₀ ≅ Y₀ := T.objObjPreimageIso Y₀
  let S := { f : L.obj X₀ ⟶ X // B.map f = e.inv.app X₀ ≫ R.map e₀.hom ≫ g }
  let Z (s : S) : CostructuredArrowDownwards e.hom g :=
    CostructuredArrowDownwards.mk _ _ X₀ e₀.inv s.val (by simp [s.property])
  have : Nonempty (CostructuredArrowDownwards e.hom g) := by
    obtain ⟨f, hf⟩ := B.map_surjective (e.inv.app _ ≫ R.map e₀.hom ≫ g)
    exact ⟨Z ⟨f, hf⟩⟩
  refine zigzag_isConnected (fun A₀ A₁ ↦ ?_)
  have H (A : CostructuredArrowDownwards e.hom g) : ∃ s, Nonempty (Z s ⟶ A) := by
    obtain ⟨a, ha⟩ := T.map_surjective (e₀.hom ≫ A.left.hom)
    refine ⟨⟨L.map a ≫ A.hom.right, ?_⟩,
      ⟨CostructuredArrow.homMk (StructuredArrow.homMk a ?_)⟩⟩
    · simp [← dsimp% NatIso.naturality_1 e a, ha, dsimp% A.hom.w]
    · cat_disch
  obtain ⟨s₀, ⟨f₀⟩⟩ := H A₀
  obtain ⟨s₁, ⟨f₁⟩⟩ := H A₁
  obtain ⟨P, hP, ⟨h⟩⟩ := he s₀.val s₁.val (by simp [s₀.property, s₁.property])
  let Z' : CostructuredArrowDownwards e.hom g :=
    CostructuredArrowDownwards.mk _ _ P.I (e₀.inv ≫ T.map P.i₀) h.h (by
      simp [R.map_comp, ← B.map_comp, dsimp% h.h₀, s₀.property,
        dsimp% e.hom.naturality_assoc P.i₀])
  calc
    Zigzag A₀ (Z s₀) := .of_inv f₀
    Zigzag (Z s₀) Z' := .of_hom <|
      CostructuredArrow.homMk (StructuredArrow.homMk P.i₀) (by simp [Z, Z', dsimp% h.h₀])
    Zigzag Z' (Z s₁) := .of_inv <|
      CostructuredArrow.homMk (StructuredArrow.homMk P.i₁) (by simp [Z, Z', dsimp% h.h₁])
    Zigzag (Z s₁) A₁ := .of_hom f₁

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.TwoSquare.GuitartExact.quotient_of_nonempty_rightHomotopy** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.TwoSquare.GuitartExact`。
形式化陈述：quotient_of_nonempty_rightHomotopy (e : T ⋙ R ≅ L ⋙ B) (he : forall ⦃X : C
⦄ ⦃Y₀ : C₀⦄ (f₀ f₁ : X ⟶ L.obj Y₀) (_ : B.map f₀ = B.map f₁), exists (P : Prepat
hObject Y₀), T.map P.p₀ = T.map P.p₁ ∧ Nonempty ((P.map L).RightHomotopy f₀ f₁))
 : GuitartExact e.inv
参数：e : T ⋙ R ≅ L ⋙ B；he : forall ⦃X : C⦄ ⦃Y₀ : C₀⦄ (f₀ f₁ : X ⟶ L.obj Y₀) (_ : B
.map f₀ = B.map f₁), exists (P : PrepathObject Y₀), T.map P.p₀ = T.map P.p₁ ∧ No
nempty ((P.map L).RightHomotopy f₀ f₁)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.TwoSquare.guitartExact_op_iff`：guitartExact_op_iff : w.op
.GuitartExact ↔ w.GuitartExact
· 使用引理 `CategoryTheory.TwoSquare.GuitartExact.quotient_of_nonempty_leftHomotopy`
：quotient_of_nonempty_leftHomotopy (e : T ⋙ R ≅ L ⋙ B) (he : forall ⦃X₀ : C₀⦄ ⦃Y
 : C⦄ (f₀ f₁ : L.obj X₀ ⟶ Y) (_ : B.map f₀ = B.map f₁), exist…
· 使用定理 `CategoryTheory.Functor.instEssSurjOppositeOp`：∀ (C : Type u₁) [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] (D : Type u₂) [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instFullOppositeOp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
-/
lemma quotient_of_nonempty_rightHomotopy (e : T ⋙ R ≅ L ⋙ B)
    (he : ∀ ⦃X : C⦄ ⦃Y₀ : C₀⦄ (f₀ f₁ : X ⟶ L.obj Y₀) (_ : B.map f₀ = B.map f₁),
      ∃ (P : PrepathObject Y₀), T.map P.p₀ = T.map P.p₁ ∧
        Nonempty ((P.map L).RightHomotopy f₀ f₁)) :
    GuitartExact e.inv := by
  rw [← guitartExact_op_iff]
  let e' : T.op ⋙ R.op ≅ L.op ⋙ B.op := NatIso.op e.symm
  refine quotient_of_nonempty_leftHomotopy e' (fun X₀ Y f₀ f₁ h ↦ ?_)
  obtain ⟨P, hP, ⟨h⟩⟩ := he f₀.unop f₁.unop (Quiver.Hom.op_inj h)
  exact ⟨P.op, Quiver.Hom.unop_inj hP, ⟨h.op⟩⟩

end CategoryTheory.TwoSquare.GuitartExact

