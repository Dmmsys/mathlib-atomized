/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!

# Biproducts in the idempotent completion of a preadditive category

In this file, we define an instance expressing that if `C` is an additive category
(i.e. is preadditive and has finite biproducts), then `Karoubi C` is also an additive category.

We also obtain that for all `P : Karoubi C` where `C` is a preadditive category `C`, there
is a canonical isomorphism `P ⊞ P.complement ≅ (toKaroubi C).obj P.X` in the category
`Karoubi C` where `P.complement` is the formal direct factor of `P.X` corresponding to
the idempotent endomorphism `𝟙 P.X - P.p`.

-/

@[expose] public section


noncomputable section

open CategoryTheory.Category

open CategoryTheory.Limits

open CategoryTheory.Preadditive

universe v

namespace CategoryTheory

namespace Idempotents

namespace Karoubi

variable {C : Type*} [Category.{v} C] [Preadditive C]

namespace Biproducts

/-- The `Bicone` used in order to obtain the existence of
the biproduct of a functor `J ⥤ Karoubi C` when the category `C` is additive. -/
@[simps]
/-
**CategoryTheory.Idempotents.Karoubi.Biproducts.bicone** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Idempotents.Karoubi.Biproducts`。
形式化陈述：bicone [HasFiniteBiproducts C] {J : Type} [Finite J] (F : J -> Karoubi C) 
: Bicone F where pt
参数：F : J -> Karoubi C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Bicone` used in order to obtain the existence of
the biproduct of a functor `J ⥤ Karoubi C` when the category `C` is additive.
-/
def bicone [HasFiniteBiproducts C] {J : Type} [Finite J] (F : J → Karoubi C) : Bicone F where
  pt :=
    { X := biproduct fun j => (F j).X
      p := biproduct.map fun j => (F j).p
      idem := by
        ext
        simp only [assoc, biproduct.map_π, biproduct.map_π_assoc, idem] }
  π j :=
    { f := (biproduct.map fun j => (F j).p) ≫ Bicone.π _ j
      comm := by
        simp only [assoc, biproduct.bicone_π, biproduct.map_π, biproduct.map_π_assoc, (F j).idem] }
  ι j :=
    { f := biproduct.ι (fun j => (F j).X) j ≫ biproduct.map fun j => (F j).p
      comm := by simp only [biproduct.ι_map, assoc, idem_assoc] }
  ι_π j j' := by
    split_ifs with h
    · subst h
      simp only [biproduct.ι_map, biproduct.bicone_π, biproduct.map_π, eqToHom_refl,
        id_f, hom_ext_iff, comp_f, assoc, bicone_ι_π_self_assoc, idem]
    · dsimp
      simp only [biproduct.ι_map, biproduct.map_π, hom_ext_iff, comp_f,
        assoc, biproduct.ι_π_ne_assoc _ h, zero_comp, comp_zero]

end Biproducts

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Idempotents.Karoubi.karoubi_hasFiniteBiproducts** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Idempotents.Karoubi`。
形式化陈述：karoubi_hasFiniteBiproducts [HasFiniteBiproducts C] : HasFiniteBiproducts 
(Karoubi C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasBiproduct_of_total`：hasBiproduct_of_total {f : 
J -> C} (b : Bicone f) (total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.pt) : HasBiproduct 
f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Idempotents.Karoubi.sum_hom`：sum_hom [Preadditive C] {P Q
 : Karoubi C} {α : Type*} (s : Finset α) (f : α -> (P ⟶ Q)) : (∑ x in s, f x).f 
= ∑ x in s, (f x).f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.biproduct.map_π`：∀ {J : Type w} {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C] {f g : J → C} [i…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_map`：∀ {J : Type w} {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C] {f g : J → C} [i…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Idempotents.Karoubi.idem_assoc`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] (self : CategoryTheory.Idempotents.Karoubi
 C) {Z : C}   (h : self.X ⟶ Z),   C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `CategoryTheory.Limits.biproduct.map_eq`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {J : Type}   [i
nst_2 : Fintype J] [inst_3 :…
-/
theorem karoubi_hasFiniteBiproducts [HasFiniteBiproducts C] : HasFiniteBiproducts (Karoubi C) :=
  { out := fun n =>
      { has_biproduct := fun F => by
          apply hasBiproduct_of_total (Biproducts.bicone F)
          simpa using! biproduct.map_eq.symm } }

attribute [instance] karoubi_hasFiniteBiproducts

/-- `P.complement` is the formal direct factor of `P.X` given by the idempotent
endomorphism `𝟙 P.X - P.p` -/
@[simps]
/-
**CategoryTheory.Idempotents.Karoubi.complement** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Idempotents.Karoubi`。
形式化陈述：complement (P : Karoubi C) : Karoubi C where X
参数：P : Karoubi C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P.complement` is the formal direct factor of `P.X` given by the idempotent
endomorphism `𝟙 P.X - P.p`
-/
def complement (P : Karoubi C) : Karoubi C where
  X := P.X
  p := 𝟙 _ - P.p
  idem := idem_of_id_sub_idem P.p P.idem

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Idempotents.Karoubi.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Idempotents.Karoubi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : Karoubi C) : HasBinaryBiproduct P P.complement :=
  hasBinaryBiproduct_of_total
    { pt := P.X
      fst := P.decompId_p
      snd := P.complement.decompId_p
      inl := P.decompId_i
      inr := P.complement.decompId_i
      inl_fst := P.decompId.symm
      inl_snd := by
        simp only [zero_def, hom_ext_iff, complement_X, comp_f,
          decompId_i_f, decompId_p_f, complement_p, comp_sub, comp_id, idem, sub_self]
      inr_fst := by
        simp only [zero_def, hom_ext_iff, complement_X, comp_f,
          decompId_i_f, complement_p, decompId_p_f, sub_comp, id_comp, idem, sub_self]
      inr_snd := P.complement.decompId.symm }
    (by
      ext
      simp only [complement_X, comp_f, decompId_i_f, decompId_p_f, complement_p, add_def, idem,
        comp_sub, comp_id, sub_comp, id_comp, sub_self, sub_zero, add_sub_cancel, id_f])

attribute [-simp] hom_ext_iff

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A formal direct factor `P : Karoubi C` of an object `P.X : C` in a
preadditive category is actually a direct factor of the image `(toKaroubi C).obj P.X`
of `P.X` in the category `Karoubi C` -/
/-
**CategoryTheory.Idempotents.Karoubi.decomposition** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Idempotents.Karoubi`。
形式化陈述：decomposition (P : Karoubi C) : P ⊞ P.complement ≅ (toKaroubi _).obj P.X w
here hom
参数：P : Karoubi C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Idempotents.Karoubi.instHasBinaryBiproductComplement`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C]   (P : CategoryTheory.Idempotents.Karou…

--- 原说明 ---
A formal direct factor `P : Karoubi C` of an object `P.X : C` in a
preadditive category is actually a direct factor of the image `(toKaroubi C).obj
 P.X`
of `P.X` in the category `Karoubi C`
-/
def decomposition (P : Karoubi C) : P ⊞ P.complement ≅ (toKaroubi _).obj P.X where
  hom := biprod.desc P.decompId_i P.complement.decompId_i
  inv := biprod.lift P.decompId_p P.complement.decompId_p
  hom_inv_id := by
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, comp_id, biprod.lift_eq, comp_add, ← decompId_assoc,
        add_eq_left, ← assoc]
      refine (?_ =≫ _).trans zero_comp
      ext
      simp only [comp_f, toKaroubi_obj_X, decompId_i_f, decompId_p_f,
        complement_p, comp_sub, comp_id, idem, sub_self, zero_def]
    · rw [biprod.inr_desc_assoc, comp_id, biprod.lift_eq, comp_add, ← decompId_assoc,
        add_eq_right, ← assoc]
      refine (?_ =≫ _).trans zero_comp
      ext
      simp only [complement_X, comp_f, decompId_i_f, complement_p,
        decompId_p_f, sub_comp, id_comp, idem, sub_self, zero_def]
  inv_hom_id := by
    ext
    simp only [toKaroubi_obj_X, biprod.lift_desc, add_def, comp_f, decompId_p_f, decompId_i_f,
      idem, complement_X, complement_p, comp_sub, comp_id, sub_comp, id_comp, sub_self, sub_zero,
      add_sub_cancel, id_f, toKaroubi_obj_p]

end Karoubi

end Idempotents

end CategoryTheory

