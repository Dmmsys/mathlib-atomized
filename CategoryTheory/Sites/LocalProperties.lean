/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic

/-!
# Local properties of sheaves

In this file we study properties of sheaves that can be checked on a covering family of objects.

## Main results

- `CategoryTheory.Sheaf.isIso_iff_of_coversTop`: A morphism of sheaves is an isomorphism if it
  is one on a cover.
-/
public section

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category* C] {K : GrothendieckTopology C} {A : Type*} [Category* A]

namespace Sheaf

variable {ι : Type*} {X : ι → C}

/-- A sheaf morphism is an isomorphism if it becomes one after pulling back along each
element of a covering family. -/
/-
**CategoryTheory.Sheaf.isIso_of_coversTop** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Sheaf`。
形式化陈述：isIso_of_coversTop (hX : K.CoversTop X) {F G : Sheaf K A} {f : F ⟶ G} (h :
 forall i, IsIso ((K.overPullback A (X i)).map f)) : IsIso f
参数：hX : K.CoversTop X；h : forall i, IsIso ((K.overPullback A (X i)).map f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.isIso_hom_iff`：isIso_hom_iff {X Y : P.Full
Subcategory} (f : X ⟶ Y) : IsIso f.hom ↔ IsIso f
· 使用定理 `CategoryTheory.NatTrans.isIso_iff_isIso_app`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.ObjectProperty.instIsIsoHomFullSubcategory`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C
} {X Y : P.FullSubcategory}   (f : X ⟶ Y) [Cate…
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.hf`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.GrothendieckTop
ology C}   {S : J.Cover X} (self : S.Arr…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.NatTrans.naturality_inv`：naturality_inv {F G : C ⥤ D} (α 
: F ⟶ G) {X Y : C} (f : X ⟶ Y) [IsIso (α.app X)] [IsIso (α.app Y)] : inv (α.app 
X) ≫ F.map f = G.map f ≫ inv…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.Relation.w`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.Grothen
dieckTopology C}   {S : J.Cover X} {I₁ I₂ : S.Ar…
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Ty
pe u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.amalgamate_map`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} 
{A : Type u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.amalgamate_map_assoc`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopolo
gy C} {A : Type u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y

--- 原说明 ---
A sheaf morphism is an isomorphism if it becomes one after pulling back along ea
ch
element of a covering family.
-/
lemma isIso_of_coversTop (hX : K.CoversTop X) {F G : Sheaf K A} {f : F ⟶ G}
    (h : ∀ i, IsIso ((K.overPullback A (X i)).map f)) :
    IsIso f := by
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  have hiso (Z : C) (i : ι) (g : Z ⟶ X i) : IsIso (f.hom.app (op Z)) :=
    (NatTrans.isIso_iff_isIso_app ((K.overPullback A (X i)).map f).hom).mp inferInstance
      (op (Over.mk g))
  intro W
  let S : K.Cover W.unop := hX.cover W.unop
  have harrow (I : S.Arrow) : IsIso (f.hom.app (op I.Y)) := by
    obtain ⟨i, ⟨g⟩⟩ := I.hf
    exact hiso I.Y i g
  let invMap : G.obj.obj (op W.unop) ⟶ F.obj.obj (op W.unop) :=
    F.property.amalgamate S (fun I => G.obj.map I.f.op ≫ inv (f.hom.app (op I.Y))) (by
      intro I₁ I₂ r
      have hZ : IsIso (f.hom.app (op r.Z)) := by
        obtain ⟨i, ⟨g⟩⟩ := I₁.hf
        exact hiso r.Z i (r.g₁ ≫ g)
      simp only [Category.assoc, f.hom.naturality_inv]
      rw [← Category.assoc, ← Category.assoc, ← G.obj.map_comp, ← G.obj.map_comp,
        ← op_comp, ← op_comp, r.w])
  refine ⟨⟨invMap, ?_, ?_⟩⟩
  · refine F.property.hom_ext S _ _ fun I => ?_
    simp only [op_unop, Category.assoc, Category.id_comp]
    rw [Presheaf.IsSheaf.amalgamate_map, ← f.hom.naturality_assoc]
    simp
  · refine G.property.hom_ext S _ _ fun I => ?_
    simp only [op_unop, Category.assoc, Category.id_comp]
    rw [← f.hom.naturality, Presheaf.IsSheaf.amalgamate_map_assoc]
    simp

/-- A sheaf morphism is an isomorphism iff it becomes one after pulling back along each
element of a covering family. -/
/-
**CategoryTheory.Sheaf.isIso_iff_of_coversTop** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Sheaf`。
形式化陈述：isIso_iff_of_coversTop (hX : K.CoversTop X) {F G : Sheaf K A} (f : F ⟶ G) 
: IsIso f ↔ forall i, IsIso ((K.overPullback A (X i)).map f)
参数：hX : K.CoversTop X；f : F ⟶ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Sheaf.isIso_of_coversTop`：isIso_of_coversTop (hX : K.Cove
rsTop X) {F G : Sheaf K A} {f : F ⟶ G} (h : forall i, IsIso ((K.overPullback A (
X i)).map f)) : IsIso f

--- 原说明 ---
A sheaf morphism is an isomorphism iff it becomes one after pulling back along e
ach
element of a covering family.
-/
lemma isIso_iff_of_coversTop (hX : K.CoversTop X) {F G : Sheaf K A} (f : F ⟶ G) :
    IsIso f ↔ ∀ i, IsIso ((K.overPullback A (X i)).map f) :=
  ⟨fun _ _ => inferInstance, fun h => isIso_of_coversTop hX h⟩

end Sheaf

end CategoryTheory

