/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Shift.ShiftSequence

/-! # Induced shift sequences

When `G : C ⥤ A` is a functor from a category equipped with a shift by a
monoid `M`, we have defined in the file `Mathlib/CategoryTheory/Shift/ShiftSequence.lean`
a type class `G.ShiftSequence M` which provides functors `G.shift a : C ⥤ A` for all `a : M`,
isomorphisms `shiftFunctor C n ⋙ G.shift a ≅ G.shift a'` when `n + a = a'`,
and isomorphisms `G.isoShift a : shiftFunctor C a ⋙ G ≅ G.shift a` for all `a`, all of
which satisfy good coherence properties. The idea is that it allows to use functors
`G.shift a` which may have better definitional properties than `shiftFunctor C a ⋙ G`.
The typical example shall be `[(homologyFunctor C (ComplexShape.up ℤ) 0).ShiftSequence ℤ]`
for any abelian category `C` (TODO).

Similarly as a shift on a category may induce a shift on a quotient or a localized
category (see the file `Mathlib/CategoryTheory/Shift/Induced.lean`), this file shows that
under certain assumptions, there is an induced "shift sequence". The main application
will be the construction of a shift sequence for the homology functor on the
homotopy category of cochain complexes (TODO), and also on the derived category (TODO).

-/

@[expose] public section

open CategoryTheory Category Functor

namespace CategoryTheory

variable {C D A : Type*} [Category* C] [Category* D] [Category* A]
  {L : C ⥤ D} {F : D ⥤ A} {G : C ⥤ A} (e : L ⋙ F ≅ G) (M : Type*)
  [AddMonoid M] [HasShift C M]
  [G.ShiftSequence M] (F' : M → D ⥤ A) (e' : ∀ m, L ⋙ F' m ≅ G.shift m)
  [((whiskeringLeft C D A).obj L).Full] [((whiskeringLeft C D A).obj L).Faithful]

namespace Functor

namespace ShiftSequence

namespace induced

/-- The `isoZero` field of the induced shift sequence. -/
/-
**CategoryTheory.Functor.ShiftSequence.induced.isoZero** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor.ShiftSequence.induced`。
形式化陈述：isoZero : F' 0 ≅ F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `isoZero` field of the induced shift sequence.
-/
noncomputable def isoZero : F' 0 ≅ F :=
  ((whiskeringLeft C D A).obj L).preimageIso (e' 0 ≪≫ G.isoShiftZero M ≪≫ e.symm)
/-
**CategoryTheory.Functor.ShiftSequence.induced.isoZero_hom_app_obj** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Functor.ShiftSequence.induced`。
形式化陈述：isoZero_hom_app_obj (X : C) : (isoZero e M F' e').hom.app (L.obj X) = (e' 
0).hom.app X ≫ (isoShiftZero G M).hom.app X ≫ e.inv.app X
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
-/
lemma isoZero_hom_app_obj (X : C) :
    (isoZero e M F' e').hom.app (L.obj X) =
      (e' 0).hom.app X ≫ (isoShiftZero G M).hom.app X ≫ e.inv.app X :=
  NatTrans.congr_app (((whiskeringLeft C D A).obj L).map_preimage _) X

variable (L G)
variable [HasShift D M] [L.CommShift M]

/-- The `shiftIso` field of the induced shift sequence. -/
/-
**CategoryTheory.Functor.ShiftSequence.induced.shiftIso** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Functor.ShiftSequence.induced`。
形式化陈述：shiftIso (n a a' : M) (ha' : n + a = a') : shiftFunctor D n ⋙ F' a ≅ F' a'
参数：n a a' : M；ha' : n + a = a'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `shiftIso` field of the induced shift sequence.
-/
noncomputable def shiftIso (n a a' : M) (ha' : n + a = a') :
    shiftFunctor D n ⋙ F' a ≅ F' a' := by
  exact ((whiskeringLeft C D A).obj L).preimageIso ((Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (L.commShiftIso n).symm _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (e' a) ≪≫
    G.shiftIso n a a' ha' ≪≫ (e' a').symm)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.ShiftSequence.induced.shiftIso_hom_app_obj** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Functor.ShiftSequence.induced`。
形式化陈述：shiftIso_hom_app_obj (n a a' : M) (ha' : n + a = a') (X : C) : (shiftIso L
 G M F' e' n a a' ha').hom.app (L.obj X) = (F' a).map ((L.commShiftIso n).inv.ap
p X) ≫ (e' a).hom.app (X⟦n⟧) ≫ (G.shiftIso n a a' ha').hom.app X ≫ (e' a').inv.a
pp X
参数：n a a' : M；ha' : n + a = a'；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftIso_hom_app_obj (n a a' : M) (ha' : n + a = a') (X : C) :
    (shiftIso L G M F' e' n a a' ha').hom.app (L.obj X) =
      (F' a).map ((L.commShiftIso n).inv.app X) ≫
        (e' a).hom.app (X⟦n⟧) ≫ (G.shiftIso n a a' ha').hom.app X ≫ (e' a').inv.app X :=
  (NatTrans.congr_app (((whiskeringLeft C D A).obj L).map_preimage _) X).trans (by simp)

attribute [irreducible] isoZero shiftIso

end induced

variable [HasShift D M] [L.CommShift M]

set_option backward.defeqAttrib.useBackward true in
/-- Given an isomorphism of functors `e : L ⋙ F ≅ G` relating functors `L : C ⥤ D`,
`F : D ⥤ A` and `G : C ⥤ A`, an additive monoid `M`, a family of functors `F' : M → D ⥤ A`
equipped with isomorphisms `e' : ∀ m, L ⋙ F' m ≅ G.shift m`, this is the shift sequence
induced on `F` induced by a shift sequence for the functor `G`, provided that
the functor `(whiskeringLeft C D A).obj L` of precomposition by `L` is fully faithful. -/
@[instance_reducible]
/-
**CategoryTheory.Functor.ShiftSequence.induced** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor.ShiftSequence`。
形式化陈述：induced : F.ShiftSequence M where sequence
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an isomorphism of functors `e : L ⋙ F ≅ G` relating functors `L : C ⥤ D`,
`F : D ⥤ A` and `G : C ⥤ A`, an additive monoid `M`, a family of functors `F' : 
M → D ⥤ A`
equipped with isomorphisms `e' : ∀ m, L ⋙ F' m ≅ G.shift m`, this is the shift s
equence
induced on `F` induced by a shift sequence for the functor `G`, provided that
the functor `(whiskeringLeft C D A).obj L` of precomposition by `L` is fully fai
thful.
-/
noncomputable def induced : F.ShiftSequence M where
  sequence := F'
  isoZero := induced.isoZero e M F' e'
  shiftIso := induced.shiftIso L G M F' e'
  shiftIso_zero a := by
    ext1
    apply ((whiskeringLeft C D A).obj L).map_injective
    ext K
    dsimp
    simp only [induced.shiftIso_hom_app_obj, shiftIso_zero_hom_app, id_obj,
      NatTrans.naturality, comp_map, Iso.hom_inv_id_app_assoc,
      comp_id, ← Functor.map_comp, L.commShiftIso_zero, CommShift.isoZero_inv_app, assoc,
      Iso.inv_hom_id_app, Functor.map_id]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext1
    apply ((whiskeringLeft C D A).obj L).map_injective
    ext K
    dsimp
    simp only [id_comp, induced.shiftIso_hom_app_obj,
      G.shiftIso_add_hom_app n m a a' a'' ha' ha'', L.commShiftIso_add,
      comp_obj, CommShift.isoAdd_inv_app, (F' a).map_comp, assoc,
      ← (e' a).hom.naturality_assoc, comp_map]
    simp only [← NatTrans.naturality_assoc, induced.shiftIso_hom_app_obj,
      ← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app, comp_obj,
      Functor.map_id, id_comp]
    dsimp
    simp only [Functor.map_comp, assoc, Iso.inv_hom_id_app_assoc]

@[simp, reassoc]
/-
**CategoryTheory.Functor.ShiftSequence.induced_isoShiftZero_hom_app_obj** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Functor.ShiftSequence`。
形式化陈述：induced_isoShiftZero_hom_app_obj (X : C) : letI
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ShiftSequence.induced.isoZero_hom_app_obj`：isoZer
o_hom_app_obj (X : C) : (isoZero e M F' e').hom.app (L.obj X) = (e' 0).hom.app X
 ≫ (isoShiftZero G M).hom.app X ≫ e.inv.app X
-/
lemma induced_isoShiftZero_hom_app_obj (X : C) :
    letI := (induced e M F' e')
    (F.isoShiftZero M).hom.app (L.obj X) =
      (e' 0).hom.app X ≫ (isoShiftZero G M).hom.app X ≫ e.inv.app X := by
  apply induced.isoZero_hom_app_obj

@[simp, reassoc]
/-
**CategoryTheory.Functor.ShiftSequence.induced_shiftIso_hom_app_obj** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Functor.ShiftSequence`。
形式化陈述：induced_shiftIso_hom_app_obj (n a a' : M) (ha' : n + a = a') (X : C) : let
I
参数：n a a' : M；ha' : n + a = a'；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ShiftSequence.induced.shiftIso_hom_app_obj`：shift
Iso_hom_app_obj (n a a' : M) (ha' : n + a = a') (X : C) : (shiftIso L G M F' e' 
n a a' ha').hom.app (L.obj X) = (F' a).map ((L.commShif…
-/
lemma induced_shiftIso_hom_app_obj (n a a' : M) (ha' : n + a = a') (X : C) :
    letI := (induced e M F' e')
    (F.shiftIso n a a' ha').hom.app (L.obj X) =
      (F.shift a).map ((L.commShiftIso n).inv.app X) ≫ (e' a).hom.app (X⟦n⟧) ≫
        (G.shiftIso n a a' ha').hom.app X ≫ (e' a').inv.app X := by
  apply induced.shiftIso_hom_app_obj

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Functor.ShiftSequence.induced_shiftMap** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor.ShiftSequence`。
形式化陈述：induced_shiftMap {n : M} {X Y : C} (f : X ⟶ Y⟦n⟧) (a a' : M) (h : n + a = 
a') : letI
参数：f : X ⟶ Y⟦n⟧；a a' : M；h : n + a = a'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.Functor.ShiftSequence.induced_shiftIso_hom_app_obj`：induc
ed_shiftIso_hom_app_obj (n a a' : M) (ha' : n + a = a') (X : C) : letI
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
-/
lemma induced_shiftMap {n : M} {X Y : C} (f : X ⟶ Y⟦n⟧) (a a' : M) (h : n + a = a') :
    letI := induced e M F' e'
    F.shiftMap (L.map f ≫ (L.commShiftIso n).hom.app _) a a' h =
      (e' a).hom.app X ≫ G.shiftMap f a a' h ≫ (e' a').inv.app Y := by
  dsimp [shiftMap]
  rw [Functor.map_comp, induced_shiftIso_hom_app_obj, assoc, assoc]
  nth_rw 2 [← Functor.map_comp_assoc]
  simp only [comp_obj, Iso.hom_inv_id_app, map_id, id_comp]
  rw [← NatTrans.naturality_assoc]
  rfl

end ShiftSequence

end Functor

end CategoryTheory

