/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Shift induced from a category to another

In this file, we introduce a sufficient condition on a functor
`F : C ⥤ D` so that a shift on `C` by a monoid `A` induces a shift on `D`.
More precisely, when the functor `(D ⥤ D) ⥤ C ⥤ D` given
by the precomposition with `F` is fully faithful, and that
all the shift functors on `C` can be lifted to functors `D ⥤ D`
(i.e. we have functors `s a : D ⥤ D` for all `a : A`, and isomorphisms
`F ⋙ s a ≅ shiftFunctor C a ⋙ F`), then these functors `s a` are
the shift functors of a term of type `HasShift D A`.

As this condition on the functor `F` is satisfied for quotient and localization
functors, the main construction `HasShift.induced` in this file shall be
used for both quotient and localized shifts.

-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

variable {C D : Type _} [Category* C] [Category* D]
  (F : C ⥤ D) {A : Type _} [AddMonoid A] [HasShift C A]
  (s : A → D ⥤ D) (i : ∀ a, F ⋙ s a ≅ shiftFunctor C a ⋙ F)
  [((whiskeringLeft C D D).obj F).Full] [((whiskeringLeft C D D).obj F).Faithful]

namespace HasShift

namespace Induced

/-- The `zero` field of the `ShiftMkCore` structure for the induced shift. -/
/-
**CategoryTheory.HasShift.Induced.zero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.HasShift.Induced`。
形式化陈述：zero : s 0 ≅ 𝟭 D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `zero` field of the `ShiftMkCore` structure for the induced shift.
-/
noncomputable def zero : s 0 ≅ 𝟭 D :=
  ((whiskeringLeft C D D).obj F).preimageIso ((i 0) ≪≫
    isoWhiskerRight (shiftFunctorZero C A) F ≪≫ F.leftUnitor ≪≫ F.rightUnitor.symm)

/-- The `add` field of the `ShiftMkCore` structure for the induced shift. -/
/-
**CategoryTheory.HasShift.Induced.add** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
HasShift.Induced`。
形式化陈述：add (a b : A) : s (a + b) ≅ s a ⋙ s b
参数：a b : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `add` field of the `ShiftMkCore` structure for the induced shift.
-/
noncomputable def add (a b : A) : s (a + b) ≅ s a ⋙ s b :=
  ((whiskeringLeft C D D).obj F).preimageIso
    (i (a + b) ≪≫ isoWhiskerRight (shiftFunctorAdd C a b) F ≪≫
      Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (i b).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (i a).symm _ ≪≫ Functor.associator _ _ _)

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.HasShift.Induced.zero_hom_app_obj** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.HasShift.Induced`。
形式化陈述：zero_hom_app_obj (X : C) : (zero F s i).hom.app (F.obj X) = (i 0).hom.app 
X ≫ F.map ((shiftFunctorZero C A).hom.app X)
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zero_hom_app_obj (X : C) :
    (zero F s i).hom.app (F.obj X) =
      (i 0).hom.app X ≫ F.map ((shiftFunctorZero C A).hom.app X) := by
  have h : whiskerLeft F (zero F s i).hom = _ :=
    ((whiskeringLeft C D D).obj F).map_preimage _
  exact (NatTrans.congr_app h X).trans (by simp)

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.HasShift.Induced.zero_inv_app_obj** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.HasShift.Induced`。
形式化陈述：zero_inv_app_obj (X : C) : (zero F s i).inv.app (F.obj X) = F.map ((shiftF
unctorZero C A).inv.app X) ≫ (i 0).inv.app X
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zero_inv_app_obj (X : C) :
    (zero F s i).inv.app (F.obj X) =
      F.map ((shiftFunctorZero C A).inv.app X) ≫ (i 0).inv.app X := by
  have h : whiskerLeft F (zero F s i).inv = _ :=
    ((whiskeringLeft C D D).obj F).map_preimage _
  exact (NatTrans.congr_app h X).trans (by simp)

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.HasShift.Induced.add_hom_app_obj** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.HasShift.Induced`。
形式化陈述：add_hom_app_obj (a b : A) (X : C) : (add F s i a b).hom.app (F.obj X) = (i
 (a + b)).hom.app X ≫ F.map ((shiftFunctorAdd C a b).hom.app X) ≫ (i b).inv.app 
((shiftFunctor C a).obj X) ≫ (s b).map ((i a).inv.app X)
参数：a b : A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_hom_app_obj (a b : A) (X : C) :
    (add F s i a b).hom.app (F.obj X) =
      (i (a + b)).hom.app X ≫ F.map ((shiftFunctorAdd C a b).hom.app X) ≫
        (i b).inv.app ((shiftFunctor C a).obj X) ≫ (s b).map ((i a).inv.app X) := by
  have h : whiskerLeft F (add F s i a b).hom = _ :=
    ((whiskeringLeft C D D).obj F).map_preimage _
  exact (NatTrans.congr_app h X).trans (by simp)

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.HasShift.Induced.add_inv_app_obj** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.HasShift.Induced`。
形式化陈述：add_inv_app_obj (a b : A) (X : C) : (add F s i a b).inv.app (F.obj X) = (s
 b).map ((i a).hom.app X) ≫ (i b).hom.app ((shiftFunctor C a).obj X) ≫ F.map ((s
hiftFunctorAdd C a b).inv.app X) ≫ (i (a + b)).inv.app X
参数：a b : A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_inv_app_obj (a b : A) (X : C) :
    (add F s i a b).inv.app (F.obj X) =
      (s b).map ((i a).hom.app X) ≫ (i b).hom.app ((shiftFunctor C a).obj X) ≫
        F.map ((shiftFunctorAdd C a b).inv.app X) ≫ (i (a + b)).inv.app X := by
  have h : whiskerLeft F (add F s i a b).inv = _ :=
    ((whiskeringLeft C D D).obj F).map_preimage _
  exact (NatTrans.congr_app h X).trans (by simp)

end Induced

variable (A)

set_option backward.defeqAttrib.useBackward true in
/-- When `F : C ⥤ D` is a functor satisfying suitable technical assumptions,
this is the induced term of type `HasShift D A` deduced from `[HasShift C A]`. -/
@[instance_reducible]
/-
**CategoryTheory.HasShift.induced** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.HasS
hift`。
形式化陈述：induced : HasShift D A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `F : C ⥤ D` is a functor satisfying suitable technical assumptions,
this is the induced term of type `HasShift D A` deduced from `[HasShift C A]`.
-/
noncomputable def induced : HasShift D A :=
  hasShiftMk D A
    { F := s
      zero := Induced.zero F s i
      add := Induced.add F s i
      zero_add_hom_app := fun n => by
        suffices (Induced.add F s i 0 n).hom =
          eqToHom (by rw [zero_add]; rfl) ≫ whiskerRight (Induced.zero F s i).inv (s n) by
          intro X
          simpa using NatTrans.congr_app this X
        apply ((whiskeringLeft C D D).obj F).map_injective
        ext X
        have eq := dcongr_arg (fun a => (i a).hom.app X) (zero_add n)
        dsimp
        simp only [Induced.add_hom_app_obj, eq, shiftFunctorAdd_zero_add_hom_app,
          Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
          eqToHom_refl, Category.id_comp, eqToHom_app, Induced.zero_inv_app_obj]
        erw [← NatTrans.naturality_assoc, Iso.hom_inv_id_app_assoc]
        rfl
      add_zero_hom_app := fun n => by
        suffices (Induced.add F s i n 0).hom =
            eqToHom (by rw [add_zero]; rfl) ≫ whiskerLeft (s n) (Induced.zero F s i).inv by
          intro X
          simpa using NatTrans.congr_app this X
        apply ((whiskeringLeft C D D).obj F).map_injective
        ext X
        dsimp
        erw [Induced.add_hom_app_obj, dcongr_arg (fun a => (i a).hom.app X) (add_zero n),
          ← cancel_mono ((s 0).map ((i n).hom.app X)), Category.assoc,
          Category.assoc, Category.assoc, Category.assoc, Category.assoc,
          Category.assoc, ← (s 0).map_comp, Iso.inv_hom_id_app, Functor.map_id, Category.comp_id,
          ← NatTrans.naturality, Induced.zero_inv_app_obj,
          shiftFunctorAdd_add_zero_hom_app]
        simp [eqToHom_map, eqToHom_app]
      assoc_hom_app := fun m₁ m₂ m₃ => by
        suffices (Induced.add F s i (m₁ + m₂) m₃).hom ≫
            whiskerRight (Induced.add F s i m₁ m₂).hom (s m₃) =
            eqToHom (by rw [add_assoc]) ≫ (Induced.add F s i m₁ (m₂ + m₃)).hom ≫
              whiskerLeft (s m₁) (Induced.add F s i m₂ m₃).hom by
          intro X
          simpa using NatTrans.congr_app this X
        apply ((whiskeringLeft C D D).obj F).map_injective
        ext X
        dsimp
        have eq := F.congr_map (shiftFunctorAdd'_assoc_hom_app
          m₁ m₂ m₃ _ _ (m₁ + m₂ + m₃) rfl rfl rfl X)
        simp only [shiftFunctorAdd'_eq_shiftFunctorAdd] at eq
        simp only [Functor.comp_obj, Functor.map_comp, shiftFunctorAdd',
          Iso.trans_hom, eqToIso.hom, NatTrans.comp_app, eqToHom_app,
          Category.assoc] at eq
        rw [← cancel_mono ((s m₃).map ((s m₂).map ((i m₁).hom.app X)))]
        simp only [Induced.add_hom_app_obj, Category.assoc, Functor.map_comp]
        slice_lhs 4 5 =>
          erw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
        erw [Category.id_comp]
        slice_lhs 6 7 =>
          erw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app,
            (s m₂).map_id, (s m₃).map_id]
        erw [Category.comp_id, ← NatTrans.naturality_assoc, reassoc_of% eq,
          dcongr_arg (fun a => (i a).hom.app X) (add_assoc m₁ m₂ m₃).symm]
        simp only [Functor.comp_obj, eqToHom_map, eqToHom_app, NatTrans.naturality_assoc,
          Induced.add_hom_app_obj, Functor.comp_map, Category.assoc, Iso.inv_hom_id_app_assoc,
          eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id,
          ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id] }

end HasShift

/-
**CategoryTheory.shiftFunctor_of_induced** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：shiftFunctor_of_induced (a : A) : letI
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma shiftFunctor_of_induced (a : A) :
    letI := HasShift.induced F A s i
    shiftFunctor D a = s a :=
  rfl

variable (A)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.shiftFunctorZero_hom_app_obj_of_induced** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory`。
形式化陈述：shiftFunctorZero_hom_app_obj_of_induced (X : C) : letI
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.HasShift.Induced.zero_hom_app_obj`：zero_hom_app_obj (X : 
C) : (zero F s i).hom.app (F.obj X) = (i 0).hom.app X ≫ F.map ((shiftFunctorZero
 C A).hom.app X)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftFunctorZero_hom_app_obj_of_induced (X : C) :
    letI := HasShift.induced F A s i
    (shiftFunctorZero D A).hom.app (F.obj X) =
      (i 0).hom.app X ≫ F.map ((shiftFunctorZero C A).hom.app X) := by
  simp only [ShiftMkCore.shiftFunctorZero_eq, HasShift.Induced.zero_hom_app_obj]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.shiftFunctorZero_inv_app_obj_of_induced** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory`。
形式化陈述：shiftFunctorZero_inv_app_obj_of_induced (X : C) : letI
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.HasShift.Induced.zero_inv_app_obj`：zero_inv_app_obj (X : 
C) : (zero F s i).inv.app (F.obj X) = F.map ((shiftFunctorZero C A).inv.app X) ≫
 (i 0).inv.app X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftFunctorZero_inv_app_obj_of_induced (X : C) :
    letI := HasShift.induced F A s i
    (shiftFunctorZero D A).inv.app (F.obj X) =
      F.map ((shiftFunctorZero C A).inv.app X) ≫ (i 0).inv.app X := by
  simp only [ShiftMkCore.shiftFunctorZero_eq, HasShift.Induced.zero_inv_app_obj]

variable {A}

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.shiftFunctorAdd_hom_app_obj_of_induced** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory`。
形式化陈述：shiftFunctorAdd_hom_app_obj_of_induced (a b : A) (X : C) : letI
参数：a b : A；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.HasShift.Induced.add_hom_app_obj`：add_hom_app_obj (a b : 
A) (X : C) : (add F s i a b).hom.app (F.obj X) = (i (a + b)).hom.app X ≫ F.map (
(shiftFunctorAdd C a b).hom.app X) ≫ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftFunctorAdd_hom_app_obj_of_induced (a b : A) (X : C) :
    letI := HasShift.induced F A s i
    (shiftFunctorAdd D a b).hom.app (F.obj X) =
      (i (a + b)).hom.app X ≫
        F.map ((shiftFunctorAdd C a b).hom.app X) ≫
        (i b).inv.app ((shiftFunctor C a).obj X) ≫
        (s b).map ((i a).inv.app X) := by
  simp only [ShiftMkCore.shiftFunctorAdd_eq, HasShift.Induced.add_hom_app_obj]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.shiftFunctorAdd_inv_app_obj_of_induced** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory`。
形式化陈述：shiftFunctorAdd_inv_app_obj_of_induced (a b : A) (X : C) : letI
参数：a b : A；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.HasShift.Induced.add_inv_app_obj`：add_inv_app_obj (a b : 
A) (X : C) : (add F s i a b).inv.app (F.obj X) = (s b).map ((i a).hom.app X) ≫ (
i b).hom.app ((shiftFunctor C a).obj …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftFunctorAdd_inv_app_obj_of_induced (a b : A) (X : C) :
    letI := HasShift.induced F A s i
    (shiftFunctorAdd D a b).inv.app (F.obj X) =
      (s b).map ((i a).hom.app X) ≫
      (i b).hom.app ((shiftFunctor C a).obj X) ≫
      F.map ((shiftFunctorAdd C a b).inv.app X) ≫
      (i (a + b)).inv.app X := by
  simp only [ShiftMkCore.shiftFunctorAdd_eq, HasShift.Induced.add_inv_app_obj]

variable (A)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When the target category of a functor `F : C ⥤ D` is equipped with
the induced shift, this is the compatibility of `F` with the shifts on
the categories `C` and `D`. -/
@[instance_reducible]
/-
**CategoryTheory.Functor.CommShift.ofInduced** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Functor.CommShift`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         (F
 : CategoryTheory.Functor C D) →           (A : Type u_3) →             [inst_2 
: AddMonoid A] →               [inst_3 : CategoryTheory.HasShift C A] →         
        (s : A → CategoryTheory.Functor D D) →                   (i : (a : A) → 
F.comp (s a) ≅ (CategoryTheory.shiftFunctor C a).comp F) →                     [
inst_4 : ((CategoryTheory.Functor.whiskeringLeft C D D).obj F).Full] →          
             [inst_5 : ((CategoryTheory.Functor.whiskeringLeft C D D).obj F).Fai
thful] → F.CommShift A
参数：F : CategoryTheory.Functor C D；A : Type u_3；s : A → CategoryTheory.Functor D 
D；i : (a : A) → F.comp (s a) ≅ (CategoryTheory.shiftFunctor C a).comp F；(Categor
yTheory.Functor.whiskeringLeft C D D).obj F；(CategoryTheory.Functor.whiskeringLe
ft C D D).obj F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When the target category of a functor `F : C ⥤ D` is equipped with
the induced shift, this is the compatibility of `F` with the shifts on
the categories `C` and `D`.
-/
noncomputable def Functor.CommShift.ofInduced :
    letI := HasShift.induced F A s i
    F.CommShift A := by
  letI := HasShift.induced F A s i
  exact
    { commShiftIso := fun a => (i a).symm
      commShiftIso_zero := by
        ext X
        dsimp
        simp only [isoZero_hom_app, shiftFunctorZero_inv_app_obj_of_induced,
          ← F.map_comp_assoc, Iso.hom_inv_id_app, F.map_id, Category.id_comp]
      commShiftIso_add := fun a b => by
        ext X
        dsimp
        simp only [isoAdd_hom_app, Iso.symm_hom, shiftFunctorAdd_inv_app_obj_of_induced,
          shiftFunctor_of_induced]
        rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
        dsimp
        rw [Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc,
          ← F.map_comp_assoc, Iso.hom_inv_id_app, F.map_id, Category.id_comp] }
/-
**CategoryTheory.Functor.commShiftIso_eq_ofInduced** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : CategoryTheory.Functo
r C D) (A : Type u_3) [inst_2 : AddMonoid A]   [inst_3 : CategoryTheory.HasShift
 C A] (s : A → CategoryTheory.Functor D D)   (i : (a : A) → F.comp (s a) ≅ (Cate
goryTheory.shiftFunctor C a).comp F)   [inst_4 : ((CategoryTheory.Functor.whiske
ringLeft C D D).obj F).Full]   [inst_5 : ((CategoryTheory.Functor.whiskeringLeft
 C D D).obj F).Faithful] (a : A),   CategoryTheory.Functor.commShiftIso F a = (i
 a).symm
参数：F : CategoryTheory.Functor C D；A : Type u_3；s : A → CategoryTheory.Functor D 
D；i : (a : A) → F.comp (s a) ≅ (CategoryTheory.shiftFunctor C a).comp F；(Categor
yTheory.Functor.whiskeringLeft C D D).obj F；(CategoryTheory.Functor.whiskeringLe
ft C D D).obj F；a : A；i a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Functor.commShiftIso_eq_ofInduced (a : A) :
    letI := HasShift.induced F A s i
    letI := Functor.CommShift.ofInduced F A s i
    F.commShiftIso a = (i a).symm := rfl

end CategoryTheory

