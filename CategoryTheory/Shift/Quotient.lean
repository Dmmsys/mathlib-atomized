/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Shift.Induced
public import Mathlib.CategoryTheory.Quotient

/-!
# The shift on a quotient category

Let `C` be a category equipped a shift by a monoid `A`. If we have a relation
on morphisms `r : HomRel C` that is compatible with the shift (i.e. if two
morphisms `f` and `g` are related, then `f⟦a⟧'` and `g⟦a⟧'` are also related
for all `a : A`), then the quotient category `Quotient r` is equipped with
a shift.

The condition `r.IsCompatibleWithShift A` on the relation `r` is a class so that
the shift can be automatically inferred on the quotient category.

-/

@[expose] public section

universe v v' u u' w

open CategoryTheory Category

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (r : HomRel C) (A : Type w) [AddMonoid A] [HasShift C A] [HasShift D A]

namespace HomRel

/-- A relation on morphisms is compatible with the shift by a monoid `A` when the
relation if preserved by the shift. -/
/-
**HomRel.IsCompatibleWithShift** 是 Mathlib 中的一个归纳类型，位于命名空间 `HomRel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     HomRel C 
→ (A : Type w) → [inst_1 : AddMonoid A] → [CategoryTheory.HasShift C A] → Prop
参数：A : Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation on morphisms is compatible with the shift by a monoid `A` when the
relation if preserved by the shift.
-/
class IsCompatibleWithShift : Prop where
  /-- the condition that the relation is preserved by the shift -/
  condition : ∀ (a : A) ⦃X Y : C⦄ (f g : X ⟶ Y), r f g → r (f⟦a⟧') (g⟦a⟧')

end HomRel

namespace CategoryTheory

/-- The shift by a monoid `A` induced on a quotient category `Quotient r` when the
relation `r` is compatible with the shift. -/
/-
**CategoryTheory.HasShift.quotient** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Has
Shift`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (r : HomR
el C) →       (A : Type w) →         [inst_1 : AddMonoid A] →           [inst_2 
: CategoryTheory.HasShift C A] →             [r.IsCompatibleWithShift A] → Categ
oryTheory.HasShift (CategoryTheory.Quotient r) A
参数：r : HomRel C；A : Type w；CategoryTheory.Quotient r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shift by a monoid `A` induced on a quotient category `Quotient r` when the
relation `r` is compatible with the shift.
-/
noncomputable instance HasShift.quotient [r.IsCompatibleWithShift A] :
    HasShift (Quotient r) A :=
  HasShift.induced (Quotient.functor r) A
    (fun a => Quotient.lift r (shiftFunctor C a ⋙ Quotient.functor r)
      (fun _ _ _ _ hfg => Quotient.sound r (HomRel.IsCompatibleWithShift.condition _ _ _ hfg)))
    (fun _ => Quotient.lift.isLift _ _ _)

/-- The functor `Quotient.functor r : C ⥤ Quotient r` commutes with the shift. -/
/-
**CategoryTheory.Quotient.functor_commShift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Quotient`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (r : HomR
el C) →       (A : Type w) →         [inst_1 : AddMonoid A] →           [inst_2 
: CategoryTheory.HasShift C A] →             [inst_3 : r.IsCompatibleWithShift A
] → (CategoryTheory.Quotient.functor r).CommShift A
参数：r : HomRel C；A : Type w；CategoryTheory.Quotient.functor r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Quotient.functor r : C ⥤ Quotient r` commutes with the shift.
-/
noncomputable instance Quotient.functor_commShift [r.IsCompatibleWithShift A] :
    (Quotient.functor r).CommShift A :=
  Functor.CommShift.ofInduced _ _ _ _
/-
**CategoryTheory.Quotient.functor_obj_shift** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Quotient`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (r : HomRel C) (A
 : Type w) [inst_1 : AddMonoid A]   [inst_2 : CategoryTheory.HasShift C A] [inst
_3 : r.IsCompatibleWithShift A] (X : C) (n : A),   (CategoryTheory.shiftFunctor 
(CategoryTheory.Quotient r) n).obj ((CategoryTheory.Quotient.functor r).obj X) =
     (CategoryTheory.Quotient.functor r).obj ((CategoryTheory.shiftFunctor C n).
obj X)
参数：r : HomRel C；A : Type w；X : C；n : A；CategoryTheory.shiftFunctor (CategoryTheo
ry.Quotient r) n；(CategoryTheory.Quotient.functor r).obj X；CategoryTheory.Quotie
nt.functor r；(CategoryTheory.shiftFunctor C n).obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Quotient.functor_obj_shift [r.IsCompatibleWithShift A] (X : C) (n : A) :
    ((Quotient.functor r).obj X)⟦n⟧ = (Quotient.functor r).obj (X⟦n⟧) := rfl

-- the construction is made irreducible in order to prevent timeouts and abuse of defeq
attribute [irreducible] HasShift.quotient Quotient.functor_commShift

namespace Quotient

variable [r.IsCompatibleWithShift A] [F.CommShift A]
    (hF : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F.map f₂)

namespace LiftCommShift

variable {A}

/-- Auxiliary definition for `Quotient.liftCommShift`. -/
/-
**CategoryTheory.Quotient.LiftCommShift.iso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Quotient.LiftCommShift`。
形式化陈述：iso (a : A) : shiftFunctor (Quotient r) a ⋙ lift r F hF ≅ lift r F hF ⋙ sh
iftFunctor D a
参数：a : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `Quotient.liftCommShift`.
-/
noncomputable def iso (a : A) :
    shiftFunctor (Quotient r) a ⋙ lift r F hF ≅ lift r F hF ⋙ shiftFunctor D a :=
  natIsoLift r ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((functor r).commShiftIso a).symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (lift.isLift r F hF) ≪≫ F.commShiftIso a ≪≫
    Functor.isoWhiskerRight (lift.isLift r F hF).symm _ ≪≫ Functor.associator _ _ _)

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Quotient.LiftCommShift.iso_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Quotient.LiftCommShift`。
形式化陈述：iso_hom_app (a : A) (X : C) : (iso F r hF a).hom.app ((functor r).obj X) =
 (lift r F hF).map (((functor r).commShiftIso a).inv.app X) ≫ (F.commShiftIso a)
.hom.app X
参数：a : A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iso_hom_app (a : A) (X : C) :
    (iso F r hF a).hom.app ((functor r).obj X) =
      (lift r F hF).map (((functor r).commShiftIso a).inv.app X) ≫
      (F.commShiftIso a).hom.app X := by
  simp [iso, lift_obj_functor_obj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Quotient.LiftCommShift.iso_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Quotient.LiftCommShift`。
形式化陈述：iso_inv_app (a : A) (X : C) : (iso F r hF a).inv.app ((functor r).obj X) =
 (F.commShiftIso a).inv.app X ≫ (lift r F hF).map (((functor r).commShiftIso a).
hom.app X)
参数：a : A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iso_inv_app (a : A) (X : C) :
    (iso F r hF a).inv.app ((functor r).obj X) =
      (F.commShiftIso a).inv.app X ≫
      (lift r F hF).map (((functor r).commShiftIso a).hom.app X) := by
  simp [iso, lift_obj_functor_obj]

attribute [irreducible] iso

end LiftCommShift

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When `r : HomRel C` is compatible with the shift by an additive monoid, and
`F : C ⥤ D` is a functor which commutes with the shift and is compatible with `r`, then
the induced functor `Quotient.lift r F _ : Quotient r ⥤ D` also commutes with the shift. -/
@[simps -isSimp commShiftIso]
/-
**CategoryTheory.Quotient.liftCommShift** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Quotient`。
形式化陈述：liftCommShift : (Quotient.lift r F hF).CommShift A where commShiftIso
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `r : HomRel C` is compatible with the shift by an additive monoid, and
`F : C ⥤ D` is a functor which commutes with the shift and is compatible with `r
`, then
the induced functor `Quotient.lift r F _ : Quotient r ⥤ D` also commutes with th
e shift.
-/
noncomputable instance liftCommShift :
    (Quotient.lift r F hF).CommShift A where
  commShiftIso := LiftCommShift.iso F r hF
  commShiftIso_zero := by
    ext1
    apply natTrans_ext
    ext X
    dsimp
    rw [LiftCommShift.iso_hom_app, (functor r).commShiftIso_zero,
      Functor.CommShift.isoZero_hom_app, Functor.CommShift.isoZero_inv_app,
      Functor.map_comp, assoc, F.commShiftIso_zero, Functor.CommShift.isoZero_hom_app,
      lift_map_functor_map, ← F.map_comp_assoc, Iso.inv_hom_id_app]
    dsimp [lift_obj_functor_obj]
    rw [F.map_id, id_comp]
  commShiftIso_add a b := by
    ext1
    apply natTrans_ext
    ext X
    dsimp
    rw [LiftCommShift.iso_hom_app, (functor r).commShiftIso_add, F.commShiftIso_add,
      Functor.CommShift.isoAdd_hom_app, Functor.CommShift.isoAdd_hom_app,
      Functor.CommShift.isoAdd_inv_app, Functor.map_comp, Functor.map_comp,
      Functor.map_comp, assoc, assoc, assoc, LiftCommShift.iso_hom_app, lift_map_functor_map]
    congr 1
    rw [← cancel_epi ((shiftFunctor (Quotient r) b ⋙ lift r F hF).map
      (NatTrans.app (Functor.commShiftIso (functor r) a).hom X))]
    simp only [← Functor.comp_map, ← Functor.comp_obj]
    rw [(LiftCommShift.iso F r hF b).hom.naturality_assoc (((functor r).commShiftIso a).hom.app X)]
    simp only [Functor.comp_obj, LiftCommShift.iso_hom_app, Iso.hom_inv_id_app,
      Functor.comp_map, assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      Functor.map_id, id_comp, lift_obj_functor_obj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Quotient.liftCommShift_compatibility** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Quotient`。
形式化陈述：liftCommShift_compatibility : NatTrans.CommShift (Quotient.lift.isLift r F
 hF).hom A where shift_comm a
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.commShiftIso_comp_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Quotient.liftCommShift_commShiftIso`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Cate
gory.{v', u'} D]   (F : CategoryTheory.F…
· 使用引理 `CategoryTheory.Quotient.LiftCommShift.iso_hom_app`：iso_hom_app (a : A) (
X : C) : (iso F r hF a).hom.app ((functor r).obj X) = (lift r F hF).map (((funct
or r).commShiftIso a).inv.app X) ≫ (F.c…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance liftCommShift_compatibility :
    NatTrans.CommShift (Quotient.lift.isLift r F hF).hom A where
  shift_comm a := by
    ext X
    dsimp
    rw [Functor.commShiftIso_comp_hom_app, liftCommShift_commShiftIso,
      LiftCommShift.iso_hom_app, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    simp [lift, Quotient.functor]

end Quotient

end CategoryTheory

