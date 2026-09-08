/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.Adjunction.Opposites

/-!
# Opposites of functors between pretriangulated categories,

If `F : C ⥤ D` is a functor between pretriangulated categories, we prove that
`F` is a triangulated functor if and only if `F.op` is a triangulated functor.
In order to do this, we first show that a `CommShift` structure on `F` naturally
gives one on `F.op` (for the shifts on `Cᵒᵖ` and `Dᵒᵖ` defined in
`CategoryTheory.Triangulated.Opposite.Basic`), and we then prove
that `F.mapTriangle.op` and `F.op.mapTriangle` correspond to each other via the
equivalences `(Triangle C)ᵒᵖ ≌ Triangle Cᵒᵖ` and `(Triangle D)ᵒᵖ ≌ Triangle Dᵒᵖ`
given by `CategoryTheory.Pretriangulated.triangleOpEquivalence`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D)
  [F.CommShift ℤ]

open Category Limits Pretriangulated Opposite

namespace Pretriangulated.Opposite

/-- If `F` commutes with shifts, so does `F.op`, for the shifts chosen on `Cᵒᵖ` in
`CategoryTheory.Triangulated.Opposite.Basic`.
-/
/-
**CategoryTheory.Pretriangulated.Opposite.commShiftFunctorOpInt** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Pretriangulated.Opposite`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.HasShift C ℤ] →           [inst_3 : CategoryTheory.HasShi
ft D ℤ] → (F : CategoryTheory.Functor C D) → [F.CommShift ℤ] → F.op.CommShift ℤ
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` commutes with shifts, so does `F.op`, for the shifts chosen on `Cᵒᵖ` in
`CategoryTheory.Triangulated.Opposite.Basic`.
-/
noncomputable scoped instance commShiftFunctorOpInt : F.op.CommShift ℤ :=
  inferInstanceAs ((PullbackShift.functor
    (AddMonoidHom.mk' (fun (n : ℤ) => -n) (by intros; lia))
      (OppositeShift.functor ℤ F)).CommShift ℤ)

variable {F}
/-
**CategoryTheory.Pretriangulated.Opposite.commShift_natTrans_op_int** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Pretriangulated.Opposite`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.H
asShift C ℤ]   [inst_3 : CategoryTheory.HasShift D ℤ] {F : CategoryTheory.Functo
r C D} [inst_4 : F.CommShift ℤ]   {G : CategoryTheory.Functor C D} [inst_5 : G.C
ommShift ℤ] (τ : F ⟶ G) [CategoryTheory.NatTrans.CommShift τ ℤ],   CategoryTheor
y.NatTrans.CommShift (CategoryTheory.NatTrans.op τ) ℤ
参数：τ : F ⟶ G；CategoryTheory.NatTrans.op τ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable scoped instance commShift_natTrans_op_int {G : C ⥤ D} [G.CommShift ℤ] (τ : F ⟶ G)
    [NatTrans.CommShift τ ℤ] : NatTrans.CommShift (NatTrans.op τ) ℤ :=
  inferInstanceAs (NatTrans.CommShift (PullbackShift.natTrans
    (AddMonoidHom.mk' (fun (n : ℤ) => -n) (by intros; lia))
      (OppositeShift.natTrans ℤ τ)) ℤ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Pretriangulated.Opposite.commShift_adjunction_op_int** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.Pretriangulated.Opposite`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.H
asShift C ℤ]   [inst_3 : CategoryTheory.HasShift D ℤ] {F : CategoryTheory.Functo
r C D} [inst_4 : F.CommShift ℤ]   {G : CategoryTheory.Functor D C} [inst_5 : G.C
ommShift ℤ] (adj : F ⊣ G) [adj.CommShift ℤ], adj.op.CommShift ℤ
参数：adj : F ⊣ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.ext`：ext {F : C ⥤ D} {G : D ⥤ C} {adj adj' : F
 ⊣ G} (h : adj.unit = adj'.unit) : adj = adj'
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
noncomputable scoped instance commShift_adjunction_op_int {G : D ⥤ C} [G.CommShift ℤ] (adj : F ⊣ G)
    [Adjunction.CommShift adj ℤ] : Adjunction.CommShift adj.op ℤ := by
  have eq : adj.op = PullbackShift.adjunction
    (AddMonoidHom.mk' (fun (n : ℤ) => -n) (by intros; lia))
      (OppositeShift.adjunction ℤ adj) := by
    ext
    dsimp [PullbackShift.adjunction, NatTrans.PullbackShift.natIsoId,
      NatTrans.PullbackShift.natIsoComp, PullbackShift.functor, PullbackShift.natTrans,
      OppositeShift.adjunction, OppositeShift.natTrans, NatTrans.OppositeShift.natIsoId,
      NatTrans.OppositeShift.natIsoComp, OppositeShift.functor]
    simp only [Category.comp_id, Category.id_comp]
  rw [eq]
  exact inferInstanceAs (Adjunction.CommShift (PullbackShift.adjunction
    (AddMonoidHom.mk' (fun (n : ℤ) => -n) (by intros; lia))
      (OppositeShift.adjunction ℤ adj)) ℤ)

end Pretriangulated.Opposite

namespace Functor

set_option backward.isDefEq.respectTransparency false in -- Needed in map_opShiftFunctorEquivalence_counitIso_hom_app_unop
@[reassoc]
/-
**CategoryTheory.Functor.op_commShiftIso_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：op_commShiftIso_hom_app (X : Cᵒᵖ) (n m : Int) (h : n + m = 0) : (F.op.comm
ShiftIso n).hom.app X = (F.map ((shiftFunctorOpIso C n m h).hom.app X).unop).op 
≫ ((F.commShiftIso m).inv.app X.unop).op ≫ (shiftFunctorOpIso D n m h).inv.app (
op (F.obj X.unop))
参数：X : Cᵒᵖ；n m : Int；h : n + m = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma op_commShiftIso_hom_app (X : Cᵒᵖ) (n m : ℤ) (h : n + m = 0) :
    (F.op.commShiftIso n).hom.app X =
      (F.map ((shiftFunctorOpIso C n m h).hom.app X).unop).op ≫
        ((F.commShiftIso m).inv.app X.unop).op ≫
        (shiftFunctorOpIso D n m h).inv.app (op (F.obj X.unop)) := by
  obtain rfl : m = -n := by lia
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Functor.op_commShiftIso_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：op_commShiftIso_inv_app (X : Cᵒᵖ) (n m : Int) (h : n + m = 0) : (F.op.comm
ShiftIso n).inv.app X = (shiftFunctorOpIso D n m h).hom.app (op (F.obj X.unop)) 
≫ ((F.commShiftIso m).hom.app X.unop).op ≫ (F.map ((shiftFunctorOpIso C n m h).i
nv.app X).unop).op
参数：X : Cᵒᵖ；n m : Int；h : n + m = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.Functor.op_commShiftIso_hom_app`：op_commShiftIso_hom_app 
(X : Cᵒᵖ) (n m : Int) (h : n + m = 0) : (F.op.commShiftIso n).hom.app X = (F.map
 ((shiftFunctorOpIso C n m h).hom.ap…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.Iso.unop_inv_hom_id_app`：unop_inv_hom_id_app : (e.inv.app
 X).unop ≫ (e.hom.app X).unop = 𝟙 _
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma op_commShiftIso_inv_app (X : Cᵒᵖ) (n m : ℤ) (h : n + m = 0) :
    (F.op.commShiftIso n).inv.app X =
      (shiftFunctorOpIso D n m h).hom.app (op (F.obj X.unop)) ≫
        ((F.commShiftIso m).hom.app X.unop).op ≫
          (F.map ((shiftFunctorOpIso C n m h).inv.app X).unop).op := by
  rw [← cancel_epi ((F.op.commShiftIso n).hom.app X), Iso.hom_inv_id_app,
    op_commShiftIso_hom_app _ X n m h, assoc, assoc]
  simp [← op_comp, ← F.map_comp]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Functor.shift_map_op** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：shift_map_op {X Y : C} (f : X ⟶ Y) (n : Int) : (F.map f).op⟦n⟧' = (F.op.co
mmShiftIso n).inv.app _ ≫ (F.map (f.op⟦n⟧').unop).op ≫ (F.op.commShiftIso n).hom
.app _
参数：f : X ⟶ Y；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatIso.naturality_1`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma shift_map_op {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    (F.map f).op⟦n⟧' = (F.op.commShiftIso n).inv.app _ ≫
      (F.map (f.op⟦n⟧').unop).op ≫ (F.op.commShiftIso n).hom.app _ :=
  (NatIso.naturality_1 (F.op.commShiftIso n) f.op).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Functor.map_shift_unop** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：map_shift_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : Int) : F.map ((f⟦n⟧').unop) = 
((F.op.commShiftIso n).inv.app Y).unop ≫ ((F.map f.unop).op⟦n⟧').unop ≫ ((F.op.c
ommShiftIso n).hom.app X).unop
参数：f : X ⟶ Y；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Functor.shift_map_op`：shift_map_op {X Y : C} (f : X ⟶ Y) 
(n : Int) : (F.map f).op⟦n⟧' = (F.op.commShiftIso n).inv.app _ ≫ (F.map (f.op⟦n⟧
').unop).op ≫ (F.op.commS…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Iso.unop_inv_hom_id_app`：unop_inv_hom_id_app : (e.inv.app
 X).unop ≫ (e.hom.app X).unop = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.unop_inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u_1}   [inst_1 : CategoryTheory.Cate
gory.{v_1, u_1} D] {F G : Category…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_shift_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ℤ) :
    F.map ((f⟦n⟧').unop) = ((F.op.commShiftIso n).inv.app Y).unop ≫
      ((F.map f.unop).op⟦n⟧').unop ≫ ((F.op.commShiftIso n).hom.app X).unop := by
  simp [shift_map_op]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Functor.map_opShiftFunctorEquivalence_unitIso_hom_app_unop** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：map_opShiftFunctorEquivalence_unitIso_hom_app_unop (X : Cᵒᵖ) (n : Int) : F
.map ((opShiftFunctorEquivalence C n).unitIso.hom.app X).unop = (F.commShiftIso 
n).hom.app _ ≫ (((F.op).commShiftIso n).inv.app X).unop⟦n⟧' ≫ ((opShiftFunctorEq
uivalence D n).unitIso.hom.app (op _)).unop
参数：X : Cᵒᵖ；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.add_right_neg`：∀ (a : ℤ), a + -a = 0
· 使用定理 `Int.add_left_neg`：∀ (a : ℤ), -a + a = 0
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.Functor.map_shiftFunctorCompIsoId_hom_app`：map_shiftFunct
orCompIsoId_hom_app [F.CommShift A] (X : C) (a b : A) (h : a + b = 0) : F.map ((
shiftFunctorCompIsoId C a b h).hom.app X) = (F…
· 使用定理 `CategoryTheory.Functor.commShiftIso_hom_naturality_assoc`：∀ {C : Type u_
1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Functor.op_commShiftIso_inv_app`：op_commShiftIso_inv_app 
(X : Cᵒᵖ) (n m : Int) (h : n + m = 0) : (F.op.commShiftIso n).inv.app X = (shift
FunctorOpIso D n m h).hom.app (op (F…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.unop_comp`：unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z
} : (f ≫ g).unop = g.unop ≫ f.unop
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma map_opShiftFunctorEquivalence_unitIso_hom_app_unop (X : Cᵒᵖ) (n : ℤ) :
    F.map ((opShiftFunctorEquivalence C n).unitIso.hom.app X).unop =
      (F.commShiftIso n).hom.app _ ≫
        (((F.op).commShiftIso n).inv.app X).unop⟦n⟧' ≫
        ((opShiftFunctorEquivalence D n).unitIso.hom.app (op _)).unop := by
  dsimp [opShiftFunctorEquivalence]
  simp only [map_comp, unop_comp, Quiver.Hom.unop_op, assoc,
    map_shiftFunctorCompIsoId_hom_app, commShiftIso_hom_naturality_assoc,
    op_commShiftIso_inv_app _ _ _ _ (add_neg_cancel n)]
  congr 3
  rw [← Functor.map_comp_assoc, ← unop_comp,
    Iso.inv_hom_id_app]
  dsimp
  rw [map_id, id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Functor.map_opShiftFunctorEquivalence_unitIso_inv_app_unop** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：map_opShiftFunctorEquivalence_unitIso_inv_app_unop (X : Cᵒᵖ) (n : Int) : F
.map ((opShiftFunctorEquivalence C n).unitIso.inv.app X).unop = ((opShiftFunctor
Equivalence D n).unitIso.inv.app (op (F.obj X.unop))).unop ≫ (((F.op).commShiftI
so n).hom.app X).unop⟦n⟧' ≫ ((F.commShiftIso n).inv.app _)
参数：X : Cᵒᵖ；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.instIsSplitMonoMap`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {X Y : C} (f : Y ⟶…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.unop_comp`：unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z
} : (f ≫ g).unop = g.unop ≫ f.unop
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.Functor.map_opShiftFunctorEquivalence_unitIso_hom_app_uno
p`：map_opShiftFunctorEquivalence_unitIso_hom_app_unop (X : Cᵒᵖ) (n : Int) : F.ma
p ((opShiftFunctorEquivalence C n).unitIso.hom.app X).unop = (F…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.Iso.unop_inv_hom_id_app`：unop_inv_hom_id_app : (e.inv.app
 X).unop ≫ (e.hom.app X).unop = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_opShiftFunctorEquivalence_unitIso_inv_app_unop (X : Cᵒᵖ) (n : ℤ) :
    F.map ((opShiftFunctorEquivalence C n).unitIso.inv.app X).unop =
      ((opShiftFunctorEquivalence D n).unitIso.inv.app (op (F.obj X.unop))).unop ≫
        (((F.op).commShiftIso n).hom.app X).unop⟦n⟧' ≫
        ((F.commShiftIso n).inv.app _) := by
  rw [← cancel_mono (F.map ((opShiftFunctorEquivalence C n).unitIso.hom.app X).unop),
    ← F.map_comp, ← unop_comp, Iso.hom_inv_id_app,
    map_opShiftFunctorEquivalence_unitIso_hom_app_unop, assoc, assoc,
    Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, ← unop_comp]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Functor.map_opShiftFunctorEquivalence_counitIso_hom_app_unop** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：map_opShiftFunctorEquivalence_counitIso_hom_app_unop (X : Cᵒᵖ) (n : Int) :
 F.map ((opShiftFunctorEquivalence C n).counitIso.hom.app X).unop = ((opShiftFun
ctorEquivalence D n).counitIso.hom.app (op (F.obj X.unop))).unop ≫ (((F.commShif
tIso n).inv.app X.unop).op⟦n⟧').unop ≫ ((F.op.commShiftIso n).hom.app (op (X.uno
p⟦n⟧))).unop
参数：X : Cᵒᵖ；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `Int.add_right_neg`：∀ (a : ℤ), a + -a = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `CategoryTheory.Functor.op_commShiftIso_hom_app_assoc`：∀ {C : Type u_1} {
D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Category
Theory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_shiftFunctorCompIsoId_inv_app_assoc`：∀ {C : T
ype u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 
: CategoryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.op_comp_assoc`：op_comp_assoc {X Y Z : C} {f : X ⟶ Y} {g :
 Y ⟶ Z} {Z' : Cᵒᵖ} {h : op X ⟶ Z'} : (f ≫ g).op ≫ h = g.op ≫ f.op ≫ h
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.op_map`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (F : CategoryTheor…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `Quiver.Hom.unop_op`：Quiver.Hom.unop_op {X Y : C} (f : X ⟶ Y) : f.op.unop
 = f
-/
lemma map_opShiftFunctorEquivalence_counitIso_hom_app_unop (X : Cᵒᵖ) (n : ℤ) :
    F.map ((opShiftFunctorEquivalence C n).counitIso.hom.app X).unop =
      ((opShiftFunctorEquivalence D n).counitIso.hom.app (op (F.obj X.unop))).unop ≫
        (((F.commShiftIso n).inv.app X.unop).op⟦n⟧').unop ≫
          ((F.op.commShiftIso n).hom.app (op (X.unop⟦n⟧))).unop := by
  apply Quiver.Hom.op_inj
  dsimp [opShiftFunctorEquivalence]
  rw [assoc, F.op_commShiftIso_hom_app_assoc _ _ _ (add_neg_cancel n), map_comp,
    map_shiftFunctorCompIsoId_inv_app_assoc, op_comp, op_comp_assoc, op_comp_assoc,
    NatTrans.naturality_assoc, op_map, Iso.inv_hom_id_app_assoc, Quiver.Hom.unop_op]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Functor.map_opShiftFunctorEquivalence_counitIso_inv_app_unop** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：map_opShiftFunctorEquivalence_counitIso_inv_app_unop (X : Cᵒᵖ) (n : Int) :
 F.map ((opShiftFunctorEquivalence C n).counitIso.inv.app X).unop = ((F.op.commS
hiftIso n).inv.app (op (X.unop⟦n⟧))).unop ≫ (((F.commShiftIso n).hom.app X.unop)
.op⟦n⟧').unop ≫ ((opShiftFunctorEquivalence D n).counitIso.inv.app (op (F.obj X.
unop))).unop
参数：X : Cᵒᵖ；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.unop_comp`：unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z
} : (f ≫ g).unop = g.unop ≫ f.unop
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.Functor.map_opShiftFunctorEquivalence_counitIso_hom_app_u
nop`：map_opShiftFunctorEquivalence_counitIso_hom_app_unop (X : Cᵒᵖ) (n : Int) : 
F.map ((opShiftFunctorEquivalence C n).counitIso.hom.app X).unop …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_opShiftFunctorEquivalence_counitIso_inv_app_unop (X : Cᵒᵖ) (n : ℤ) :
    F.map ((opShiftFunctorEquivalence C n).counitIso.inv.app X).unop =
      ((F.op.commShiftIso n).inv.app (op (X.unop⟦n⟧))).unop ≫
        (((F.commShiftIso n).hom.app X.unop).op⟦n⟧').unop ≫
          ((opShiftFunctorEquivalence D n).counitIso.inv.app (op (F.obj X.unop))).unop := by
  rw [← cancel_epi (F.map ((opShiftFunctorEquivalence C n).counitIso.hom.app X).unop),
    ← F.map_comp, ← unop_comp, Iso.inv_hom_id_app,
    map_opShiftFunctorEquivalence_counitIso_hom_app_unop]
  dsimp
  simp only [map_id, assoc, ← Functor.map_comp_assoc,
    ← unop_comp, Iso.inv_hom_id_app_assoc, ← op_comp,
    Iso.inv_hom_id_app]
  simp

end Functor

variable [HasZeroObject C] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasZeroObject D] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Functor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
If `F : C ⥤ D` commutes with shifts, this expresses the compatibility of `F.mapTriangle`
with the equivalences `Pretriangulated.triangleOpEquivalence` on `C` and `D`.
-/
@[simps!]
/-
**CategoryTheory.Functor.mapTriangleOpCompTriangleOpEquivalenceFunctorApp** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：mapTriangleOpCompTriangleOpEquivalenceFunctorApp (T : Triangle C) : (trian
gleOpEquivalence D).functor.obj (op (F.mapTriangle.obj T)) ≅ F.op.mapTriangle.ob
j ((triangleOpEquivalence C).functor.obj (op T))
参数：T : Triangle C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` commutes with shifts, this expresses the compatibility of `F.mapT
riangle`
with the equivalences `Pretriangulated.triangleOpEquivalence` on `C` and `D`.
-/
noncomputable def mapTriangleOpCompTriangleOpEquivalenceFunctorApp (T : Triangle C) :
    (triangleOpEquivalence D).functor.obj (op (F.mapTriangle.obj T)) ≅
      F.op.mapTriangle.obj ((triangleOpEquivalence C).functor.obj (op T)) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [shift_map_op, map_opShiftFunctorEquivalence_counitIso_inv_app_unop])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
If `F : C ⥤ D` commutes with shifts, this expresses the compatibility of `F.mapTriangle`
with the equivalences `Pretriangulated.triangleOpEquivalence` on `C` and `D`.
-/
/-
**CategoryTheory.Functor.mapTriangleOpCompTriangleOpEquivalenceFunctor** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：mapTriangleOpCompTriangleOpEquivalenceFunctor : F.mapTriangle.op ⋙ (triang
leOpEquivalence D).functor ≅ (triangleOpEquivalence C).functor ⋙ F.op.mapTriangl
e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` commutes with shifts, this expresses the compatibility of `F.mapT
riangle`
with the equivalences `Pretriangulated.triangleOpEquivalence` on `C` and `D`.
-/
noncomputable def mapTriangleOpCompTriangleOpEquivalenceFunctor :
    F.mapTriangle.op ⋙ (triangleOpEquivalence D).functor ≅
      (triangleOpEquivalence C).functor ⋙ F.op.mapTriangle :=
  NatIso.ofComponents
    (fun T ↦ F.mapTriangleOpCompTriangleOpEquivalenceFunctorApp T.unop)
    (by intros; ext <;> dsimp <;> simp only [id_comp, comp_id])

/--
If `F : C ⥤ D` commutes with shifts, this is the 2-commutative square of categories
`CategoryTheory.Functor.mapTriangleOpCompTriangleOpEquivalenceFunctor`.
-/
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` commutes with shifts, this is the 2-commutative square of categor
ies
`CategoryTheory.Functor.mapTriangleOpCompTriangleOpEquivalenceFunctor`.
-/
noncomputable instance :
    CatCommSq (F.mapTriangle.op) (triangleOpEquivalence C).functor
      (triangleOpEquivalence D).functor F.op.mapTriangle :=
  ⟨F.mapTriangleOpCompTriangleOpEquivalenceFunctor⟩

/--
Vertical inverse of the 2-commutative square of
`CategoryTheory.Functor.mapTriangleOpCompTriangleOpEquivalenceFunctor`.
-/
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Vertical inverse of the 2-commutative square of
`CategoryTheory.Functor.mapTriangleOpCompTriangleOpEquivalenceFunctor`.
-/
noncomputable instance :
    CatCommSq (F.op.mapTriangle) (triangleOpEquivalence C).inverse
      (triangleOpEquivalence D).inverse F.mapTriangle.op :=
  CatCommSq.vInv (F.mapTriangle.op) (triangleOpEquivalence C)
      (triangleOpEquivalence D) F.op.mapTriangle inferInstance

/--
If `F : C ⥤ D` commutes with shifts, this expresses the compatibility of `F.mapTriangle`
with the equivalences `Pretriangulated.triangleOpEquivalence` on `C` and `D`.
-/
/-
**CategoryTheory.Functor.opMapTriangleCompTriangleOpEquivalenceInverse** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：opMapTriangleCompTriangleOpEquivalenceInverse : F.op.mapTriangle ⋙ (triang
leOpEquivalence D).inverse ≅ (triangleOpEquivalence C).inverse ⋙ F.mapTriangle.o
p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` commutes with shifts, this expresses the compatibility of `F.mapT
riangle`
with the equivalences `Pretriangulated.triangleOpEquivalence` on `C` and `D`.
-/
noncomputable def opMapTriangleCompTriangleOpEquivalenceInverse :
    F.op.mapTriangle ⋙ (triangleOpEquivalence D).inverse ≅
      (triangleOpEquivalence C).inverse ⋙ F.mapTriangle.op :=
  CatCommSq.iso (F.op.mapTriangle) (triangleOpEquivalence C).inverse
      (triangleOpEquivalence D).inverse F.mapTriangle.op

end Functor

namespace Pretriangulated.Opposite

open CategoryTheory.Functor in
/-- If `F` is triangulated, so is `F.op`.
-/
/-
**CategoryTheory.Pretriangulated.Opposite.functor_isTriangulated_op** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Pretriangulated.Opposite`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.H
asShift C ℤ]   [inst_3 : CategoryTheory.HasShift D ℤ] (F : CategoryTheory.Functo
r C D) [inst_4 : F.CommShift ℤ]   [inst_5 : CategoryTheory.Limits.HasZeroObject 
C] [inst_6 : CategoryTheory.Preadditive C]   [inst_7 : ∀ (n : ℤ), (CategoryTheor
y.shiftFunctor C n).Additive] [inst_8 : CategoryTheory.Pretriangulated C]   [ins
t_9 : CategoryTheory.Limits.HasZeroObject D] [inst_10 : CategoryTheory.Preadditi
ve D]   [inst_11 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor D n).Additive] [inst_
12 : CategoryTheory.Pretriangulated D]   [F.IsTriangulated], F.op.IsTriangulated
参数：F : CategoryTheory.Functor C D；n : ℤ；CategoryTheory.shiftFunctor C n；n : ℤ；Ca
tegoryTheory.shiftFunctor D n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.Opposite.instAdditiveOppositeShiftFunctor
Int`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Ca
tegoryTheory.HasShift C ℤ]   [inst_2 : CategoryTheory.Preadditive…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pretriangulated.mem_distTriang_op_iff`：mem_distTriang_op_
iff (T : Triangle Cᵒᵖ) : (T in distTriang Cᵒᵖ) ↔ ((triangleOpEquivalence C).inve
rse.obj T).unop in distTriang C
· 使用定理 `CategoryTheory.Pretriangulated.isomorphic_distinguished`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZer
oObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用引理 `CategoryTheory.Functor.map_distinguished`：map_distinguished [F.IsTriangu
lated] (T : Triangle C) (hT : T in distTriang C) : F.mapTriangle.obj T in distTr
iang D
· 使用引理 `CategoryTheory.Pretriangulated.unop_distinguished`：unop_distinguished (T
 : Triangle Cᵒᵖ) (hT : T in distTriang Cᵒᵖ) : ((triangleOpEquivalence C).inverse
.obj T).unop in distTriang C

--- 原说明 ---
If `F` is triangulated, so is `F.op`.
-/
scoped instance functor_isTriangulated_op [F.IsTriangulated] : F.op.IsTriangulated where
  map_distinguished T dT := by
    rw [mem_distTriang_op_iff]
    exact Pretriangulated.isomorphic_distinguished _
      ((F.map_distinguished _ (unop_distinguished _ dT))) _
      (((opMapTriangleCompTriangleOpEquivalenceInverse F).symm.app T).unop)

end Pretriangulated.Opposite

namespace Functor

/-- If `F.op` is triangulated, so is `F`.
-/
/-
**CategoryTheory.Functor.isTriangulated_of_op** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：isTriangulated_of_op [F.op.IsTriangulated] : F.IsTriangulated where map_di
stinguished T dT
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.Opposite.instAdditiveOppositeShiftFunctor
Int`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Ca
tegoryTheory.HasShift C ℤ]   [inst_2 : CategoryTheory.Preadditive…
· 使用引理 `CategoryTheory.Pretriangulated.distinguished_iff_of_iso`：distinguished_i
ff_of_iso {T₁ T₂ : Triangle C} (e : T₁ ≅ T₂) : T₁ in distTriang C ↔ T₂ in distTr
iang C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Opposite.unop_op`：unop_op (x : α) : unop (op x) = x
· 使用定理 `CategoryTheory.Functor.id_obj`：id_obj (X : C) : (𝟭 C).obj X = X
· 使用定理 `CategoryTheory.Functor.comp_obj`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   {E : Type u₃} [ins…
· 使用引理 `CategoryTheory.Pretriangulated.mem_distTriang_op_iff`：mem_distTriang_op_
iff (T : Triangle Cᵒᵖ) : (T in distTriang Cᵒᵖ) ↔ ((triangleOpEquivalence C).inve
rse.obj T).unop in distTriang C
· 使用定理 `CategoryTheory.Functor.op_obj`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (F : CategoryTheor…
· 使用引理 `CategoryTheory.Functor.map_distinguished`：map_distinguished [F.IsTriangu
lated] (T : Triangle C) (hT : T in distTriang C) : F.mapTriangle.obj T in distTr
iang D
· 使用引理 `CategoryTheory.Pretriangulated.op_distinguished`：op_distinguished (T : T
riangle C) (hT : T in distTriang C) : ((triangleOpEquivalence C).functor.obj (Op
posite.op T)) in distTriang Cᵒᵖ

--- 原说明 ---
If `F.op` is triangulated, so is `F`.
-/
lemma isTriangulated_of_op [F.op.IsTriangulated] : F.IsTriangulated where
  map_distinguished T dT := by
    have := distinguished_iff_of_iso ((triangleOpEquivalence D).unitIso.app
      (Opposite.op (F.mapTriangle.obj T))).unop
    rw [Functor.id_obj, Opposite.unop_op (F.mapTriangle.obj T)] at this
    rw [← this, Functor.comp_obj, ← mem_distTriang_op_iff, ← Functor.op_obj, ← Functor.comp_obj,
      distinguished_iff_of_iso ((mapTriangleOpCompTriangleOpEquivalenceFunctor F).app
      (Opposite.op T))]
    exact F.op.map_distinguished _ (op_distinguished _ dT)

open Pretriangulated.Opposite in
/-- `F` is triangulated if and only if `F.op` is triangulated.
-/
/-
**CategoryTheory.Functor.op_isTriangulated_iff** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：op_isTriangulated_iff : F.op.IsTriangulated ↔ F.IsTriangulated
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.Opposite.instAdditiveOppositeShiftFunctor
Int`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Ca
tegoryTheory.HasShift C ℤ]   [inst_2 : CategoryTheory.Preadditive…
· 使用引理 `CategoryTheory.Functor.isTriangulated_of_op`：isTriangulated_of_op [F.op.
IsTriangulated] : F.IsTriangulated where map_distinguished T dT
· 使用定理 `CategoryTheory.Pretriangulated.Opposite.functor_isTriangulated_op`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
`F` is triangulated if and only if `F.op` is triangulated.
-/
lemma op_isTriangulated_iff : F.op.IsTriangulated ↔ F.IsTriangulated :=
  ⟨fun _ ↦ F.isTriangulated_of_op, fun _ ↦ inferInstance⟩

end Functor

end CategoryTheory

