/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Basic
public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-! # Shifted morphisms in the opposite category

If `C` is a category equipped with a shift by `ℤ`, `X` and `Y` are objects
of `C`, and `n : ℤ`, we define a bijection
`ShiftedHom.opEquiv : ShiftedHom X Y n ≃ ShiftedHom (Opposite.op Y) (Opposite.op X) n`.
We also introduce `ShiftedHom.opEquiv'` which produces a bijection
`ShiftedHom X Y a' ≃ (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧)` when `n + a = a'`.
The compatibilities that are obtained shall be used in order to study
the homological functor `preadditiveYoneda.obj B : Cᵒᵖ ⥤ Type _` when `B` is an object
in a pretriangulated category `C`.

-/

@[expose] public section

namespace CategoryTheory

open Category Pretriangulated.Opposite Pretriangulated

variable {C : Type*} [Category* C] [HasShift C ℤ] {X Y Z : C}

namespace ShiftedHom

/-- The bijection `ShiftedHom X Y n ≃ ShiftedHom (Opposite.op Y) (Opposite.op X) n` when
`n : ℤ`, and `X` and `Y` are objects of a category equipped with a shift by `ℤ`. -/
/-
**CategoryTheory.ShiftedHom.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sh
iftedHom`。
形式化陈述：opEquiv (n : Int) : ShiftedHom X Y n ≃ ShiftedHom (Opposite.op Y) (Opposit
e.op X) n
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The bijection `ShiftedHom X Y n ≃ ShiftedHom (Opposite.op Y) (Opposite.op X) n` 
when
`n : ℤ`, and `X` and `Y` are objects of a category equipped with a shift by `ℤ`.
-/
noncomputable def opEquiv (n : ℤ) :
    ShiftedHom X Y n ≃ ShiftedHom (Opposite.op Y) (Opposite.op X) n :=
  Quiver.Hom.opEquiv.trans
    ((opShiftFunctorEquivalence C n).symm.toAdjunction.homEquiv (Opposite.op Y) (Opposite.op X))
/-
**CategoryTheory.ShiftedHom.opEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ShiftedHom`。
形式化陈述：opEquiv_symm_apply {n : Int} (f : ShiftedHom (Opposite.op Y) (Opposite.op 
X) n) : (opEquiv n).symm f = ((opShiftFunctorEquivalence C n).unitIso.inv.app (O
pposite.op X)).unop ≫ f.unop⟦n⟧'
参数：f : ShiftedHom (Opposite.op Y) (Opposite.op X) n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma opEquiv_symm_apply {n : ℤ} (f : ShiftedHom (Opposite.op Y) (Opposite.op X) n) :
    (opEquiv n).symm f =
      ((opShiftFunctorEquivalence C n).unitIso.inv.app (Opposite.op X)).unop ≫ f.unop⟦n⟧' :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShiftedHom.opEquiv_symm_apply_comp** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ShiftedHom`。
形式化陈述：opEquiv_symm_apply_comp {X Y : C} {a : Int} (f : ShiftedHom (Opposite.op X
) (Opposite.op Y) a) {b : Int} {Z : C} (z : ShiftedHom X Z b) {c : Int} (h : b +
 a = c) : ((ShiftedHom.opEquiv a).symm f).comp z h = (ShiftedHom.opEquiv a).symm
 (z.op ≫ f) ≫ (shiftFunctorAdd' C b a c h).inv.app Z
参数：f : ShiftedHom (Opposite.op X) (Opposite.op Y) a；z : ShiftedHom X Z b；h : b +
 a = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShiftedHom.opEquiv_symm_apply`：opEquiv_symm_apply {n : In
t} (f : ShiftedHom (Opposite.op Y) (Opposite.op X) n) : (opEquiv n).symm f = ((o
pShiftFunctorEquivalence C n).unit…
· 使用定理 `CategoryTheory.ShiftedHom.comp.eq_1`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_2 : Ca
tegoryTheory.HasShift C M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opEquiv_symm_apply_comp {X Y : C} {a : ℤ}
    (f : ShiftedHom (Opposite.op X) (Opposite.op Y) a) {b : ℤ} {Z : C}
    (z : ShiftedHom X Z b) {c : ℤ} (h : b + a = c) :
    ((ShiftedHom.opEquiv a).symm f).comp z h =
      (ShiftedHom.opEquiv a).symm (z.op ≫ f) ≫
        (shiftFunctorAdd' C b a c h).inv.app Z := by
  rw [ShiftedHom.opEquiv_symm_apply, ShiftedHom.opEquiv_symm_apply,
    ShiftedHom.comp]
  dsimp
  simp only [assoc, Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShiftedHom.opEquiv_symm_comp** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ShiftedHom`。
形式化陈述：opEquiv_symm_comp {a b : Int} (f : ShiftedHom (Opposite.op Z) (Opposite.op
 Y) a) (g : ShiftedHom (Opposite.op Y) (Opposite.op X) b) {c : Int} (h : b + a =
 c) : (opEquiv _).symm (f.comp g h) = ((opEquiv _).symm g).comp ((opEquiv _).sym
m f) (by lia)
参数：f : ShiftedHom (Opposite.op Z) (Opposite.op Y) a；g : ShiftedHom (Opposite.op 
Y) (Opposite.op X) b；h : b + a = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShiftedHom.opEquiv_symm_apply`：opEquiv_symm_apply {n : In
t} (f : ShiftedHom (Opposite.op Y) (Opposite.op X) n) : (opEquiv n).symm f = ((o
pShiftFunctorEquivalence C n).unit…
· 使用引理 `CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_add_unitIso_inv
_app_eq`：opShiftFunctorEquivalence_add_unitIso_inv_app_eq (X : Cᵒᵖ) (m n p : Int
) (h : m + n = p
· 使用定理 `CategoryTheory.ShiftedHom.comp.eq_1`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_2 : Ca
tegoryTheory.HasShift C M…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.unop_comp_assoc`：unop_comp_assoc {X Y Z : Cᵒᵖ} {f : X ⟶ Y
} {g : Y ⟶ Z} {Z' : C} {h : unop X ⟶ Z'} : (f ≫ g).unop ≫ h = g.unop ≫ f.unop ≫ 
h
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
-/
lemma opEquiv_symm_comp {a b : ℤ}
    (f : ShiftedHom (Opposite.op Z) (Opposite.op Y) a)
    (g : ShiftedHom (Opposite.op Y) (Opposite.op X) b)
    {c : ℤ} (h : b + a = c) :
    (opEquiv _).symm (f.comp g h) =
      ((opEquiv _).symm g).comp ((opEquiv _).symm f) (by lia) := by
  rw [opEquiv_symm_apply, opEquiv_symm_apply,
    opShiftFunctorEquivalence_add_unitIso_inv_app_eq _ _ _ _ (show a + b = c by lia), comp, comp]
  dsimp
  rw [assoc, assoc, assoc, assoc, ← Functor.map_comp, ← unop_comp_assoc,
    Iso.inv_hom_id_app]
  dsimp
  rw [assoc, id_comp, Functor.map_comp, ← NatTrans.naturality_assoc,
    ← NatTrans.naturality, opEquiv_symm_apply]
  dsimp
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc]
  rw [← unop_comp_assoc]
  erw [← NatTrans.naturality]
  rfl

/-- The bijection `ShiftedHom X Y a' ≃ (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧)`
when integers `n`, `a` and `a'` satisfy `n + a = a'`, and `X` and `Y` are objects
of a category equipped with a shift by `ℤ`. -/
/-
**CategoryTheory.ShiftedHom.opEquiv'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.S
hiftedHom`。
形式化陈述：opEquiv' (n a a' : Int) (h : n + a = a') : ShiftedHom X Y a' ≃ (Opposite.o
p (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧)
参数：n a a' : Int；h : n + a = a'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The bijection `ShiftedHom X Y a' ≃ (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧)`
when integers `n`, `a` and `a'` satisfy `n + a = a'`, and `X` and `Y` are object
s
of a category equipped with a shift by `ℤ`.
-/
noncomputable def opEquiv' (n a a' : ℤ) (h : n + a = a') :
    ShiftedHom X Y a' ≃ (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧) :=
  ((shiftFunctorAdd' C a n a' (by lia)).symm.app Y).homToEquiv.symm.trans (opEquiv n)
/-
**CategoryTheory.ShiftedHom.opEquiv'_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.ShiftedHom`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.HasShift C ℤ] {X Y : C}   {n a : ℤ}   (f : Opposite.op ((CategoryT
heory.shiftFunctor C a).obj Y) ⟶ (CategoryTheory.shiftFunctor Cᵒᵖ n).obj (Opposi
te.op X))   (a' : ℤ) (h : n + a = a'),   (CategoryTheory.ShiftedHom.opEquiv' n a
 a' h).symm f =     CategoryTheory.CategoryStruct.comp ((CategoryTheory.ShiftedH
om.opEquiv n).symm f)       ((CategoryTheory.shiftFunctorAdd' C a n a' ⋯).inv.ap
p Y)
参数：f : Opposite.op ((CategoryTheory.shiftFunctor C a).obj Y) ⟶ (CategoryTheory.s
hiftFunctor Cᵒᵖ n).obj (Opposite.op X)；a' : ℤ；h : n + a = a'；CategoryTheory.Shif
tedHom.opEquiv' n a a' h；(CategoryTheory.ShiftedHom.opEquiv n).symm f；(CategoryT
heory.shiftFunctorAdd' C a n a' ⋯).inv.app Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma opEquiv'_symm_apply {n a : ℤ} (f : Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧)
    (a' : ℤ) (h : n + a = a') :
    (opEquiv' n a a' h).symm f =
      (opEquiv n).symm f ≫ (shiftFunctorAdd' C a n a' (by lia)).inv.app _ :=
  rfl
/-
**CategoryTheory.ShiftedHom.opEquiv'_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.ShiftedHom`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.HasShift C ℤ] {X Y : C} {a' : ℤ}   (f : CategoryTheory.ShiftedHom 
X Y a') (n a : ℤ) (h : n + a = a'),   (CategoryTheory.ShiftedHom.opEquiv' n a a'
 h) f =     (CategoryTheory.ShiftedHom.opEquiv n)       (CategoryTheory.Category
Struct.comp f ((CategoryTheory.shiftFunctorAdd' C a n a' ⋯).hom.app Y))
参数：f : CategoryTheory.ShiftedHom X Y a'；n a : ℤ；h : n + a = a'；CategoryTheory.Sh
iftedHom.opEquiv' n a a' h；CategoryTheory.ShiftedHom.opEquiv n；CategoryTheory.Ca
tegoryStruct.comp f ((CategoryTheory.shiftFunctorAdd' C a n a' ⋯).hom.app Y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opEquiv'_apply {a' : ℤ} (f : ShiftedHom X Y a') (n a : ℤ) (h : n + a = a') :
    opEquiv' n a a' h f =
      opEquiv n (f ≫ (shiftFunctorAdd' C a n a' (by lia)).hom.app Y) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShiftedHom.opEquiv'_symm_op_opShiftFunctorEquivalence_counitIso
_inv_app_op_shift** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ShiftedHom`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.HasShift C ℤ] {X Y Z : C}   {n m : ℤ} (f : CategoryTheory.ShiftedH
om X Y n) (g : CategoryTheory.ShiftedHom Y Z m) (q : ℤ) (hq : n + m = q),   (Cat
egoryTheory.ShiftedHom.opEquiv' n m q hq).symm       (CategoryTheory.CategoryStr
uct.comp (Quiver.Hom.op g)         (CategoryTheory.CategoryStruct.comp          
 ((CategoryTheory.Pretriangulated.opShiftFunctorEquivalence C n).counitIso.inv.a
pp (Opposite.op Y))           ((CategoryTheory.shiftFunctor Cᵒᵖ n).map (Quiver.H
om.op f)))) =     f.comp g ⋯
参数：f : CategoryTheory.ShiftedHom X Y n；g : CategoryTheory.ShiftedHom Y Z m；q : ℤ
；hq : n + m = q；CategoryTheory.ShiftedHom.opEquiv' n m q hq；CategoryTheory.Categ
oryStruct.comp (Quiver.Hom.op g)         (CategoryTheory.CategoryStruct.comp    
       ((CategoryTheory.Pretriangulated.opShiftFunctorEquivalence C n).counitIso
.inv.app (Opposite.op Y))           ((CategoryTheory.shiftFunctor Cᵒᵖ n).map (Qu
iver.Hom.op f)))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShiftedHom.opEquiv'_symm_apply`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.HasShift C ℤ] {X 
Y : C}   {n a : ℤ}   (f : Opposite.…
· 使用引理 `CategoryTheory.ShiftedHom.opEquiv_symm_apply`：opEquiv_symm_apply {n : In
t} (f : ShiftedHom (Opposite.op Y) (Opposite.op X) n) : (opEquiv n).symm f = ((o
pShiftFunctorEquivalence C n).unit…
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_unitIso_inv_nat
urality`：opShiftFunctorEquivalence_unitIso_inv_naturality (n : Int) {X Y : Cᵒᵖ} 
(f : X ⟶ Y) : (f⟦n⟧').unop⟦n⟧'.op ≫ (opShiftFunctorEquivalence C n).u…
· 使用定理 `CategoryTheory.Equivalence.inverse_counitInv_comp_assoc`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (e : C ≌ D) (Y : D…
-/
lemma opEquiv'_symm_op_opShiftFunctorEquivalence_counitIso_inv_app_op_shift
    {n m : ℤ} (f : ShiftedHom X Y n) (g : ShiftedHom Y Z m)
    (q : ℤ) (hq : n + m = q) :
    (opEquiv' n m q hq).symm
        (g.op ≫ (opShiftFunctorEquivalence C n).counitIso.inv.app _ ≫ f.op⟦n⟧') =
      f.comp g (by lia) := by
  rw [opEquiv'_symm_apply, opEquiv_symm_apply]
  dsimp [comp]
  apply Quiver.Hom.op_inj
  simp only [assoc, Functor.map_comp, op_comp, Quiver.Hom.op_unop,
    opShiftFunctorEquivalence_unitIso_inv_naturality]
  erw [(opShiftFunctorEquivalence C n).inverse_counitInv_comp_assoc (Opposite.op Y)]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShiftedHom.opEquiv'_symm_comp** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.ShiftedHom`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.HasShift C ℤ] {X Y Z : C}   (f : Y ⟶ X) {n a : ℤ}   (x : Opposite.
op ((CategoryTheory.shiftFunctor C a).obj Z) ⟶ (CategoryTheory.shiftFunctor Cᵒᵖ 
n).obj (Opposite.op X))   (a' : ℤ) (h : n + a = a'),   (CategoryTheory.ShiftedHo
m.opEquiv' n a a' h).symm       (CategoryTheory.CategoryStruct.comp x ((Category
Theory.shiftFunctor Cᵒᵖ n).map f.op)) =     CategoryTheory.CategoryStruct.comp f
 ((CategoryTheory.ShiftedHom.opEquiv' n a a' h).symm x)
参数：f : Y ⟶ X；x : Opposite.op ((CategoryTheory.shiftFunctor C a).obj Z) ⟶ (Catego
ryTheory.shiftFunctor Cᵒᵖ n).obj (Opposite.op X)；a' : ℤ；h : n + a = a'；CategoryT
heory.ShiftedHom.opEquiv' n a a' h；CategoryTheory.CategoryStruct.comp x ((Catego
ryTheory.shiftFunctor Cᵒᵖ n).map f.op)；(CategoryTheory.ShiftedHom.opEquiv' n a a
' h).symm x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_unitIso_inv_nat
urality`：opShiftFunctorEquivalence_unitIso_inv_naturality (n : Int) {X Y : Cᵒᵖ} 
(f : X ⟶ Y) : (f⟦n⟧').unop⟦n⟧'.op ≫ (opShiftFunctorEquivalence C n).u…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opEquiv'_symm_comp (f : Y ⟶ X) {n a : ℤ} (x : Opposite.op (Z⟦a⟧) ⟶ (Opposite.op X⟦n⟧))
    (a' : ℤ) (h : n + a = a') :
    (opEquiv' n a a' h).symm (x ≫ f.op⟦n⟧') = f ≫ (opEquiv' n a a' h).symm x :=
  Quiver.Hom.op_inj (by simp [opEquiv'_symm_apply, opEquiv_symm_apply])

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShiftedHom.opEquiv'_zero_add_symm** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.ShiftedHom`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.HasShift C ℤ] {X Y : C} (a : ℤ)   (f : Opposite.op ((CategoryTheor
y.shiftFunctor C a).obj Y) ⟶ (CategoryTheory.shiftFunctor Cᵒᵖ 0).obj (Opposite.o
p X)),   (CategoryTheory.ShiftedHom.opEquiv' 0 a a ⋯).symm f =     CategoryTheor
y.CategoryStruct.comp ((CategoryTheory.shiftFunctorZero Cᵒᵖ ℤ).hom.app (Opposite
.op X)).unop f.unop
参数：a : ℤ；f : Opposite.op ((CategoryTheory.shiftFunctor C a).obj Y) ⟶ (CategoryTh
eory.shiftFunctor Cᵒᵖ 0).obj (Opposite.op X)；CategoryTheory.ShiftedHom.opEquiv' 
0 a a ⋯；(CategoryTheory.shiftFunctorZero Cᵒᵖ ℤ).hom.app (Opposite.op X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_zero_unitIso_in
v_app`：opShiftFunctorEquivalence_zero_unitIso_inv_app (X : Cᵒᵖ) : (opShiftFuncto
rEquivalence C 0).unitIso.inv.app X = (((shiftFunctorZero Cᵒᵖ Int).…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.shiftFunctorAdd'_add_zero`：∀ (C : Type u) {A : Type u_1} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [inst_2 : Cat
egoryTheory.HasShift C A] (a :…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opEquiv'_zero_add_symm (a : ℤ) (f : Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦(0 : ℤ)⟧) :
    (opEquiv' 0 a a (zero_add a)).symm f =
      ((shiftFunctorZero Cᵒᵖ ℤ).hom.app _).unop ≫ f.unop := by
  simp [opEquiv'_symm_apply, opEquiv_symm_apply, shiftFunctorAdd'_add_zero,
    opShiftFunctorEquivalence_zero_unitIso_inv_app]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShiftedHom.opEquiv'_add_symm** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ShiftedHom`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.HasShift C ℤ] {X Y : C}   (n m a a' a'' : ℤ) (ha' : n + a = a') (h
a'' : m + a' = a'')   (x :     Opposite.op ((CategoryTheory.shiftFunctor C a).ob
j Y) ⟶       (CategoryTheory.shiftFunctor Cᵒᵖ (m + n)).obj (Opposite.op X)),   (
CategoryTheory.ShiftedHom.opEquiv' (m + n) a a'' ⋯).symm x =     (CategoryTheory
.ShiftedHom.opEquiv' m a' a'' ha'').symm       (Quiver.Hom.op         ((Category
Theory.ShiftedHom.opEquiv' n a a' ha').symm           (CategoryTheory.CategorySt
ruct.comp x ((CategoryTheory.shiftFunctorAdd Cᵒᵖ m n).hom.app (Opposite.op X))))
)
参数：n m a a' a'' : ℤ；ha' : n + a = a'；ha'' : m + a' = a''；x :     Opposite.op ((C
ategoryTheory.shiftFunctor C a).obj Y) ⟶       (CategoryTheory.shiftFunctor Cᵒᵖ 
(m + n)).obj (Opposite.op X)；CategoryTheory.ShiftedHom.opEquiv' (m + n) a a'' ⋯；
CategoryTheory.ShiftedHom.opEquiv' m a' a'' ha''；Quiver.Hom.op         ((Categor
yTheory.ShiftedHom.opEquiv' n a a' ha').symm           (CategoryTheory.CategoryS
truct.comp x ((CategoryTheory.shiftFunctorAdd Cᵒᵖ m n).hom.app (Opposite.op X)))
)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_add_unitIso_inv
_app_eq`：opShiftFunctorEquivalence_add_unitIso_inv_app_eq (X : Cᵒᵖ) (m n p : Int
) (h : m + n = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.shiftFunctorAdd'_assoc_inv_app`：∀ {C : Type u} {A : Type 
u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [inst_2 
: CategoryTheory.HasShift C A] (a₁ …
-/
lemma opEquiv'_add_symm (n m a a' a'' : ℤ) (ha' : n + a = a') (ha'' : m + a' = a'')
    (x : (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦m + n⟧)) :
    (opEquiv' (m + n) a a'' (by lia)).symm x =
      (opEquiv' m a' a'' ha'').symm ((opEquiv' n a a' ha').symm
        (x ≫ (shiftFunctorAdd Cᵒᵖ m n).hom.app _)).op := by
  simp only [opEquiv'_symm_apply, opEquiv_symm_apply,
    opShiftFunctorEquivalence_add_unitIso_inv_app_eq _ _ _ _ (add_comm n m)]
  dsimp
  simp only [assoc, Functor.map_comp, ← shiftFunctorAdd'_eq_shiftFunctorAdd,
    ← NatTrans.naturality_assoc,
    shiftFunctorAdd'_assoc_inv_app a n m a' (m + n) a'' (by lia) (by lia) (by lia)]
  rfl

section Preadditive

variable [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.ShiftedHom.opEquiv_symm_add** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShiftedHom`。
形式化陈述：opEquiv_symm_add {n : Int} (x y : ShiftedHom (Opposite.op Y) (Opposite.op 
X) n) : (opEquiv n).symm (x + y) = (opEquiv n).symm x + (opEquiv n).symm y
参数：x y : ShiftedHom (Opposite.op Y) (Opposite.op X) n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
-/
lemma opEquiv_symm_add {n : ℤ} (x y : ShiftedHom (Opposite.op Y) (Opposite.op X) n) :
    (opEquiv n).symm (x + y) = (opEquiv n).symm x + (opEquiv n).symm y := by
  dsimp [opEquiv_symm_apply]
  rw [← Preadditive.comp_add, ← Functor.map_add]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.ShiftedHom.opEquiv'_symm_add** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ShiftedHom`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.HasShift C ℤ] {X Y : C}   [inst_2 : CategoryTheory.Preadditive C] 
[∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] {n a : ℤ}   (x y :     O
pposite.op ((CategoryTheory.shiftFunctor C a).obj Y) ⟶ (CategoryTheory.shiftFunc
tor Cᵒᵖ n).obj (Opposite.op X))   (a' : ℤ) (h : n + a = a'),   (CategoryTheory.S
hiftedHom.opEquiv' n a a' h).symm (x + y) =     (CategoryTheory.ShiftedHom.opEqu
iv' n a a' h).symm x + (CategoryTheory.ShiftedHom.opEquiv' n a a' h).symm y
参数：n : ℤ；CategoryTheory.shiftFunctor C n；x y :     Opposite.op ((CategoryTheory.
shiftFunctor C a).obj Y) ⟶ (CategoryTheory.shiftFunctor Cᵒᵖ n).obj (Opposite.op 
X)；a' : ℤ；h : n + a = a'；CategoryTheory.ShiftedHom.opEquiv' n a a' h；x + y；Categ
oryTheory.ShiftedHom.opEquiv' n a a' h；CategoryTheory.ShiftedHom.opEquiv' n a a'
 h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShiftedHom.opEquiv_symm_add`：opEquiv_symm_add {n : Int} (
x y : ShiftedHom (Opposite.op Y) (Opposite.op X) n) : (opEquiv n).symm (x + y) =
 (opEquiv n).symm x + (opEquiv n…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
-/
lemma opEquiv'_symm_add {n a : ℤ} (x y : (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧))
    (a' : ℤ) (h : n + a = a') :
    (opEquiv' n a a' h).symm (x + y) =
      (opEquiv' n a a' h).symm x + (opEquiv' n a a' h).symm y := by
  dsimp [opEquiv']
  rw [opEquiv_symm_add, Preadditive.add_comp]

end Preadditive

end ShiftedHom

end CategoryTheory

