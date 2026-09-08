/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Shift.Opposite
public import Mathlib.CategoryTheory.Shift.Pullback

/-!
# The shift on the opposite category of a pretriangulated category

Let `C` be a (pre)triangulated category. We already have a shift on `Cᵒᵖ` given
by `CategoryTheory.Shift.Opposite`, but this is not the shift that we want to
make `Cᵒᵖ` into a (pre)triangulated category.
The correct shift on `Cᵒᵖ` is obtained by combining the constructions in the files
`CategoryTheory.Shift.Opposite` and `CategoryTheory.Shift.Pullback`.
When the user opens `CategoryTheory.Pretriangulated.Opposite`, the
category `Cᵒᵖ` is equipped with the shift by `ℤ` such that
shifting by `n : ℤ` on `Cᵒᵖ` corresponds to the shift by
`-n` on `C`. This is actually a definitional equality, but the user
should not rely on this, and instead use the isomorphism
`shiftFunctorOpIso C n m hnm : shiftFunctor Cᵒᵖ n ≅ (shiftFunctor C m).op`
where `hnm : n + m = 0`.

Some compatibilities between the shifts on `C` and `Cᵒᵖ` are also expressed through
the equivalence of categories `opShiftFunctorEquivalence C n : Cᵒᵖ ≌ Cᵒᵖ` whose
functor is `shiftFunctor Cᵒᵖ n` and whose inverse functor is `(shiftFunctor C n).op`.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive ZeroObject

variable (C : Type*) [Category* C]

namespace Pretriangulated

variable [HasShift C ℤ]

namespace Opposite

set_option backward.privateInPublic true in
/-- As it is unclear whether the opposite category `Cᵒᵖ` should always be equipped
with the shift by `ℤ` such that shifting by `n` on `Cᵒᵖ` corresponds to shifting
by `-n` on `C`, the user shall have to do `open CategoryTheory.Pretriangulated.Opposite`
in order to get this shift and the (pre)triangulated structure on `Cᵒᵖ`. -/
/-
**CategoryTheory.Pretriangulated.Opposite.OppositeShiftAux** 是 Mathlib 中的一个缩写定义，
位于命名空间 `CategoryTheory.Pretriangulated.Opposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As it is unclear whether the opposite category `Cᵒᵖ` should always be equipped
with the shift by `ℤ` such that shifting by `n` on `Cᵒᵖ` corresponds to shifting
by `-n` on `C`, the user shall have to do `open CategoryTheory.Pretriangulated.O
pposite`
in order to get this shift and the (pre)triangulated structure on `Cᵒᵖ`.
-/
private abbrev OppositeShiftAux :=
  PullbackShift (OppositeShift C ℤ)
    (AddMonoidHom.mk' (fun (n : ℤ) => -n) (by intros; lia))

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The category `Cᵒᵖ` is equipped with the shift such that the shift by `n` on `Cᵒᵖ`
corresponds to the shift by `-n` on `C`. -/
/-
**CategoryTheory.Pretriangulated.Opposite.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Pretriangulated.Opposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category `Cᵒᵖ` is equipped with the shift such that the shift by `n` on `Cᵒᵖ
`
corresponds to the shift by `-n` on `C`.
-/
scoped instance : HasShift Cᵒᵖ ℤ :=
  inferInstanceAs <| HasShift (OppositeShiftAux C) ℤ
/-
**CategoryTheory.Pretriangulated.Opposite.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Pretriangulated.Opposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] (n : ℤ) :
    (shiftFunctor Cᵒᵖ n).Additive :=
  inferInstanceAs <| (shiftFunctor (OppositeShiftAux C) n).Additive

end Opposite

open Pretriangulated.Opposite

/-- The shift functor on the opposite category identifies to the opposite functor
of a shift functor on the original category. -/
/-
**CategoryTheory.Pretriangulated.shiftFunctorOpIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Pretriangulated`。
形式化陈述：shiftFunctorOpIso (n m : Int) (hnm : n + m = 0) : shiftFunctor Cᵒᵖ n ≅ (sh
iftFunctor C m).op
参数：n m : Int；hnm : n + m = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shift functor on the opposite category identifies to the opposite functor
of a shift functor on the original category.
-/
def shiftFunctorOpIso (n m : ℤ) (hnm : n + m = 0) :
    shiftFunctor Cᵒᵖ n ≅ (shiftFunctor C m).op := eqToIso (by
  obtain rfl : m = -n := by lia
  rfl)

variable {C}
/-
**CategoryTheory.Pretriangulated.shiftFunctorZero_op_hom_app** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：shiftFunctorZero_op_hom_app (X : Cᵒᵖ) : (shiftFunctorZero Cᵒᵖ Int).hom.app
 X = (shiftFunctorOpIso C 0 0 (zero_add 0)).hom.app X ≫ ((shiftFunctorZero C Int
).inv.app X.unop).op
参数：X : Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma shiftFunctorZero_op_hom_app (X : Cᵒᵖ) :
    (shiftFunctorZero Cᵒᵖ ℤ).hom.app X = (shiftFunctorOpIso C 0 0 (zero_add 0)).hom.app X ≫
      ((shiftFunctorZero C ℤ).inv.app X.unop).op := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Pretriangulated.shiftFunctorZero_op_inv_app** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：shiftFunctorZero_op_inv_app (X : Cᵒᵖ) : (shiftFunctorZero Cᵒᵖ Int).inv.app
 X = ((shiftFunctorZero C Int).hom.app X.unop).op ≫ (shiftFunctorOpIso C 0 0 (ze
ro_add 0)).inv.app X
参数：X : Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
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
· 使用引理 `CategoryTheory.Pretriangulated.shiftFunctorZero_op_hom_app`：shiftFunctor
Zero_op_hom_app (X : Cᵒᵖ) : (shiftFunctorZero Cᵒᵖ Int).hom.app X = (shiftFunctor
OpIso C 0 0 (zero_add 0)).hom.app X ≫ ((shiftFun…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.op_comp_assoc`：op_comp_assoc {X Y Z : C} {f : X ⟶ Y} {g :
 Y ⟶ Z} {Z' : Cᵒᵖ} {h : op X ⟶ Z'} : (f ≫ g).op ≫ h = g.op ≫ f.op ≫ h
· 使用定理 `CategoryTheory.op_id`：op_id {X : C} : (𝟙 X).op = 𝟙 (op X)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma shiftFunctorZero_op_inv_app (X : Cᵒᵖ) :
    (shiftFunctorZero Cᵒᵖ ℤ).inv.app X =
      ((shiftFunctorZero C ℤ).hom.app X.unop).op ≫
      (shiftFunctorOpIso C 0 0 (zero_add 0)).inv.app X := by
  rw [← cancel_epi ((shiftFunctorZero Cᵒᵖ ℤ).hom.app X), Iso.hom_inv_id_app,
    shiftFunctorZero_op_hom_app, assoc, ← op_comp_assoc, Iso.hom_inv_id_app, op_id,
    id_comp, Iso.hom_inv_id_app]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Pretriangulated.shiftFunctorAdd'_op_hom_app** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.HasShift C ℤ] (X : Cᵒᵖ)   (a₁ a₂ a₃ : ℤ) (h : a₁ + a₂ = a₃) (b₁ b₂
 b₃ : ℤ) (h₁ : a₁ + b₁ = 0) (h₂ : a₂ + b₂ = 0) (h₃ : a₃ + b₃ = 0),   (CategoryTh
eory.shiftFunctorAdd' Cᵒᵖ a₁ a₂ a₃ h).hom.app X =     CategoryTheory.CategoryStr
uct.comp ((CategoryTheory.Pretriangulated.shiftFunctorOpIso C a₃ b₃ h₃).hom.app 
X)       (CategoryTheory.CategoryStruct.comp ((CategoryTheory.shiftFunctorAdd' C
 b₁ b₂ b₃ ⋯).inv.app (Opposite.unop X)).op         (CategoryTheory.CategoryStruc
t.comp           ((CategoryTheory.Pretriangulated.shiftFunctorOpIso C a₂ b₂ h₂).
inv.app             (Opposite.op ((CategoryTheory.shiftFunctor C b₁).1 (Opposite
.unop X))))           ((CategoryTheory.shiftFunctor Cᵒᵖ a₂).map             ((Ca
tegoryTheory.Pretriangulated.shiftFunctorOpIso C a₁ b₁ h₁).inv.app X))))
参数：X : Cᵒᵖ；a₁ a₂ a₃ : ℤ；h : a₁ + a₂ = a₃；b₁ b₂ b₃ : ℤ；h₁ : a₁ + b₁ = 0；h₂ : a₂ +
 b₂ = 0；h₃ : a₃ + b₃ = 0；CategoryTheory.shiftFunctorAdd' Cᵒᵖ a₁ a₂ a₃ h；(Categor
yTheory.Pretriangulated.shiftFunctorOpIso C a₃ b₃ h₃).hom.app X；CategoryTheory.C
ategoryStruct.comp ((CategoryTheory.shiftFunctorAdd' C b₁ b₂ b₃ ⋯).inv.app (Oppo
site.unop X)).op         (CategoryTheory.CategoryStruct.comp           ((Categor
yTheory.Pretriangulated.shiftFunctorOpIso C a₂ b₂ h₂).inv.app             (Oppos
ite.op ((CategoryTheory.shiftFunctor C b₁).1 (Opposite.unop X))))           ((Ca
tegoryTheory.shiftFunctor Cᵒᵖ a₂).map             ((CategoryTheory.Pretriangulat
ed.shiftFunctorOpIso C a₁ b₁ h₁).inv.app X)))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.pullbackShiftFunctorAdd'_hom_app`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A : Type u_2} {B : Type u_3} [inst_1 : 
AddMonoid A]   [inst_2 : AddMonoid B]…
· 使用定理 `CategoryTheory.oppositeShiftFunctorAdd'_hom_app`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A : Type u_2} [inst_1 : AddMonoid A]   
[inst_2 : CategoryTheory.HasShift C A…
-/
lemma shiftFunctorAdd'_op_hom_app (X : Cᵒᵖ) (a₁ a₂ a₃ : ℤ) (h : a₁ + a₂ = a₃)
    (b₁ b₂ b₃ : ℤ) (h₁ : a₁ + b₁ = 0) (h₂ : a₂ + b₂ = 0) (h₃ : a₃ + b₃ = 0) :
    (shiftFunctorAdd' Cᵒᵖ a₁ a₂ a₃ h).hom.app X =
      (shiftFunctorOpIso C _ _ h₃).hom.app X ≫
        ((shiftFunctorAdd' C b₁ b₂ b₃ (by lia)).inv.app X.unop).op ≫
        (shiftFunctorOpIso C _ _ h₂).inv.app _ ≫
        (shiftFunctor Cᵒᵖ a₂).map ((shiftFunctorOpIso C _ _ h₁).inv.app X) := by
  erw [@pullbackShiftFunctorAdd'_hom_app (OppositeShift C ℤ) _ _ _ _ _ _ _ X
    a₁ a₂ a₃ h b₁ b₂ b₃ (by dsimp; lia) (by dsimp; lia) (by dsimp; lia)]
  rw [oppositeShiftFunctorAdd'_hom_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Pretriangulated.shiftFunctorAdd'_op_inv_app** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.HasShift C ℤ] (X : Cᵒᵖ)   (a₁ a₂ a₃ : ℤ) (h : a₁ + a₂ = a₃) (b₁ b₂
 b₃ : ℤ) (h₁ : a₁ + b₁ = 0) (h₂ : a₂ + b₂ = 0) (h₃ : a₃ + b₃ = 0),   (CategoryTh
eory.shiftFunctorAdd' Cᵒᵖ a₁ a₂ a₃ h).inv.app X =     CategoryTheory.CategoryStr
uct.comp       ((CategoryTheory.shiftFunctor Cᵒᵖ a₂).map         ((CategoryTheor
y.Pretriangulated.shiftFunctorOpIso C a₁ b₁ h₁).hom.app X))       (CategoryTheor
y.CategoryStruct.comp         ((CategoryTheory.Pretriangulated.shiftFunctorOpIso
 C a₂ b₂ h₂).hom.app           ((CategoryTheory.shiftFunctor C b₁).op.obj X))   
      (CategoryTheory.CategoryStruct.comp           ((CategoryTheory.shiftFuncto
rAdd' C b₁ b₂ b₃ ⋯).hom.app (Opposite.unop X)).op           ((CategoryTheory.Pre
triangulated.shiftFunctorOpIso C a₃ b₃ h₃).inv.app X)))
参数：X : Cᵒᵖ；a₁ a₂ a₃ : ℤ；h : a₁ + a₂ = a₃；b₁ b₂ b₃ : ℤ；h₁ : a₁ + b₁ = 0；h₂ : a₂ +
 b₂ = 0；h₃ : a₃ + b₃ = 0；CategoryTheory.shiftFunctorAdd' Cᵒᵖ a₁ a₂ a₃ h；(Categor
yTheory.shiftFunctor Cᵒᵖ a₂).map         ((CategoryTheory.Pretriangulated.shiftF
unctorOpIso C a₁ b₁ h₁).hom.app X)；CategoryTheory.CategoryStruct.comp         ((
CategoryTheory.Pretriangulated.shiftFunctorOpIso C a₂ b₂ h₂).hom.app           (
(CategoryTheory.shiftFunctor C b₁).op.obj X))         (CategoryTheory.CategorySt
ruct.comp           ((CategoryTheory.shiftFunctorAdd' C b₁ b₂ b₃ ⋯).hom.app (Opp
osite.unop X)).op           ((CategoryTheory.Pretriangulated.shiftFunctorOpIso C
 a₃ b₃ h₃).inv.app X))。
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
· 使用定理 `CategoryTheory.Pretriangulated.shiftFunctorAdd'_op_hom_app`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.HasS
hift C ℤ] (X : Cᵒᵖ)   (a₁ a₂ a₃ : ℤ) (h : a₁ + a…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.op_comp_assoc`：op_comp_assoc {X Y Z : C} {f : X ⟶ Y} {g :
 Y ⟶ Z} {Z' : Cᵒᵖ} {h : op X ⟶ Z'} : (f ≫ g).op ≫ h = g.op ≫ f.op ≫ h
· 使用定理 `CategoryTheory.op_id`：op_id {X : C} : (𝟙 X).op = 𝟙 (op X)
-/
lemma shiftFunctorAdd'_op_inv_app (X : Cᵒᵖ) (a₁ a₂ a₃ : ℤ) (h : a₁ + a₂ = a₃)
    (b₁ b₂ b₃ : ℤ) (h₁ : a₁ + b₁ = 0) (h₂ : a₂ + b₂ = 0) (h₃ : a₃ + b₃ = 0) :
    (shiftFunctorAdd' Cᵒᵖ a₁ a₂ a₃ h).inv.app X =
      (shiftFunctor Cᵒᵖ a₂).map ((shiftFunctorOpIso C _ _ h₁).hom.app X) ≫
      (shiftFunctorOpIso C _ _ h₂).hom.app _ ≫
      ((shiftFunctorAdd' C b₁ b₂ b₃ (by lia)).hom.app X.unop).op ≫
      (shiftFunctorOpIso C _ _ h₃).inv.app X := by
  rw [← cancel_epi ((shiftFunctorAdd' Cᵒᵖ a₁ a₂ a₃ h).hom.app X), Iso.hom_inv_id_app,
    shiftFunctorAdd'_op_hom_app X a₁ a₂ a₃ h b₁ b₂ b₃ h₁ h₂ h₃,
    assoc, assoc, assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Functor.map_id, id_comp, Iso.inv_hom_id_app_assoc]
  rw [← op_comp_assoc, Iso.hom_inv_id_app, op_id, id_comp, Iso.hom_inv_id_app]
/-
**CategoryTheory.Pretriangulated.shiftFunctor_op_map** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Pretriangulated`。
形式化陈述：shiftFunctor_op_map {K L : Cᵒᵖ} (φ : K ⟶ L) (n m : Int) (hnm : n + m = 0
参数：φ : K ⟶ L；n m : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatIso.naturality_2`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma shiftFunctor_op_map {K L : Cᵒᵖ} (φ : K ⟶ L) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    (shiftFunctor Cᵒᵖ n).map φ =
      (shiftFunctorOpIso C n m hnm).hom.app K ≫ ((shiftFunctor C m).map φ.unop).op ≫
        (shiftFunctorOpIso C n m hnm).inv.app L :=
  (NatIso.naturality_2 (shiftFunctorOpIso C n m hnm) φ).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
variable (C) in
/-- The autoequivalence `Cᵒᵖ ≌ Cᵒᵖ` whose functor is `shiftFunctor Cᵒᵖ n` and whose inverse
functor is `(shiftFunctor C n).op`. In most cases, it is not necessary to unfold the
definitions of the unit and counit isomorphisms: the compatibilities they satisfy
are stated as separate lemmas. -/
@[simps functor inverse, implicit_reducible]
/-
**CategoryTheory.Pretriangulated.opShiftFunctorEquivalence** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：opShiftFunctorEquivalence (n : Int) : Cᵒᵖ ≌ Cᵒᵖ where functor
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Int.add_left_neg`：∀ (a : ℤ), -a + a = 0
· 使用定理 `Int.add_right_neg`：∀ (a : ℤ), a + -a = 0

--- 原说明 ---
The autoequivalence `Cᵒᵖ ≌ Cᵒᵖ` whose functor is `shiftFunctor Cᵒᵖ n` and whose 
inverse
functor is `(shiftFunctor C n).op`. In most cases, it is not necessary to unfold
 the
definitions of the unit and counit isomorphisms: the compatibilities they satisf
y
are stated as separate lemmas.
-/
def opShiftFunctorEquivalence (n : ℤ) : Cᵒᵖ ≌ Cᵒᵖ where
  functor := shiftFunctor Cᵒᵖ n
  inverse := (shiftFunctor C n).op
  unitIso := NatIso.op (shiftFunctorCompIsoId C (-n) n n.add_left_neg) ≪≫
    Functor.isoWhiskerRight (shiftFunctorOpIso C n (-n) n.add_right_neg).symm (shiftFunctor C n).op
  counitIso := Functor.isoWhiskerLeft _ (shiftFunctorOpIso C n (-n) n.add_right_neg) ≪≫
    NatIso.op (shiftFunctorCompIsoId C n (-n) n.add_right_neg).symm
  functor_unitIso_comp X := Quiver.Hom.unop_inj (by
    dsimp [shiftFunctorOpIso]
    erw [comp_id, Functor.map_id, comp_id]
    change (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).inv.app (X.unop⟦-n⟧) ≫
      ((shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).hom.app X.unop)⟦-n⟧' = 𝟙 _
    rw [shift_shiftFunctorCompIsoId_neg_add_cancel_hom_app n X.unop, Iso.inv_hom_id_app])

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_unitIso_hom_app** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：opShiftFunctorEquivalence_unitIso_hom_app (X : Cᵒᵖ) (n m : Int) (hnm : n +
 m = 0
参数：X : Cᵒᵖ；n m : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma opShiftFunctorEquivalence_unitIso_hom_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    (opShiftFunctorEquivalence C n).unitIso.hom.app X =
      ((shiftFunctorCompIsoId C m n (by lia)).hom.app X.unop).op ≫
        (((shiftFunctorOpIso C n m hnm).inv.app (X)).unop⟦n⟧').op := by
  obtain rfl : m = -n := by lia
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_unitIso_inv_app** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：opShiftFunctorEquivalence_unitIso_inv_app (X : Cᵒᵖ) (n m : Int) (hnm : n +
 m = 0
参数：X : Cᵒᵖ；n m : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma opShiftFunctorEquivalence_unitIso_inv_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    (opShiftFunctorEquivalence C n).unitIso.inv.app X =
      (((shiftFunctorOpIso C n m hnm).hom.app (X)).unop⟦n⟧').op ≫
      ((shiftFunctorCompIsoId C m n (by lia)).inv.app X.unop).op := by
  obtain rfl : m = -n := by lia
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_counitIso_hom_app** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：opShiftFunctorEquivalence_counitIso_hom_app (X : Cᵒᵖ) (n m : Int) (hnm : n
 + m = 0
参数：X : Cᵒᵖ；n m : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma opShiftFunctorEquivalence_counitIso_hom_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    (opShiftFunctorEquivalence C n).counitIso.hom.app X =
      (shiftFunctorOpIso C n m hnm).hom.app (Opposite.op (X.unop⟦n⟧)) ≫
        ((shiftFunctorCompIsoId C n m hnm).inv.app X.unop).op
        := by
  obtain rfl : m = -n := by lia
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_counitIso_inv_app** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：opShiftFunctorEquivalence_counitIso_inv_app (X : Cᵒᵖ) (n m : Int) (hnm : n
 + m = 0
参数：X : Cᵒᵖ；n m : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma opShiftFunctorEquivalence_counitIso_inv_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    (opShiftFunctorEquivalence C n).counitIso.inv.app X =
      ((shiftFunctorCompIsoId C n m hnm).hom.app X.unop).op ≫
        (shiftFunctorOpIso C n m hnm).inv.app (Opposite.op (X.unop⟦n⟧)) := by
  obtain rfl : m = -n := by lia
  rfl

/-! The naturality of the unit and counit isomorphisms are restated in the following
lemmas so as to mitigate the need for `erw`. -/

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_unitIso_hom_naturalit
y** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：opShiftFunctorEquivalence_unitIso_hom_naturality (n : Int) {X Y : Cᵒᵖ} (f 
: X ⟶ Y) : f ≫ (opShiftFunctorEquivalence C n).unitIso.hom.app Y = (opShiftFunct
orEquivalence C n).unitIso.hom.app X ≫ (f⟦n⟧').unop⟦n⟧'.op
参数：n : Int；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma opShiftFunctorEquivalence_unitIso_hom_naturality (n : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    f ≫ (opShiftFunctorEquivalence C n).unitIso.hom.app Y =
      (opShiftFunctorEquivalence C n).unitIso.hom.app X ≫ (f⟦n⟧').unop⟦n⟧'.op :=
  (opShiftFunctorEquivalence C n).unitIso.hom.naturality f

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_unitIso_inv_naturalit
y** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：opShiftFunctorEquivalence_unitIso_inv_naturality (n : Int) {X Y : Cᵒᵖ} (f 
: X ⟶ Y) : (f⟦n⟧').unop⟦n⟧'.op ≫ (opShiftFunctorEquivalence C n).unitIso.inv.app
 Y = (opShiftFunctorEquivalence C n).unitIso.inv.app X ≫ f
参数：n : Int；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma opShiftFunctorEquivalence_unitIso_inv_naturality (n : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (f⟦n⟧').unop⟦n⟧'.op ≫ (opShiftFunctorEquivalence C n).unitIso.inv.app Y =
      (opShiftFunctorEquivalence C n).unitIso.inv.app X ≫ f :=
  (opShiftFunctorEquivalence C n).unitIso.inv.naturality f

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_counitIso_hom_natural
ity** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：opShiftFunctorEquivalence_counitIso_hom_naturality (n : Int) {X Y : Cᵒᵖ} (
f : X ⟶ Y) : f.unop⟦n⟧'.op⟦n⟧' ≫ (opShiftFunctorEquivalence C n).counitIso.hom.a
pp Y = (opShiftFunctorEquivalence C n).counitIso.hom.app X ≫ f
参数：n : Int；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma opShiftFunctorEquivalence_counitIso_hom_naturality (n : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    f.unop⟦n⟧'.op⟦n⟧' ≫ (opShiftFunctorEquivalence C n).counitIso.hom.app Y =
      (opShiftFunctorEquivalence C n).counitIso.hom.app X ≫ f :=
  (opShiftFunctorEquivalence C n).counitIso.hom.naturality f

set_option backward.isDefEq.respectTransparency false in -- This is needed in CategoryTheory/Triangulated/Opposite/Triangle.lean
@[reassoc (attr := simp)]
/-
**CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_counitIso_inv_natural
ity** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：opShiftFunctorEquivalence_counitIso_inv_naturality (n : Int) {X Y : Cᵒᵖ} (
f : X ⟶ Y) : f ≫ (opShiftFunctorEquivalence C n).counitIso.inv.app Y = (opShiftF
unctorEquivalence C n).counitIso.inv.app X ≫ f.unop⟦n⟧'.op⟦n⟧'
参数：n : Int；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma opShiftFunctorEquivalence_counitIso_inv_naturality (n : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    f ≫ (opShiftFunctorEquivalence C n).counitIso.inv.app Y =
      (opShiftFunctorEquivalence C n).counitIso.inv.app X ≫ f.unop⟦n⟧'.op⟦n⟧' :=
  (opShiftFunctorEquivalence C n).counitIso.inv.naturality f

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_zero_unitIso_hom_app*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：opShiftFunctorEquivalence_zero_unitIso_hom_app (X : Cᵒᵖ) : (opShiftFunctor
Equivalence C 0).unitIso.hom.app X = ((shiftFunctorZero C Int).hom.app X.unop).o
p ≫ (((shiftFunctorZero Cᵒᵖ Int).inv.app X).unop⟦(0 : Int)⟧').op
参数：X : Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `Int.add_right_neg`：∀ (a : ℤ), a + -a = 0
· 使用定理 `Int.add_left_neg`：∀ (a : ℤ), -a + a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pretriangulated.shiftFunctorZero_op_inv_app`：shiftFunctor
Zero_op_inv_app (X : Cᵒᵖ) : (shiftFunctorZero Cᵒᵖ Int).inv.app X = ((shiftFuncto
rZero C Int).hom.app X.unop).op ≫ (shiftFunctorO…
· 使用定理 `CategoryTheory.unop_comp`：unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z
} : (f ≫ g).unop = g.unop ≫ f.unop
· 使用定理 `Quiver.Hom.unop_op`：Quiver.Hom.unop_op {X Y : C} (f : X ⟶ Y) : f.op.unop
 = f
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CategoryTheory.shiftFunctorCompIsoId_zero_zero_hom_app`：shiftFunctorComp
IsoId_zero_zero_hom_app (X : C) : (shiftFunctorCompIsoId C 0 0 (add_zero 0)).hom
.app X = ((shiftFunctorZero C A).hom.app X)⟦…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
lemma opShiftFunctorEquivalence_zero_unitIso_hom_app (X : Cᵒᵖ) :
    (opShiftFunctorEquivalence C 0).unitIso.hom.app X =
      ((shiftFunctorZero C ℤ).hom.app X.unop).op ≫
      (((shiftFunctorZero Cᵒᵖ ℤ).inv.app X).unop⟦(0 : ℤ)⟧').op := by
  apply Quiver.Hom.unop_inj
  dsimp [opShiftFunctorEquivalence]
  rw [shiftFunctorZero_op_inv_app, unop_comp, Quiver.Hom.unop_op, Functor.map_comp,
    shiftFunctorCompIsoId_zero_zero_hom_app, assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_zero_unitIso_inv_app*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：opShiftFunctorEquivalence_zero_unitIso_inv_app (X : Cᵒᵖ) : (opShiftFunctor
Equivalence C 0).unitIso.inv.app X = (((shiftFunctorZero Cᵒᵖ Int).hom.app X).uno
p⟦(0 : Int)⟧').op ≫ ((shiftFunctorZero C Int).inv.app X.unop).op
参数：X : Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `Int.add_left_neg`：∀ (a : ℤ), -a + a = 0
· 使用定理 `Int.add_right_neg`：∀ (a : ℤ), a + -a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pretriangulated.shiftFunctorZero_op_hom_app`：shiftFunctor
Zero_op_hom_app (X : Cᵒᵖ) : (shiftFunctorZero Cᵒᵖ Int).hom.app X = (shiftFunctor
OpIso C 0 0 (zero_add 0)).hom.app X ≫ ((shiftFun…
· 使用定理 `CategoryTheory.unop_comp`：unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z
} : (f ≫ g).unop = g.unop ≫ f.unop
· 使用定理 `Quiver.Hom.unop_op`：Quiver.Hom.unop_op {X Y : C} (f : X ⟶ Y) : f.op.unop
 = f
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CategoryTheory.shiftFunctorCompIsoId_zero_zero_inv_app`：shiftFunctorComp
IsoId_zero_zero_inv_app (X : C) : (shiftFunctorCompIsoId C 0 0 (add_zero 0)).inv
.app X = (shiftFunctorZero C A).inv.app X ≫ …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
lemma opShiftFunctorEquivalence_zero_unitIso_inv_app (X : Cᵒᵖ) :
    (opShiftFunctorEquivalence C 0).unitIso.inv.app X =
      (((shiftFunctorZero Cᵒᵖ ℤ).hom.app X).unop⟦(0 : ℤ)⟧').op ≫
        ((shiftFunctorZero C ℤ).inv.app X.unop).op := by
  apply Quiver.Hom.unop_inj
  dsimp [opShiftFunctorEquivalence]
  rw [shiftFunctorZero_op_hom_app, unop_comp, Quiver.Hom.unop_op, Functor.map_comp,
    shiftFunctorCompIsoId_zero_zero_inv_app, assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_add_unitIso_hom_app_e
q** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：opShiftFunctorEquivalence_add_unitIso_hom_app_eq (X : Cᵒᵖ) (m n p : Int) (
h : m + n = p
参数：X : Cᵒᵖ；m n p : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.add_left_neg`：∀ (a : ℤ), -a + a = 0
· 使用定理 `Int.add_right_neg`：∀ (a : ℤ), a + -a = 0
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Pretriangulated.shiftFunctorAdd'_op_inv_app`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.HasS
hift C ℤ] (X : Cᵒᵖ)   (a₁ a₂ a₃ : ℤ) (h : a₁ + a…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Pretriangulated.shiftFunctor_op_map`：shiftFunctor_op_map 
{K L : Cᵒᵖ} (φ : K ⟶ L) (n m : Int) (hnm : n + m = 0
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `CategoryTheory.shiftFunctorCompIsoId_add'_hom_app`：∀ {C : Type u} {A : T
ype u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddGroup A]   [inst
_2 : CategoryTheory.HasShift C A] {X : …
-/
lemma opShiftFunctorEquivalence_add_unitIso_hom_app_eq
    (X : Cᵒᵖ) (m n p : ℤ) (h : m + n = p := by lia) :
    (opShiftFunctorEquivalence C p).unitIso.hom.app X =
      (opShiftFunctorEquivalence C n).unitIso.hom.app X ≫
      (((opShiftFunctorEquivalence C m).unitIso.hom.app (X⟦n⟧)).unop⟦n⟧').op ≫
      ((shiftFunctorAdd' C m n p h).hom.app _).op ≫
      (((shiftFunctorAdd' Cᵒᵖ n m p (by lia)).inv.app X).unop⟦p⟧').op := by
  dsimp [opShiftFunctorEquivalence]
  simp only [shiftFunctorAdd'_op_inv_app _ n m p (by lia) _ _ _ (add_neg_cancel n)
    (add_neg_cancel m) (add_neg_cancel p), shiftFunctor_op_map _ m (-m),
    Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [Functor.map_id, Functor.map_id, Functor.map_id, Functor.map_id,
    id_comp, id_comp, id_comp, comp_id, comp_id]
  dsimp
  rw [comp_id, shiftFunctorCompIsoId_add'_hom_app _ _ _ _ _ _
    (neg_add_cancel m) (neg_add_cancel n) (neg_add_cancel p) h]
  dsimp
  rw [Category.assoc, Category.assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_add_unitIso_inv_app_e
q** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：opShiftFunctorEquivalence_add_unitIso_inv_app_eq (X : Cᵒᵖ) (m n p : Int) (
h : m + n = p
参数：X : Cᵒᵖ；m n p : Int。
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
· 使用定理 `CategoryTheory.Functor.instIsSplitMonoApp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_add_unitIso_hom
_app_eq`：opShiftFunctorEquivalence_add_unitIso_hom_app_eq (X : Cᵒᵖ) (m n p : Int
) (h : m + n = p
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opShiftFunctorEquivalence_add_unitIso_inv_app_eq
    (X : Cᵒᵖ) (m n p : ℤ) (h : m + n = p := by lia) :
    (opShiftFunctorEquivalence C p).unitIso.inv.app X =
      (((shiftFunctorAdd' Cᵒᵖ n m p (by lia)).hom.app X).unop⟦p⟧').op ≫
      ((shiftFunctorAdd' C m n p h).inv.app _).op ≫
      (((opShiftFunctorEquivalence C m).unitIso.inv.app (X⟦n⟧)).unop⟦n⟧').op ≫
      (opShiftFunctorEquivalence C n).unitIso.inv.app X := by
  rw [← cancel_mono ((opShiftFunctorEquivalence C p).unitIso.hom.app X), Iso.inv_hom_id_app,
    opShiftFunctorEquivalence_add_unitIso_hom_app_eq _ _ _ _ h,
    Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc]
  apply Quiver.Hom.unop_inj
  dsimp
  simp only [Category.assoc,
    ← unop_comp, Iso.inv_hom_id_app, Functor.comp_obj, Functor.op_obj, unop_id,
    Functor.map_id, id_comp, ← Functor.map_comp, Iso.hom_inv_id_app]
/-
**CategoryTheory.Pretriangulated.shift_unop_opShiftFunctorEquivalence_counitIso_
inv_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：shift_unop_opShiftFunctorEquivalence_counitIso_inv_app (X : Cᵒᵖ) (n : Int)
 : ((opShiftFunctorEquivalence C n).counitIso.inv.app X).unop⟦n⟧' = ((opShiftFun
ctorEquivalence C n).unitIso.hom.app ((Opposite.op ((X.unop)⟦n⟧)))).unop
参数：X : Cᵒᵖ；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Equivalence.unit_app_inverse`：unit_app_inverse (e : C ≌ D
) (Y : D) : e.unit.app (e.inverse.obj Y) = e.inverse.map (e.counitInv.app Y)
-/
lemma shift_unop_opShiftFunctorEquivalence_counitIso_inv_app (X : Cᵒᵖ) (n : ℤ) :
    ((opShiftFunctorEquivalence C n).counitIso.inv.app X).unop⟦n⟧' =
      ((opShiftFunctorEquivalence C n).unitIso.hom.app ((Opposite.op ((X.unop)⟦n⟧)))).unop :=
  Quiver.Hom.op_inj ((opShiftFunctorEquivalence C n).unit_app_inverse X).symm
/-
**CategoryTheory.Pretriangulated.shift_unop_opShiftFunctorEquivalence_counitIso_
hom_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：shift_unop_opShiftFunctorEquivalence_counitIso_hom_app (X : Cᵒᵖ) (n : Int)
 : ((opShiftFunctorEquivalence C n).counitIso.hom.app X).unop⟦n⟧' = ((opShiftFun
ctorEquivalence C n).unitIso.inv.app ((Opposite.op (X.unop⟦n⟧)))).unop
参数：X : Cᵒᵖ；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Equivalence.unitInv_app_inverse`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (e : C ≌ D) (Y : D…
-/
lemma shift_unop_opShiftFunctorEquivalence_counitIso_hom_app (X : Cᵒᵖ) (n : ℤ) :
    ((opShiftFunctorEquivalence C n).counitIso.hom.app X).unop⟦n⟧' =
      ((opShiftFunctorEquivalence C n).unitIso.inv.app ((Opposite.op (X.unop⟦n⟧)))).unop :=
  Quiver.Hom.op_inj ((opShiftFunctorEquivalence C n).unitInv_app_inverse X).symm
/-
**CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_counitIso_inv_app_shi
ft** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：opShiftFunctorEquivalence_counitIso_inv_app_shift (X : Cᵒᵖ) (n : Int) : (o
pShiftFunctorEquivalence C n).counitIso.inv.app (X⟦n⟧) = ((opShiftFunctorEquival
ence C n).unitIso.hom.app X)⟦n⟧'
参数：X : Cᵒᵖ；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.counitInv_app_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (e : C ≌ D) (X : C…
-/
lemma opShiftFunctorEquivalence_counitIso_inv_app_shift (X : Cᵒᵖ) (n : ℤ) :
    (opShiftFunctorEquivalence C n).counitIso.inv.app (X⟦n⟧) =
      ((opShiftFunctorEquivalence C n).unitIso.hom.app X)⟦n⟧' :=
  (opShiftFunctorEquivalence C n).counitInv_app_functor X
/-
**CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_counitIso_hom_app_shi
ft** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：opShiftFunctorEquivalence_counitIso_hom_app_shift (X : Cᵒᵖ) (n : Int) : (o
pShiftFunctorEquivalence C n).counitIso.hom.app (X⟦n⟧) = ((opShiftFunctorEquival
ence C n).unitIso.inv.app X)⟦n⟧'
参数：X : Cᵒᵖ；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.counit_app_functor`：counit_app_functor (e : C
 ≌ D) (X : C) : e.counit.app (e.functor.obj X) = e.functor.map (e.unitInv.app X)
-/
lemma opShiftFunctorEquivalence_counitIso_hom_app_shift (X : Cᵒᵖ) (n : ℤ) :
    (opShiftFunctorEquivalence C n).counitIso.hom.app (X⟦n⟧) =
      ((opShiftFunctorEquivalence C n).unitIso.inv.app X)⟦n⟧' :=
  (opShiftFunctorEquivalence C n).counit_app_functor X

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Pretriangulated.shiftFunctorCompIsoId_op_hom_app** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：shiftFunctorCompIsoId_op_hom_app (X : Cᵒᵖ) (n m : Int) (hnm : n + m = 0
参数：X : Cᵒᵖ；n m : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Pretriangulated.shiftFunctorAdd'_op_inv_app`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.HasS
hift C ℤ] (X : Cᵒᵖ)   (a₁ a₂ a₃ : ℤ) (h : a₁ + a…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftFunctorCompIsoId_op_hom_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    (shiftFunctorCompIsoId Cᵒᵖ n m hnm).hom.app X =
      ((shiftFunctorOpIso C n m hnm).hom.app X)⟦m⟧' ≫
        (shiftFunctorOpIso C m n (by lia)).hom.app (Opposite.op (X.unop⟦m⟧)) ≫
          ((shiftFunctorCompIsoId C m n (by lia)).inv.app X.unop).op := by
  simp [shiftFunctorCompIsoId, shiftFunctorZero_op_hom_app X,
    shiftFunctorAdd'_op_inv_app X n m 0 hnm m n 0 hnm (by lia) (add_zero 0)]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Pretriangulated.shiftFunctorCompIsoId_op_inv_app** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：shiftFunctorCompIsoId_op_inv_app (X : Cᵒᵖ) (n m : Int) (hnm : n + m = 0
参数：X : Cᵒᵖ；n m : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `CategoryTheory.Pretriangulated.shiftFunctorZero_op_inv_app`：shiftFunctor
Zero_op_inv_app (X : Cᵒᵖ) : (shiftFunctorZero Cᵒᵖ Int).inv.app X = ((shiftFuncto
rZero C Int).hom.app X.unop).op ≫ (shiftFunctorO…
· 使用定理 `CategoryTheory.Pretriangulated.shiftFunctorAdd'_op_hom_app`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.HasS
hift C ℤ] (X : Cᵒᵖ)   (a₁ a₂ a₃ : ℤ) (h : a₁ + a…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftFunctorCompIsoId_op_inv_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    (shiftFunctorCompIsoId Cᵒᵖ n m hnm).inv.app X =
      ((shiftFunctorCompIsoId C m n (by omega)).hom.app X.unop).op ≫
        (shiftFunctorOpIso C m n (by omega)).inv.app (Opposite.op (X.unop⟦m⟧)) ≫
          ((shiftFunctorOpIso C n m hnm).inv.app X)⟦m⟧' := by
  simp [shiftFunctorCompIsoId, shiftFunctorZero_op_inv_app X,
    shiftFunctorAdd'_op_hom_app X n m 0 hnm m n 0 hnm (by lia) (add_zero 0)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Pretriangulated.shift_opShiftFunctorEquivalence_counitIso_inv_a
pp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：shift_opShiftFunctorEquivalence_counitIso_inv_app (X : C) (m n : Int) (hmn
 : m + n = 0
参数：X : C；m n : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.add_right_neg`：∀ (a : ℤ), a + -a = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Pretriangulated.shiftFunctor_op_map`：shiftFunctor_op_map 
{K L : Cᵒᵖ} (φ : K ⟶ L) (n m : Int) (hnm : n + m = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.shift_shiftFunctorCompIsoId_hom_app`：shift_shiftFunctorCo
mpIsoId_hom_app (n m : A) (h : n + m = 0) (X : C) : ((shiftFunctorCompIsoId C n 
m h).hom.app X)⟦n⟧' = (shiftFunctorCompI…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.shiftFunctorComm_inv_app_of_add_eq_zero`：shiftFunctorComm
_inv_app_of_add_eq_zero (m n : A) (hmn : m + n = 0) (X : C) : (shiftFunctorComm 
C m n).inv.app X = (shiftFunctorCompIsoId C …
· 使用引理 `CategoryTheory.Pretriangulated.shiftFunctorCompIsoId_op_hom_app`：shiftFu
nctorCompIsoId_op_hom_app (X : Cᵒᵖ) (n m : Int) (hnm : n + m = 0
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.Pretriangulated.shiftFunctorCompIsoId_op_inv_app`：shiftFu
nctorCompIsoId_op_inv_app (X : Cᵒᵖ) (n m : Int) (hnm : n + m = 0
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Mathlib.Tactic.CategoryTheory.CancelIso.hom_inv_id_of_eq_assoc`：hom_inv_
id_of_eq_assoc {C : Type*} [Category* C] {x y : C} (f : x ⟶ y) [IsIso f] (g : y 
⟶ x) (h : inv f = g) {z : C} (k : x ⟶ z) : f ≫ g ≫ k…
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用引理 `CategoryTheory.shiftFunctorCompIsoId_naturality_1`：shiftFunctorCompIsoId
_naturality_1 (i j : A) (hij : i + j = 0) : (shiftFunctorCompIsoId C i j hij).in
v.app X ≫ f⟦i⟧'⟦j⟧' ≫ (shiftFunctorComp…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma shift_opShiftFunctorEquivalence_counitIso_inv_app
    (X : C) (m n : ℤ) (hmn : m + n = 0 := by lia) :
    ((opShiftFunctorEquivalence C n).counitIso.inv.app (Opposite.op X))⟦m⟧' =
      (opShiftFunctorEquivalence C n).counitIso.inv.app ((Opposite.op X)⟦m⟧) ≫
        (((shiftFunctorOpIso C m n hmn).hom.app (Opposite.op X)).unop⟦n⟧').op⟦n⟧' ≫
          ((shiftFunctorOpIso C m n hmn).inv.app (Opposite.op (X⟦n⟧)))⟦n⟧' ≫
            (shiftFunctorComm Cᵒᵖ n m).inv.app (Opposite.op (X⟦n⟧)) := by
  obtain rfl : m = -n := by lia
  dsimp [opShiftFunctorEquivalence]
  simp only [shiftFunctor_op_map _ (-n) n, shiftFunctor_op_map _ n (-n),
    shiftFunctorComm_inv_app_of_add_eq_zero n (-n) (by lia), assoc,
    shiftFunctorCompIsoId_op_inv_app, shiftFunctorCompIsoId_op_hom_app,
    shift_shiftFunctorCompIsoId_hom_app, op_comp, unop_comp, Quiver.Hom.unop_op,
    Functor.map_comp, Iso.inv_hom_id_app_assoc, Functor.op_obj]
  apply Quiver.Hom.unop_inj
  simp

/-- Given objects `X` and `Y` in `Cᵒᵖ`, this is the bijection
`(op (X.unop⟦n⟧) ⟶ Y) ≃ (X ⟶ Y⟦n⟧)` for any `n : ℤ`. -/
/-
**CategoryTheory.Pretriangulated.opShiftFunctorEquivalenceSymmHomEquiv** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：opShiftFunctorEquivalenceSymmHomEquiv {n : Int} {X Y : Cᵒᵖ} : (Opposite.op
 (X.unop⟦n⟧) ⟶ Y) ≃ (X ⟶ Y⟦n⟧)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given objects `X` and `Y` in `Cᵒᵖ`, this is the bijection
`(op (X.unop⟦n⟧) ⟶ Y) ≃ (X ⟶ Y⟦n⟧)` for any `n : ℤ`.
-/
def opShiftFunctorEquivalenceSymmHomEquiv {n : ℤ} {X Y : Cᵒᵖ} :
    (Opposite.op (X.unop⟦n⟧) ⟶ Y) ≃ (X ⟶ Y⟦n⟧) :=
  (opShiftFunctorEquivalence C n).symm.toAdjunction.homEquiv X Y

@[reassoc]
/-
**CategoryTheory.Pretriangulated.opShiftFunctorEquivalenceSymmHomEquiv_apply** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：opShiftFunctorEquivalenceSymmHomEquiv_apply {n : Int} {X Y : Cᵒᵖ} (f : Opp
osite.op (X.unop⟦n⟧) ⟶ Y) : opShiftFunctorEquivalenceSymmHomEquiv f = (opShiftFu
nctorEquivalence C n).counitIso.inv.app X ≫ (shiftFunctor Cᵒᵖ n).map f
参数：f : Opposite.op (X.unop⟦n⟧) ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opShiftFunctorEquivalenceSymmHomEquiv_apply {n : ℤ} {X Y : Cᵒᵖ}
    (f : Opposite.op (X.unop⟦n⟧) ⟶ Y) :
    opShiftFunctorEquivalenceSymmHomEquiv f =
      (opShiftFunctorEquivalence C n).counitIso.inv.app X ≫ (shiftFunctor Cᵒᵖ n).map f := rfl

@[reassoc]
/-
**CategoryTheory.Pretriangulated.opShiftFunctorEquivalenceSymmHomEquiv_left_inv*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：opShiftFunctorEquivalenceSymmHomEquiv_left_inv {n : Int} {X Y : Cᵒᵖ} (f : 
Opposite.op (X.unop⟦n⟧) ⟶ Y) : ((opShiftFunctorEquivalence C n).unitIso.inv.app 
Y).unop ≫ (opShiftFunctorEquivalenceSymmHomEquiv f).unop⟦n⟧' = f.unop
参数：f : Opposite.op (X.unop⟦n⟧) ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
lemma opShiftFunctorEquivalenceSymmHomEquiv_left_inv
    {n : ℤ} {X Y : Cᵒᵖ} (f : Opposite.op (X.unop⟦n⟧) ⟶ Y) :
    ((opShiftFunctorEquivalence C n).unitIso.inv.app Y).unop ≫
      (opShiftFunctorEquivalenceSymmHomEquiv f).unop⟦n⟧' = f.unop :=
  Quiver.Hom.op_inj (opShiftFunctorEquivalenceSymmHomEquiv.left_inv f)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Pretriangulated.shift_opShiftFunctorEquivalenceSymmHomEquiv_uno
p** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：shift_opShiftFunctorEquivalenceSymmHomEquiv_unop {n : Int} {X Y : Cᵒᵖ} (f 
: Opposite.op (X.unop⟦n⟧) ⟶ Y) : (opShiftFunctorEquivalenceSymmHomEquiv f).unop⟦
n⟧' = ((opShiftFunctorEquivalence C n).unitIso.hom.app Y).unop ≫ f.unop
参数：f : Opposite.op (X.unop⟦n⟧) ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Pretriangulated.opShiftFunctorEquivalenceSymmHomEquiv_lef
t_inv`：opShiftFunctorEquivalenceSymmHomEquiv_left_inv {n : Int} {X Y : Cᵒᵖ} (f :
 Opposite.op (X.unop⟦n⟧) ⟶ Y) : ((opShiftFunctorEquivalence C n).un…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.unop_hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u_1}   [inst_1 : CategoryTheory.Cate
gory.{v_1, u_1} D] {F G : Category…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shift_opShiftFunctorEquivalenceSymmHomEquiv_unop
    {n : ℤ} {X Y : Cᵒᵖ} (f : Opposite.op (X.unop⟦n⟧) ⟶ Y) :
    (opShiftFunctorEquivalenceSymmHomEquiv f).unop⟦n⟧' =
      ((opShiftFunctorEquivalence C n).unitIso.hom.app Y).unop ≫ f.unop := by
  rw [← opShiftFunctorEquivalenceSymmHomEquiv_left_inv]
  simp

end Pretriangulated

end CategoryTheory

