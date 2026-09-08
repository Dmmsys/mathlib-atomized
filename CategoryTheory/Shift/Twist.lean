/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Center.Basic
public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Twisting a shift

Given a category `C` equipped with a shift by a monoid `A`, we introduce
a structure `t : TwistShiftData C A` which consists of a collection of
invertible elements in the center of the category `C` (typically, `C` will
be preadditive, and these will be signs), which allow to introduce a type
synonym category `t.Category` with identical shift functors as `C` but where
the isomorphisms `shiftFunctorAdd` have been modified.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] (A : Type w) [AddMonoid A] [HasShift C A]

/-- Given a category `C` equipped with a shift by a monoid `A` -/
/-
**CategoryTheory.TwistShiftData** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：TwistShiftData where /-- The invertible elements in the center of `C` whic
h are used to modify the `shiftFunctorAdd` isomorphisms. -/ z (a b : A) : (CatCe
nter C)ˣ z_zero_zero : z 0 0 = 1
参数：a b : A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a category `C` equipped with a shift by a monoid `A`
-/
structure TwistShiftData where
  /-- The invertible elements in the center of `C` which are used to
  modify the `shiftFunctorAdd` isomorphisms. -/
  z (a b : A) : (CatCenter C)ˣ
  z_zero_zero : z 0 0 = 1 := by cat_disch
  assoc (a b c : A) : z (a + b) c * z a b = z a (b + c) * z b c := by cat_disch
  commShift (a b : A) : NatTrans.CommShift (z a b).val A := by infer_instance

namespace TwistShiftData

variable {C A} (t : TwistShiftData C A)

attribute [local simp] z_zero_zero

@[simp]
/-
**CategoryTheory.TwistShiftData.z_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.TwistShiftData`。
形式化陈述：z_zero_right (a : A) : t.z a 0 = 1
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CategoryTheory.TwistShiftData.z_zero_zero`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {A : Type w} [inst_1 : AddMonoid A]   [inst_2 : Cate
goryTheory.HasShift C A] (self …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `CategoryTheory.TwistShiftData.assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {A : Type w} [inst_1 : AddMonoid A]   [inst_2 : CategoryTh
eory.HasShift C A] (self …
-/
lemma z_zero_right (a : A) : t.z a 0 = 1 := by simpa using t.assoc a 0 0

@[simp]
/-
**CategoryTheory.TwistShiftData.z_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.TwistShiftData`。
形式化陈述：z_zero_left (b : A) : t.z 0 b = 1
参数：b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CategoryTheory.TwistShiftData.z_zero_right`：z_zero_right (a : A) : t.z a
 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `CategoryTheory.TwistShiftData.assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {A : Type w} [inst_1 : AddMonoid A]   [inst_2 : CategoryTh
eory.HasShift C A] (self …
-/
lemma z_zero_left (b : A) : t.z 0 b = 1 := by simpa using t.assoc 0 0 b

attribute [instance] commShift

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.TwistShiftData.shift_z_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.TwistShiftData`。
形式化陈述：shift_z_app (a b c : A) (X : C) : ((t.z a b).val.app X)⟦c⟧' = (t.z a b).va
l.app (X⟦c⟧)
参数：a b c : A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.commShiftIso_id_hom_app`：∀ (C : Type u_1) [inst :
 CategoryTheory.Category.{v_1, u_1} C] {A : Type u_4} [inst_1 : AddMonoid A]   [
inst_2 : CategoryTheory.HasShift C A…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.NatTrans.shift_app_comm`：shift_app_comm (a : A) (X : C) :
 (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' = τ.app (X⟦a⟧) ≫ (F₂.commShiftIso
 a).hom.app X
· 使用定理 `CategoryTheory.TwistShiftData.commShift`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {A : Type w} [inst_1 : AddMonoid A]   [inst_2 : Catego
ryTheory.HasShift C A] (self …
-/
lemma shift_z_app (a b c : A) (X : C) :
    ((t.z a b).val.app X)⟦c⟧' = (t.z a b).val.app (X⟦c⟧) := by
  simpa using NatTrans.shift_app_comm (t.z a b).val c X

/-- Given `t : TwistShiftData C A`, this is a type synonym for the category `C`,
which the same shift functors as `C` but where the `shiftFunctorAdd` isomorphisms
have been modified using `t`. -/
@[nolint unusedArguments]
/-
**CategoryTheory.TwistShiftData.Category** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.TwistShiftData`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {A : Type
 w} →       [inst_1 : AddMonoid A] → [inst_2 : CategoryTheory.HasShift C A] → Ca
tegoryTheory.TwistShiftData C A → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `t : TwistShiftData C A`, this is a type synonym for the category `C`,
which the same shift functors as `C` but where the `shiftFunctorAdd` isomorphism
s
have been modified using `t`.
-/
protected def Category (_ : TwistShiftData C A) : Type u := C
/-
**CategoryTheory.TwistShiftData.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Twist
ShiftData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category t.Category := inferInstanceAs (Category C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given `t : TwistShiftData C A`, the shift on the category `TwistShift t` has
the same shift functors as `C`, the same isomorphism `shiftFunctorZero` isomorphism,
but the `shiftFunctorAdd` isomorphisms are modified using `t`. -/
/-
**CategoryTheory.TwistShiftData.shiftMkCore** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.TwistShiftData`。
形式化陈述：shiftMkCore : ShiftMkCore t.Category A where F a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `t : TwistShiftData C A`, the shift on the category `TwistShift t` has
the same shift functors as `C`, the same isomorphism `shiftFunctorZero` isomorph
ism,
but the `shiftFunctorAdd` isomorphisms are modified using `t`.
-/
def shiftMkCore : ShiftMkCore t.Category A where
  F a := shiftFunctor C a
  zero := shiftFunctorZero C A
  add a b := NatIso.ofComponents (fun X ↦ t.z a b • (shiftFunctorAdd C a b).app X) (by
    simp [CatCenter.naturality_assoc, CatCenter.naturality, CatCenter.smul_iso_hom_eq])
  add_zero_hom_app := by simp [shiftFunctorAdd_add_zero_hom_app, CatCenter.smul_iso_hom_eq]
  zero_add_hom_app := by simp [shiftFunctorAdd_zero_add_hom_app, CatCenter.smul_iso_hom_eq]
  assoc_hom_app a b c X := by
    dsimp
    simp only [Functor.map_comp, Category.assoc, CatCenter.smul_iso_hom_eq]
    rw [CatCenter.naturality, CatCenter.naturality_assoc, CatCenter.naturality_assoc,
      CatCenter.naturality_assoc, CatCenter.naturality_assoc, CatCenter.naturality_assoc,
      t.shift_z_app, CatCenter.naturality, CatCenter.naturality_assoc,
      ← CatCenter.mul_app_assoc, ← CatCenter.mul_app_assoc,
      ← Units.val_mul, ← Units.val_mul, t.assoc a b c]
    simp [shiftFunctorAdd_assoc_hom_app (C := C) a b c X, shiftFunctorAdd']
/-
**CategoryTheory.TwistShiftData.hasShift** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.TwistShiftData`。
形式化陈述：hasShift : HasShift t.Category A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasShift : HasShift t.Category A := hasShiftMk _ _ (shiftMkCore t)

/-- Given `t : TwistShiftData C A`, the shift functors on `t.Category`
identify to the shift functors on `C`. -/
/-
**CategoryTheory.TwistShiftData.shiftIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.TwistShiftData`。
形式化陈述：shiftIso (m : A) : shiftFunctor t.Category m ≅ shiftFunctor C m
参数：m : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `t : TwistShiftData C A`, the shift functors on `t.Category`
identify to the shift functors on `C`.
-/
noncomputable def shiftIso (m : A) : shiftFunctor t.Category m ≅ shiftFunctor C m :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.TwistShiftData.shiftFunctor_map** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.TwistShiftData`。
形式化陈述：shiftFunctor_map {X Y : t.Category} (f : X ⟶ Y) (m : A) : (shiftFunctor t.
Category m).map f = (t.shiftIso m).hom.app X ≫ (shiftFunctor C m).map f ≫ (t.shi
ftIso m).inv.app Y
参数：f : X ⟶ Y；m : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftFunctor_map {X Y : t.Category} (f : X ⟶ Y) (m : A) :
    (shiftFunctor t.Category m).map f =
      (t.shiftIso m).hom.app X ≫ (shiftFunctor C m).map f ≫ (t.shiftIso m).inv.app Y := by
  simp
/-
**CategoryTheory.TwistShiftData.shiftFunctorZero_hom_app** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.TwistShiftData`。
形式化陈述：shiftFunctorZero_hom_app (X : t.Category) : (shiftFunctorZero t.Category A
).hom.app X = (shiftIso t (0 : A)).hom.app X ≫ (shiftFunctorZero C A).hom.app X
参数：X : t.Category。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma shiftFunctorZero_hom_app (X : t.Category) :
    (shiftFunctorZero t.Category A).hom.app X =
      (shiftIso t (0 : A)).hom.app X ≫ (shiftFunctorZero C A).hom.app X :=
  (Category.id_comp _).symm
/-
**CategoryTheory.TwistShiftData.shiftFunctorZero_inv_app** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.TwistShiftData`。
形式化陈述：shiftFunctorZero_inv_app (X : t.Category) : (shiftFunctorZero t.Category A
).inv.app X = (shiftFunctorZero C A).inv.app X ≫ (shiftIso t (0 : A)).inv.app X
参数：X : t.Category。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma shiftFunctorZero_inv_app (X : t.Category) :
    (shiftFunctorZero t.Category A).inv.app X =
      (shiftFunctorZero C A).inv.app X ≫ (shiftIso t (0 : A)).inv.app X :=
  (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.TwistShiftData.shiftFunctorAdd'_hom_app** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.TwistShiftData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A : Type w} [ins
t_1 : AddMonoid A]   [inst_2 : CategoryTheory.HasShift C A] (t : CategoryTheory.
TwistShiftData C A) (i j k : A) (h : i + j = k)   (X : t.Category),   (CategoryT
heory.shiftFunctorAdd' t.Category i j k h).hom.app X =     ↑(t.z i j) •       Ca
tegoryTheory.CategoryStruct.comp ((t.shiftIso k).hom.app X)         (CategoryThe
ory.CategoryStruct.comp ((CategoryTheory.shiftFunctorAdd' C i j k h).hom.app X) 
          (CategoryTheory.CategoryStruct.comp ((CategoryTheory.shiftFunctor C j)
.map ((t.shiftIso i).inv.app X))             ((t.shiftIso j).inv.app ((CategoryT
heory.shiftFunctor t.Category i).obj X))))
参数：t : CategoryTheory.TwistShiftData C A；i j k : A；h : i + j = k；X : t.Category；
CategoryTheory.shiftFunctorAdd' t.Category i j k h；t.z i j；(t.shiftIso k).hom.ap
p X；CategoryTheory.CategoryStruct.comp ((CategoryTheory.shiftFunctorAdd' C i j k
 h).hom.app X)           (CategoryTheory.CategoryStruct.comp ((CategoryTheory.sh
iftFunctor C j).map ((t.shiftIso i).inv.app X))             ((t.shiftIso j).inv.
app ((CategoryTheory.shiftFunctor t.Category i).obj X)))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftFunctorAdd'_hom_app (i j k : A) (h : i + j = k) (X : t.Category) :
    (shiftFunctorAdd' t.Category i j k h).hom.app X =
      (t.z i j).val • (t.shiftIso k).hom.app X ≫
        (shiftFunctorAdd' C i j k h).hom.app X ≫
        (shiftFunctor C j).map ((t.shiftIso i).inv.app X) ≫ (t.shiftIso j).inv.app _ := by
  have : (shiftFunctorAdd' t.Category i j k h).hom.app X =
      (t.z i j).val • (shiftFunctorAdd' C i j k h).hom.app X := by
    dsimp [shiftFunctorAdd']
    cat_disch
  rw [this]
  congr
  change _ = 𝟙 _ ≫ _ ≫ (shiftFunctor C j).map (𝟙 _) ≫ 𝟙 _
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.TwistShiftData.shiftFunctorAdd'_inv_app** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.TwistShiftData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A : Type w} [ins
t_1 : AddMonoid A]   [inst_2 : CategoryTheory.HasShift C A] (t : CategoryTheory.
TwistShiftData C A) (i j k : A) (h : i + j = k)   (X : t.Category),   (CategoryT
heory.shiftFunctorAdd' t.Category i j k h).inv.app X =     ↑(t.z i j)⁻¹ •       
CategoryTheory.CategoryStruct.comp ((t.shiftIso j).hom.app ((CategoryTheory.shif
tFunctor t.Category i).obj X))         (CategoryTheory.CategoryStruct.comp ((Cat
egoryTheory.shiftFunctor C j).map ((t.shiftIso i).hom.app X))           (Categor
yTheory.CategoryStruct.comp ((CategoryTheory.shiftFunctorAdd' C i j k h).inv.app
 X)             ((t.shiftIso k).inv.app X)))
参数：t : CategoryTheory.TwistShiftData C A；i j k : A；h : i + j = k；X : t.Category；
CategoryTheory.shiftFunctorAdd' t.Category i j k h；t.z i j；(t.shiftIso j).hom.ap
p ((CategoryTheory.shiftFunctor t.Category i).obj X)；CategoryTheory.CategoryStru
ct.comp ((CategoryTheory.shiftFunctor C j).map ((t.shiftIso i).hom.app X))      
     (CategoryTheory.CategoryStruct.comp ((CategoryTheory.shiftFunctorAdd' C i j
 k h).inv.app X)             ((t.shiftIso k).inv.app X))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftFunctorAdd'_inv_app (i j k : A) (h : i + j = k) (X : t.Category) :
    (shiftFunctorAdd' t.Category i j k h).inv.app X =
      ((t.z i j)⁻¹).val • (t.shiftIso j).hom.app _ ≫
        (shiftFunctor C j).map ((t.shiftIso i).hom.app X) ≫
        (shiftFunctorAdd' C i j k h).inv.app X ≫
        (t.shiftIso k).inv.app X := by
  have : (shiftFunctorAdd' t.Category i j k h).inv.app X =
      ((t.z i j)⁻¹).val • (shiftFunctorAdd' C i j k h).inv.app X := by
    dsimp [shiftFunctorAdd']
    cat_disch
  rw [this]
  congr
  change _ = 𝟙 _ ≫ (shiftFunctor C j).map (𝟙 _) ≫ _ ≫ 𝟙 _
  simp

end TwistShiftData

end CategoryTheory

