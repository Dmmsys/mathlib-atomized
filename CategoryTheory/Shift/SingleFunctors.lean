/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Functors from a category to a category with a shift

Given a category `C`, and a category `D` equipped with a shift by a monoid `A`,
we define a structure `SingleFunctors C D A` which contains the data of
functors `functor a : C ⥤ D` for all `a : A` and isomorphisms
`shiftIso n a a' h : functor a' ⋙ shiftFunctor D n ≅ functor a`
whenever `n + a = a'`. These isomorphisms should satisfy certain compatibilities
with respect to the shift on `D`.

This notion is similar to `Functor.ShiftSequence` which can be used in order to
attach shifted versions of a homological functor `D ⥤ C` with `D` a
triangulated category and `C` an abelian category. However, the definition
`SingleFunctors` is for functors in the other direction: it is meant to
ease the formalization of the compatibilities with shifts of the
functors `C ⥤ CochainComplex C ℤ` (or `C ⥤ DerivedCategory C` (TODO))
which sends an object `X : C` to a complex where `X` sits in a single degree.

-/

@[expose] public section

open CategoryTheory Category ZeroObject Limits Functor

variable (C D E E' : Type*) [Category* C] [Category* D] [Category* E] [Category* E']
  (A : Type*) [AddMonoid A] [HasShift D A] [HasShift E A] [HasShift E' A]

namespace CategoryTheory

/-- The type of families of functors `A → C ⥤ D` which are compatible with
the shift by `A` on the category `D`. -/
/-
**CategoryTheory.SingleFunctors** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u_1) →   (D : Type u_2) →     [CategoryTheory.Category.{v_1, u_1
} C] →       [inst : CategoryTheory.Category.{v_2, u_2} D] →         (A : Type u
_5) →           [inst_1 : AddMonoid A] → [CategoryTheory.HasShift D A] → Type (m
ax (max (max (max u_1 u_2) u_5) v_1) v_2)
参数：max (max (max u_1 u_2) u_5) v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of families of functors `A → C ⥤ D` which are compatible with
the shift by `A` on the category `D`.
-/
structure SingleFunctors where
  /-- a family of functors `C ⥤ D` indexed by the elements of the additive monoid `A` -/
  functor (a : A) : C ⥤ D
  /-- the isomorphism `functor a' ⋙ shiftFunctor D n ≅ functor a` when `n + a = a'` -/
  shiftIso (n a a' : A) (ha' : n + a = a') : functor a' ⋙ shiftFunctor D n ≅ functor a
  /-- `shiftIso 0` is the obvious isomorphism. -/
  shiftIso_zero (a : A) :
    shiftIso 0 a a (zero_add a) = isoWhiskerLeft _ (shiftFunctorZero D A)
  /-- `shiftIso (m + n)` is determined by `shiftIso m` and `shiftIso n`. -/
  shiftIso_add (n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'') :
    shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha'']) =
      isoWhiskerLeft _ (shiftFunctorAdd D m n) ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (shiftIso m a' a'' ha'') _ ≪≫ shiftIso n a a' ha'

variable {C D E A}
variable (F G H : SingleFunctors C D A)

namespace SingleFunctors

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.SingleFunctors.shiftIso_add_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.SingleFunctors`。
形式化陈述：shiftIso_add_hom_app (n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' 
= a'') (X : C) : (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).hom.a
pp X = (shiftFunctorAdd D m n).hom.app ((F.functor a'').obj X) ≫ ((F.shiftIso m 
a' a'' ha'').hom.app X)⟦n⟧' ≫ (F.shiftIso n a a' ha').hom.app X
参数：n m a a' a'' : A；ha' : n + a = a'；ha'' : m + a' = a''；X : C。
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
· 使用定理 `CategoryTheory.SingleFunctors.shiftIso_add`：∀ {C : Type u_1} {D : Type u
_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} D] {A : Type u_…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftIso_add_hom_app (n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).hom.app X =
      (shiftFunctorAdd D m n).hom.app ((F.functor a'').obj X) ≫
        ((F.shiftIso m a' a'' ha'').hom.app X)⟦n⟧' ≫
        (F.shiftIso n a a' ha').hom.app X := by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.SingleFunctors.shiftIso_add_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.SingleFunctors`。
形式化陈述：shiftIso_add_inv_app (n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' 
= a'') (X : C) : (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).inv.a
pp X = (F.shiftIso n a a' ha').inv.app X ≫ ((F.shiftIso m a' a'' ha'').inv.app X
)⟦n⟧' ≫ (shiftFunctorAdd D m n).inv.app ((F.functor a'').obj X)
参数：n m a a' a'' : A；ha' : n + a = a'；ha'' : m + a' = a''；X : C。
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
· 使用定理 `CategoryTheory.SingleFunctors.shiftIso_add`：∀ {C : Type u_1} {D : Type u
_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} D] {A : Type u_…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftIso_add_inv_app (n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).inv.app X =
      (F.shiftIso n a a' ha').inv.app X ≫
      ((F.shiftIso m a' a'' ha'').inv.app X)⟦n⟧' ≫
      (shiftFunctorAdd D m n).inv.app ((F.functor a'').obj X) := by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']
/-
**CategoryTheory.SingleFunctors.shiftIso_add'** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.SingleFunctors`。
形式化陈述：shiftIso_add' (n m mn : A) (hnm : m + n = mn) (a a' a'' : A) (ha' : n + a 
= a') (ha'' : m + a' = a'') : F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', 
add_assoc]) = isoWhiskerLeft _ (shiftFunctorAdd' D m n mn hnm) ≪≫ (Functor.assoc
iator _ _ _).symm ≪≫ isoWhiskerRight (F.shiftIso m a' a'' ha'') _ ≪≫ F.shiftIso 
n a a' ha'
参数：n m mn : A；hnm : m + n = mn；a a' a'' : A；ha' : n + a = a'；ha'' : m + a' = a''
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd`：∀ (C : Type u) {A : 
Type u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [in
st_2 : CategoryTheory.HasShift C A] (i j…
· 使用定理 `CategoryTheory.SingleFunctors.shiftIso_add`：∀ {C : Type u_1} {D : Type u
_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} D] {A : Type u_…
-/
lemma shiftIso_add' (n m mn : A) (hnm : m + n = mn) (a a' a'' : A)
    (ha' : n + a = a') (ha'' : m + a' = a'') :
    F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc]) =
      isoWhiskerLeft _ (shiftFunctorAdd' D m n mn hnm) ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (F.shiftIso m a' a'' ha'') _ ≪≫ F.shiftIso n a a' ha' := by
  subst hnm
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd, shiftIso_add]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.SingleFunctors.shiftIso_add'_hom_app** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.SingleFunctors`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {A : Type u_5} [inst_2 : A
ddMonoid A]   [inst_3 : CategoryTheory.HasShift D A] (F : CategoryTheory.SingleF
unctors C D A) (n m mn : A) (hnm : m + n = mn)   (a a' a'' : A) (ha' : n + a = a
') (ha'' : m + a' = a'') (X : C),   (F.shiftIso mn a a'' ⋯).hom.app X =     Cate
goryTheory.CategoryStruct.comp ((CategoryTheory.shiftFunctorAdd' D m n mn hnm).h
om.app ((F.functor a'').obj X))       (CategoryTheory.CategoryStruct.comp ((Cate
goryTheory.shiftFunctor D n).map ((F.shiftIso m a' a'' ha'').hom.app X))        
 ((F.shiftIso n a a' ha').hom.app X))
参数：F : CategoryTheory.SingleFunctors C D A；n m mn : A；hnm : m + n = mn；a a' a'' 
: A；ha' : n + a = a'；ha'' : m + a' = a''；X : C；F.shiftIso mn a a'' ⋯；(CategoryTh
eory.shiftFunctorAdd' D m n mn hnm).hom.app ((F.functor a'').obj X)；CategoryTheo
ry.CategoryStruct.comp ((CategoryTheory.shiftFunctor D n).map ((F.shiftIso m a' 
a'' ha'').hom.app X))         ((F.shiftIso n a a' ha').hom.app X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.SingleFunctors.shiftIso_add'`：shiftIso_add' (n m mn : A) 
(hnm : m + n = mn) (a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'') : F.s
hiftIso mn a a'' (by rw [← hnm, ←…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftIso_add'_hom_app (n m mn : A) (hnm : m + n = mn) (a a' a'' : A)
    (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc])).hom.app X =
      (shiftFunctorAdd' D m n mn hnm).hom.app ((F.functor a'').obj X) ≫
        ((F.shiftIso m a' a'' ha'').hom.app X)⟦n⟧' ≫ (F.shiftIso n a a' ha').hom.app X := by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.SingleFunctors.shiftIso_add'_inv_app** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.SingleFunctors`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {A : Type u_5} [inst_2 : A
ddMonoid A]   [inst_3 : CategoryTheory.HasShift D A] (F : CategoryTheory.SingleF
unctors C D A) (n m mn : A) (hnm : m + n = mn)   (a a' a'' : A) (ha' : n + a = a
') (ha'' : m + a' = a'') (X : C),   (F.shiftIso mn a a'' ⋯).inv.app X =     Cate
goryTheory.CategoryStruct.comp ((F.shiftIso n a a' ha').inv.app X)       (Catego
ryTheory.CategoryStruct.comp ((CategoryTheory.shiftFunctor D n).map ((F.shiftIso
 m a' a'' ha'').inv.app X))         ((CategoryTheory.shiftFunctorAdd' D m n mn h
nm).inv.app ((F.functor a'').obj X)))
参数：F : CategoryTheory.SingleFunctors C D A；n m mn : A；hnm : m + n = mn；a a' a'' 
: A；ha' : n + a = a'；ha'' : m + a' = a''；X : C；F.shiftIso mn a a'' ⋯；(F.shiftIso
 n a a' ha').inv.app X；CategoryTheory.CategoryStruct.comp ((CategoryTheory.shift
Functor D n).map ((F.shiftIso m a' a'' ha'').inv.app X))         ((CategoryTheor
y.shiftFunctorAdd' D m n mn hnm).inv.app ((F.functor a'').obj X))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.SingleFunctors.shiftIso_add'`：shiftIso_add' (n m mn : A) 
(hnm : m + n = mn) (a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'') : F.s
hiftIso mn a a'' (by rw [← hnm, ←…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftIso_add'_inv_app (n m mn : A) (hnm : m + n = mn) (a a' a'' : A)
    (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc])).inv.app X =
      (F.shiftIso n a a' ha').inv.app X ≫
      ((F.shiftIso m a' a'' ha'').inv.app X)⟦n⟧' ≫
      (shiftFunctorAdd' D m n mn hnm).inv.app ((F.functor a'').obj X) := by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

@[simp]
/-
**CategoryTheory.SingleFunctors.shiftIso_zero_hom_app** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.SingleFunctors`。
形式化陈述：shiftIso_zero_hom_app (a : A) (X : C) : (F.shiftIso 0 a a (zero_add a)).ho
m.app X = (shiftFunctorZero D A).hom.app _
参数：a : A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SingleFunctors.shiftIso_zero`：∀ {C : Type u_1} {D : Type 
u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Ca
tegory.{v_2, u_2} D] {A : Type u_…
-/
lemma shiftIso_zero_hom_app (a : A) (X : C) :
    (F.shiftIso 0 a a (zero_add a)).hom.app X = (shiftFunctorZero D A).hom.app _ := by
  rw [shiftIso_zero]
  rfl

@[simp]
/-
**CategoryTheory.SingleFunctors.shiftIso_zero_inv_app** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.SingleFunctors`。
形式化陈述：shiftIso_zero_inv_app (a : A) (X : C) : (F.shiftIso 0 a a (zero_add a)).in
v.app X = (shiftFunctorZero D A).inv.app _
参数：a : A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SingleFunctors.shiftIso_zero`：∀ {C : Type u_1} {D : Type 
u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Ca
tegory.{v_2, u_2} D] {A : Type u_…
-/
lemma shiftIso_zero_inv_app (a : A) (X : C) :
    (F.shiftIso 0 a a (zero_add a)).inv.app X = (shiftFunctorZero D A).inv.app _ := by
  rw [shiftIso_zero]
  rfl

/-- The morphisms in the category `SingleFunctors C D A` -/
@[ext]
/-
**CategoryTheory.SingleFunctors.Hom** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Si
ngleFunctors`。
形式化陈述：Hom where /-- a family of natural transformations `F.functor a ⟶ G.functor
 a` -/ hom (a : A) : F.functor a ⟶ G.functor a comm (n a a' : A) (ha' : n + a = 
a') : (F.shiftIso n a a' ha').hom ≫ hom a = whiskerRight (hom a') (shiftFunctor 
D n) ≫ (G.shiftIso n a a' ha').hom
参数：a : A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphisms in the category `SingleFunctors C D A`
-/
structure Hom where
  /-- a family of natural transformations `F.functor a ⟶ G.functor a` -/
  hom (a : A) : F.functor a ⟶ G.functor a
  comm (n a a' : A) (ha' : n + a = a') : (F.shiftIso n a a' ha').hom ≫ hom a =
    whiskerRight (hom a') (shiftFunctor D n) ≫ (G.shiftIso n a a' ha').hom := by cat_disch

namespace Hom

attribute [reassoc] comm
attribute [local simp] comm comm_assoc

/-- The identity morphism in `SingleFunctors C D A`. -/
@[simps]
/-
**CategoryTheory.SingleFunctors.Hom.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.SingleFunctors.Hom`。
形式化陈述：id : Hom F F where hom _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity morphism in `SingleFunctors C D A`.
-/
def id : Hom F F where
  hom _ := 𝟙 _

variable {F G H}

/-- The composition of morphisms in `SingleFunctors C D A`. -/
@[simps]
/-
**CategoryTheory.SingleFunctors.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.SingleFunctors.Hom`。
形式化陈述：comp (α : Hom F G) (β : Hom G H) : Hom F H where hom a
参数：α : Hom F G；β : Hom G H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of morphisms in `SingleFunctors C D A`.
-/
def comp (α : Hom F G) (β : Hom G H) : Hom F H where
  hom a := α.hom a ≫ β.hom a

end Hom

/-
**CategoryTheory.SingleFunctors.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Singl
eFunctors`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (SingleFunctors C D A) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[simp]
/-
**CategoryTheory.SingleFunctors.id_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.SingleFunctors`。
形式化陈述：id_hom (a : A) : Hom.hom (𝟙 F) a = 𝟙 _
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_hom (a : A) : Hom.hom (𝟙 F) a = 𝟙 _ := rfl

variable {F G H}

@[simp, reassoc]
/-
**CategoryTheory.SingleFunctors.comp_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.SingleFunctors`。
形式化陈述：comp_hom (f : F ⟶ G) (g : G ⟶ H) (a : A) : (f ≫ g).hom a = f.hom a ≫ g.hom
 a
参数：f : F ⟶ G；g : G ⟶ H；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_hom (f : F ⟶ G) (g : G ⟶ H) (a : A) : (f ≫ g).hom a = f.hom a ≫ g.hom a := rfl

@[ext]
/-
**CategoryTheory.SingleFunctors.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.SingleFunctors`。
形式化陈述：hom_ext (f g : F ⟶ G) (h : f.hom = g.hom) : f = g
参数：f g : F ⟶ G；h : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SingleFunctors.Hom.ext`：∀ {C : Type u_1} {D : Type u_2} {
inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryTheory.Category
.{v_2, u_2} D} {A : Type u_…
-/
lemma hom_ext (f g : F ⟶ G) (h : f.hom = g.hom) : f = g := Hom.ext h

/-- Construct an isomorphism in `SingleFunctors C D A` by giving
level-wise isomorphisms and checking compatibility only in the forward direction. -/
@[simps]
/-
**CategoryTheory.SingleFunctors.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
SingleFunctors`。
形式化陈述：isoMk (iso : forall a, (F.functor a ≅ G.functor a)) (comm : forall (n a a'
 : A) (ha' : n + a = a'), (F.shiftIso n a a' ha').hom ≫ (iso a).hom = whiskerRig
ht (iso a').hom (shiftFunctor D n) ≫ (G.shiftIso n a a' ha').hom) : F ≅ G where 
hom
参数：iso : forall a, (F.functor a ≅ G.functor a)；comm : forall (n a a' : A) (ha' :
 n + a = a'), (F.shiftIso n a a' ha').hom ≫ (iso a).hom = whiskerRight (iso a').
hom (shiftFunctor D n) ≫ (G.shiftIso n a a' ha').hom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism in `SingleFunctors C D A` by giving
level-wise isomorphisms and checking compatibility only in the forward direction
.
-/
def isoMk (iso : ∀ a, (F.functor a ≅ G.functor a))
    (comm : ∀ (n a a' : A) (ha' : n + a = a'), (F.shiftIso n a a' ha').hom ≫ (iso a).hom =
      whiskerRight (iso a').hom (shiftFunctor D n) ≫ (G.shiftIso n a a' ha').hom) :
    F ≅ G where
  hom :=
    { hom := fun a => (iso a).hom
      comm := comm }
  inv :=
    { hom := fun a => (iso a).inv
      comm := fun n a a' ha' => by
        rw [← cancel_mono (iso a).hom, assoc, assoc, Iso.inv_hom_id, comp_id, comm,
          ← whiskerRight_comp_assoc, Iso.inv_hom_id, whiskerRight_id', id_comp] }

variable (C D)

/-- The evaluation `SingleFunctors C D A ⥤ C ⥤ D` for some `a : A`. -/
@[simps]
/-
**CategoryTheory.SingleFunctors.evaluation** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.SingleFunctors`。
形式化陈述：evaluation (a : A) : SingleFunctors C D A ⥤ C ⥤ D where obj F
参数：a : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The evaluation `SingleFunctors C D A ⥤ C ⥤ D` for some `a : A`.
-/
def evaluation (a : A) : SingleFunctors C D A ⥤ C ⥤ D where
  obj F := F.functor a
  map {_ _} φ := φ.hom a

variable {C D}

@[reassoc (attr := simp)]
/-
**CategoryTheory.SingleFunctors.hom_inv_id_hom** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.SingleFunctors`。
形式化陈述：hom_inv_id_hom (e : F ≅ G) (n : A) : e.hom.hom n ≫ e.inv.hom n = 𝟙 _
参数：e : F ≅ G；n : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.SingleFunctors.comp_hom`：comp_hom (f : F ⟶ G) (g : G ⟶ H)
 (a : A) : (f ≫ g).hom a = f.hom a ≫ g.hom a
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用引理 `CategoryTheory.SingleFunctors.id_hom`：id_hom (a : A) : Hom.hom (𝟙 F) a =
 𝟙 _
-/
lemma hom_inv_id_hom (e : F ≅ G) (n : A) : e.hom.hom n ≫ e.inv.hom n = 𝟙 _ := by
  rw [← comp_hom, e.hom_inv_id, id_hom]

@[reassoc (attr := simp)]
/-
**CategoryTheory.SingleFunctors.inv_hom_id_hom** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.SingleFunctors`。
形式化陈述：inv_hom_id_hom (e : F ≅ G) (n : A) : e.inv.hom n ≫ e.hom.hom n = 𝟙 _
参数：e : F ≅ G；n : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.SingleFunctors.comp_hom`：comp_hom (f : F ⟶ G) (g : G ⟶ H)
 (a : A) : (f ≫ g).hom a = f.hom a ≫ g.hom a
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用引理 `CategoryTheory.SingleFunctors.id_hom`：id_hom (a : A) : Hom.hom (𝟙 F) a =
 𝟙 _
-/
lemma inv_hom_id_hom (e : F ≅ G) (n : A) : e.inv.hom n ≫ e.hom.hom n = 𝟙 _ := by
  rw [← comp_hom, e.inv_hom_id, id_hom]

@[reassoc (attr := simp)]
/-
**CategoryTheory.SingleFunctors.hom_inv_id_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.SingleFunctors`。
形式化陈述：hom_inv_id_hom_app (e : F ≅ G) (n : A) (X : C) : (e.hom.hom n).app X ≫ (e.
inv.hom n).app X = 𝟙 _
参数：e : F ≅ G；n : A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.comp_app`：comp_app {F G H : C ⥤ D} (α : F ⟶ G) (
β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X
· 使用引理 `CategoryTheory.SingleFunctors.hom_inv_id_hom`：hom_inv_id_hom (e : F ≅ G)
 (n : A) : e.hom.hom n ≫ e.inv.hom n = 𝟙 _
· 使用定理 `CategoryTheory.NatTrans.id_app`：id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ 
F).app X = 𝟙 (F.obj X)
-/
lemma hom_inv_id_hom_app (e : F ≅ G) (n : A) (X : C) :
    (e.hom.hom n).app X ≫ (e.inv.hom n).app X = 𝟙 _ := by
  rw [← NatTrans.comp_app, hom_inv_id_hom, NatTrans.id_app]

@[reassoc (attr := simp)]
/-
**CategoryTheory.SingleFunctors.inv_hom_id_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.SingleFunctors`。
形式化陈述：inv_hom_id_hom_app (e : F ≅ G) (n : A) (X : C) : (e.inv.hom n).app X ≫ (e.
hom.hom n).app X = 𝟙 _
参数：e : F ≅ G；n : A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.comp_app`：comp_app {F G H : C ⥤ D} (α : F ⟶ G) (
β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X
· 使用引理 `CategoryTheory.SingleFunctors.inv_hom_id_hom`：inv_hom_id_hom (e : F ≅ G)
 (n : A) : e.inv.hom n ≫ e.hom.hom n = 𝟙 _
· 使用定理 `CategoryTheory.NatTrans.id_app`：id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ 
F).app X = 𝟙 (F.obj X)
-/
lemma inv_hom_id_hom_app (e : F ≅ G) (n : A) (X : C) :
    (e.inv.hom n).app X ≫ (e.hom.hom n).app X = 𝟙 _ := by
  rw [← NatTrans.comp_app, inv_hom_id_hom, NatTrans.id_app]
/-
**CategoryTheory.SingleFunctors.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Singl
eFunctors`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : F ⟶ G) [IsIso f] (n : A) : IsIso (f.hom n) :=
  inferInstanceAs <| IsIso ((evaluation C D n).map f)

variable (F)

set_option backward.defeqAttrib.useBackward true in
/-- Given `F : SingleFunctors C D A`, and a functor `G : D ⥤ E` which commutes
with the shift by `A`, this is the "composition" of `F` and `G` in `SingleFunctors C E A`. -/
@[simps! functor shiftIso_hom_app shiftIso_inv_app]
/-
**CategoryTheory.SingleFunctors.postcomp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.SingleFunctors`。
形式化陈述：postcomp (G : D ⥤ E) [G.CommShift A] : SingleFunctors C E A where functor 
a
参数：G : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : SingleFunctors C D A`, and a functor `G : D ⥤ E` which commutes
with the shift by `A`, this is the "composition" of `F` and `G` in `SingleFuncto
rs C E A`.
-/
def postcomp (G : D ⥤ E) [G.CommShift A] :
    SingleFunctors C E A where
  functor a := F.functor a ⋙ G
  shiftIso n a a' ha' :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (G.commShiftIso n).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (F.shiftIso n a a' ha') G
  shiftIso_zero a := by
    ext X
    dsimp
    simp only [Functor.commShiftIso_zero, Functor.CommShift.isoZero_inv_app,
      SingleFunctors.shiftIso_zero_hom_app, id_comp, assoc, ← G.map_comp, Iso.inv_hom_id_app,
      Functor.map_id, Functor.id_obj, comp_id]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext X
    dsimp
    simp only [F.shiftIso_add_hom_app n m a a' a'' ha' ha'', Functor.commShiftIso_add,
      Functor.CommShift.isoAdd_inv_app, Functor.map_comp, id_comp, assoc,
      Functor.commShiftIso_inv_naturality_assoc]
    simp only [← G.map_comp, Iso.inv_hom_id_app_assoc]

variable (C A)

set_option backward.defeqAttrib.useBackward true in
/-- The functor `SingleFunctors C D A ⥤ SingleFunctors C E A` given by the postcomposition
by a functor `G : D ⥤ E` which commutes with the shift. -/
@[simps]
/-
**CategoryTheory.SingleFunctors.postcompFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.SingleFunctors`。
形式化陈述：postcompFunctor (G : D ⥤ E) [G.CommShift A] : SingleFunctors C D A ⥤ Singl
eFunctors C E A where obj F
参数：G : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `SingleFunctors C D A ⥤ SingleFunctors C E A` given by the postcompo
sition
by a functor `G : D ⥤ E` which commutes with the shift.
-/
def postcompFunctor (G : D ⥤ E) [G.CommShift A] :
    SingleFunctors C D A ⥤ SingleFunctors C E A where
  obj F := F.postcomp G
  map {F₁ F₂} φ :=
    { hom := fun a => whiskerRight (φ.hom a) G
      comm := fun n a a' ha' => by
        ext X
        simpa using G.congr_map (congr_app (φ.comm n a a' ha') X) }

variable {C E' A}

set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism `(F.postcomp G).postcomp G' ≅ F.postcomp (G ⋙ G')`. -/
@[simps!]
/-
**CategoryTheory.SingleFunctors.postcompPostcompIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.SingleFunctors`。
形式化陈述：postcompPostcompIso (G : D ⥤ E) (G' : E ⥤ E') [G.CommShift A] [G'.CommShif
t A] : (F.postcomp G).postcomp G' ≅ F.postcomp (G ⋙ G')
参数：G : D ⥤ E；G' : E ⥤ E'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `(F.postcomp G).postcomp G' ≅ F.postcomp (G ⋙ G')`.
-/
def postcompPostcompIso (G : D ⥤ E) (G' : E ⥤ E') [G.CommShift A] [G'.CommShift A] :
    (F.postcomp G).postcomp G' ≅ F.postcomp (G ⋙ G') :=
  isoMk (fun _ => Functor.associator _ _ _) (fun n a a' ha' => by
    ext X
    simp [Functor.commShiftIso_comp_inv_app])

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `F.postcomp G ≅ F.postcomp G'` induced by an isomorphism `e : G ≅ G'`
which commutes with the shift. -/
@[simps!]
/-
**CategoryTheory.SingleFunctors.postcompIsoOfIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.SingleFunctors`。
形式化陈述：postcompIsoOfIso {G G' : D ⥤ E} (e : G ≅ G') [G.CommShift A] [G'.CommShift
 A] [NatTrans.CommShift e.hom A] : F.postcomp G ≅ F.postcomp G'
参数：e : G ≅ G'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `F.postcomp G ≅ F.postcomp G'` induced by an isomorphism `e : G 
≅ G'`
which commutes with the shift.
-/
def postcompIsoOfIso {G G' : D ⥤ E} (e : G ≅ G') [G.CommShift A] [G'.CommShift A]
    [NatTrans.CommShift e.hom A] :
    F.postcomp G ≅ F.postcomp G' :=
  isoMk (fun a => isoWhiskerLeft (F.functor a) e) (fun n a a' ha' => by
    ext X
    simp [NatTrans.shift_app e.hom n])

end SingleFunctors

end CategoryTheory

