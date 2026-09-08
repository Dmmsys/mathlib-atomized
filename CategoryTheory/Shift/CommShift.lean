/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.CategoryTheory.NatIso

/-!
# Functors which commute with shifts

Let `C` and `D` be two categories equipped with shifts by an additive monoid `A`. In this file,
we define the notion of functor `F : C ⥤ D` which "commutes" with these shifts. The associated
type class is `[F.CommShift A]`. The data consists of commutation isomorphisms
`F.commShiftIso a : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` for all `a : A`
which satisfy a compatibility with the addition and the zero. After this was formalised in Lean,
it was found that this definition is exactly the definition which appears in Jean-Louis
Verdier's thesis (I 1.2.3/1.2.4), although the language is different. (In Verdier's thesis,
the shift is not given by a monoidal functor `Discrete A ⥤ C ⥤ C`, but by a fibred
category `C ⥤ BA`, where `BA` is the category with one object, the endomorphisms of which
identify to `A`. The choice of a cleavage for this fibered category gives the individual
shift functors.)

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

open Category

namespace Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  (F : C ⥤ D) (G : D ⥤ E) (A B : Type*) [AddMonoid A] [AddCommMonoid B]
  [HasShift C A] [HasShift D A] [HasShift E A]
  [HasShift C B] [HasShift D B]

namespace CommShift

/-- For any functor `F : C ⥤ D`, this is the obvious isomorphism
`shiftFunctor C (0 : A) ⋙ F ≅ F ⋙ shiftFunctor D (0 : A)` deduced from the
isomorphisms `shiftFunctorZero` on both categories `C` and `D`. -/
@[simps!]
/-
**CategoryTheory.Functor.CommShift.isoZero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor.CommShift`。
形式化陈述：isoZero : shiftFunctor C (0 : A) ⋙ F ≅ F ⋙ shiftFunctor D (0 : A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any functor `F : C ⥤ D`, this is the obvious isomorphism
`shiftFunctor C (0 : A) ⋙ F ≅ F ⋙ shiftFunctor D (0 : A)` deduced from the
isomorphisms `shiftFunctorZero` on both categories `C` and `D`.
-/
noncomputable def isoZero : shiftFunctor C (0 : A) ⋙ F ≅ F ⋙ shiftFunctor D (0 : A) :=
  isoWhiskerRight (shiftFunctorZero C A) F ≪≫ F.leftUnitor ≪≫
     F.rightUnitor.symm ≪≫ isoWhiskerLeft F (shiftFunctorZero D A).symm

/-- For any functor `F : C ⥤ D` and any `a` in `A` such that `a = 0`,
this is the obvious isomorphism `shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` deduced from the
isomorphisms `shiftFunctorZero'` on both categories `C` and `D`. -/
@[simps!]
/-
**CategoryTheory.Functor.CommShift.isoZero'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor.CommShift`。
形式化陈述：isoZero' (a : A) (ha : a = 0) : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D 
a
参数：a : A；ha : a = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any functor `F : C ⥤ D` and any `a` in `A` such that `a = 0`,
this is the obvious isomorphism `shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` de
duced from the
isomorphisms `shiftFunctorZero'` on both categories `C` and `D`.
-/
noncomputable def isoZero' (a : A) (ha : a = 0) : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a :=
  isoWhiskerRight (shiftFunctorZero' C a ha) F ≪≫ F.leftUnitor ≪≫
     F.rightUnitor.symm ≪≫ isoWhiskerLeft F (shiftFunctorZero' D a ha).symm

@[simp]
/-
**CategoryTheory.Functor.CommShift.isoZero'_eq_isoZero** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Functor.CommShift`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : CategoryTheory.Functo
r C D) (A : Type u_4) [inst_2 : AddMonoid A]   [inst_3 : CategoryTheory.HasShift
 C A] [inst_4 : CategoryTheory.HasShift D A],   CategoryTheory.Functor.CommShift
.isoZero' F A 0 ⋯ = CategoryTheory.Functor.CommShift.isoZero F A
参数：F : CategoryTheory.Functor C D；A : Type u_4。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.CommShift.isoZero_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isoZero'_eq_isoZero : isoZero' F A 0 rfl = isoZero F A := by
  ext; simp [isoZero', shiftFunctorZero']

variable {F A}

/-- If a functor `F : C ⥤ D` is equipped with "commutation isomorphisms" with the
shifts by `a` and `b`, then there is a commutation isomorphism with the shift by `c` when
`a + b = c`. -/
@[simps!]
/-
**CategoryTheory.Functor.CommShift.isoAdd'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor.CommShift`。
形式化陈述：isoAdd' {a b c : A} (h : a + b = c) (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shift
Functor D a) (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) : shiftFunctor C
 c ⋙ F ≅ F ⋙ shiftFunctor D c
参数：h : a + b = c；e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a；e₂ : shiftFunc
tor C b ⋙ F ≅ F ⋙ shiftFunctor D b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a functor `F : C ⥤ D` is equipped with "commutation isomorphisms" with the
shifts by `a` and `b`, then there is a commutation isomorphism with the shift by
 `c` when
`a + b = c`.
-/
noncomputable def isoAdd' {a b c : A} (h : a + b = c)
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) :
    shiftFunctor C c ⋙ F ≅ F ⋙ shiftFunctor D c :=
  isoWhiskerRight (shiftFunctorAdd' C _ _ _ h) F ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ e₂ ≪≫ (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e₁ _ ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (shiftFunctorAdd' D _ _ _ h).symm

/-- If a functor `F : C ⥤ D` is equipped with "commutation isomorphisms" with the
shifts by `a` and `b`, then there is a commutation isomorphism with the shift by `a + b`. -/
/-
**CategoryTheory.Functor.CommShift.isoAdd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor.CommShift`。
形式化陈述：isoAdd {a b : A} (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a) (e₂ : 
shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) : shiftFunctor C (a + b) ⋙ F ≅ F ⋙ 
shiftFunctor D (a + b)
参数：e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a；e₂ : shiftFunctor C b ⋙ F ≅ 
F ⋙ shiftFunctor D b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a functor `F : C ⥤ D` is equipped with "commutation isomorphisms" with the
shifts by `a` and `b`, then there is a commutation isomorphism with the shift by
 `a + b`.
-/
noncomputable def isoAdd {a b : A}
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) :
    shiftFunctor C (a + b) ⋙ F ≅ F ⋙ shiftFunctor D (a + b) :=
  CommShift.isoAdd' rfl e₁ e₂

@[simp]
/-
**CategoryTheory.Functor.CommShift.isoAdd_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Functor.CommShift`。
形式化陈述：isoAdd_hom_app {a b : A} (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a
) (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) (X : C) : (CommShift.isoAdd
 e₁ e₂).hom.app X = F.map ((shiftFunctorAdd C a b).hom.app X) ≫ e₂.hom.app ((shi
ftFunctor C a).obj X) ≫ (shiftFunctor D b).map (e₁.hom.app X) ≫ (shiftFunctorAdd
 D a b).inv.app (F.obj X)
参数：e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a；e₂ : shiftFunctor C b ⋙ F ≅ 
F ⋙ shiftFunctor D b；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.CommShift.isoAdd'_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] {F : Categor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd`：∀ (C : Type u) {A : 
Type u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [in
st_2 : CategoryTheory.HasShift C A] (i j…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isoAdd_hom_app {a b : A}
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) (X : C) :
      (CommShift.isoAdd e₁ e₂).hom.app X =
        F.map ((shiftFunctorAdd C a b).hom.app X) ≫ e₂.hom.app ((shiftFunctor C a).obj X) ≫
          (shiftFunctor D b).map (e₁.hom.app X) ≫ (shiftFunctorAdd D a b).inv.app (F.obj X) := by
  simp only [isoAdd, isoAdd'_hom_app, shiftFunctorAdd'_eq_shiftFunctorAdd]

@[simp]
/-
**CategoryTheory.Functor.CommShift.isoAdd_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Functor.CommShift`。
形式化陈述：isoAdd_inv_app {a b : A} (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a
) (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) (X : C) : (CommShift.isoAdd
 e₁ e₂).inv.app X = (shiftFunctorAdd D a b).hom.app (F.obj X) ≫ (shiftFunctor D 
b).map (e₁.inv.app X) ≫ e₂.inv.app ((shiftFunctor C a).obj X) ≫ F.map ((shiftFun
ctorAdd C a b).inv.app X)
参数：e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a；e₂ : shiftFunctor C b ⋙ F ≅ 
F ⋙ shiftFunctor D b；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.CommShift.isoAdd'_inv_app`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] {F : Categor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd`：∀ (C : Type u) {A : 
Type u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [in
st_2 : CategoryTheory.HasShift C A] (i j…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isoAdd_inv_app {a b : A}
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) (X : C) :
      (CommShift.isoAdd e₁ e₂).inv.app X = (shiftFunctorAdd D a b).hom.app (F.obj X) ≫
        (shiftFunctor D b).map (e₁.inv.app X) ≫ e₂.inv.app ((shiftFunctor C a).obj X) ≫
        F.map ((shiftFunctorAdd C a b).inv.app X) := by
  simp only [isoAdd, isoAdd'_inv_app, shiftFunctorAdd'_eq_shiftFunctorAdd]
/-
**CategoryTheory.Functor.CommShift.isoAdd'_isoZero** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Functor.CommShift`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {F : CategoryTheory.Functo
r C D} {A : Type u_4} [inst_2 : AddMonoid A]   [inst_3 : CategoryTheory.HasShift
 C A] [inst_4 : CategoryTheory.HasShift D A] {a : A}   (e : (CategoryTheory.shif
tFunctor C a).comp F ≅ F.comp (CategoryTheory.shiftFunctor D a)),   CategoryTheo
ry.Functor.CommShift.isoAdd' ⋯ e (CategoryTheory.Functor.CommShift.isoZero F A) 
= e
参数：e : (CategoryTheory.shiftFunctor C a).comp F ≅ F.comp (CategoryTheory.shiftFu
nctor D a)；CategoryTheory.Functor.CommShift.isoZero F A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.CommShift.isoAdd'_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] {F : Categor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.shiftFunctorAdd'_add_zero_hom_app`：∀ {C : Type u} {A : Ty
pe u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [inst
_2 : CategoryTheory.HasShift C A] (a :…
· 使用定理 `CategoryTheory.Functor.CommShift.isoZero_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.shiftFunctorAdd'_add_zero_inv_app`：∀ {C : Type u} {A : Ty
pe u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [inst
_2 : CategoryTheory.HasShift C A] (a :…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isoAdd'_isoZero {a : A}
    (e : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a) :
    isoAdd' (add_zero a) e (isoZero F A) = e := by
  ext X
  simp [shiftFunctorAdd'_add_zero_hom_app, ← Functor.map_comp_assoc,
    shiftFunctorAdd'_add_zero_inv_app]
/-
**CategoryTheory.Functor.CommShift.isoZero_isoAdd'_** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Functor.CommShift`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {F : CategoryTheory.Functo
r C D} {A : Type u_4} [inst_2 : AddMonoid A]   [inst_3 : CategoryTheory.HasShift
 C A] [inst_4 : CategoryTheory.HasShift D A] {a : A}   (e : (CategoryTheory.shif
tFunctor C a).comp F ≅ F.comp (CategoryTheory.shiftFunctor D a)),   CategoryTheo
ry.Functor.CommShift.isoAdd' ⋯ (CategoryTheory.Functor.CommShift.isoZero F A) e 
= e
参数：e : (CategoryTheory.shiftFunctor C a).comp F ≅ F.comp (CategoryTheory.shiftFu
nctor D a)；CategoryTheory.Functor.CommShift.isoZero F A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.CommShift.isoAdd'_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] {F : Categor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.shiftFunctorAdd'_zero_add_hom_app`：∀ {C : Type u} {A : Ty
pe u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [inst
_2 : CategoryTheory.HasShift C A] (a :…
· 使用定理 `CategoryTheory.Functor.CommShift.isoZero_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.shiftFunctorAdd'_zero_add_inv_app`：∀ {C : Type u} {A : Ty
pe u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [inst
_2 : CategoryTheory.HasShift C A] (a :…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isoZero_isoAdd'_ {a : A}
    (e : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a) :
    isoAdd' (zero_add a) (isoZero F A) e = e := by
  ext X
  have := e.hom.naturality ((shiftFunctorZero C A).inv.app X)
  dsimp at this
  simp [shiftFunctorAdd'_zero_add_hom_app,
    shiftFunctorAdd'_zero_add_inv_app, ← map_comp,
    reassoc_of% this]
/-
**CategoryTheory.Functor.CommShift.isoAdd'_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Functor.CommShift`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {F : CategoryTheory.Functo
r C D} {A : Type u_4} [inst_2 : AddMonoid A]   [inst_3 : CategoryTheory.HasShift
 C A] [inst_4 : CategoryTheory.HasShift D A] {a b c ab bc abc : A}   (ea : (Cate
goryTheory.shiftFunctor C a).comp F ≅ F.comp (CategoryTheory.shiftFunctor D a)) 
  (eb : (CategoryTheory.shiftFunctor C b).comp F ≅ F.comp (CategoryTheory.shiftF
unctor D b))   (ec : (CategoryTheory.shiftFunctor C c).comp F ≅ F.comp (Category
Theory.shiftFunctor D c)) (hab : a + b = ab)   (hbc : b + c = bc) (h : a + b + c
 = abc),   CategoryTheory.Functor.CommShift.isoAdd' ⋯ (CategoryTheory.Functor.Co
mmShift.isoAdd' hab ea eb) ec =     CategoryTheory.Functor.CommShift.isoAdd' ⋯ e
a (CategoryTheory.Functor.CommShift.isoAdd' hbc eb ec)
参数：ea : (CategoryTheory.shiftFunctor C a).comp F ≅ F.comp (CategoryTheory.shiftF
unctor D a)；eb : (CategoryTheory.shiftFunctor C b).comp F ≅ F.comp (CategoryTheo
ry.shiftFunctor D b)；ec : (CategoryTheory.shiftFunctor C c).comp F ≅ F.comp (Cat
egoryTheory.shiftFunctor D c)；hab : a + b = ab；hbc : b + c = bc；h : a + b + c = 
abc；CategoryTheory.Functor.CommShift.isoAdd' hab ea eb；CategoryTheory.Functor.Co
mmShift.isoAdd' hbc eb ec。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.NatTrans.naturality_2`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   {F G : CategoryThe…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.CommShift.isoAdd'_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] {F : Categor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.shiftFunctorAdd'_assoc_hom_app`：∀ {C : Type u} {A : Type 
u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [inst_2 
: CategoryTheory.HasShift C A] (a₁ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.shiftFunctorAdd'_assoc_inv_app`：∀ {C : Type u} {A : Type 
u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [inst_2 
: CategoryTheory.HasShift C A] (a₁ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isoAdd'_assoc {a b c ab bc abc : A}
    (ea : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (eb : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b)
    (ec : shiftFunctor C c ⋙ F ≅ F ⋙ shiftFunctor D c)
    (hab : a + b = ab) (hbc : b + c = bc) (h : a + b + c = abc) :
    isoAdd' (show ab + c = abc by rwa [← hab]) (isoAdd' hab ea eb) ec =
      isoAdd' (show a + bc = abc by grind) ea (isoAdd' hbc eb ec) := by
  ext X
  have := NatTrans.naturality_2 ec.hom ((shiftFunctorAdd' C a b ab hab).app X)
  dsimp at this ⊢
  simp only [isoAdd'_hom_app, Category.assoc]
  rw [← NatTrans.naturality_assoc, ← this, Category.assoc, ← F.map_comp_assoc,
    shiftFunctorAdd'_assoc_hom_app a b c ab bc abc hab hbc h,
    Functor.map_comp_assoc, Category.assoc]
  simp_rw [← Functor.map_comp_assoc]
  simp [shiftFunctorAdd'_assoc_inv_app a b c ab bc abc hab hbc h]

end CommShift

/-- A functor `F` commutes with the shift by a monoid `A` if it is equipped with
commutation isomorphisms with the shifts by all `a : A`, and these isomorphisms
satisfy coherence properties with respect to `0 : A` and the addition in `A`. -/
/-
**CategoryTheory.Functor.CommShift** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：CommShift (F : C ⥤ D) (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D
 A] where /-- The commutation isomorphisms for all `a`-shifts this functor is eq
uipped with -/ commShiftIso (F) (a : A) : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFuncto
r D a commShiftIso_zero (F) (A) : commShiftIso 0 = CommShift.isoZero F A
参数：F : C ⥤ D；A : Type*；F；a : A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F` commutes with the shift by a monoid `A` if it is equipped with
commutation isomorphisms with the shifts by all `a : A`, and these isomorphisms
satisfy coherence properties with respect to `0 : A` and the addition in `A`.
-/
class CommShift (F : C ⥤ D) (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A] where
  /-- The commutation isomorphisms for all `a`-shifts this functor is equipped with -/
  commShiftIso (F) (a : A) : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a
  commShiftIso_zero (F) (A) : commShiftIso 0 = CommShift.isoZero F A := by cat_disch
  commShiftIso_add (F) (a b : A) :
    commShiftIso (a + b) = CommShift.isoAdd (commShiftIso a) (commShiftIso b) := by cat_disch

variable {A}

export CommShift (commShiftIso commShiftIso_zero commShiftIso_add)

section

variable [F.CommShift A]

-- Note: The following two lemmas are introduced in order to have more proofs work `by simp`.
-- Indeed, `simp only [(F.commShiftIso a).hom.naturality f]` would almost never work because
-- of the compositions of functors which appear in both the source and target of
-- `F.commShiftIso a`. Otherwise, we would be forced to use `erw [NatTrans.naturality]`.

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.commShiftIso_hom_naturality** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：commShiftIso_hom_naturality {X Y : C} (f : X ⟶ Y) (a : A) : dsimp% F.map (
f⟦a⟧') ≫ (F.commShiftIso a).hom.app Y = (F.commShiftIso a).hom.app X ≫ (F.map f)
⟦a⟧'
参数：f : X ⟶ Y；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma commShiftIso_hom_naturality {X Y : C} (f : X ⟶ Y) (a : A) :
    dsimp% F.map (f⟦a⟧') ≫ (F.commShiftIso a).hom.app Y =
      (F.commShiftIso a).hom.app X ≫ (F.map f)⟦a⟧' :=
  (F.commShiftIso a).hom.naturality f

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.commShiftIso_inv_naturality** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：commShiftIso_inv_naturality {X Y : C} (f : X ⟶ Y) (a : A) : dsimp% (F.map 
f)⟦a⟧' ≫ (F.commShiftIso a).inv.app Y = (F.commShiftIso a).inv.app X ≫ F.map (f⟦
a⟧')
参数：f : X ⟶ Y；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma commShiftIso_inv_naturality {X Y : C} (f : X ⟶ Y) (a : A) :
    dsimp% (F.map f)⟦a⟧' ≫ (F.commShiftIso a).inv.app Y =
      (F.commShiftIso a).inv.app X ≫ F.map (f⟦a⟧') :=
  (F.commShiftIso a).inv.naturality f

variable (A) in
set_option linter.docPrime false in
/-
**CategoryTheory.Functor.commShiftIso_zero'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：commShiftIso_zero' (a : A) (h : a = 0) : F.commShiftIso a = CommShift.isoZ
ero' F A a h
参数：a : A；h : a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.CommShift.isoZero'_eq_isoZero`：∀ {C : Type u_1} {
D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Category
Theory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.CommShift.commShiftIso_zero`：∀ {C : Type u_1} {D 
: Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryTh
eory.Category.{v_2, u_2} D} (F : Categor…
-/
lemma commShiftIso_zero' (a : A) (h : a = 0) :
    F.commShiftIso a = CommShift.isoZero' F A a h := by
  subst h; rw [CommShift.isoZero'_eq_isoZero, commShiftIso_zero]
/-
**CategoryTheory.Functor.commShiftIso_add'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：commShiftIso_add' {a b c : A} (h : a + b = c) : F.commShiftIso c = CommShi
ft.isoAdd' h (F.commShiftIso a) (F.commShiftIso b)
参数：h : a + b = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.CommShift.commShiftIso_add`：∀ {C : Type u_1} {D :
 Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryThe
ory.Category.{v_2, u_2} D} (F : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma commShiftIso_add' {a b c : A} (h : a + b = c) :
    F.commShiftIso c = CommShift.isoAdd' h (F.commShiftIso a) (F.commShiftIso b) := by
  subst h
  simp only [commShiftIso_add, CommShift.isoAdd]

end

namespace CommShift

variable (C) in
@[simps! -isSimp commShiftIso_hom_app commShiftIso_inv_app]
/-
**CategoryTheory.Functor.CommShift.id** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Functor.CommShift`。
形式化陈述：id : CommShift (𝟭 C) A where commShiftIso
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance id : CommShift (𝟭 C) A where
  commShiftIso := fun _ => rightUnitor _ ≪≫ (leftUnitor _).symm

@[simps! -isSimp commShiftIso_hom_app commShiftIso_inv_app]
/-
**CategoryTheory.Functor.CommShift.comp** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Functor.CommShift`。
形式化陈述：comp [F.CommShift A] [G.CommShift A] : (F ⋙ G).CommShift A where commShift
Iso a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance comp [F.CommShift A] [G.CommShift A] : (F ⋙ G).CommShift A where
  commShiftIso a := (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (F.commShiftIso a) _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (G.commShiftIso a) ≪≫
    (Functor.associator _ _ _).symm
  commShiftIso_zero := by
    ext X
    dsimp
    simp only [id_comp, comp_id, commShiftIso_zero, isoZero_hom_app, ← Functor.map_comp_assoc,
      assoc, Iso.inv_hom_id_app, id_obj, comp_map, comp_obj]
  commShiftIso_add := fun a b => by
    ext X
    dsimp
    simp only [commShiftIso_add, isoAdd_hom_app]
    dsimp
    simp only [comp_id, id_comp, assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, comp_obj]
    simp only [map_comp, assoc, commShiftIso_hom_naturality_assoc]

end CommShift

alias commShiftIso_id_hom_app := CommShift.id_commShiftIso_hom_app
alias commShiftIso_id_inv_app := CommShift.id_commShiftIso_inv_app
alias commShiftIso_comp_hom_app := CommShift.comp_commShiftIso_hom_app
alias commShiftIso_comp_inv_app := CommShift.comp_commShiftIso_inv_app

attribute [simp] commShiftIso_id_hom_app commShiftIso_id_inv_app

variable {B}

/-
**CategoryTheory.Functor.map_shiftFunctorComm_hom_app** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：map_shiftFunctorComm_hom_app [F.CommShift B] (X : C) (a b : B) : F.map ((s
hiftFunctorComm C a b).hom.app X) = (F.commShiftIso b).hom.app (X⟦a⟧) ≫ ((F.comm
ShiftIso a).hom.app X)⟦b⟧' ≫ (shiftFunctorComm D a b).hom.app (F.obj X) ≫ ((F.co
mmShiftIso b).inv.app X)⟦a⟧' ≫ (F.commShiftIso a).inv.app (X⟦b⟧)
参数：X : C；a b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.CommShift.commShiftIso_add`：∀ {C : Type u_1} {D :
 Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryThe
ory.Category.{v_2, u_2} D} (F : Categor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.shiftFunctorComm_eq`：shiftFunctorComm_eq (i j k : A) (h :
 i + j = k) : shiftFunctorComm C i j = (shiftFunctorAdd' C i j k h).symm ≪≫ shif
tFunctorAdd' C j i k (by…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd`：∀ (C : Type u) {A : 
Type u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [in
st_2 : CategoryTheory.HasShift C A] (i j…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用引理 `CategoryTheory.Functor.CommShift.isoAdd_hom_app`：isoAdd_hom_app {a b : A
} (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a) (e₂ : shiftFunctor C b ⋙ F 
≅ F ⋙ shiftFunctor D b) (X : C) : (Co…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
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
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `CategoryTheory.Functor.commShiftIso_add'`：commShiftIso_add' {a b c : A} 
(h : a + b = c) : F.commShiftIso c = CommShift.isoAdd' h (F.commShiftIso a) (F.c
ommShiftIso b)
· 使用定理 `CategoryTheory.Functor.CommShift.isoAdd'_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] {F : Categor…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
（共 32 条，此处仅展示前 30 条）
-/
lemma map_shiftFunctorComm_hom_app [F.CommShift B] (X : C) (a b : B) :
    F.map ((shiftFunctorComm C a b).hom.app X) = (F.commShiftIso b).hom.app (X⟦a⟧) ≫
      ((F.commShiftIso a).hom.app X)⟦b⟧' ≫ (shiftFunctorComm D a b).hom.app (F.obj X) ≫
      ((F.commShiftIso b).inv.app X)⟦a⟧' ≫ (F.commShiftIso a).inv.app (X⟦b⟧) := by
  have eq := NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add a b)) X
  simp only [comp_obj, CommShift.isoAdd_hom_app,
    ← cancel_epi (F.map ((shiftFunctorAdd C a b).inv.app X)),
    ← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id, Category.id_comp] at eq
  simp only [shiftFunctorComm_eq D a b _ rfl]
  dsimp
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, Category.assoc,
    ← reassoc_of% eq, shiftFunctorComm_eq C a b _ rfl]
  dsimp
  rw [Functor.map_comp]
  simp only [NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add' (add_comm b a))) X,
    CommShift.isoAdd'_hom_app, Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp, comp_obj, Category.comp_id]

@[simp, reassoc]
/-
**CategoryTheory.Functor.map_shiftFunctorCompIsoId_hom_app** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Functor`。
形式化陈述：map_shiftFunctorCompIsoId_hom_app [F.CommShift A] (X : C) (a b : A) (h : a
 + b = 0) : F.map ((shiftFunctorCompIsoId C a b h).hom.app X) = (F.commShiftIso 
b).hom.app (X⟦a⟧) ≫ ((F.commShiftIso a).hom.app X)⟦b⟧' ≫ (shiftFunctorCompIsoId 
D a b h).hom.app (F.obj X)
参数：X : C；a b : A；h : a + b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.commShiftIso_add'`：commShiftIso_add' {a b c : A} 
(h : a + b = c) : F.commShiftIso c = CommShift.isoAdd' h (F.commShiftIso a) (F.c
ommShiftIso b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.CommShift.commShiftIso_zero`：∀ {C : Type u_1} {D 
: Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryTh
eory.Category.{v_2, u_2} D} (F : Categor…
· 使用定理 `CategoryTheory.Functor.CommShift.isoZero_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.CommShift.isoAdd'_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] {F : Categor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_shiftFunctorCompIsoId_hom_app [F.CommShift A] (X : C) (a b : A) (h : a + b = 0) :
    F.map ((shiftFunctorCompIsoId C a b h).hom.app X) =
      (F.commShiftIso b).hom.app (X⟦a⟧) ≫ ((F.commShiftIso a).hom.app X)⟦b⟧' ≫
        (shiftFunctorCompIsoId D a b h).hom.app (F.obj X) := by
  dsimp [shiftFunctorCompIsoId]
  have eq := NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add' h)) X
  simp only [commShiftIso_zero, comp_obj, CommShift.isoZero_hom_app,
    CommShift.isoAdd'_hom_app] at eq
  rw [← cancel_epi (F.map ((shiftFunctorAdd' C a b 0 h).hom.app X)), ← reassoc_of% eq, F.map_comp]
  simp only [Iso.inv_hom_id_app, id_obj, Category.comp_id, ← F.map_comp_assoc, Iso.hom_inv_id_app,
    F.map_id, Category.id_comp]

@[simp, reassoc]
/-
**CategoryTheory.Functor.map_shiftFunctorCompIsoId_inv_app** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Functor`。
形式化陈述：map_shiftFunctorCompIsoId_inv_app [F.CommShift A] (X : C) (a b : A) (h : a
 + b = 0) : F.map ((shiftFunctorCompIsoId C a b h).inv.app X) = (shiftFunctorCom
pIsoId D a b h).inv.app (F.obj X) ≫ ((F.commShiftIso a).inv.app X)⟦b⟧' ≫ (F.comm
ShiftIso b).inv.app (X⟦a⟧)
参数：X : C；a b : A；h : a + b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `CategoryTheory.Functor.map_shiftFunctorCompIsoId_hom_app`：map_shiftFunct
orCompIsoId_hom_app [F.CommShift A] (X : C) (a b : A) (h : a + b = 0) : F.map ((
shiftFunctorCompIsoId C a b h).hom.app X) = (F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_shiftFunctorCompIsoId_inv_app [F.CommShift A] (X : C) (a b : A) (h : a + b = 0) :
    F.map ((shiftFunctorCompIsoId C a b h).inv.app X) =
      (shiftFunctorCompIsoId D a b h).inv.app (F.obj X) ≫
        ((F.commShiftIso a).inv.app X)⟦b⟧' ≫ (F.commShiftIso b).inv.app (X⟦a⟧) := by
  rw [← cancel_epi (F.map ((shiftFunctorCompIsoId C a b h).hom.app X)), ← F.map_comp,
    Iso.hom_inv_id_app, F.map_id, map_shiftFunctorCompIsoId_hom_app]
  simp only [comp_obj, id_obj, Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]

end Functor

namespace NatTrans

variable {C D E J : Type*} [Category* C] [Category* D] [Category* E] [Category* J]
  {F₁ F₂ F₃ : C ⥤ D} (τ : F₁ ⟶ F₂) (τ' : F₂ ⟶ F₃) (e : F₁ ≅ F₂)
    (G G' : D ⥤ E) (τ'' : G ⟶ G') (H : E ⥤ J)
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A] [HasShift E A] [HasShift J A]
  [F₁.CommShift A] [F₂.CommShift A] [F₃.CommShift A]
    [G.CommShift A] [G'.CommShift A] [H.CommShift A]

variable {A} in
/-- Auxiliary structure for `NatTrans.CommShift` when we need to
show a compatibility of a natural transformation `τ : F₁ ⟶ F₂` with
respect to the shift by a specific element `a`. See also
`NatTrans.CommShift.of_core` -/
/-
**CategoryTheory.NatTrans.CommShiftCore** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryThe
ory.NatTrans`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {F
₁ F₂ : CategoryTheory.Functor C D} →           (F₁ ⟶ F₂) →             {A : Type
 u_5} →               [inst_2 : AddMonoid A] →                 [inst_3 : Categor
yTheory.HasShift C A] →                   [inst_4 : CategoryTheory.HasShift D A]
 → [F₁.CommShift A] → [F₂.CommShift A] → A → Prop
参数：F₁ ⟶ F₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary structure for `NatTrans.CommShift` when we need to
show a compatibility of a natural transformation `τ : F₁ ⟶ F₂` with
respect to the shift by a specific element `a`. See also
`NatTrans.CommShift.of_core`
-/
structure CommShiftCore (a : A) : Prop where
  shift_comm : (F₁.commShiftIso a).hom ≫ Functor.whiskerRight τ _ =
    Functor.whiskerLeft _ τ ≫ (F₂.commShiftIso a).hom

namespace CommShiftCore

attribute [reassoc] shift_comm

section

variable {A} {a : A} (hτ : CommShiftCore τ a)

include hτ

@[reassoc]
/-
**CategoryTheory.NatTrans.CommShiftCore.shift_app_comm** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.NatTrans.CommShiftCore`。
形式化陈述：shift_app_comm (X : C) : (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' = τ
.app (X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.NatTrans.CommShiftCore.shift_comm`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] {F₁ F₂ : Cat…
-/
lemma shift_app_comm (X : C) :
    (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' =
      τ.app (X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X :=
  congr_app hτ.shift_comm X

@[reassoc]
/-
**CategoryTheory.NatTrans.CommShiftCore.shift_app** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.NatTrans.CommShiftCore`。
形式化陈述：shift_app (X : C) : (τ.app X)⟦a⟧' = (F₁.commShiftIso a).inv.app X ≫ τ.app 
(X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.NatTrans.CommShiftCore.shift_app_comm`：shift_app_comm (X 
: C) : (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' = τ.app (X⟦a⟧) ≫ (F₂.commSh
iftIso a).hom.app X
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
-/
lemma shift_app (X : C) :
    (τ.app X)⟦a⟧' = (F₁.commShiftIso a).inv.app X ≫
      τ.app (X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X := by
  rw [← hτ.shift_app_comm, Iso.inv_hom_id_app_assoc]

@[reassoc]
/-
**CategoryTheory.NatTrans.CommShiftCore.app_shift** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.NatTrans.CommShiftCore`。
形式化陈述：app_shift (X : C) : τ.app (X⟦a⟧) = (F₁.commShiftIso a).hom.app X ≫ (τ.app 
X)⟦a⟧' ≫ (F₂.commShiftIso a).inv.app X
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.CommShiftCore.shift_app_comm_assoc`：∀ {C : Type 
u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Ca
tegoryTheory.Category.{v_2, u_2} D] {F₁ F₂ : Cat…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma app_shift (X : C) :
    τ.app (X⟦a⟧) = (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' ≫
      (F₂.commShiftIso a).inv.app X := by
  simp [hτ.shift_app_comm_assoc τ X]

end

variable {τ}

/-
**CategoryTheory.NatTrans.CommShiftCore.zero** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.NatTrans.CommShiftCore`。
形式化陈述：zero : CommShiftCore τ (0 : A) where shift_comm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.CommShift.commShiftIso_zero`：∀ {C : Type u_1} {D 
: Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryTh
eory.Category.{v_2, u_2} D} (F : Categor…
· 使用定理 `CategoryTheory.Functor.CommShift.isoZero_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zero : CommShiftCore τ (0 : A) where
  shift_comm := by
    ext X
    simp [Functor.commShiftIso_zero, ← NatTrans.naturality]

variable {A}
/-
**CategoryTheory.NatTrans.CommShiftCore.add** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.NatTrans.CommShiftCore`。
形式化陈述：add {a b : A} (ha : CommShiftCore τ a) (hb : CommShiftCore τ b) : CommShif
tCore τ (a + b) where shift_comm
参数：ha : CommShiftCore τ a；hb : CommShiftCore τ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.CommShift.commShiftIso_add`：∀ {C : Type u_1} {D :
 Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryThe
ory.Category.{v_2, u_2} D} (F : Categor…
· 使用引理 `CategoryTheory.Functor.CommShift.isoAdd_hom_app`：isoAdd_hom_app {a b : A
} (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a) (e₂ : shiftFunctor C b ⋙ F 
≅ F ⋙ shiftFunctor D b) (X : C) : (Co…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality_2`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.CommShiftCore.app_shift_assoc`：∀ {C : Type u_1} 
{D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} D] {F₁ F₂ : Cat…
· 使用引理 `CategoryTheory.NatTrans.CommShiftCore.app_shift`：app_shift (X : C) : τ.a
pp (X⟦a⟧) = (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' ≫ (F₂.commShiftIso a).
inv.app X
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add {a b : A} (ha : CommShiftCore τ a) (hb : CommShiftCore τ b) :
    CommShiftCore τ (a + b) where
  shift_comm := by
    ext X
    have := (shiftFunctorAdd D a b).inv.naturality (τ.app X)
    dsimp at this ⊢
    simp only [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app,
      ← NatTrans.naturality_2 τ ((shiftFunctorAdd C a b).app X),
      Functor.comp_obj, hb.app_shift_assoc, ha.app_shift, assoc,
      (shiftFunctor D b).map_comp_assoc]
    simp [← Functor.map_comp_assoc, this]

end CommShiftCore

/-- If `τ : F₁ ⟶ F₂` is a natural transformation between two functors
which commute with a shift by an additive monoid `A`, this typeclass
asserts a compatibility of `τ` with these shifts. -/
/-
**CategoryTheory.NatTrans.CommShift** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory.Nat
Trans`。
形式化陈述：CommShift : Prop where shift_comm (a : A) : (F₁.commShiftIso a).hom ≫ Func
tor.whiskerRight τ _ = Functor.whiskerLeft _ τ ≫ (F₂.commShiftIso a).hom
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `τ : F₁ ⟶ F₂` is a natural transformation between two functors
which commute with a shift by an additive monoid `A`, this typeclass
asserts a compatibility of `τ` with these shifts.
-/
class CommShift : Prop where
  shift_comm (a : A) : (F₁.commShiftIso a).hom ≫ Functor.whiskerRight τ _ =
    Functor.whiskerLeft _ τ ≫ (F₂.commShiftIso a).hom := by cat_disch

section

variable {A}

variable {τ} in
/-
**CategoryTheory.NatTrans.CommShift.of_core** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.NatTrans.CommShift`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {F₁ F₂ : CategoryTheory.Fu
nctor C D} {τ : F₁ ⟶ F₂} {A : Type u_5}   [inst_2 : AddMonoid A] [inst_3 : Categ
oryTheory.HasShift C A] [inst_4 : CategoryTheory.HasShift D A]   [inst_5 : F₁.Co
mmShift A] [inst_6 : F₂.CommShift A],   (∀ (a : A), CategoryTheory.NatTrans.Comm
ShiftCore τ a) → CategoryTheory.NatTrans.CommShift τ A
参数：∀ (a : A), CategoryTheory.NatTrans.CommShiftCore τ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.CommShiftCore.shift_comm`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] {F₁ F₂ : Cat…
-/
lemma CommShift.of_core (h : ∀ (a : A), CommShiftCore τ a) :
    CommShift τ A where
  shift_comm a := (h a).shift_comm

variable [NatTrans.CommShift τ A]

@[reassoc]
/-
**CategoryTheory.NatTrans.shift_comm** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.N
atTrans`。
形式化陈述：shift_comm (a : A) : (F₁.commShiftIso a).hom ≫ Functor.whiskerRight τ _ = 
Functor.whiskerLeft _ τ ≫ (F₂.commShiftIso a).hom
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.CommShift.shift_comm`：∀ {C : Type u_1} {D : Type
 u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryTheory.C
ategory.{v_2, u_2} D} {F₁ F₂ : Cat…
-/
lemma shift_comm (a : A) :
    (F₁.commShiftIso a).hom ≫ Functor.whiskerRight τ _ =
      Functor.whiskerLeft _ τ ≫ (F₂.commShiftIso a).hom := by
  apply CommShift.shift_comm

@[reassoc]
/-
**CategoryTheory.NatTrans.shift_app_comm** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.NatTrans`。
形式化陈述：shift_app_comm (a : A) (X : C) : (F₁.commShiftIso a).hom.app X ≫ (τ.app X)
⟦a⟧' = τ.app (X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X
参数：a : A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.NatTrans.shift_comm`：shift_comm (a : A) : (F₁.commShiftIs
o a).hom ≫ Functor.whiskerRight τ _ = Functor.whiskerLeft _ τ ≫ (F₂.commShiftIso
 a).hom
-/
lemma shift_app_comm (a : A) (X : C) :
    (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' =
      τ.app (X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X :=
  congr_app (shift_comm τ a) X

@[reassoc]
/-
**CategoryTheory.NatTrans.shift_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Na
tTrans`。
形式化陈述：shift_app (a : A) (X : C) : (τ.app X)⟦a⟧' = (F₁.commShiftIso a).inv.app X 
≫ τ.app (X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X
参数：a : A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.NatTrans.shift_app_comm`：shift_app_comm (a : A) (X : C) :
 (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' = τ.app (X⟦a⟧) ≫ (F₂.commShiftIso
 a).hom.app X
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
-/
lemma shift_app (a : A) (X : C) :
    (τ.app X)⟦a⟧' = (F₁.commShiftIso a).inv.app X ≫
      τ.app (X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X := by
  rw [← shift_app_comm, Iso.inv_hom_id_app_assoc]

@[reassoc]
/-
**CategoryTheory.NatTrans.app_shift** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Na
tTrans`。
形式化陈述：app_shift (a : A) (X : C) : τ.app (X⟦a⟧) = (F₁.commShiftIso a).hom.app X ≫
 (τ.app X)⟦a⟧' ≫ (F₂.commShiftIso a).inv.app X
参数：a : A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.shift_app_comm_assoc`：∀ {C : Type u_1} {D : Type
 u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_2} D] {F₁ F₂ : Cat…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma app_shift (a : A) (X : C) :
    τ.app (X⟦a⟧) = (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' ≫
      (F₂.commShiftIso a).inv.app X := by
  simp [shift_app_comm_assoc τ a X]

end

namespace CommShift

/-
**CategoryTheory.NatTrans.CommShift.of_iso_inv** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.NatTrans.CommShift`。
形式化陈述：of_iso_inv [NatTrans.CommShift e.hom A] : NatTrans.CommShift e.inv A
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.shift_app_comm_assoc`：∀ {C : Type u_1} {D : Type
 u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_2} D] {F₁ F₂ : Cat…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
instance of_iso_inv [NatTrans.CommShift e.hom A] :
    NatTrans.CommShift e.inv A := ⟨fun a => by
  ext X
  dsimp
  rw [← cancel_epi (e.hom.app (X⟦a⟧)), e.hom_inv_id_app_assoc, ← shift_app_comm_assoc,
    ← Functor.map_comp, e.hom_inv_id_app, Functor.map_id, Category.comp_id]⟩
/-
**CategoryTheory.NatTrans.CommShift.of_iso_symm** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.NatTrans.CommShift`。
形式化陈述：of_iso_symm [NatTrans.CommShift e.hom A] : NatTrans.CommShift e.symm.hom A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance of_iso_symm [NatTrans.CommShift e.hom A] : NatTrans.CommShift e.symm.hom A :=
  NatTrans.CommShift.of_iso_inv e A
/-
**CategoryTheory.NatTrans.CommShift.of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.NatTrans.CommShift`。
形式化陈述：of_isIso [IsIso τ] [NatTrans.CommShift τ A] : NatTrans.CommShift (inv τ) A
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_isIso [IsIso τ] [NatTrans.CommShift τ A] :
    NatTrans.CommShift (inv τ) A := by
  have : NatTrans.CommShift (asIso τ).hom A := by assumption
  change NatTrans.CommShift (asIso τ).inv A
  infer_instance

variable (F₁) in
/-
**CategoryTheory.NatTrans.CommShift.id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.NatTrans.CommShift`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F₁ : CategoryTheory.Funct
or C D) (A : Type u_5)   [inst_2 : AddMonoid A] [inst_3 : CategoryTheory.HasShif
t C A] [inst_4 : CategoryTheory.HasShift D A]   [inst_5 : F₁.CommShift A], Categ
oryTheory.NatTrans.CommShift (CategoryTheory.CategoryStruct.id F₁) A
参数：F₁ : CategoryTheory.Functor C D；A : Type u_5；CategoryTheory.CategoryStruct.id
 F₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.whiskerRight_id'`：whiskerRight_id' {G : C ⥤ D} (F
 : D ⥤ E) : whiskerRight (𝟙 G) F = 𝟙 (G.comp F)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance id : NatTrans.CommShift (𝟙 F₁) A where

attribute [local simp] Functor.commShiftIso_comp_hom_app
  shift_app_comm shift_app_comm_assoc
/-
**CategoryTheory.NatTrans.CommShift.comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.NatTrans.CommShift`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {F₁ F₂ F₃ : CategoryTheory
.Functor C D} (τ : F₁ ⟶ F₂) (τ' : F₂ ⟶ F₃)   (A : Type u_5) [inst_2 : AddMonoid 
A] [inst_3 : CategoryTheory.HasShift C A] [inst_4 : CategoryTheory.HasShift D A]
   [inst_5 : F₁.CommShift A] [inst_6 : F₂.CommShift A] [inst_7 : F₃.CommShift A]
 [CategoryTheory.NatTrans.CommShift τ A]   [CategoryTheory.NatTrans.CommShift τ'
 A],   CategoryTheory.NatTrans.CommShift (CategoryTheory.CategoryStruct.comp τ τ
') A
参数：τ : F₁ ⟶ F₂；τ' : F₂ ⟶ F₃；A : Type u_5；CategoryTheory.CategoryStruct.comp τ τ'
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.whiskerRight_comp`：whiskerRight_comp {G H K : C ⥤
 D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) : whiskerRight (α ≫ β) F = whiskerRight 
α F ≫ whiskerRight β F
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.NatTrans.shift_app_comm_assoc`：∀ {C : Type u_1} {D : Type
 u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_2} D] {F₁ F₂ : Cat…
· 使用引理 `CategoryTheory.NatTrans.shift_app_comm`：shift_app_comm (a : A) (X : C) :
 (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' = τ.app (X⟦a⟧) ≫ (F₂.commShiftIso
 a).hom.app X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance comp [NatTrans.CommShift τ A] [NatTrans.CommShift τ' A] :
    NatTrans.CommShift (τ ≫ τ') A where
/-
**CategoryTheory.NatTrans.CommShift.whiskerRight** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.NatTrans.CommShift`。
形式化陈述：whiskerRight [NatTrans.CommShift τ A] : NatTrans.CommShift (Functor.whiske
rRight τ G) A
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerRight_twice`：whiskerRight_twice {H K : B ⥤
 C} (F : C ⥤ D) (G : D ⥤ E) (α : H ⟶ K) : whiskerRight (whiskerRight α F) G = (F
unctor.associator _ _ _).hom ≫ …
· 使用定理 `CategoryTheory.Functor.commShiftIso_comp_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.NatTrans.shift_app_comm`：shift_app_comm (a : A) (X : C) :
 (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' = τ.app (X⟦a⟧) ≫ (F₂.commShiftIso
 a).hom.app X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance whiskerRight [NatTrans.CommShift τ A] :
    NatTrans.CommShift (Functor.whiskerRight τ G) A := ⟨fun a => by
  ext X
  simp only [Functor.whiskerRight_twice, comp_app, Functor.commShiftIso_comp_hom_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.associator_inv_app, comp_id, id_comp, assoc, ← Functor.commShiftIso_hom_naturality, ←
    G.map_comp_assoc, shift_app_comm, Functor.whiskerLeft_app]⟩
/-
**CategoryTheory.NatTrans.CommShift.whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.NatTrans.CommShift`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {E : Type u_3} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_3, u_3} E]   {F₁ : CategoryTheory.Functor C D} (G G' :
 CategoryTheory.Functor D E) (τ'' : G ⟶ G') (A : Type u_5)   [inst_3 : AddMonoid
 A] [inst_4 : CategoryTheory.HasShift C A] [inst_5 : CategoryTheory.HasShift D A
]   [inst_6 : CategoryTheory.HasShift E A] [inst_7 : F₁.CommShift A] [inst_8 : G
.CommShift A] [inst_9 : G'.CommShift A]   [CategoryTheory.NatTrans.CommShift τ''
 A], CategoryTheory.NatTrans.CommShift (F₁.whiskerLeft τ'') A
参数：G G' : CategoryTheory.Functor D E；τ'' : G ⟶ G'；A : Type u_5；F₁.whiskerLeft τ'
'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerLeft_twice`：whiskerLeft_twice (F : B ⥤ C) 
(G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) : whiskerLeft F (whiskerLeft G α) = (Funct
or.associator _ _ _).inv ≫ whi…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.commShiftIso_comp_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} …
· 使用引理 `CategoryTheory.NatTrans.shift_app_comm`：shift_app_comm (a : A) (X : C) :
 (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' = τ.app (X⟦a⟧) ≫ (F₂.commShiftIso
 a).hom.app X
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance whiskerLeft [NatTrans.CommShift τ'' A] :
    NatTrans.CommShift (Functor.whiskerLeft F₁ τ'') A where
/-
**CategoryTheory.NatTrans.CommShift.associator** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.NatTrans.CommShift`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {E : Type u_3} {J : Type u_4} [inst : Cate
goryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2}
 D] [inst_2 : CategoryTheory.Category.{v_3, u_3} E]   [inst_3 : CategoryTheory.C
ategory.{v_4, u_4} J] {F₁ : CategoryTheory.Functor C D} (G : CategoryTheory.Func
tor D E)   (H : CategoryTheory.Functor E J) (A : Type u_5) [inst_4 : AddMonoid A
] [inst_5 : CategoryTheory.HasShift C A]   [inst_6 : CategoryTheory.HasShift D A
] [inst_7 : CategoryTheory.HasShift E A] [inst_8 : CategoryTheory.HasShift J A] 
  [inst_9 : F₁.CommShift A] [inst_10 : G.CommShift A] [inst_11 : H.CommShift A],
   CategoryTheory.NatTrans.CommShift (F₁.associator G H).hom A
参数：G : CategoryTheory.Functor D E；H : CategoryTheory.Functor E J；A : Type u_5；F₁
.associator G H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.commShiftIso_comp_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
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
instance associator : CommShift (Functor.associator F₁ G H).hom A where
/-
**CategoryTheory.NatTrans.CommShift.leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.NatTrans.CommShift`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {F₁ : CategoryTheory.Funct
or C D} (A : Type u_5)   [inst_2 : AddMonoid A] [inst_3 : CategoryTheory.HasShif
t C A] [inst_4 : CategoryTheory.HasShift D A]   [inst_5 : F₁.CommShift A], Categ
oryTheory.NatTrans.CommShift F₁.leftUnitor.hom A
参数：A : Type u_5。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.commShiftIso_comp_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.commShiftIso_id_hom_app`：∀ (C : Type u_1) [inst :
 CategoryTheory.Category.{v_1, u_1} C] {A : Type u_4} [inst_1 : AddMonoid A]   [
inst_2 : CategoryTheory.HasShift C A…
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
instance leftUnitor : CommShift F₁.leftUnitor.hom A where
/-
**CategoryTheory.NatTrans.CommShift.rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.NatTrans.CommShift`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {F₁ : CategoryTheory.Funct
or C D} (A : Type u_5)   [inst_2 : AddMonoid A] [inst_3 : CategoryTheory.HasShif
t C A] [inst_4 : CategoryTheory.HasShift D A]   [inst_5 : F₁.CommShift A], Categ
oryTheory.NatTrans.CommShift F₁.rightUnitor.hom A
参数：A : Type u_5。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.commShiftIso_comp_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.commShiftIso_id_hom_app`：∀ (C : Type u_1) [inst :
 CategoryTheory.Category.{v_1, u_1} C] {A : Type u_4} [inst_1 : AddMonoid A]   [
inst_2 : CategoryTheory.HasShift C A…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance rightUnitor : CommShift F₁.rightUnitor.hom A where

end CommShift

end NatTrans

namespace Functor

namespace CommShift

variable {C D E : Type*} [Category* C] [Category* D]
  {F : C ⥤ D} {G : C ⥤ D} (e : F ≅ G)
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A]
  [F.CommShift A]

/-- If `e : F ≅ G` is an isomorphism of functors and if `F` commutes with the
shift, then `G` also commutes with the shift. -/
@[simps! -isSimp commShiftIso_hom_app commShiftIso_inv_app, instance_reducible]
/-
**CategoryTheory.Functor.CommShift.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor.CommShift`。
形式化陈述：ofIso : G.CommShift A where commShiftIso a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `e : F ≅ G` is an isomorphism of functors and if `F` commutes with the
shift, then `G` also commutes with the shift.
-/
def ofIso : G.CommShift A where
  commShiftIso a := isoWhiskerLeft _ e.symm ≪≫ F.commShiftIso a ≪≫ isoWhiskerRight e _
  commShiftIso_zero := by
    ext X
    simp [F.commShiftIso_zero, ← NatTrans.naturality]
  commShiftIso_add a b := by
    ext X
    simp only [comp_obj, F.commShiftIso_add, Iso.trans_hom, isoWhiskerLeft_hom,
      Iso.symm_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app,
      isoAdd_hom_app, whiskerRight_app, assoc, map_comp, NatTrans.naturality_assoc,
      NatIso.cancel_natIso_inv_left]
    simp only [← Functor.map_comp_assoc, e.hom_inv_id_app_assoc]
    simp only [← NatTrans.naturality, comp_obj, comp_map, map_comp, assoc]
/-
**CategoryTheory.Functor.CommShift.ofIso_compatibility** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor.CommShift`。
形式化陈述：ofIso_compatibility : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofIso_compatibility :
    letI := ofIso e A
    NatTrans.CommShift e.hom A := by
  let := ofIso e A
  exact ⟨fun a => by ext; simp [ofIso_commShiftIso_hom_app]⟩

end CommShift

end Functor

namespace Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] {A : Type*}

section hasShiftOfFullyFaithful

variable [AddMonoid A] [HasShift D A]
  {F : C ⥤ D} (hF : F.FullyFaithful)
  (s : A → C ⥤ C) (i : ∀ i, s i ⋙ F ≅ F ⋙ shiftFunctor D i)

namespace CommShift

set_option backward.isDefEq.respectTransparency false in
/-- If `F : C ⥤ D` is a fully faithful functor which is used
to construct a shift by `A` on `C` from a shift on `D`,
then the functor `F` itself commutes with the shift by `A`. -/
@[instance_reducible]
/-
**CategoryTheory.Functor.CommShift.ofHasShiftOfFullyFaithful** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Functor.CommShift`。
形式化陈述：ofHasShiftOfFullyFaithful : letI
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` is a fully faithful functor which is used
to construct a shift by `A` on `C` from a shift on `D`,
then the functor `F` itself commutes with the shift by `A`.
-/
def ofHasShiftOfFullyFaithful :
    letI := hF.hasShift s i; F.CommShift A := by
  letI := hF.hasShift s i
  exact
  { commShiftIso := i
    commShiftIso_zero := by
      ext X
      simp [ShiftMkCore.shiftFunctorZero_eq]
    commShiftIso_add := fun a b => by
      ext X
      simp [ShiftMkCore.shiftFunctorAdd_eq, ShiftMkCore.shiftFunctor_eq,
        ← Functor.map_comp_assoc] }

end CommShift

/-
**CategoryTheory.Functor.shiftFunctorIso_ofHasShiftOfFullyFaithful** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：shiftFunctorIso_ofHasShiftOfFullyFaithful (a : A) : letI
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma shiftFunctorIso_ofHasShiftOfFullyFaithful (a : A) :
    letI := hF.hasShift s i
    letI := CommShift.ofHasShiftOfFullyFaithful hF s i
    F.commShiftIso a = i a := by
  rfl

end hasShiftOfFullyFaithful

@[reassoc]
/-
**CategoryTheory.Functor.map_shiftFunctorComm** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：map_shiftFunctorComm [AddCommMonoid A] [HasShift C A] [HasShift D A] (F : 
C ⥤ D) [F.CommShift A] (X : C) (a b : A) : F.map ((shiftFunctorComm C a b).hom.a
pp X) = (F.commShiftIso b).hom.app (X⟦a⟧) ≫ ((F.commShiftIso a).hom.app X)⟦b⟧' ≫
 (shiftFunctorComm D a b).hom.app (F.obj X) ≫ ((F.commShiftIso b).inv.app X)⟦a⟧'
 ≫ (F.commShiftIso a).inv.app (X⟦b⟧)
参数：F : C ⥤ D；X : C；a b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.map_shiftFunctorComm_hom_app`：map_shiftFunctorCom
m_hom_app [F.CommShift B] (X : C) (a b : B) : F.map ((shiftFunctorComm C a b).ho
m.app X) = (F.commShiftIso b).hom.app (X⟦…
-/
lemma map_shiftFunctorComm
    [AddCommMonoid A] [HasShift C A] [HasShift D A]
    (F : C ⥤ D) [F.CommShift A] (X : C) (a b : A) :
    F.map ((shiftFunctorComm C a b).hom.app X) = (F.commShiftIso b).hom.app (X⟦a⟧) ≫
      ((F.commShiftIso a).hom.app X)⟦b⟧' ≫ (shiftFunctorComm D a b).hom.app (F.obj X) ≫
      ((F.commShiftIso b).inv.app X)⟦a⟧' ≫ (F.commShiftIso a).inv.app (X⟦b⟧) :=
  map_shiftFunctorComm_hom_app _ _ _ _

namespace CommShift

variable {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H)
  [Full G] [Faithful G]
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A] [HasShift E A]
  [G.CommShift A] [H.CommShift A]

namespace OfComp

variable {A}

/-- Auxiliary definition for `Functor.CommShift.ofComp`. -/
/-
**CategoryTheory.Functor.CommShift.OfComp.iso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor.CommShift.OfComp`。
形式化陈述：iso (a : A) : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a
参数：a : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `Functor.CommShift.ofComp`.
-/
noncomputable def iso (a : A) : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a :=
  ((whiskeringRight C D E).obj G).preimageIso
    (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ e ≪≫
      H.commShiftIso a ≪≫ isoWhiskerRight e.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft F (G.commShiftIso a).symm ≪≫ (Functor.associator _ _ _).symm)

@[simp, reassoc]
/-
**CategoryTheory.Functor.CommShift.OfComp.map_iso_hom_app** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor.CommShift.OfComp`。
形式化陈述：map_iso_hom_app (a : A) (X : C) : G.map ((iso e a).hom.app X) = e.hom.app 
(X⟦a⟧) ≫ (H.commShiftIso a).hom.app X ≫ (e.inv.app X)⟦a⟧' ≫ (G.commShiftIso a).i
nv.app (F.obj X)
参数：a : A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
-/
lemma map_iso_hom_app (a : A) (X : C) :
    G.map ((iso e a).hom.app X) = e.hom.app (X⟦a⟧) ≫
      (H.commShiftIso a).hom.app X ≫ (e.inv.app X)⟦a⟧' ≫
      (G.commShiftIso a).inv.app (F.obj X) := by
  have h : ((whiskeringRight C D E).obj G).map (iso e a).hom = _ :=
    Functor.map_preimage _ _
  simpa using congr_app h X

@[simp, reassoc]
/-
**CategoryTheory.Functor.CommShift.OfComp.map_iso_inv_app** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor.CommShift.OfComp`。
形式化陈述：map_iso_inv_app (a : A) (X : C) : G.map ((iso e a).inv.app X) = (G.commShi
ftIso a).hom.app (F.obj X) ≫ (e.hom.app X)⟦a⟧' ≫ (H.commShiftIso a).inv.app X ≫ 
e.inv.app (X⟦a⟧)
参数：a : A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
-/
lemma map_iso_inv_app (a : A) (X : C) :
    G.map ((iso e a).inv.app X) =
      (G.commShiftIso a).hom.app (F.obj X) ≫ (e.hom.app X)⟦a⟧' ≫
      (H.commShiftIso a).inv.app X ≫ e.inv.app (X⟦a⟧) := by
  have h : ((whiskeringRight C D E).obj G).map (iso e a).inv = _ :=
    Functor.map_preimage _ _
  simpa using congr_app h X

attribute [irreducible] iso

end OfComp

/-- Given an isomorphism `e : F ⋙ G ≅ H` where `G` is fully faithful,
the functor `F` commutes with shifts by `A` if `G` and `H` do. -/
@[instance_reducible]
/-
**CategoryTheory.Functor.CommShift.ofComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor.CommShift`。
形式化陈述：ofComp : F.CommShift A where commShiftIso
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an isomorphism `e : F ⋙ G ≅ H` where `G` is fully faithful,
the functor `F` commutes with shifts by `A` if `G` and `H` do.
-/
noncomputable def ofComp : F.CommShift A where
  commShiftIso := OfComp.iso e
  commShiftIso_zero := by
    ext X
    apply G.map_injective
    simp [G.commShiftIso_zero, H.commShiftIso_zero]
  commShiftIso_add a b := by
    ext X
    apply G.map_injective
    simp only [comp_obj, OfComp.map_iso_hom_app, H.commShiftIso_add, isoAdd_hom_app,
      G.commShiftIso_add, isoAdd_inv_app, NatTrans.naturality_assoc, comp_map, assoc,
      Iso.inv_hom_id_app_assoc, map_comp]
    simp only [← NatTrans.naturality_assoc, ← commShiftIso_inv_naturality_assoc,
      ← Functor.map_comp_assoc]
    congr 4
    simp
/-
**CategoryTheory.Functor.CommShift.ofComp_compatibility** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor.CommShift`。
形式化陈述：ofComp_compatibility : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.commShiftIso_comp_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Functor.CommShift.OfComp.map_iso_hom_app`：map_iso_hom_app
 (a : A) (X : C) : G.map ((iso e a).hom.app X) = e.hom.app (X⟦a⟧) ≫ (H.commShift
Iso a).hom.app X ≫ (e.inv.app X)⟦a⟧' ≫ (G.com…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofComp_compatibility :
    letI := ofComp e
    NatTrans.CommShift e.hom A := by
  let := ofComp e
  refine ⟨fun a ↦ ?_⟩
  ext X
  simp [commShiftIso_comp_hom_app, show F.commShiftIso a = OfComp.iso e a from rfl,
    ← Functor.map_comp]

end CommShift

end Functor

/--
Assume that we have a diagram of categories
```
C₁ ⥤ D₁
‖     ‖
v     v
C₂ ⥤ D₂
‖     ‖
v     v
C₃ ⥤ D₃
```
with functors `F₁₂ : C₁ ⥤ C₂`, `F₂₃ : C₂ ⥤ C₃` and `F₁₃ : C₁ ⥤ C₃` on the first
column that are related by a natural transformation `α : F₁₃ ⟶ F₁₂ ⋙ F₂₃`
and similarly `β : G₁₂ ⋙ G₂₃ ⟶ G₁₃` on the second column. Assume that we have
natural transformations
`e₁₂ : F₁₂ ⋙ L₂ ⟶ L₁ ⋙ G₁₂` (top square), `e₂₃ : F₂₃ ⋙ L₃ ⟶ L₂ ⋙ G₂₃` (bottom square),
and `e₁₃ : F₁₃ ⋙ L₃ ⟶ L₁ ⋙ G₁₃` (outer square), where the horizontal functors
are denoted `L₁`, `L₂` and `L₃`. Assume that `e₁₃` is determined by the other
natural transformations `α`, `e₂₃`, `e₁₂` and `β`. Then, if all these categories
are equipped with a shift by an additive monoid `A`, and all these functors commute with
these shifts, then the natural transformation `e₁₃` of the outer square commutes with the
shift if all `α`, `e₂₃`, `e₁₂` and `β` do. -/
/-
**CategoryTheory.NatTrans.CommShift.verticalComposition** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.NatTrans.CommShift`。
形式化陈述：∀ {C₁ : Type u_1} {C₂ : Type u_2} {C₃ : Type u_3} {D₁ : Type u_4} {D₂ : Ty
pe u_5} {D₃ : Type u_6}   [inst : CategoryTheory.Category.{v_1, u_1} C₁] [inst_1
 : CategoryTheory.Category.{v_2, u_2} C₂]   [inst_2 : CategoryTheory.Category.{v
_3, u_3} C₃] [inst_3 : CategoryTheory.Category.{v_4, u_4} D₁]   [inst_4 : Catego
ryTheory.Category.{v_5, u_5} D₂] [inst_5 : CategoryTheory.Category.{v_6, u_6} D₃
]   {F₁₂ : CategoryTheory.Functor C₁ C₂} {F₂₃ : CategoryTheory.Functor C₂ C₃} {F
₁₃ : CategoryTheory.Functor C₁ C₃}   (α : F₁₃ ⟶ F₁₂.comp F₂₃) {G₁₂ : CategoryThe
ory.Functor D₁ D₂} {G₂₃ : CategoryTheory.Functor D₂ D₃}   {G₁₃ : CategoryTheory.
Functor D₁ D₃} (β : G₁₂.comp G₂₃ ⟶ G₁₃) {L₁ : CategoryTheory.Functor C₁ D₁}   {L
₂ : CategoryTheory.Functor C₂ D₂} {L₃ : CategoryTheory.Functor C₃ D₃} (e₁₂ : F₁₂
.comp L₂ ⟶ L₁.comp G₁₂)   (e₂₃ : F₂₃.comp L₃ ⟶ L₂.comp G₂₃) (e₁₃ : F₁₃.comp L₃ ⟶
 L₁.comp G₁₃) (A : Type u_7) [inst_6 : AddMonoid A]   [inst_7 : CategoryTheory.H
asShift C₁ A] [inst_8 : CategoryTheory.HasShift C₂ A]   [inst_9 : CategoryTheory
.HasShift C₃ A] [inst_10 : CategoryTheory.HasShift D₁ A]   [inst_11 : CategoryTh
eory.HasShift D₂ A] [inst_12 : CategoryTheory.HasShift D₃ A] [inst_13 : F₁₂.Comm
Shift A]   [inst_14 : F₂₃.CommShift A] [inst_15 : F₁₃.CommShift A] [CategoryTheo
ry.NatTrans.CommShift α A]   [inst_17 : G₁₂.CommShift A] [inst_18 : G₂₃.CommShif
t A] [inst_19 : G₁₃.CommShift A]   [CategoryTheory.NatTrans.CommShift β A] [inst
_21 : L₁.CommShift A] [inst_22 : L₂.CommShift A]   [inst_23 : L₃.CommShift A] [C
ategoryTheory.NatTrans.CommShift e₁₂ A] [CategoryTheory.NatTrans.CommShift e₂₃ A
],   e₁₃ =       CategoryTheory.CategoryStruct.comp (CategoryTheory.Functor.whis
kerRight α L₃)         (CategoryTheory.CategoryStruct.comp ⋯ ⋯) →     CategoryTh
eory.NatTrans.CommShift e₁₃ A
参数：α : F₁₃ ⟶ F₁₂.comp F₂₃；β : G₁₂.comp G₂₃ ⟶ G₁₃；e₁₂ : F₁₂.comp L₂ ⟶ L₁.comp G₁₂
；e₂₃ : F₂₃.comp L₃ ⟶ L₂.comp G₂₃；e₁₃ : F₁₃.comp L₃ ⟶ L₁.comp G₁₃；A : Type u_7；Ca
tegoryTheory.Functor.whiskerRight α L₃；CategoryTheory.CategoryStruct.comp ⋯ ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.CommShift.comp`：∀ {C : Type u_1} {D : Type u_2} 
[inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Categor
y.{v_2, u_2} D] {F₁ F₂ F₃ : …
· 使用定理 `CategoryTheory.NatTrans.CommShift.associator`：∀ {C : Type u_1} {D : Type
 u_2} {E : Type u_3} {J : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C
]   [inst_1 : CategoryTheory.Categ…
· 使用定理 `CategoryTheory.NatTrans.CommShift.whiskerLeft`：∀ {C : Type u_1} {D : Typ
e u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : 
CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Assume that we have a diagram of categories
```
C₁ ⥤ D₁
‖     ‖
v     v
C₂ ⥤ D₂
‖     ‖
v     v
C₃ ⥤ D₃
```
with functors `F₁₂ : C₁ ⥤ C₂`, `F₂₃ : C₂ ⥤ C₃` and `F₁₃ : C₁ ⥤ C₃` on the first
column that are related by a natural transformation `α : F₁₃ ⟶ F₁₂ ⋙ F₂₃`
and similarly `β : G₁₂ ⋙ G₂₃ ⟶ G₁₃` on the second column. Assume that we have
natural transformations
`e₁₂ : F₁₂ ⋙ L₂ ⟶ L₁ ⋙ G₁₂` (top square), `e₂₃ : F₂₃ ⋙ L₃ ⟶ L₂ ⋙ G₂₃` (bottom sq
uare),
and `e₁₃ : F₁₃ ⋙ L₃ ⟶ L₁ ⋙ G₁₃` (outer square), where the horizontal functors
are denoted `L₁`, `L₂` and `L₃`. Assume that `e₁₃` is determined by the other
natural transformations `α`, `e₂₃`, `e₁₂` and `β`. Then, if all these categories
are equipped with a shift by an additive monoid `A`, and all these functors comm
ute with
these shifts, then the natural transformation `e₁₃` of the outer square commutes
 with the
shift if all `α`, `e₂₃`, `e₁₂` and `β` do.
-/
lemma NatTrans.CommShift.verticalComposition {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
    [Category* C₁] [Category* C₂] [Category* C₃] [Category* D₁] [Category* D₂] [Category* D₃]
    {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃} {F₁₃ : C₁ ⥤ C₃} (α : F₁₃ ⟶ F₁₂ ⋙ F₂₃)
    {G₁₂ : D₁ ⥤ D₂} {G₂₃ : D₂ ⥤ D₃} {G₁₃ : D₁ ⥤ D₃} (β : G₁₂ ⋙ G₂₃ ⟶ G₁₃)
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃}
    (e₁₂ : F₁₂ ⋙ L₂ ⟶ L₁ ⋙ G₁₂) (e₂₃ : F₂₃ ⋙ L₃ ⟶ L₂ ⋙ G₂₃) (e₁₃ : F₁₃ ⋙ L₃ ⟶ L₁ ⋙ G₁₃)
    (A : Type*) [AddMonoid A] [HasShift C₁ A] [HasShift C₂ A] [HasShift C₃ A]
    [HasShift D₁ A] [HasShift D₂ A] [HasShift D₃ A]
    [F₁₂.CommShift A] [F₂₃.CommShift A] [F₁₃.CommShift A] [CommShift α A]
    [G₁₂.CommShift A] [G₂₃.CommShift A] [G₁₃.CommShift A] [CommShift β A]
    [L₁.CommShift A] [L₂.CommShift A] [L₃.CommShift A]
    [CommShift e₁₂ A] [CommShift e₂₃ A]
    (h₁₃ : e₁₃ = Functor.whiskerRight α L₃ ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft F₁₂ e₂₃ ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight e₁₂ G₂₃ ≫ (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft L₁ β) : CommShift e₁₃ A := by
  subst h₁₃
  infer_instance

end CategoryTheory

