/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The pullback of a shift by a monoid morphism

Given a shift by a monoid `B` on a category `C` and a monoid morphism `φ : A →+ B`,
we define a shift by `A` on a category `PullbackShift C φ` which is a type synonym for `C`.

If `F : C ⥤ D` is a functor between categories equipped with shifts by `B`, we define
a type synonym `PullbackShift.functor F φ` for `F`. When `F` has a `CommShift` structure
by `B`, we define a pulled back `CommShift` structure by `A` on `PullbackShift.functor F φ`.

Similarly, if `τ` is a natural transformation between functors `F,G : C ⥤ D`, we define
a type synonym
`PullbackShift.natTrans τ φ : PullbackShift.functor F φ ⟶ PullbackShift.functor G φ`.
When `τ` has a `CommShift` structure by `B` (i.e. is compatible with `CommShift` structures
on `F` and `G`), we define a pulled back `CommShift` structure by `A` on
`PullbackShift.natTrans τ φ`.

Finally, if we have an adjunction `F ⊣ G` (with `G : D ⥤ C`), we define a type synonym
`PullbackShift.adjunction adj φ : PullbackShift.functor F φ ⊣ PullbackShift.functor G φ`
and we show that, if `adj` is compatible with `CommShift` structures
on `F` and `G`, then `PullbackShift.adjunction adj φ` is also compatible with the pulled back
`CommShift` structures.
-/

@[expose] public section

namespace CategoryTheory

open Limits Category

variable (C : Type*) [Category* C] {A B : Type*} [AddMonoid A] [AddMonoid B]

/-- The category `PullbackShift C φ` is equipped with a shift such that for all `a`,
the shift functor by `a` is `shiftFunctor C (φ a)`. -/
@[nolint unusedArguments]
/-
**CategoryTheory.PullbackShift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：PullbackShift [HasShift C B] (_ : A ->+ B)
参数：_ : A ->+ B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category `PullbackShift C φ` is equipped with a shift such that for all `a`,
the shift functor by `a` is `shiftFunctor C (φ a)`.
-/
def PullbackShift [HasShift C B] (_ : A →+ B) := C
deriving Category

attribute [local instance] endofunctorMonoidalCategory

variable [HasShift C B] (φ : A →+ B)

set_option backward.isDefEq.respectTransparency false in
/-- The shift on `PullbackShift C φ` is obtained by precomposing the shift on `C` with
the monoidal functor `Discrete.addMonoidalFunctor φ : Discrete A ⥤ Discrete B`. -/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shift on `PullbackShift C φ` is obtained by precomposing the shift on `C` wi
th
the monoidal functor `Discrete.addMonoidalFunctor φ : Discrete A ⥤ Discrete B`.
-/
instance : HasShift (PullbackShift C φ) A where
  shift := Discrete.addMonoidalFunctor φ ⋙ shiftMonoidalFunctor C B
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject C] : HasZeroObject (PullbackShift C φ) :=
  inferInstanceAs <| HasZeroObject C
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preadditive C] : Preadditive (PullbackShift C φ) :=
  inferInstanceAs <| Preadditive C
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preadditive C] (a : A) [(shiftFunctor C (φ a)).Additive] :
    (shiftFunctor (PullbackShift C φ) a).Additive :=
  inferInstanceAs (shiftFunctor C (φ a)).Additive

/-- When `b = φ a`, this is the canonical
isomorphism `shiftFunctor (PullbackShift C φ) a ≅ shiftFunctor C b`. -/
/-
**CategoryTheory.pullbackShiftIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：pullbackShiftIso (a : A) (b : B) (h : b = φ a) : shiftFunctor (PullbackShi
ft C φ) a ≅ shiftFunctor C b
参数：a : A；b : B；h : b = φ a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `b = φ a`, this is the canonical
isomorphism `shiftFunctor (PullbackShift C φ) a ≅ shiftFunctor C b`.
-/
def pullbackShiftIso (a : A) (b : B) (h : b = φ a) :
    shiftFunctor (PullbackShift C φ) a ≅ shiftFunctor C b := eqToIso (by subst h; rfl)

variable {C}
variable (X : PullbackShift C φ) (a₁ a₂ a₃ : A) (h : a₁ + a₂ = a₃) (b₁ b₂ b₃ : B)
  (h₁ : b₁ = φ a₁) (h₂ : b₂ = φ a₂) (h₃ : b₃ = φ a₃)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.pullbackShiftFunctorZero_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：pullbackShiftFunctorZero_inv_app : (shiftFunctorZero _ A).inv.app X = (shi
ftFunctorZero C B).inv.app X ≫ (pullbackShiftIso C φ 0 0 (by simp)).inv.app X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
-/
lemma pullbackShiftFunctorZero_inv_app :
    (shiftFunctorZero _ A).inv.app X =
      (shiftFunctorZero C B).inv.app X ≫ (pullbackShiftIso C φ 0 0 (by simp)).inv.app X := by
  change (shiftFunctorZero C B).inv.app X ≫ _ = _
  dsimp [Discrete.eqToHom, Discrete.addMonoidalFunctor_ε]
  congr 2
  apply eqToHom_map

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.pullbackShiftFunctorZero_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：pullbackShiftFunctorZero_hom_app : (shiftFunctorZero _ A).hom.app X = (pul
lbackShiftIso C φ 0 0 (by simp)).hom.app X ≫ (shiftFunctorZero C B).hom.app X
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
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.pullbackShiftFunctorZero_inv_app`：pullbackShiftFunctorZer
o_inv_app : (shiftFunctorZero _ A).inv.app X = (shiftFunctorZero C B).inv.app X 
≫ (pullbackShiftIso C φ 0 0 (by simp)…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
-/
lemma pullbackShiftFunctorZero_hom_app :
    (shiftFunctorZero _ A).hom.app X =
      (pullbackShiftIso C φ 0 0 (by simp)).hom.app X ≫ (shiftFunctorZero C B).hom.app X := by
  rw [← cancel_epi ((shiftFunctorZero _ A).inv.app X), Iso.inv_hom_id_app,
    pullbackShiftFunctorZero_inv_app, assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.pullbackShiftFunctorZero'_inv_app** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {A : Type u
_2} {B : Type u_3} [inst_1 : AddMonoid A]   [inst_2 : AddMonoid B] [inst_3 : Cat
egoryTheory.HasShift C B] (φ : A →+ B) (X : CategoryTheory.PullbackShift C φ),  
 (CategoryTheory.shiftFunctorZero (CategoryTheory.PullbackShift C φ) A).inv.app 
X =     CategoryTheory.CategoryStruct.comp ((CategoryTheory.shiftFunctorZero' C 
(φ 0) ⋯).inv.app X)       ((CategoryTheory.pullbackShiftIso C φ 0 (φ 0) ⋯).inv.a
pp X)
参数：φ : A →+ B；X : CategoryTheory.PullbackShift C φ；CategoryTheory.shiftFunctorZe
ro (CategoryTheory.PullbackShift C φ) A；(CategoryTheory.shiftFunctorZero' C (φ 0
) ⋯).inv.app X；(CategoryTheory.pullbackShiftIso C φ 0 (φ 0) ⋯).inv.app X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.pullbackShiftFunctorZero_inv_app`：pullbackShiftFunctorZer
o_inv_app : (shiftFunctorZero _ A).inv.app X = (shiftFunctorZero C B).inv.app X 
≫ (pullbackShiftIso C φ 0 0 (by simp)…
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.eqToHom_app`：eqToHom_app {F G : C ⥤ D} (h : F = G) (X : C
) : (eqToHom h : F ⟶ G).app X = eqToHom (Functor.congr_obj h X)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma pullbackShiftFunctorZero'_inv_app :
    (shiftFunctorZero _ A).inv.app X = (shiftFunctorZero' C (φ 0) (by rw [map_zero])).inv.app X ≫
      (pullbackShiftIso C φ 0 (φ 0) rfl).inv.app X := by
  rw [pullbackShiftFunctorZero_inv_app]
  simp only [Functor.id_obj, pullbackShiftIso, eqToIso.inv, eqToHom_app, shiftFunctorZero',
    Iso.trans_inv, NatTrans.comp_app, eqToIso_refl, Iso.refl_inv, NatTrans.id_app, assoc]
  erw [comp_id]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.pullbackShiftFunctorZero'_hom_app** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {A : Type u
_2} {B : Type u_3} [inst_1 : AddMonoid A]   [inst_2 : AddMonoid B] [inst_3 : Cat
egoryTheory.HasShift C B] (φ : A →+ B) (X : CategoryTheory.PullbackShift C φ),  
 (CategoryTheory.shiftFunctorZero (CategoryTheory.PullbackShift C φ) A).hom.app 
X =     CategoryTheory.CategoryStruct.comp ((CategoryTheory.pullbackShiftIso C φ
 0 (φ 0) ⋯).hom.app X)       ((CategoryTheory.shiftFunctorZero' C (φ 0) ⋯).hom.a
pp X)
参数：φ : A →+ B；X : CategoryTheory.PullbackShift C φ；CategoryTheory.shiftFunctorZe
ro (CategoryTheory.PullbackShift C φ) A；(CategoryTheory.pullbackShiftIso C φ 0 (
φ 0) ⋯).hom.app X；(CategoryTheory.shiftFunctorZero' C (φ 0) ⋯).hom.app X。
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
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.pullbackShiftFunctorZero'_inv_app`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {A : Type u_2} {B : Type u_3} [inst_1 :
 AddMonoid A]   [inst_2 : AddMonoid B]…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
-/
lemma pullbackShiftFunctorZero'_hom_app :
    (shiftFunctorZero _ A).hom.app X = (pullbackShiftIso C φ 0 (φ 0) rfl).hom.app X ≫
      (shiftFunctorZero' C (φ 0) (by rw [map_zero])).hom.app X := by
  rw [← cancel_epi ((shiftFunctorZero _ A).inv.app X), Iso.inv_hom_id_app,
    pullbackShiftFunctorZero'_inv_app, assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.pullbackShiftFunctorAdd'_inv_app** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {A : Type u
_2} {B : Type u_3} [inst_1 : AddMonoid A]   [inst_2 : AddMonoid B] [inst_3 : Cat
egoryTheory.HasShift C B] (φ : A →+ B) (X : CategoryTheory.PullbackShift C φ)   
(a₁ a₂ a₃ : A) (h : a₁ + a₂ = a₃) (b₁ b₂ b₃ : B) (h₁ : b₁ = φ a₁) (h₂ : b₂ = φ a
₂) (h₃ : b₃ = φ a₃),   (CategoryTheory.shiftFunctorAdd' (CategoryTheory.Pullback
Shift C φ) a₁ a₂ a₃ h).inv.app X =     CategoryTheory.CategoryStruct.comp       
((CategoryTheory.shiftFunctor (CategoryTheory.PullbackShift C φ) a₂).map        
 ((CategoryTheory.pullbackShiftIso C φ a₁ b₁ h₁).hom.app X))       (CategoryTheo
ry.CategoryStruct.comp         ((CategoryTheory.pullbackShiftIso C φ a₂ b₂ h₂).h
om.app ((CategoryTheory.shiftFunctor C b₁).obj X))         (CategoryTheory.Categ
oryStruct.comp ((CategoryTheory.shiftFunctorAdd' C b₁ b₂ b₃ ⋯).inv.app X)       
    ((CategoryTheory.pullbackShiftIso C φ a₃ b₃ h₃).inv.app X)))
参数：φ : A →+ B；X : CategoryTheory.PullbackShift C φ；a₁ a₂ a₃ : A；h : a₁ + a₂ = a₃
；b₁ b₂ b₃ : B；h₁ : b₁ = φ a₁；h₂ : b₂ = φ a₂；h₃ : b₃ = φ a₃；CategoryTheory.shiftF
unctorAdd' (CategoryTheory.PullbackShift C φ) a₁ a₂ a₃ h；(CategoryTheory.shiftFu
nctor (CategoryTheory.PullbackShift C φ) a₂).map         ((CategoryTheory.pullba
ckShiftIso C φ a₁ b₁ h₁).hom.app X)；CategoryTheory.CategoryStruct.comp         (
(CategoryTheory.pullbackShiftIso C φ a₂ b₂ h₂).hom.app ((CategoryTheory.shiftFun
ctor C b₁).obj X))         (CategoryTheory.CategoryStruct.comp ((CategoryTheory.
shiftFunctorAdd' C b₁ b₂ b₃ ⋯).inv.app X)           ((CategoryTheory.pullbackShi
ftIso C φ a₃ b₃ h₃).inv.app X))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd`：∀ (C : Type u) {A : 
Type u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [in
st_2 : CategoryTheory.HasShift C A] (i j…
· 使用定理 `AddMonoidHom.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N) (a b : M), f (a + b) = f a + f b
· 使用定理 `CategoryTheory.Discrete.addMonoidalFunctor_μ`：∀ {M : Type u} [inst : Add
Monoid M] {N : Type u'} [inst_1 : AddMonoid N] (F : M →+ N)   (m₁ m₂ : CategoryT
heory.Discrete M),   CategoryTheor…
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
-/
lemma pullbackShiftFunctorAdd'_inv_app :
    (shiftFunctorAdd' _ a₁ a₂ a₃ h).inv.app X =
      (shiftFunctor (PullbackShift C φ) a₂).map ((pullbackShiftIso C φ a₁ b₁ h₁).hom.app X) ≫
        (pullbackShiftIso C φ a₂ b₂ h₂).hom.app _ ≫
        (shiftFunctorAdd' C b₁ b₂ b₃ (by rw [h₁, h₂, h₃, ← h, φ.map_add])).inv.app X ≫
        (pullbackShiftIso C φ a₃ b₃ h₃).inv.app X := by
  subst h₁ h₂ h
  obtain rfl : b₃ = φ a₁ + φ a₂ := by rw [h₃, φ.map_add]
  simp only [NatTrans.naturality_assoc]
  erw [Functor.map_id, id_comp, id_comp, shiftFunctorAdd'_eq_shiftFunctorAdd,
    shiftFunctorAdd'_eq_shiftFunctorAdd]
  change _ ≫ _ = _
  congr 1
  rw [Discrete.addMonoidalFunctor_μ]
  dsimp [Discrete.eqToHom]
  congr 2
  apply eqToHom_map

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.pullbackShiftFunctorAdd'_hom_app** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {A : Type u
_2} {B : Type u_3} [inst_1 : AddMonoid A]   [inst_2 : AddMonoid B] [inst_3 : Cat
egoryTheory.HasShift C B] (φ : A →+ B) (X : CategoryTheory.PullbackShift C φ)   
(a₁ a₂ a₃ : A) (h : a₁ + a₂ = a₃) (b₁ b₂ b₃ : B) (h₁ : b₁ = φ a₁) (h₂ : b₂ = φ a
₂) (h₃ : b₃ = φ a₃),   (CategoryTheory.shiftFunctorAdd' (CategoryTheory.Pullback
Shift C φ) a₁ a₂ a₃ h).hom.app X =     CategoryTheory.CategoryStruct.comp ((Cate
goryTheory.pullbackShiftIso C φ a₃ b₃ h₃).hom.app X)       (CategoryTheory.Categ
oryStruct.comp ((CategoryTheory.shiftFunctorAdd' C b₁ b₂ b₃ ⋯).hom.app X)       
  (CategoryTheory.CategoryStruct.comp           ((CategoryTheory.pullbackShiftIs
o C φ a₂ b₂ h₂).inv.app ((CategoryTheory.shiftFunctor C b₁).obj X))           ((
CategoryTheory.shiftFunctor (CategoryTheory.PullbackShift C φ) a₂).map          
   ((CategoryTheory.pullbackShiftIso C φ a₁ b₁ h₁).inv.app X))))
参数：φ : A →+ B；X : CategoryTheory.PullbackShift C φ；a₁ a₂ a₃ : A；h : a₁ + a₂ = a₃
；b₁ b₂ b₃ : B；h₁ : b₁ = φ a₁；h₂ : b₂ = φ a₂；h₃ : b₃ = φ a₃；CategoryTheory.shiftF
unctorAdd' (CategoryTheory.PullbackShift C φ) a₁ a₂ a₃ h；(CategoryTheory.pullbac
kShiftIso C φ a₃ b₃ h₃).hom.app X；CategoryTheory.CategoryStruct.comp ((CategoryT
heory.shiftFunctorAdd' C b₁ b₂ b₃ ⋯).hom.app X)         (CategoryTheory.Category
Struct.comp           ((CategoryTheory.pullbackShiftIso C φ a₂ b₂ h₂).inv.app ((
CategoryTheory.shiftFunctor C b₁).obj X))           ((CategoryTheory.shiftFuncto
r (CategoryTheory.PullbackShift C φ) a₂).map             ((CategoryTheory.pullba
ckShiftIso C φ a₁ b₁ h₁).inv.app X)))。
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
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.pullbackShiftFunctorAdd'_inv_app`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A : Type u_2} {B : Type u_3} [inst_1 : 
AddMonoid A]   [inst_2 : AddMonoid B]…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
lemma pullbackShiftFunctorAdd'_hom_app :
    (shiftFunctorAdd' _ a₁ a₂ a₃ h).hom.app X =
      (pullbackShiftIso C φ a₃ b₃ h₃).hom.app X ≫
      (shiftFunctorAdd' C b₁ b₂ b₃ (by rw [h₁, h₂, h₃, ← h, φ.map_add])).hom.app X ≫
      (pullbackShiftIso C φ a₂ b₂ h₂).inv.app _ ≫
      (shiftFunctor (PullbackShift C φ) a₂).map ((pullbackShiftIso C φ a₁ b₁ h₁).inv.app X) := by
  rw [← cancel_epi ((shiftFunctorAdd' _ a₁ a₂ a₃ h).inv.app X), Iso.inv_hom_id_app,
    pullbackShiftFunctorAdd'_inv_app φ X a₁ a₂ a₃ h b₁ b₂ b₃ h₁ h₂ h₃, assoc, assoc, assoc,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  rfl

variable {D : Type*} [Category* D] [HasShift D B] (F : C ⥤ D) [F.CommShift B]

/--
The functor `F`, seen as a functor from `PullbackShift C φ` to `PullbackShift D φ`.
Then a `CommShift B` instance on `F` will define a `CommShift A` instance on
`PullbackShift.functor F φ`, and we won't have to juggle with two `CommShift` instances
on `F`.
-/
/-
**CategoryTheory.PullbackShift.functor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.PullbackShift`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {A 
: Type u_2} →       {B : Type u_3} →         [inst_1 : AddMonoid A] →           
[inst_2 : AddMonoid B] →             [inst_3 : CategoryTheory.HasShift C B] →   
            (φ : A →+ B) →                 {D : Type u_4} →                   [i
nst_4 : CategoryTheory.Category.{v_2, u_4} D] →                     [inst_5 : Ca
tegoryTheory.HasShift D B] →                       CategoryTheory.Functor C D → 
                        CategoryTheory.Functor (CategoryTheory.PullbackShift C φ
) (CategoryTheory.PullbackShift D φ)
参数：φ : A →+ B；CategoryTheory.PullbackShift C φ；CategoryTheory.PullbackShift D φ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `F`, seen as a functor from `PullbackShift C φ` to `PullbackShift D 
φ`.
Then a `CommShift B` instance on `F` will define a `CommShift A` instance on
`PullbackShift.functor F φ`, and we won't have to juggle with two `CommShift` in
stances
on `F`.
-/
def PullbackShift.functor : PullbackShift C φ ⥤ PullbackShift D φ := F

variable {F} in
/--
The natural transformation `τ`, seen as a natural transformation from `PullbackShift.functor F φ`
to `PullbackShift.functor G φ`. Then a `CommShift B` instance on `τ` will define a `CommShift A`
instance on `PullbackShift.natTrans τ φ`, and we won't have to juggle with two `CommShift`
instances on `τ`.
-/
/-
**CategoryTheory.PullbackShift.natTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.PullbackShift`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {A 
: Type u_2} →       {B : Type u_3} →         [inst_1 : AddMonoid A] →           
[inst_2 : AddMonoid B] →             [inst_3 : CategoryTheory.HasShift C B] →   
            (φ : A →+ B) →                 {D : Type u_4} →                   [i
nst_4 : CategoryTheory.Category.{v_2, u_4} D] →                     [inst_5 : Ca
tegoryTheory.HasShift D B] →                       {F G : CategoryTheory.Functor
 C D} →                         (F ⟶ G) → (CategoryTheory.PullbackShift.functor 
φ F ⟶ CategoryTheory.PullbackShift.functor φ G)
参数：φ : A →+ B；F ⟶ G；CategoryTheory.PullbackShift.functor φ F ⟶ CategoryTheory.Pu
llbackShift.functor φ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `τ`, seen as a natural transformation from `PullbackS
hift.functor F φ`
to `PullbackShift.functor G φ`. Then a `CommShift B` instance on `τ` will define
 a `CommShift A`
instance on `PullbackShift.natTrans τ φ`, and we won't have to juggle with two `
CommShift`
instances on `τ`.
-/
def PullbackShift.natTrans {G : C ⥤ D} (τ : F ⟶ G) :
    PullbackShift.functor φ F ⟶ PullbackShift.functor φ G := τ

namespace Functor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `F : C ⥤ D` commutes with the shifts on `C` and `D`, then `PullbackShift.functor F φ`
commutes with their pullbacks by an additive map `φ`.
-/
/-
**CategoryTheory.Functor.commShiftPullback** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：commShiftPullback : (PullbackShift.functor φ F).CommShift A where commShif
tIso a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` commutes with the shifts on `C` and `D`, then `PullbackShift.func
tor F φ`
commutes with their pullbacks by an additive map `φ`.
-/
instance commShiftPullback : (PullbackShift.functor φ F).CommShift A where
  commShiftIso a := isoWhiskerRight (pullbackShiftIso C φ a (φ a) rfl) F ≪≫
    F.commShiftIso (φ a) ≪≫ isoWhiskerLeft _ (pullbackShiftIso D φ a (φ a) rfl).symm
  commShiftIso_zero := by
    ext
    dsimp
    simp only [F.commShiftIso_zero' (A := B) (φ 0) (by rw [map_zero]), CommShift.isoZero'_hom_app,
      assoc, CommShift.isoZero_hom_app, pullbackShiftFunctorZero'_hom_app, map_comp,
      pullbackShiftFunctorZero'_inv_app]
    rfl
  commShiftIso_add _ _ := by
    ext
    simp only [PullbackShift.functor, comp_obj, Iso.trans_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      CommShift.isoAdd_hom_app, map_comp, assoc]
    rw [F.commShiftIso_add' (φ.map_add _ _).symm,
      ← shiftFunctorAdd'_eq_shiftFunctorAdd, ← shiftFunctorAdd'_eq_shiftFunctorAdd,
      pullbackShiftFunctorAdd'_hom_app φ _ _ _ _ rfl _ _ _ rfl rfl rfl,
      pullbackShiftFunctorAdd'_inv_app φ _ _ _ _ rfl _ _ _ rfl rfl rfl]
    simp only [CommShift.isoAdd'_hom_app, assoc, map_comp, NatTrans.naturality_assoc,
      Iso.inv_hom_id_app_assoc]
    slice_rhs 9 10 => rw [← map_comp, Iso.inv_hom_id_app, map_id]
    simp only [comp_obj, id_comp]
    rw [← Functor.comp_map F (shiftFunctor D _), ← (F.commShiftIso _).hom.naturality_assoc]
    slice_rhs 4 5 => rw [← map_comp, (pullbackShiftIso C φ _ _ rfl).hom.naturality, map_comp]
    slice_rhs 3 4 => rw [← map_comp, Iso.inv_hom_id_app, map_id]
    simp only [comp_obj, id_comp, comp_map, assoc]
    slice_rhs 3 4 => rw [← map_comp, ← map_comp, Iso.inv_hom_id_app, map_id, map_id]
    rw [id_comp, assoc, assoc]
    rfl
/-
**CategoryTheory.Functor.commShiftPullback_iso_eq** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：commShiftPullback_iso_eq (a : A) (b : B) (h : b = φ a) : (PullbackShift.fu
nctor φ F).commShiftIso a (C
参数：a : A；b : B；h : b = φ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma commShiftPullback_iso_eq (a : A) (b : B) (h : b = φ a) :
    (PullbackShift.functor φ F).commShiftIso a (C := PullbackShift C φ) (D := PullbackShift D φ) =
      isoWhiskerRight (pullbackShiftIso C φ a b h) F ≪≫ (F.commShiftIso b) ≪≫
        isoWhiskerLeft F (pullbackShiftIso D φ a b h).symm := by
  obtain rfl : b = φ a := h
  rfl

end Functor

namespace NatTrans

variable {F} {G : C ⥤ D} [G.CommShift B]

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.Functor in
/-
**CategoryTheory.NatTrans.commShiftPullback** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.NatTrans`。
形式化陈述：commShiftPullback (τ : F ⟶ G) [NatTrans.CommShift τ B] : NatTrans.CommShif
t (PullbackShift.natTrans φ τ) A where shift_comm _
参数：τ : F ⟶ G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Functor.commShiftPullback_iso_eq`：commShiftPullback_iso_e
q (a : A) (b : B) (h : b = φ a) : (PullbackShift.functor φ F).commShiftIso a (C
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance commShiftPullback (τ : F ⟶ G) [NatTrans.CommShift τ B] :
    NatTrans.CommShift (PullbackShift.natTrans φ τ) A where
  shift_comm _ := by
    ext
    dsimp [PullbackShift.natTrans]
    simp only [commShiftPullback_iso_eq φ _ _ _ rfl, Iso.trans_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, Iso.symm_hom, comp_app, whiskerRight_app, whiskerLeft_app,
      assoc]
    rw [← τ.naturality_assoc]
    simp [← NatTrans.shift_app_comm_assoc]

variable (C) in
/-- The natural isomorphism between the identity of `PullbackShift C φ` and the
pullback of the identity of `C`.
-/
/-
**CategoryTheory.NatTrans.PullbackShift.natIsoId** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.NatTrans.PullbackShift`。
形式化陈述：(C : Type u_1) →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {A 
: Type u_2} →       {B : Type u_3} →         [inst_1 : AddMonoid A] →           
[inst_2 : AddMonoid B] →             [inst_3 : CategoryTheory.HasShift C B] →   
            (φ : A →+ B) →                 CategoryTheory.Functor.id (CategoryTh
eory.PullbackShift C φ) ≅                   CategoryTheory.PullbackShift.functor
 φ (CategoryTheory.Functor.id C)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism between the identity of `PullbackShift C φ` and the
pullback of the identity of `C`.
-/
def PullbackShift.natIsoId : 𝟭 (PullbackShift C φ) ≅ PullbackShift.functor φ (𝟭 C) := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
This expresses the compatibility between two `CommShift` structures by `A` on (synonyms of)
`𝟭 C`: the canonical `CommShift` structure on `𝟭 (PullbackShift C φ)`, and the `CommShift`
structure on `PullbackShift.functor (𝟭 C) φ` (i.e the pullback of the canonical `CommShift`
structure on `𝟭 C`).
-/
/-
**CategoryTheory.NatTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.NatTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This expresses the compatibility between two `CommShift` structures by `A` on (s
ynonyms of)
`𝟭 C`: the canonical `CommShift` structure on `𝟭 (PullbackShift C φ)`, and the `
CommShift`
structure on `PullbackShift.functor (𝟭 C) φ` (i.e the pullback of the canonical 
`CommShift`
structure on `𝟭 C`).
-/
instance : NatTrans.CommShift (PullbackShift.natIsoId C φ).hom A where
  shift_comm _ := by
    ext
    simp [PullbackShift.natIsoId, Functor.commShiftPullback_iso_eq]

variable (F) {E : Type*} [Category* E] [HasShift E B] (G : D ⥤ E) [G.CommShift B]

/-- The natural isomorphism between the pullback of `F ⋙ G` and the
composition of the pullbacks of `F` and `G`.
-/
/-
**CategoryTheory.NatTrans.PullbackShift.natIsoComp** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.NatTrans.PullbackShift`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {A 
: Type u_2} →       {B : Type u_3} →         [inst_1 : AddMonoid A] →           
[inst_2 : AddMonoid B] →             [inst_3 : CategoryTheory.HasShift C B] →   
            (φ : A →+ B) →                 {D : Type u_4} →                   [i
nst_4 : CategoryTheory.Category.{v_2, u_4} D] →                     [inst_5 : Ca
tegoryTheory.HasShift D B] →                       (F : CategoryTheory.Functor C
 D) →                         {E : Type u_5} →                           [inst_6
 : CategoryTheory.Category.{v_3, u_5} E] →                             [inst_7 :
 CategoryTheory.HasShift E B] →                               (G : CategoryTheor
y.Functor D E) →                                 CategoryTheory.PullbackShift.fu
nctor φ (F.comp G) ≅                                   (CategoryTheory.PullbackS
hift.functor φ F).comp                                     (CategoryTheory.Pullb
ackShift.functor φ G)
参数：φ : A →+ B；F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.co
mp G；CategoryTheory.PullbackShift.functor φ F；CategoryTheory.PullbackShift.funct
or φ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism between the pullback of `F ⋙ G` and the
composition of the pullbacks of `F` and `G`.
-/
def PullbackShift.natIsoComp : PullbackShift.functor φ (F ⋙ G) ≅
    PullbackShift.functor φ F ⋙ PullbackShift.functor φ G := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
Suppose that `F` and `G` have `CommShift` structure by `B`. This expresses the
compatibility between two `CommShift` structures by `A` on (synonyms of) `F ⋙ G`:
the `CommShift` structure on `PullbackShift.functor (F ⋙ G) φ` (i.e the pullback of the
composition of `CommShift` structures by `B` on `F` and `G`), and that on
`PullbackShift.functor F φ ⋙ PullbackShift.functor G φ` (i.e. the one coming from
the composition of the pulled back `CommShift` structures on `F` and `G`).
-/
open CategoryTheory.Functor in
/-
**CategoryTheory.NatTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.NatTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatTrans.CommShift (PullbackShift.natIsoComp φ F G).hom A where
  shift_comm _ := by
    ext
    dsimp [PullbackShift.natIsoComp]
    simp only [commShiftPullback_iso_eq φ _ _ _ rfl, Iso.trans_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, Iso.symm_hom, comp_app, comp_obj, whiskerRight_app, Functor.comp_map,
      commShiftIso_comp_hom_app, whiskerLeft_app, assoc, map_id, comp_id, map_comp, id_comp]
    dsimp [PullbackShift.functor]
    slice_rhs 3 4 => rw [← G.map_comp, Iso.inv_hom_id_app]
    simp

end NatTrans

set_option backward.isDefEq.respectTransparency false in
/--
The adjunction `adj`, seen as an adjunction between `PullbackShift.functor F φ`
and `PullbackShift.functor G φ`.
-/
@[simps -isSimp]
/-
**CategoryTheory.PullbackShift.adjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.PullbackShift`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {A 
: Type u_2} →       {B : Type u_3} →         [inst_1 : AddMonoid A] →           
[inst_2 : AddMonoid B] →             [inst_3 : CategoryTheory.HasShift C B] →   
            (φ : A →+ B) →                 {D : Type u_4} →                   [i
nst_4 : CategoryTheory.Category.{v_2, u_4} D] →                     [inst_5 : Ca
tegoryTheory.HasShift D B] →                       {F : CategoryTheory.Functor C
 D} →                         {G : CategoryTheory.Functor D C} →                
           (F ⊣ G) →                             (CategoryTheory.PullbackShift.f
unctor φ F ⊣ CategoryTheory.PullbackShift.functor φ G)
参数：φ : A →+ B；F ⊣ G；CategoryTheory.PullbackShift.functor φ F ⊣ CategoryTheory.Pu
llbackShift.functor φ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction `adj`, seen as an adjunction between `PullbackShift.functor F φ`
and `PullbackShift.functor G φ`.
-/
def PullbackShift.adjunction {F} {G : D ⥤ C} (adj : F ⊣ G) :
    PullbackShift.functor φ F ⊣ PullbackShift.functor φ G where
  unit := (NatTrans.PullbackShift.natIsoId C φ).hom ≫
    PullbackShift.natTrans φ adj.unit ≫ (NatTrans.PullbackShift.natIsoComp φ F G).hom
  counit := (NatTrans.PullbackShift.natIsoComp φ G F).inv ≫
    PullbackShift.natTrans φ adj.counit ≫ (NatTrans.PullbackShift.natIsoId D φ).inv
  left_triangle_components _ := by
    simp [PullbackShift.natTrans, NatTrans.PullbackShift.natIsoComp,
      NatTrans.PullbackShift.natIsoId, PullbackShift.functor]
  right_triangle_components _ := by
    simp [PullbackShift.natTrans, NatTrans.PullbackShift.natIsoComp,
      NatTrans.PullbackShift.natIsoId, PullbackShift.functor]

namespace Adjunction

variable {F} {G : D ⥤ C} (adj : F ⊣ G) [G.CommShift B]

/--
If an adjunction `F ⊣ G` is compatible with `CommShift` structures on `F` and `G`, then
it is also compatible with the pulled back `CommShift` structures by an additive map
`φ : B →+ A`.
-/
/-
**CategoryTheory.Adjunction.commShiftPullback** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Adjunction`。
形式化陈述：commShiftPullback [adj.CommShift B] : (PullbackShift.adjunction φ adj).Com
mShift A where commShift_unit
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.CommShift.comp`：∀ {C : Type u_1} {D : Type u_2} 
[inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Categor
y.{v_2, u_2} D] {F₁ F₂ F₃ : …
· 使用定理 `CategoryTheory.NatTrans.instCommShiftPullbackShiftHomFunctorNatIsoId`：∀ 
{C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {A : Type u_2} {B :
 Type u_3} [inst_1 : AddMonoid A]   [inst_2 : AddMonoid B]…
· 使用定理 `CategoryTheory.Adjunction.CommShift.commShift_unit`：∀ {C : Type u_1} {D 
: Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryTh
eory.Category.{v_2, u_2} D} {F : Categor…
· 使用定理 `CategoryTheory.NatTrans.instCommShiftPullbackShiftHomFunctorNatIsoComp`：
∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {A : Type u_2} {B
 : Type u_3} [inst_1 : AddMonoid A]   [inst_2 : AddMonoid B]…
· 使用定理 `CategoryTheory.Adjunction.CommShift.commShift_counit`：∀ {C : Type u_1} {
D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : Category
Theory.Category.{v_2, u_2} D} {F : Categor…

--- 原说明 ---
If an adjunction `F ⊣ G` is compatible with `CommShift` structures on `F` and `G
`, then
it is also compatible with the pulled back `CommShift` structures by an additive
 map
`φ : B →+ A`.
-/
instance commShiftPullback [adj.CommShift B] : (PullbackShift.adjunction φ adj).CommShift A where
  commShift_unit := by
    dsimp [PullbackShift.adjunction]
    infer_instance
  commShift_counit := by
    dsimp [PullbackShift.adjunction]
    infer_instance

end Adjunction

end CategoryTheory

