/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.CatCommSq
public import Mathlib.CategoryTheory.GuitartExact.Basic

/-!
# Vertical composition of Guitart exact squares

In this file, we show that the vertical composition of Guitart exact squares
is Guitart exact.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

open Category

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* D₁] [Category* D₂] [Category* D₃]

namespace TwoSquare

section WhiskerVertical

variable {T : C₁ ⥤ D₁} {L : C₁ ⥤ C₂} {R : D₁ ⥤ D₂} {B : C₂ ⥤ D₂} (w : TwoSquare T L R B)
  {L' : C₁ ⥤ C₂} {R' : D₁ ⥤ D₂}

/-- Given `w : TwoSquare T L R B`, one may obtain a 2-square `TwoSquare T L' R' B` if we
provide natural transformations `α : L ⟶ L'` and `β : R' ⟶ R`. -/
@[simps!]
/-
**CategoryTheory.TwoSquare.whiskerVertical** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.TwoSquare`。
形式化陈述：whiskerVertical (α : L ⟶ L') (β : R' ⟶ R) : TwoSquare T L' R' B
参数：α : L ⟶ L'；β : R' ⟶ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `w : TwoSquare T L R B`, one may obtain a 2-square `TwoSquare T L' R' B` i
f we
provide natural transformations `α : L ⟶ L'` and `β : R' ⟶ R`.
-/
def whiskerVertical (α : L ⟶ L') (β : R' ⟶ R) :
    TwoSquare T L' R' B :=
  (w.whiskerLeft α).whiskerRight β

namespace GuitartExact

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A 2-square stays Guitart exact if we replace the left and right functors
by isomorphic functors. See also `whiskerVertical_iff`. -/
/-
**CategoryTheory.TwoSquare.GuitartExact.whiskerVertical** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.TwoSquare.GuitartExact`。
形式化陈述：whiskerVertical [w.GuitartExact] (α : L ≅ L') (β : R ≅ R') : (w.whiskerVer
tical α.hom β.inv).GuitartExact
参数：α : L ≅ L'；β : R ≅ R'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.TwoSquare.guitartExact_iff_initial`：guitartExact_iff_init
ial : w.GuitartExact ↔ forall (X₂ : C₂), (w.structuredArrowDownwards X₂).Initial
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.initial_natIso_iff`：initial_natIso_iff {F F' : C 
⥤ D} (i : F ≅ F') : Initial F ↔ Initial F'
· 使用定理 `CategoryTheory.TwoSquare.instInitialStructuredArrowObjStructuredArrowDow
nwardsOfGuitartExact`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type 
u₄} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Cate
go…
· 使用定理 `CategoryTheory.Functor.initial_of_isLeftAdjoint`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…

--- 原说明 ---
A 2-square stays Guitart exact if we replace the left and right functors
by isomorphic functors. See also `whiskerVertical_iff`.
-/
lemma whiskerVertical [w.GuitartExact] (α : L ≅ L') (β : R ≅ R') :
    (w.whiskerVertical α.hom β.inv).GuitartExact := by
  rw [guitartExact_iff_initial]
  intro X₂
  let e : structuredArrowDownwards (w.whiskerVertical α.hom β.inv) X₂ ≅
      w.structuredArrowDownwards X₂ ⋙ (StructuredArrow.mapIso (β.app X₂)).functor :=
    NatIso.ofComponents (fun f => StructuredArrow.isoMk (α.symm.app f.right) (by
      dsimp
      simp only [NatTrans.naturality_assoc, assoc, ← B.map_comp,
        Iso.hom_inv_id_app, B.map_id, comp_id]))
  rw [Functor.initial_natIso_iff e]
  infer_instance

/-- A 2-square is Guitart exact iff it is so after replacing the left and right functors by
isomorphic functors. -/
@[simp]
/-
**CategoryTheory.TwoSquare.GuitartExact.whiskerVertical_iff** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.TwoSquare.GuitartExact`。
形式化陈述：whiskerVertical_iff (α : L ≅ L') (β : R ≅ R') : (w.whiskerVertical α.hom β
.inv).GuitartExact ↔ w.GuitartExact
参数：α : L ≅ L'；β : R ≅ R'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.TwoSquare.ext`：ext (w w' : TwoSquare T L R B) (h : forall
 (X : C₁), w.natTrans.app X = w'.natTrans.app X) : w = w'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.TwoSquare.GuitartExact.whiskerVertical`：whiskerVertical [
w.GuitartExact] (α : L ≅ L') (β : R ≅ R') : (w.whiskerVertical α.hom β.inv).Guit
artExact

--- 原说明 ---
A 2-square is Guitart exact iff it is so after replacing the left and right func
tors by
isomorphic functors.
-/
lemma whiskerVertical_iff (α : L ≅ L') (β : R ≅ R') :
    (w.whiskerVertical α.hom β.inv).GuitartExact ↔ w.GuitartExact := by
  constructor
  · intro h
    have : w = (w.whiskerVertical α.hom β.inv).whiskerVertical α.inv β.hom := by
      ext X₁
      simp only [Functor.comp_obj, whiskerVertical_app, assoc, Iso.hom_inv_id_app_assoc,
        ← B.map_comp, Iso.hom_inv_id_app, B.map_id, comp_id]
    rw [this]
    exact whiskerVertical (w.whiskerVertical α.hom β.inv) α.symm β.symm
  · intro h
    exact whiskerVertical w α β
/-
**CategoryTheory.TwoSquare.GuitartExact.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.TwoSquare.GuitartExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [w.GuitartExact] (α : L ⟶ L') (β : R' ⟶ R)
    [IsIso α] [IsIso β] : (w.whiskerVertical α β).GuitartExact :=
  whiskerVertical w (asIso α) (asIso β).symm

end GuitartExact

end WhiskerVertical

section VerticalComposition

variable {H₁ : C₁ ⥤ D₁} {L₁ : C₁ ⥤ C₂} {R₁ : D₁ ⥤ D₂} {H₂ : C₂ ⥤ D₂}
  (w : TwoSquare H₁ L₁ R₁ H₂)
  {L₂ : C₂ ⥤ C₃} {R₂ : D₂ ⥤ D₃} {H₃ : C₃ ⥤ D₃}
  (w' : TwoSquare H₂ L₂ R₂ H₃)

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical isomorphism between
`w.structuredArrowDownwards Y₁ ⋙ w'.structuredArrowDownwards (R₁.obj Y₁)` and
`(w ≫ᵥ w').structuredArrowDownwards Y₁.` -/
/-
**CategoryTheory.TwoSquare.structuredArrowDownwardsComp** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.TwoSquare`。
形式化陈述：structuredArrowDownwardsComp (Y₁ : D₁) : w.structuredArrowDownwards Y₁ ⋙ w
'.structuredArrowDownwards (R₁.obj Y₁) ≅ (w ≫ᵥ w').structuredArrowDownwards Y₁
参数：Y₁ : D₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism between
`w.structuredArrowDownwards Y₁ ⋙ w'.structuredArrowDownwards (R₁.obj Y₁)` and
`(w ≫ᵥ w').structuredArrowDownwards Y₁.`
-/
def structuredArrowDownwardsComp (Y₁ : D₁) :
    w.structuredArrowDownwards Y₁ ⋙ w'.structuredArrowDownwards (R₁.obj Y₁) ≅
      (w ≫ᵥ w').structuredArrowDownwards Y₁ :=
  NatIso.ofComponents (fun _ => StructuredArrow.isoMk (Iso.refl _))

/-- The vertical composition of 2-squares. (Variant where we allow the replacement of
the vertical compositions by isomorphic functors.) -/
@[simps!]
/-
**CategoryTheory.TwoSquare.vComp'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.TwoS
quare`。
形式化陈述：vComp' {L₁₂ : C₁ ⥤ C₃} {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ L₂ ≅ L₁₂) (eR : R₁ ⋙ R₂ 
≅ R₁₂) : TwoSquare H₁ L₁₂ R₁₂ H₃
参数：eL : L₁ ⋙ L₂ ≅ L₁₂；eR : R₁ ⋙ R₂ ≅ R₁₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The vertical composition of 2-squares. (Variant where we allow the replacement o
f
the vertical compositions by isomorphic functors.)
-/
def vComp' {L₁₂ : C₁ ⥤ C₃} {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ L₂ ≅ L₁₂)
    (eR : R₁ ⋙ R₂ ≅ R₁₂) : TwoSquare H₁ L₁₂ R₁₂ H₃ :=
  (w ≫ᵥ w').whiskerVertical eL.hom eR.inv

namespace GuitartExact

/-
**CategoryTheory.TwoSquare.GuitartExact.vComp** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.TwoSquare.GuitartExact`。
形式化陈述：vComp [hw : w.GuitartExact] [hw' : w'.GuitartExact] : (w ≫ᵥ w').GuitartExa
ct
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.initial_natIso_iff`：initial_natIso_iff {F F' : C 
⥤ D} (i : F ≅ F') : Initial F ↔ Initial F'
· 使用定理 `CategoryTheory.TwoSquare.instInitialStructuredArrowObjStructuredArrowDow
nwardsOfGuitartExact`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type 
u₄} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Cate
go…
-/
instance vComp [hw : w.GuitartExact] [hw' : w'.GuitartExact] :
    (w ≫ᵥ w').GuitartExact := by
  simp only [TwoSquare.guitartExact_iff_initial]
  intro Y₁
  rw [← Functor.initial_natIso_iff (structuredArrowDownwardsComp w w' Y₁)]
  infer_instance
/-
**CategoryTheory.TwoSquare.GuitartExact.vComp'** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.TwoSquare.GuitartExact`。
形式化陈述：vComp' [GuitartExact w] [GuitartExact w'] {L₁₂ : C₁ ⥤ C₃} {R₁₂ : D₁ ⥤ D₃} 
(eL : L₁ ⋙ L₂ ≅ L₁₂) (eR : R₁ ⋙ R₂ ≅ R₁₂) : (w.vComp' w' eL eR).GuitartExact
参数：eL : L₁ ⋙ L₂ ≅ L₁₂；eR : R₁ ⋙ R₂ ≅ R₁₂。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.TwoSquare.GuitartExact.instWhiskerVerticalOfIsIsoFunctor`
：∀ {C₁ : Type u_1} {C₂ : Type u_2} {D₁ : Type u_4} {D₂ : Type u_5} [inst : Categ
oryTheory.Category.{v_1, u_1} C₁]   [inst_1 : CategoryTheory.…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
instance vComp' [GuitartExact w] [GuitartExact w'] {L₁₂ : C₁ ⥤ C₃}
    {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ L₂ ≅ L₁₂)
    (eR : R₁ ⋙ R₂ ≅ R₁₂) : (w.vComp' w' eL eR).GuitartExact := by
  dsimp only [TwoSquare.vComp']
  infer_instance
/-
**CategoryTheory.TwoSquare.GuitartExact.of_vComp** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.TwoSquare.GuitartExact`。
形式化陈述：of_vComp [R₁.EssSurj] [w.GuitartExact] [(w ≫ᵥ w').GuitartExact] : w'.Guita
rtExact
参数：w ≫ᵥ w'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.TwoSquare.guitartExact_iff_initial`：guitartExact_iff_init
ial : w.GuitartExact ↔ forall (X₂ : C₂), (w.structuredArrowDownwards X₂).Initial
· 使用引理 `CategoryTheory.TwoSquare.structuredArrowDownwards_initial_iff_of_iso`：st
ructuredArrowDownwards_initial_iff_of_iso {X₂ X₂' : C₂} (e : X₂ ≅ X₂') : (w.stru
cturedArrowDownwards X₂).Initial ↔ (w.structuredArrowDownw…
· 使用定理 `CategoryTheory.Functor.initial_of_natIso`：initial_of_natIso {F F' : C ⥤ 
D} [Initial F] (i : F ≅ F') : Initial F' where out _
· 使用定理 `CategoryTheory.TwoSquare.instInitialStructuredArrowObjStructuredArrowDow
nwardsOfGuitartExact`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type 
u₄} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Cate
go…
· 使用定理 `CategoryTheory.Functor.initial_of_initial_comp`：initial_of_initial_comp 
[Initial F] [Initial (F ⋙ G)] : Initial G
-/
lemma of_vComp [R₁.EssSurj] [w.GuitartExact] [(w ≫ᵥ w').GuitartExact] :
    w'.GuitartExact := by
  rw [guitartExact_iff_initial]
  intro Y₂
  rw [structuredArrowDownwards_initial_iff_of_iso _ (R₁.objObjPreimageIso Y₂).symm]
  have := Functor.initial_of_natIso (structuredArrowDownwardsComp w w' (R₁.objPreimage Y₂)).symm
  exact Functor.initial_of_initial_comp (w.structuredArrowDownwards (R₁.objPreimage Y₂)) _
/-
**CategoryTheory.TwoSquare.GuitartExact.of_vComp'** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.TwoSquare.GuitartExact`。
形式化陈述：of_vComp' {L₁₂ : C₁ ⥤ C₃} {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ L₂ ≅ L₁₂) (eR : R₁ ⋙ 
R₂ ≅ R₁₂) [R₁.EssSurj] [w.GuitartExact] [h : (w.vComp' w' eL eR).GuitartExact] :
 w'.GuitartExact
参数：eL : L₁ ⋙ L₂ ≅ L₁₂；eR : R₁ ⋙ R₂ ≅ R₁₂；w.vComp' w' eL eR。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.TwoSquare.GuitartExact.of_vComp`：of_vComp [R₁.EssSurj] [w
.GuitartExact] [(w ≫ᵥ w').GuitartExact] : w'.GuitartExact
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.TwoSquare.GuitartExact.whiskerVertical_iff`：whiskerVertic
al_iff (α : L ≅ L') (β : R ≅ R') : (w.whiskerVertical α.hom β.inv).GuitartExact 
↔ w.GuitartExact
-/
lemma of_vComp' {L₁₂ : C₁ ⥤ C₃} {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ L₂ ≅ L₁₂) (eR : R₁ ⋙ R₂ ≅ R₁₂)
    [R₁.EssSurj] [w.GuitartExact] [h : (w.vComp' w' eL eR).GuitartExact] :
    w'.GuitartExact := by
  dsimp [TwoSquare.vComp'] at h
  rw [whiskerVertical_iff] at h
  exact of_vComp w w'
/-
**CategoryTheory.TwoSquare.GuitartExact.vComp_iff_of_essSurj** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.TwoSquare.GuitartExact`。
形式化陈述：vComp_iff_of_essSurj [R₁.EssSurj] [w.GuitartExact] : (w ≫ᵥ w').GuitartExac
t ↔ w'.GuitartExact
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.TwoSquare.GuitartExact.of_vComp`：of_vComp [R₁.EssSurj] [w
.GuitartExact] [(w ≫ᵥ w').GuitartExact] : w'.GuitartExact
-/
lemma vComp_iff_of_essSurj [R₁.EssSurj] [w.GuitartExact] :
    (w ≫ᵥ w').GuitartExact ↔ w'.GuitartExact :=
  ⟨fun _ ↦ of_vComp w w', fun _ ↦ inferInstance⟩
/-
**CategoryTheory.TwoSquare.GuitartExact.vComp'_iff_of_essSurj** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.TwoSquare.GuitartExact`。
形式化陈述：∀ {C₁ : Type u_1} {C₂ : Type u_2} {C₃ : Type u_3} {D₁ : Type u_4} {D₂ : Ty
pe u_5} {D₃ : Type u_6}   [inst : CategoryTheory.Category.{v_1, u_1} C₁] [inst_1
 : CategoryTheory.Category.{v_2, u_2} C₂]   [inst_2 : CategoryTheory.Category.{v
_3, u_3} C₃] [inst_3 : CategoryTheory.Category.{v_4, u_4} D₁]   [inst_4 : Catego
ryTheory.Category.{v_5, u_5} D₂] [inst_5 : CategoryTheory.Category.{v_6, u_6} D₃
]   {H₁ : CategoryTheory.Functor C₁ D₁} {L₁ : CategoryTheory.Functor C₁ C₂} {R₁ 
: CategoryTheory.Functor D₁ D₂}   {H₂ : CategoryTheory.Functor C₂ D₂} (w : Categ
oryTheory.TwoSquare H₁ L₁ R₁ H₂) {L₂ : CategoryTheory.Functor C₂ C₃}   {R₂ : Cat
egoryTheory.Functor D₂ D₃} {H₃ : CategoryTheory.Functor C₃ D₃} (w' : CategoryThe
ory.TwoSquare H₂ L₂ R₂ H₃)   {L₁₂ : CategoryTheory.Functor C₁ C₃} {R₁₂ : Categor
yTheory.Functor D₁ D₃} (eL : L₁.comp L₂ ≅ L₁₂)   (eR : R₁.comp R₂ ≅ R₁₂) [R₁.Ess
Surj] [w.GuitartExact], (w.vComp' w' eL eR).GuitartExact ↔ w'.GuitartExact
参数：w : CategoryTheory.TwoSquare H₁ L₁ R₁ H₂；w' : CategoryTheory.TwoSquare H₂ L₂ 
R₂ H₃；eL : L₁.comp L₂ ≅ L₁₂；eR : R₁.comp R₂ ≅ R₁₂；w.vComp' w' eL eR。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.TwoSquare.GuitartExact.of_vComp'`：of_vComp' {L₁₂ : C₁ ⥤ C
₃} {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ L₂ ≅ L₁₂) (eR : R₁ ⋙ R₂ ≅ R₁₂) [R₁.EssSurj] [w.Gui
tartExact] [h : (w.vComp' w' eL eR).G…
-/
lemma vComp'_iff_of_essSurj
    {L₁₂ : C₁ ⥤ C₃} {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ L₂ ≅ L₁₂) (eR : R₁ ⋙ R₂ ≅ R₁₂)
    [R₁.EssSurj] [w.GuitartExact] :
    (w.vComp' w' eL eR).GuitartExact ↔ w'.GuitartExact :=
  ⟨fun _ ↦ of_vComp' w w' eL eR, fun _ ↦ inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.TwoSquare.GuitartExact.vComp_iff_of_equivalences** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.TwoSquare.GuitartExact`。
形式化陈述：vComp_iff_of_equivalences (eL : C₂ ≌ C₃) (eR : D₂ ≌ D₃) (w' : H₂ ⋙ eR.func
tor ≅ eL.functor ⋙ H₃) : (w ≫ᵥ w'.hom).GuitartExact ↔ w.GuitartExact
参数：eL : C₂ ≌ C₃；eR : D₂ ≌ D₃；w' : H₂ ⋙ eR.functor ≅ eL.functor ⋙ H₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.TwoSquare.ext`：ext (w w' : TwoSquare T L R B) (h : forall
 (X : C₁), w.natTrans.app X = w'.natTrans.app X) : w = w'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.TwoSquare.vComp'_app`：∀ {C₁ : Type u_1} {C₂ : Type u_2} {
C₃ : Type u_3} {D₁ : Type u_4} {D₂ : Type u_5} {D₃ : Type u_6}   [inst : Categor
yTheory.Category.{v_1, u_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.TwoSquare.vComp_app`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ 
: Type u₃} {C₄ : Type u₄} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1
 : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Equivalence.inv_fun_map`：inv_fun_map (e : C ≌ D) (X Y : C
) (f : X ⟶ Y) : e.inverse.map (e.functor.map f) = e.unitInv.app X ≫ f ≫ e.unit.a
pp Y
· 使用定理 `CategoryTheory.CatCommSq.vInv_iso_hom_app`：∀ {C₁ : Type u_1} {C₂ : Type 
u_2} {C₃ : Type u_3} {C₄ : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} 
C₁]   [inst_1 : CategoryTheory.…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.Equivalence.counitInv_app_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (e : C ≌ D) (X : C…
· 使用定理 `CategoryTheory.Functor.comp_map`：comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y :
 C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f)
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.TwoSquare.guitartExact_of_isEquivalence_of_isIso`：∀ {C₁ :
 Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
lemma vComp_iff_of_equivalences (eL : C₂ ≌ C₃) (eR : D₂ ≌ D₃)
    (w' : H₂ ⋙ eR.functor ≅ eL.functor ⋙ H₃) :
    (w ≫ᵥ w'.hom).GuitartExact ↔ w.GuitartExact := by
  constructor
  · intro hww'
    let : CatCommSq H₂ eL.functor eR.functor H₃ := ⟨w'⟩
    have hw' : CatCommSq.iso H₂ eL.functor eR.functor H₃ = w' := rfl
    let : CatCommSq H₃ eL.inverse eR.inverse H₂ := CatCommSq.vInvEquiv _ _ _ _ inferInstance
    let w'' := CatCommSq.iso H₃ eL.inverse eR.inverse H₂
    let α : (L₁ ⋙ eL.functor) ⋙ eL.inverse ≅ L₁ :=
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L₁ eL.unitIso.symm ≪≫ L₁.rightUnitor
    let β : (R₁ ⋙ eR.functor) ⋙ eR.inverse ≅ R₁ :=
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft R₁ eR.unitIso.symm ≪≫ R₁.rightUnitor
    have : w = (w ≫ᵥ w'.hom).vComp' w''.hom α β := by
      ext X₁
      simp? [w'', α, β] says
        simp only [Functor.comp_obj, vComp'_app, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
          Iso.symm_inv, assoc, NatTrans.comp_app, Functor.id_obj, Functor.rightUnitor_inv_app,
          Functor.whiskerLeft_app, Functor.associator_inv_app, comp_id, id_comp, vComp_app,
          Functor.map_comp, Equivalence.inv_fun_map, CatCommSq.vInv_iso_hom_app, Iso.trans_hom,
          Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.associator_hom_app,
          Functor.rightUnitor_hom_app, Iso.hom_inv_id_app_assoc, w'', α, β]
      simp only [hw', ← eR.inverse.map_comp_assoc]
      rw [Equivalence.counitInv_app_functor, ← Functor.comp_map, ← NatTrans.naturality_assoc]
      simp [← H₂.map_comp]
    rw [this]
    infer_instance
  · intro
    exact vComp w w'.hom

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.TwoSquare.GuitartExact.vComp'_iff_of_equivalences** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.TwoSquare.GuitartExact`。
形式化陈述：∀ {C₁ : Type u_1} {C₂ : Type u_2} {C₃ : Type u_3} {D₁ : Type u_4} {D₂ : Ty
pe u_5} {D₃ : Type u_6}   [inst : CategoryTheory.Category.{v_1, u_1} C₁] [inst_1
 : CategoryTheory.Category.{v_2, u_2} C₂]   [inst_2 : CategoryTheory.Category.{v
_3, u_3} C₃] [inst_3 : CategoryTheory.Category.{v_4, u_4} D₁]   [inst_4 : Catego
ryTheory.Category.{v_5, u_5} D₂] [inst_5 : CategoryTheory.Category.{v_6, u_6} D₃
]   {H₁ : CategoryTheory.Functor C₁ D₁} {L₁ : CategoryTheory.Functor C₁ C₂} {R₁ 
: CategoryTheory.Functor D₁ D₂}   {H₂ : CategoryTheory.Functor C₂ D₂} (w : Categ
oryTheory.TwoSquare H₁ L₁ R₁ H₂) {H₃ : CategoryTheory.Functor C₃ D₃}   (E : C₂ ≌
 C₃) (E' : D₂ ≌ D₃) (w' : H₂.comp E'.functor ≅ E.functor.comp H₃) {L₁₂ : Categor
yTheory.Functor C₁ C₃}   {R₁₂ : CategoryTheory.Functor D₁ D₃} (eL : L₁.comp E.fu
nctor ≅ L₁₂) (eR : R₁.comp E'.functor ≅ R₁₂),   (w.vComp' w'.hom eL eR).GuitartE
xact ↔ w.GuitartExact
参数：w : CategoryTheory.TwoSquare H₁ L₁ R₁ H₂；E : C₂ ≌ C₃；E' : D₂ ≌ D₃；w' : H₂.com
p E'.functor ≅ E.functor.comp H₃；eL : L₁.comp E.functor ≅ L₁₂；eR : R₁.comp E'.fu
nctor ≅ R₁₂；w.vComp' w'.hom eL eR。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.TwoSquare.GuitartExact.vComp_iff_of_equivalences`：vComp_i
ff_of_equivalences (eL : C₂ ≌ C₃) (eR : D₂ ≌ D₃) (w' : H₂ ⋙ eR.functor ≅ eL.func
tor ⋙ H₃) : (w ≫ᵥ w'.hom).GuitartExact ↔ w.GuitartExa…
· 使用定理 `CategoryTheory.TwoSquare.vComp'.eq_1`：∀ {C₁ : Type u_1} {C₂ : Type u_2} 
{C₃ : Type u_3} {D₁ : Type u_4} {D₂ : Type u_5} {D₃ : Type u_6}   [inst : Catego
ryTheory.Category.{v_1, u_…
· 使用引理 `CategoryTheory.TwoSquare.GuitartExact.whiskerVertical_iff`：whiskerVertic
al_iff (α : L ≅ L') (β : R ≅ R') : (w.whiskerVertical α.hom β.inv).GuitartExact 
↔ w.GuitartExact
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma vComp'_iff_of_equivalences (E : C₂ ≌ C₃) (E' : D₂ ≌ D₃)
    (w' : H₂ ⋙ E'.functor ≅ E.functor ⋙ H₃) {L₁₂ : C₁ ⥤ C₃}
    {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ E.functor ≅ L₁₂)
    (eR : R₁ ⋙ E'.functor ≅ R₁₂) :
    (w.vComp' w'.hom eL eR).GuitartExact ↔ w.GuitartExact := by
  rw [← vComp_iff_of_equivalences w E E' w', TwoSquare.vComp', whiskerVertical_iff]

end GuitartExact

end VerticalComposition

end TwoSquare

end CategoryTheory

