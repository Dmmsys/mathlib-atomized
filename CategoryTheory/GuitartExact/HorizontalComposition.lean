/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GuitartExact.Opposite

/-!
# Horizontal composition of Guitart exact squares

In this file, we show that the horizontal composition of Guitart exact squares
is Guitart exact.

-/

@[expose] public section

namespace CategoryTheory

open Category

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* D₁] [Category* D₂] [Category* D₃]

namespace TwoSquare

section WhiskerHorizontal

variable {T : C₁ ⥤ D₁} {L : C₁ ⥤ C₂} {R : D₁ ⥤ D₂} {B : C₂ ⥤ D₂} (w : TwoSquare T L R B)
  {T' : C₁ ⥤ D₁} {B' : C₂ ⥤ D₂}

/-- Given `w : TwoSquare T L R B`, one may obtain a 2-square `TwoSquare T' L R B'` if we
provide natural transformations `α : T ⟶ T'` and `β : B' ⟶ B`. -/
@[simps!]
/-
**CategoryTheory.TwoSquare.whiskerHorizontal** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.TwoSquare`。
形式化陈述：whiskerHorizontal (α : T' ⟶ T) (β : B ⟶ B') : TwoSquare T' L R B'
参数：α : T' ⟶ T；β : B ⟶ B'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `w : TwoSquare T L R B`, one may obtain a 2-square `TwoSquare T' L R B'` i
f we
provide natural transformations `α : T ⟶ T'` and `β : B' ⟶ B`.
-/
def whiskerHorizontal (α : T' ⟶ T) (β : B ⟶ B') :
    TwoSquare T' L R B' :=
  (w.whiskerTop α).whiskerBottom β

namespace GuitartExact

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A 2-square stays Guitart exact if we replace the top and bottom functors
by isomorphic functors. See also `whiskerHorizontal_iff`. -/
/-
**CategoryTheory.TwoSquare.GuitartExact.whiskerHorizontal** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.TwoSquare.GuitartExact`。
形式化陈述：whiskerHorizontal [w.GuitartExact] (α : T ≅ T') (β : B ≅ B') : (w.whiskerH
orizontal α.inv β.hom).GuitartExact
参数：α : T ≅ T'；β : B ≅ B'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.TwoSquare.guitartExact_iff_final`：guitartExact_iff_final 
: w.GuitartExact ↔ forall (X₃ : C₃), (w.costructuredArrowRightwards X₃).Final
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.TwoSquare.whiskerHorizontal_app`：∀ {C₁ : Type u_1} {C₂ : 
Type u_2} {D₁ : Type u_4} {D₂ : Type u_5} [inst : CategoryTheory.Category.{v_1, 
u_1} C₁]   [inst_1 : CategoryTheory.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.final_natIso_iff`：final_natIso_iff {F F' : C ⥤ D}
 (i : F ≅ F') : Final F ↔ Final F'
· 使用定理 `CategoryTheory.TwoSquare.instFinalCostructuredArrowObjCostructuredArrowR
ightwardsOfGuitartExact`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Ty
pe u₄} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.C
atego…
· 使用定理 `CategoryTheory.Functor.final_of_isRightAdjoint`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…

--- 原说明 ---
A 2-square stays Guitart exact if we replace the top and bottom functors
by isomorphic functors. See also `whiskerHorizontal_iff`.
-/
lemma whiskerHorizontal [w.GuitartExact] (α : T ≅ T') (β : B ≅ B') :
    (w.whiskerHorizontal α.inv β.hom).GuitartExact := by
  rw [guitartExact_iff_final]
  intro X₂
  let e : costructuredArrowRightwards (w.whiskerHorizontal α.inv β.hom) X₂ ≅
      w.costructuredArrowRightwards X₂ ⋙ (CostructuredArrow.mapIso (β.app X₂)).functor :=
    NatIso.ofComponents (fun f ↦ CostructuredArrow.isoMk (α.symm.app f.left))
  rw [Functor.final_natIso_iff e]
  infer_instance

/-- A 2-square is Guitart exact iff it is so after replacing the top and bottom functors by
isomorphic functors. -/
@[simp]
/-
**CategoryTheory.TwoSquare.GuitartExact.whiskerHorizontal_iff** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.TwoSquare.GuitartExact`。
形式化陈述：whiskerHorizontal_iff (α : T ≅ T') (β : B ≅ B') : (w.whiskerHorizontal α.i
nv β.hom).GuitartExact ↔ w.GuitartExact
参数：α : T ≅ T'；β : B ≅ B'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.TwoSquare.guitartExact_op_iff`：guitartExact_op_iff : w.op
.GuitartExact ↔ w.GuitartExact
· 使用引理 `CategoryTheory.TwoSquare.GuitartExact.whiskerVertical_iff`：whiskerVertic
al_iff (α : L ≅ L') (β : R ≅ R') : (w.whiskerVertical α.hom β.inv).GuitartExact 
↔ w.GuitartExact
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A 2-square is Guitart exact iff it is so after replacing the top and bottom func
tors by
isomorphic functors.
-/
lemma whiskerHorizontal_iff (α : T ≅ T') (β : B ≅ B') :
    (w.whiskerHorizontal α.inv β.hom).GuitartExact ↔ w.GuitartExact := by
  rw [← guitartExact_op_iff, ← w.guitartExact_op_iff,
    ← whiskerVertical_iff w.op (NatIso.op α.symm) (NatIso.op β.symm)]
  rfl
/-
**CategoryTheory.TwoSquare.GuitartExact.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.TwoSquare.GuitartExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [w.GuitartExact] (α : T' ⟶ T) (β : B ⟶ B')
    [IsIso α] [IsIso β] : (w.whiskerHorizontal α β).GuitartExact :=
  whiskerHorizontal w (asIso α).symm (asIso β)

end GuitartExact

end WhiskerHorizontal

section HorizontalComposition

variable {V₁ : C₁ ⥤ D₁} {T₁ : C₁ ⥤ C₂} {B₁ : D₁ ⥤ D₂} {V₂ : C₂ ⥤ D₂}
  (w : TwoSquare T₁ V₁ V₂ B₁)
  {T₂ : C₂ ⥤ C₃} {B₂ : D₂ ⥤ D₃} {V₃ : C₃ ⥤ D₃}
  (w' : TwoSquare T₂ V₂ V₃ B₂)

/-- The horizontal composition of 2-squares. (Variant where we allow the replacement of
the horizontal compositions by isomorphic functors.) -/
@[simps!]
/-
**CategoryTheory.TwoSquare.hComp'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.TwoS
quare`。
形式化陈述：hComp' {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ 
≅ B₁₂) : TwoSquare T₁₂ V₁ V₃ B₁₂
参数：eT : T₁ ⋙ T₂ ≅ T₁₂；eB : B₁ ⋙ B₂ ≅ B₁₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The horizontal composition of 2-squares. (Variant where we allow the replacement
 of
the horizontal compositions by isomorphic functors.)
-/
def hComp' {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ ≅ B₁₂) :
    TwoSquare T₁₂ V₁ V₃ B₁₂ :=
  (w ≫ₕ w').whiskerHorizontal eT.inv eB.hom

namespace GuitartExact

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.TwoSquare.GuitartExact.hComp** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.TwoSquare.GuitartExact`。
形式化陈述：hComp [w.GuitartExact] [w'.GuitartExact] : (w ≫ₕ w').GuitartExact
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.TwoSquare.guitartExact_op_iff`：guitartExact_op_iff : w.op
.GuitartExact ↔ w.GuitartExact
· 使用引理 `CategoryTheory.TwoSquare.ext`：ext (w w' : TwoSquare T L R B) (h : forall
 (X : C₁), w.natTrans.app X = w'.natTrans.app X) : w = w'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.TwoSquare.hComp_app`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ 
: Type u₃} {C₄ : Type u₄} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1
 : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.TwoSquare.vComp_app`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ 
: Type u₃} {C₄ : Type u₄} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1
 : CategoryTheory.Catego…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance hComp [w.GuitartExact] [w'.GuitartExact] :
    (w ≫ₕ w').GuitartExact := by
  rw [← guitartExact_op_iff]
  have : (w ≫ₕ w').op = w.op ≫ᵥ w'.op := by ext; simp
  rw [this]
  exact inferInstanceAs (w.op ≫ᵥ w'.op).GuitartExact
/-
**CategoryTheory.TwoSquare.GuitartExact.hComp'** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.TwoSquare.GuitartExact`。
形式化陈述：hComp' {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ 
≅ B₁₂) [w.GuitartExact] [w'.GuitartExact] : (w.hComp' w' eT eB).GuitartExact
参数：eT : T₁ ⋙ T₂ ≅ T₁₂；eB : B₁ ⋙ B₂ ≅ B₁₂。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.TwoSquare.GuitartExact.instWhiskerHorizontalOfIsIsoFuncto
r`：∀ {C₁ : Type u_1} {C₂ : Type u_2} {D₁ : Type u_4} {D₂ : Type u_5} [inst : Cat
egoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : CategoryTheory.…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance hComp' {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ ≅ B₁₂)
    [w.GuitartExact] [w'.GuitartExact] :
    (w.hComp' w' eT eB).GuitartExact := by
  dsimp only [TwoSquare.hComp']
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism between
`w.costructuredArrowRightwards Y₁ ⋙ w'.costructuredArrowRightwards (B₁.obj Y₁)` and
`(w ≫ₕ w').costructuredArrowRightwards Y₁`. -/
/-
**CategoryTheory.TwoSquare.GuitartExact.costructuredArrowRightwardsComp** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.TwoSquare.GuitartExact`。
形式化陈述：costructuredArrowRightwardsComp (Y₁ : D₁) : w.costructuredArrowRightwards 
Y₁ ⋙ w'.costructuredArrowRightwards (B₁.obj Y₁) ≅ (w ≫ₕ w').costructuredArrowRig
htwards Y₁
参数：Y₁ : D₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism between
`w.costructuredArrowRightwards Y₁ ⋙ w'.costructuredArrowRightwards (B₁.obj Y₁)` 
and
`(w ≫ₕ w').costructuredArrowRightwards Y₁`.
-/
def costructuredArrowRightwardsComp (Y₁ : D₁) :
    w.costructuredArrowRightwards Y₁ ⋙ w'.costructuredArrowRightwards (B₁.obj Y₁) ≅
      (w ≫ₕ w').costructuredArrowRightwards Y₁ :=
  NatIso.ofComponents (fun _ => CostructuredArrow.isoMk (Iso.refl _))
/-
**CategoryTheory.TwoSquare.GuitartExact.of_hComp** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.TwoSquare.GuitartExact`。
形式化陈述：of_hComp [B₁.EssSurj] [w.GuitartExact] [(w ≫ₕ w').GuitartExact] : w'.Guita
rtExact
参数：w ≫ₕ w'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.TwoSquare.guitartExact_iff_final`：guitartExact_iff_final 
: w.GuitartExact ↔ forall (X₃ : C₃), (w.costructuredArrowRightwards X₃).Final
· 使用引理 `CategoryTheory.TwoSquare.costructuredArrowRightwards_final_iff_of_iso`：c
ostructuredArrowRightwards_final_iff_of_iso {X₃ X₃' : C₃} (e : X₃ ≅ X₃') : (w.co
structuredArrowRightwards X₃).Final ↔ (w.costructuredArrowR…
· 使用定理 `CategoryTheory.Functor.final_of_natIso`：final_of_natIso {F F' : C ⥤ D} [
Final F] (i : F ≅ F') : Final F' where out _
· 使用定理 `CategoryTheory.TwoSquare.instFinalCostructuredArrowObjCostructuredArrowR
ightwardsOfGuitartExact`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Ty
pe u₄} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.C
atego…
· 使用定理 `CategoryTheory.Functor.final_of_final_comp`：final_of_final_comp [hF : Fi
nal F] [hFG : Final (F ⋙ G)] : Final G
-/
lemma of_hComp [B₁.EssSurj] [w.GuitartExact] [(w ≫ₕ w').GuitartExact] :
    w'.GuitartExact := by
  rw [guitartExact_iff_final]
  intro Y₂
  rw [costructuredArrowRightwards_final_iff_of_iso _ (B₁.objObjPreimageIso Y₂).symm]
  have : (w.costructuredArrowRightwards (B₁.objPreimage Y₂) ⋙
      w'.costructuredArrowRightwards (B₁.obj (B₁.objPreimage Y₂))).Final :=
    (Functor.final_of_natIso (costructuredArrowRightwardsComp w w' _).symm :)
  exact Functor.final_of_final_comp (w.costructuredArrowRightwards (B₁.objPreimage Y₂)) _
/-
**CategoryTheory.TwoSquare.GuitartExact.of_hComp'** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.TwoSquare.GuitartExact`。
形式化陈述：of_hComp' {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ 
B₂ ≅ B₁₂) [B₁.EssSurj] [w.GuitartExact] [h : (w.hComp' w' eT eB).GuitartExact] :
 w'.GuitartExact
参数：eT : T₁ ⋙ T₂ ≅ T₁₂；eB : B₁ ⋙ B₂ ≅ B₁₂；w.hComp' w' eT eB。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.TwoSquare.GuitartExact.of_hComp`：of_hComp [B₁.EssSurj] [w
.GuitartExact] [(w ≫ₕ w').GuitartExact] : w'.GuitartExact
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.TwoSquare.GuitartExact.whiskerHorizontal_iff`：whiskerHori
zontal_iff (α : T ≅ T') (β : B ≅ B') : (w.whiskerHorizontal α.inv β.hom).Guitart
Exact ↔ w.GuitartExact
-/
lemma of_hComp' {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ ≅ B₁₂)
    [B₁.EssSurj] [w.GuitartExact] [h : (w.hComp' w' eT eB).GuitartExact] :
    w'.GuitartExact := by
  dsimp [TwoSquare.hComp'] at h
  rw [whiskerHorizontal_iff] at h
  exact of_hComp w w'
/-
**CategoryTheory.TwoSquare.GuitartExact.hComp_iff_of_essSurj** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.TwoSquare.GuitartExact`。
形式化陈述：hComp_iff_of_essSurj [B₁.EssSurj] [w.GuitartExact] : (w ≫ₕ w').GuitartExac
t ↔ w'.GuitartExact
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.TwoSquare.GuitartExact.of_hComp`：of_hComp [B₁.EssSurj] [w
.GuitartExact] [(w ≫ₕ w').GuitartExact] : w'.GuitartExact
-/
lemma hComp_iff_of_essSurj [B₁.EssSurj] [w.GuitartExact] :
    (w ≫ₕ w').GuitartExact ↔ w'.GuitartExact :=
  ⟨fun _ ↦ of_hComp w w', fun _ ↦ inferInstance⟩
/-
**CategoryTheory.TwoSquare.GuitartExact.hComp'_iff_of_essSurj** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.TwoSquare.GuitartExact`。
形式化陈述：∀ {C₁ : Type u_1} {C₂ : Type u_2} {C₃ : Type u_3} {D₁ : Type u_4} {D₂ : Ty
pe u_5} {D₃ : Type u_6}   [inst : CategoryTheory.Category.{v_1, u_1} C₁] [inst_1
 : CategoryTheory.Category.{v_2, u_2} C₂]   [inst_2 : CategoryTheory.Category.{v
_3, u_3} C₃] [inst_3 : CategoryTheory.Category.{v_4, u_4} D₁]   [inst_4 : Catego
ryTheory.Category.{v_5, u_5} D₂] [inst_5 : CategoryTheory.Category.{v_6, u_6} D₃
]   {V₁ : CategoryTheory.Functor C₁ D₁} {T₁ : CategoryTheory.Functor C₁ C₂} {B₁ 
: CategoryTheory.Functor D₁ D₂}   {V₂ : CategoryTheory.Functor C₂ D₂} (w : Categ
oryTheory.TwoSquare T₁ V₁ V₂ B₁) {T₂ : CategoryTheory.Functor C₂ C₃}   {B₂ : Cat
egoryTheory.Functor D₂ D₃} {V₃ : CategoryTheory.Functor C₃ D₃} (w' : CategoryThe
ory.TwoSquare T₂ V₂ V₃ B₂)   {T₁₂ : CategoryTheory.Functor C₁ C₃} {B₁₂ : Categor
yTheory.Functor D₁ D₃} (eT : T₁.comp T₂ ≅ T₁₂)   (eB : B₁.comp B₂ ≅ B₁₂) [B₁.Ess
Surj] [w.GuitartExact], (w.hComp' w' eT eB).GuitartExact ↔ w'.GuitartExact
参数：w : CategoryTheory.TwoSquare T₁ V₁ V₂ B₁；w' : CategoryTheory.TwoSquare T₂ V₂ 
V₃ B₂；eT : T₁.comp T₂ ≅ T₁₂；eB : B₁.comp B₂ ≅ B₁₂；w.hComp' w' eT eB。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.TwoSquare.GuitartExact.of_hComp'`：of_hComp' {T₁₂ : C₁ ⥤ C
₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ ≅ B₁₂) [B₁.EssSurj] [w.Gui
tartExact] [h : (w.hComp' w' eT eB).G…
-/
lemma hComp'_iff_of_essSurj
    {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ ≅ B₁₂)
    [B₁.EssSurj] [w.GuitartExact] :
    (w.hComp' w' eT eB).GuitartExact ↔ w'.GuitartExact :=
  ⟨fun _ ↦ of_hComp' w w' eT eB, fun _ ↦ inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.TwoSquare.GuitartExact.hComp_iff_of_equivalences** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.TwoSquare.GuitartExact`。
形式化陈述：hComp_iff_of_equivalences (eT : C₂ ≌ C₃) (eB : D₂ ≌ D₃) (w' : eT.functor ⋙
 V₃ ≅ V₂ ⋙ eB.functor) : (w ≫ₕ w'.hom).GuitartExact ↔ w.GuitartExact
参数：eT : C₂ ≌ C₃；eB : D₂ ≌ D₃；w' : eT.functor ⋙ V₃ ≅ V₂ ⋙ eB.functor。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.TwoSquare.ext`：ext (w w' : TwoSquare T L R B) (h : forall
 (X : C₁), w.natTrans.app X = w'.natTrans.app X) : w = w'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.TwoSquare.hComp_app`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ 
: Type u₃} {C₄ : Type u₄} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1
 : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.TwoSquare.vComp_app`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ 
: Type u₃} {C₄ : Type u₄} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1
 : CategoryTheory.Catego…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.TwoSquare.guitartExact_op_iff`：guitartExact_op_iff : w.op
.GuitartExact ↔ w.GuitartExact
· 使用引理 `CategoryTheory.TwoSquare.GuitartExact.vComp_iff_of_equivalences`：vComp_i
ff_of_equivalences (eL : C₂ ≌ C₃) (eR : D₂ ≌ D₃) (w' : H₂ ⋙ eR.functor ≅ eL.func
tor ⋙ H₃) : (w ≫ᵥ w'.hom).GuitartExact ↔ w.GuitartExa…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hComp_iff_of_equivalences (eT : C₂ ≌ C₃) (eB : D₂ ≌ D₃)
    (w' : eT.functor ⋙ V₃ ≅ V₂ ⋙ eB.functor) :
    (w ≫ₕ w'.hom).GuitartExact ↔ w.GuitartExact := by
  let w'' : V₂.op ⋙ eB.op.functor ≅ eT.op.functor ⋙ V₃.op := NatIso.op w'
  have : (w ≫ₕ w'.hom).op = (w.op ≫ᵥ w''.hom) := by ext; simp [w'']
  rw [← guitartExact_op_iff, ← guitartExact_op_iff w,
    ← vComp_iff_of_equivalences _ _ _ w'', this]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.TwoSquare.GuitartExact.hComp'_iff_of_equivalences** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.TwoSquare.GuitartExact`。
形式化陈述：∀ {C₁ : Type u_1} {C₂ : Type u_2} {C₃ : Type u_3} {D₁ : Type u_4} {D₂ : Ty
pe u_5} {D₃ : Type u_6}   [inst : CategoryTheory.Category.{v_1, u_1} C₁] [inst_1
 : CategoryTheory.Category.{v_2, u_2} C₂]   [inst_2 : CategoryTheory.Category.{v
_3, u_3} C₃] [inst_3 : CategoryTheory.Category.{v_4, u_4} D₁]   [inst_4 : Catego
ryTheory.Category.{v_5, u_5} D₂] [inst_5 : CategoryTheory.Category.{v_6, u_6} D₃
]   {V₁ : CategoryTheory.Functor C₁ D₁} {T₁ : CategoryTheory.Functor C₁ C₂} {B₁ 
: CategoryTheory.Functor D₁ D₂}   {V₂ : CategoryTheory.Functor C₂ D₂} (w : Categ
oryTheory.TwoSquare T₁ V₁ V₂ B₁) {V₃ : CategoryTheory.Functor C₃ D₃}   (E : C₂ ≌
 C₃) (E' : D₂ ≌ D₃) (w' : E.functor.comp V₃ ≅ V₂.comp E'.functor) {T₁₂ : Categor
yTheory.Functor C₁ C₃}   {B₁₂ : CategoryTheory.Functor D₁ D₃} (eT : T₁.comp E.fu
nctor ≅ T₁₂) (eB : B₁.comp E'.functor ≅ B₁₂),   (w.hComp' w'.hom eT eB).GuitartE
xact ↔ w.GuitartExact
参数：w : CategoryTheory.TwoSquare T₁ V₁ V₂ B₁；E : C₂ ≌ C₃；E' : D₂ ≌ D₃；w' : E.func
tor.comp V₃ ≅ V₂.comp E'.functor；eT : T₁.comp E.functor ≅ T₁₂；eB : B₁.comp E'.fu
nctor ≅ B₁₂；w.hComp' w'.hom eT eB。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.TwoSquare.GuitartExact.hComp_iff_of_equivalences`：hComp_i
ff_of_equivalences (eT : C₂ ≌ C₃) (eB : D₂ ≌ D₃) (w' : eT.functor ⋙ V₃ ≅ V₂ ⋙ eB
.functor) : (w ≫ₕ w'.hom).GuitartExact ↔ w.GuitartExa…
· 使用定理 `CategoryTheory.TwoSquare.hComp'.eq_1`：∀ {C₁ : Type u_1} {C₂ : Type u_2} 
{C₃ : Type u_3} {D₁ : Type u_4} {D₂ : Type u_5} {D₃ : Type u_6}   [inst : Catego
ryTheory.Category.{v_1, u_…
· 使用引理 `CategoryTheory.TwoSquare.GuitartExact.whiskerHorizontal_iff`：whiskerHori
zontal_iff (α : T ≅ T') (β : B ≅ B') : (w.whiskerHorizontal α.inv β.hom).Guitart
Exact ↔ w.GuitartExact
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hComp'_iff_of_equivalences (E : C₂ ≌ C₃) (E' : D₂ ≌ D₃)
    (w' : E.functor ⋙ V₃ ≅ V₂ ⋙ E'.functor)
    {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ E.functor ≅ T₁₂)
    (eB : B₁ ⋙ E'.functor ≅ B₁₂) :
    (w.hComp' w'.hom eT eB).GuitartExact ↔ w.GuitartExact := by
  rw [← hComp_iff_of_equivalences w E E' w', TwoSquare.hComp', whiskerHorizontal_iff]

end GuitartExact

end HorizontalComposition

end TwoSquare

end CategoryTheory

