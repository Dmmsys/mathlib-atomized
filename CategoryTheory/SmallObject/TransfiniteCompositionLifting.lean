/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous

/-!
# The left lifting property is stable under transfinite composition

In this file, we show that if `W : MorphismProperty C`, then
`W.llp.IsStableUnderTransfiniteCompositionOfShape J`, i.e.
the class of morphisms which have the left lifting property with
respect to `W` is stable under transfinite composition.

The main technical lemma is
`HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot`.
It corresponds to the particular case `W` contains only one morphism `p : X ⟶ Y`:
it shows that a transfinite composition of morphisms that have the left
lifting property with respect to `p` also has the left lifting property
with respect to `p`.

About the proof, given a colimit cocone `c` for a well-order-continuous
functor `F : J ⥤ C` from a well-ordered type `J`, we introduce a projective
system `sqFunctor c p f g : Jᵒᵖ ⥤ Type _` which associates to any `j : J`
the structure `SqStruct c p f g j` which consists of those morphisms `f'`
which makes the diagram below commute. The data of such compatible `f'` for
all `j` shall give the expected lifting `c.pt ⟶ X` for the outer square.

```
         f
F.obj ⊥ --> X
   |      Λ |
   |   f'╱  |
   v    ╱   |
F.obj j     | p
   |        |
   |        |
   v    g   v
  c.pt ---> Y
```
This is constructed by transfinite induction on `j`:
* When `j = ⊥`, this is `f`;
* In order to pass from `j` to `Order.succ j`, we use the assumption that
  `F.obj j ⟶ F.obj (Order.succ j)` has the left lifting property with respect to `p`;
* When `j` is a limit element, we use the "continuity" of `F`.

-/

@[expose] public section

universe t w v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C]

namespace HasLiftingProperty

variable {J : Type w} [LinearOrder J] [OrderBot J]

namespace transfiniteComposition

variable {F : J ⥤ C} (c : Cocone F) (hc : IsColimit c)
  {X Y : C} (p : X ⟶ Y) (f : F.obj ⊥ ⟶ X) (g : c.pt ⟶ Y)

/-- Given a cocone `c` for a functor `F : J ⥤ C` from a well-ordered type,
and maps `p : X ⟶ Y`, `f : F.obj ⊥ ⟶ X`, `g : c.pt ⟶ Y`, this structure
contains the data of a map `F.obj j ⟶ X` such that `F.map (homOfLE bot_le) ≫ f' = f`
and `f' ≫ p = c.ι.app j ≫ g`. (This implies that the outer square below
commutes, see `SqStruct.w`.)

```
         f
F.obj ⊥ --> X
   |      Λ |
   |   f'╱  |
   v    ╱   |
F.obj j     | p
   |        |
   |        |
   v    g   v
  c.pt ---> Y
```
-/
@[ext]
/-
**CategoryTheory.HasLiftingProperty.transfiniteComposition.SqStruct** 是 Mathlib 
中的一个结构，位于命名空间 `CategoryTheory.HasLiftingProperty.transfiniteComposition`。
形式化陈述：SqStruct (j : J) where /-- a morphism `F.obj j ⟶ X` -/ f' : F.obj j ⟶ X w₁
 : F.map (homOfLE bot_le) ≫ f' = f
参数：j : J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cocone `c` for a functor `F : J ⥤ C` from a well-ordered type,
and maps `p : X ⟶ Y`, `f : F.obj ⊥ ⟶ X`, `g : c.pt ⟶ Y`, this structure
contains the data of a map `F.obj j ⟶ X` such that `F.map (homOfLE bot_le) ≫ f' 
= f`
and `f' ≫ p = c.ι.app j ≫ g`. (This implies that the outer square below
commutes, see `SqStruct.w`.)

```
         f
F.obj ⊥ --> X
   |      Λ |
   |   f'╱  |
   v    ╱   |
F.obj j     | p
   |        |
   |        |
   v    g   v
  c.pt ---> Y
```
-/
structure SqStruct (j : J) where
  /-- a morphism `F.obj j ⟶ X` -/
  f' : F.obj j ⟶ X
  w₁ : F.map (homOfLE bot_le) ≫ f' = f := by cat_disch
  w₂ : f' ≫ p = c.ι.app j ≫ g := by cat_disch

namespace SqStruct

attribute [reassoc (attr := simp)] w₁ w₂

variable {c p f g} {j : J} (sq' : SqStruct c p f g j)

set_option backward.isDefEq.respectTransparency false in
include sq' in
@[reassoc]
/-
**CategoryTheory.HasLiftingProperty.transfiniteComposition.SqStruct.w** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.HasLiftingProperty.transfiniteComposition.SqStru
ct`。
形式化陈述：w : f ≫ p = c.ι.app ⊥ ≫ g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.HasLiftingProperty.transfiniteComposition.SqStruct.w₁`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : Li
nearOrder J] [inst_2 : OrderBot J]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.HasLiftingProperty.transfiniteComposition.SqStruct.w₂`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : Li
nearOrder J] [inst_2 : OrderBot J]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.Cocone.w_assoc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u
₃} C]   {F : CategoryTheor…
-/
lemma w : f ≫ p = c.ι.app ⊥ ≫ g := by
  rw [← sq'.w₁, assoc, sq'.w₂, Cocone.w_assoc]

set_option backward.defeqAttrib.useBackward true in
/--
Given `sq' : SqStruct c p f g j`, this is the commutative square
```
               sq'.f'
F.obj j --------------------> X
   |                          |
   |                          |p
   v                      g   v
F.obj (succ j) ---> c.pt ---> Y
```

(Using the lifting property for this square is the key ingredient
in the proof that the left lifting property with respect to `p`
is stable under transfinite composition.) -/
/-
**CategoryTheory.HasLiftingProperty.transfiniteComposition.SqStruct.sq** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.HasLiftingProperty.transfiniteComposition.SqStr
uct`。
形式化陈述：sq [SuccOrder J] : CommSq sq'.f' (F.map (homOfLE (Order.le_succ j))) p (c.
ι.app _ ≫ g) where w
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.HasLiftingProperty.transfiniteComposition.SqStruct.w₂`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : Li
nearOrder J] [inst_2 : OrderBot J]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given `sq' : SqStruct c p f g j`, this is the commutative square
```
               sq'.f'
F.obj j --------------------> X
   |                          |
   |                          |p
   v                      g   v
F.obj (succ j) ---> c.pt ---> Y
```

(Using the lifting property for this square is the key ingredient
in the proof that the left lifting property with respect to `p`
is stable under transfinite composition.)
-/
lemma sq [SuccOrder J] :
    CommSq sq'.f' (F.map (homOfLE (Order.le_succ j))) p (c.ι.app _ ≫ g) where
  w := by simp

set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `sqFunctor`. -/
@[simps]
/-
**CategoryTheory.HasLiftingProperty.transfiniteComposition.SqStruct.map** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.HasLiftingProperty.transfiniteComposition.SqSt
ruct`。
形式化陈述：map {j' : J} (α : j' ⟶ j) : SqStruct c p f g j' where f'
参数：α : j' ⟶ j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `sqFunctor`.
-/
def map {j' : J} (α : j' ⟶ j) : SqStruct c p f g j' where
  f' := F.map α ≫ sq'.f'
  w₁ := by
    rw [← F.map_comp_assoc]
    exact sq'.w₁

end SqStruct

/-- The projective system `j ↦ SqStruct c p f g j.unop`. -/
@[simps]
/-
**CategoryTheory.HasLiftingProperty.transfiniteComposition.sqFunctor** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.HasLiftingProperty.transfiniteComposition`。
形式化陈述：sqFunctor : Jᵒᵖ ⥤ Type _ where obj j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projective system `j ↦ SqStruct c p f g j.unop`.
-/
def sqFunctor : Jᵒᵖ ⥤ Type _ where
  obj j := SqStruct c p f g j.unop
  map α := ↾fun sq' ↦ sq'.map α.unop

variable [F.IsWellOrderContinuous]

namespace wellOrderInductionData

variable {p c f g} {j : J} (hj : Order.IsSuccLimit j)
  (s : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙ sqFunctor c p f g).sections)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `transfiniteComposition.wellOrderInductionData`. -/
/-
**CategoryTheory.HasLiftingProperty.transfiniteComposition.wellOrderInductionDat
a.liftHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.HasLiftingProperty.transfini
teComposition.wellOrderInductionData`。
形式化陈述：liftHom : F.obj j ⟶ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `transfiniteComposition.wellOrderInductionData`.
-/
noncomputable def liftHom : F.obj j ⟶ X :=
  (F.isColimitOfIsWellOrderContinuous j hj).desc
    (Cocone.mk _
      { app := fun i ↦ (s.1 ⟨i⟩).f'
        naturality i i' g := by
          have := congr_arg SqStruct.f' (s.2 g.op)
          dsimp at this ⊢
          rw [this, comp_id] })

@[reassoc]
/-
**CategoryTheory.HasLiftingProperty.transfiniteComposition.wellOrderInductionDat
a.liftHom_fac** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.HasLiftingProperty.trans
finiteComposition.wellOrderInductionData`。
形式化陈述：liftHom_fac (i : J) (hi : i < j) : F.map (homOfLE hi.le) ≫ liftHom hj s = 
(s.1 ⟨⟨i, hi⟩⟩).f'
参数：i : J；hi : i < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `PrincipalSeg.monotone`：monotone [PartialOrder α] (f : α <i β) : Monotone
 f
-/
lemma liftHom_fac (i : J) (hi : i < j) :
    F.map (homOfLE hi.le) ≫ liftHom hj s = (s.1 ⟨⟨i, hi⟩⟩).f' :=
  (F.isColimitOfIsWellOrderContinuous j hj).fac _ ⟨i, hi⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `transfiniteComposition.wellOrderInductionData`. -/
@[simps]
/-
**CategoryTheory.HasLiftingProperty.transfiniteComposition.wellOrderInductionDat
a.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.HasLiftingProperty.transfiniteC
omposition.wellOrderInductionData`。
形式化陈述：lift : (sqFunctor c p f g).obj (Opposite.op j) where f'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `transfiniteComposition.wellOrderInductionData`.
-/
noncomputable def lift : (sqFunctor c p f g).obj (Opposite.op j) where
  f' := liftHom hj s
  w₁ := by
    have h : ⊥ < j := Ne.bot_lt' (by
      rintro rfl
      exact Order.not_isSuccLimit_bot hj)
    rw [liftHom_fac hj s ⊥ h]
    simpa using (s.1 ⟨⊥, h⟩).w₁
  w₂ := (F.isColimitOfIsWellOrderContinuous j hj).hom_ext (fun ⟨i, hij⟩ ↦ by
    have := (s.1 ⟨i, hij⟩).w₂
    dsimp at this ⊢
    rw [liftHom_fac_assoc _ _ _ hij, this, Cocone.w_assoc])

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.HasLiftingProperty.transfiniteComposition.wellOrderInductionDat
a.map_lift** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.HasLiftingProperty.transfin
iteComposition.wellOrderInductionData`。
形式化陈述：map_lift {i : J} (hij : i < j) : (lift hj s).map (homOfLE hij.le) = s.1 ⟨⟨
i, hij⟩⟩
参数：hij : i < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `CategoryTheory.HasLiftingProperty.transfiniteComposition.SqStruct.ext`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {J : Type w} {inst_1 : L
inearOrder J} {inst_2 : OrderBot J}   {F : CategoryTheory.F…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `CategoryTheory.HasLiftingProperty.transfiniteComposition.wellOrderInduct
ionData.liftHom_fac`：liftHom_fac (i : J) (hi : i < j) : F.map (homOfLE hi.le) ≫ 
liftHom hj s = (s.1 ⟨⟨i, hi⟩⟩).f'
-/
lemma map_lift {i : J} (hij : i < j) :
    (lift hj s).map (homOfLE hij.le) = s.1 ⟨⟨i, hij⟩⟩ := by
  ext
  apply liftHom_fac

end wellOrderInductionData

variable {p} [SuccOrder J] [WellFoundedLT J]

section

variable (hF : ∀ (j : J) (_ : ¬IsMax j),
  HasLiftingPropertyFixedBot (F.map (homOfLE (Order.le_succ j))) p (c.ι.app _ ≫ g))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open wellOrderInductionData in
/-- The projective system `sqFunctor c p f g` has a `WellOrderInductionData` structure. -/
/-
**CategoryTheory.HasLiftingProperty.transfiniteComposition.wellOrderInductionDat
a** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.HasLiftingProperty.transfiniteCompos
ition`。
形式化陈述：wellOrderInductionData : (sqFunctor c p f g).WellOrderInductionData where 
succ j hj sq'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.HasLiftingProperty.transfiniteComposition.wellOrderInduct
ionData.map_lift`：map_lift {i : J} (hij : i < j) : (lift hj s).map (homOfLE hij.
le) = s.1 ⟨⟨i, hij⟩⟩

--- 原说明 ---
The projective system `sqFunctor c p f g` has a `WellOrderInductionData` structu
re.
-/
noncomputable def wellOrderInductionData :
    (sqFunctor c p f g).WellOrderInductionData where
  succ j hj sq' :=
    have := hF j hj sq'.f'
    have := hF j hj
    { f' := sq'.sq.lift
      w₁ := by
        dsimp
        simp only [← sq'.w₁]
        conv_rhs => rw [← sq'.sq.fac_left, ← F.map_comp_assoc]
        rfl }
  map_succ j hj sq' := by cat_disch
  lift j hj s := lift hj s
  map_lift j hj s i hij := map_lift hj s hij

include hF hc

variable {c f g} (sq : CommSq f (c.ι.app ⊥) p g)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.HasLiftingProperty.transfiniteComposition.hasLift** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.HasLiftingProperty.transfiniteComposition`。
形式化陈述：hasLift : sq.HasLift
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用引理 `CategoryTheory.Functor.WellOrderInductionData.surjective`：surjective : F
unction.Surjective ((fun s => s (op ⊥)) ∘ Subtype.val : F.sections -> F.obj (op 
⊥))
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.HasLiftingProperty.transfiniteComposition.SqStruct.w₂`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : Li
nearOrder J] [inst_2 : OrderBot J]   {F : CategoryTheory.F…
-/
lemma hasLift : sq.HasLift := by
  obtain ⟨s, hs⟩ := (wellOrderInductionData c f g hF).surjective { w₂ := sq.w, .. }
  replace hs := congr_arg SqStruct.f' hs
  dsimp at hs
  let t : Cocone F := Cocone.mk X
    { app j := (s.1 ⟨j⟩).f'
      naturality j j' g := by simpa using congr_arg SqStruct.f' (s.2 g.op) }
  let l := hc.desc t
  have hl (j : J) : c.ι.app j ≫ l = (s.1 ⟨j⟩).f' := hc.fac t j
  exact ⟨⟨{
    l := l
    fac_left := by rw [hl, hs]
    fac_right := hc.hom_ext (fun j ↦ by rw [reassoc_of% (hl j), SqStruct.w₂])}⟩⟩
/-
**CategoryTheory.HasLiftingProperty.transfiniteComposition.hasLiftingPropertyFix
edBot_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.HasLiftingProperty.transfiniteC
omposition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasLiftingPropertyFixedBot_ι_app_bot : HasLiftingPropertyFixedBot (c.ι.app ⊥) p g :=
  fun _ sq ↦ hasLift hc hF sq

end

variable {c} (hF : ∀ (j : J) (_ : ¬IsMax j),
  HasLiftingProperty (F.map (homOfLE (Order.le_succ j))) p)

include hc hF
/-
**CategoryTheory.HasLiftingProperty.transfiniteComposition.hasLiftingProperty_**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.HasLiftingProperty.transfiniteCompositi
on`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasLiftingProperty_ι_app_bot : HasLiftingProperty (c.ι.app ⊥) p where
  sq_hasLift sq := hasLift hc (fun j hj _ _ ↦ by have := hF j hj; infer_instance) sq

end transfiniteComposition

end HasLiftingProperty

namespace MorphismProperty

variable (W : MorphismProperty C)
  (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.isStableUnderTransfiniteCompositionOfShape_llp
** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：isStableUnderTransfiniteCompositionOfShape_llp : W.llp.IsStableUnderTransf
initeCompositionOfShape J
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.isStableUnderTransfiniteCompositionOfSha
pe_iff`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTh
eory.MorphismProperty C) (J : Type w)   [inst_1 : LinearOrder J] [in…
· 使用引理 `CategoryTheory.HasLiftingProperty.transfiniteComposition.hasLiftingPrope
rty_ι_app_bot`：hasLiftingProperty_ι_app_bot : HasLiftingProperty (c.ι.app ⊥) p w
here sq_hasLift sq
· 使用定理 `CategoryTheory.TransfiniteCompositionOfShape.isWellOrderContinuous`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : Line
arOrder J] [inst_2 : OrderBot J]   {X Y : C} {f : X ⟶ Y}…
· 使用定理 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.map_mem`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheory.Morp
hismProperty C} {J : Type w}   [inst_1 : LinearOrder J] [in…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsIsoOfIsStableUnderRetracts`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Mor
phismProperty C}   [P.IsStableUnderRetracts], P.RespectsIso
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.TransfiniteCompositionOfShape.fac`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : LinearOrder J] [inst_2
 : OrderBot J]   {X Y : C} {f : X ⟶ Y}…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isStableUnderTransfiniteCompositionOfShape_llp :
    W.llp.IsStableUnderTransfiniteCompositionOfShape J := by
  rw [isStableUnderTransfiniteCompositionOfShape_iff]
  rintro X Y f ⟨h⟩
  have : W.llp (h.incl.app ⊥) := fun _ _ p hp ↦
    HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot
      (hc := h.isColimit) (fun j hj ↦ h.map_mem j hj _ hp)
  exact (MorphismProperty.arrow_mk_iso_iff _
    (Arrow.isoMk h.isoBot.symm (Iso.refl _))).2 this
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsStableUnderTransfiniteComposition.{w} W.llp where
/-
**CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le_llp_rlp** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：transfiniteCompositionsOfShape_le_llp_rlp : W.transfiniteCompositionsOfSha
pe J <= W.rlp.llp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_monotone`
：transfiniteCompositionsOfShape_monotone : Monotone (transfiniteCompositionsOfSh
ape (C
· 使用引理 `CategoryTheory.MorphismProperty.le_llp_rlp`：le_llp_rlp : T <= T.rlp.llp
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.isStableUnderTransfiniteCompositionOfSha
pe_iff`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTh
eory.MorphismProperty C) (J : Type w)   [inst_1 : LinearOrder J] [in…
-/
lemma transfiniteCompositionsOfShape_le_llp_rlp :
    W.transfiniteCompositionsOfShape J ≤ W.rlp.llp := by
  have := W.rlp.isStableUnderTransfiniteCompositionOfShape_llp J
  rw [isStableUnderTransfiniteCompositionOfShape_iff] at this
  exact le_trans (transfiniteCompositionsOfShape_monotone J W.le_llp_rlp) this
/-
**CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_pushouts_coprod
ucts_le_llp_rlp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp : (coproduct
s.{t} W).pushouts.transfiniteCompositionsOfShape J <= W.rlp.llp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.MorphismProperty.rlp_pushouts`：rlp_pushouts : T.pushouts.
rlp = T.rlp
· 使用引理 `CategoryTheory.MorphismProperty.rlp_coproducts`：rlp_coproducts : (coprod
ucts.{w} T).rlp = T.rlp
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le_llp_rl
p`：transfiniteCompositionsOfShape_le_llp_rlp : W.transfiniteCompositionsOfShape 
J <= W.rlp.llp
-/
lemma transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp :
    (coproducts.{t} W).pushouts.transfiniteCompositionsOfShape J ≤ W.rlp.llp := by
  simpa using transfiniteCompositionsOfShape_le_llp_rlp (coproducts.{t} W).pushouts J
/-
**CategoryTheory.MorphismProperty.retracts_transfiniteCompositionsOfShape_pushou
ts_coproducts_le_llp_rlp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismPrope
rty`。
形式化陈述：retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp : (
(coproducts.{t} W).pushouts.transfiniteCompositionsOfShape J).retracts <= W.rlp.
llp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.le_llp_iff_le_rlp`：le_llp_iff_le_rlp (T'
 : MorphismProperty C) : T <= T'.llp ↔ T' <= T.rlp
· 使用引理 `CategoryTheory.MorphismProperty.rlp_retracts`：rlp_retracts : T.retracts.
rlp = T.rlp
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_pushouts_
coproducts_le_llp_rlp`：transfiniteCompositionsOfShape_pushouts_coproducts_le_llp
_rlp : (coproducts.{t} W).pushouts.transfiniteCompositionsOfShape J <= W.rlp.llp
-/
lemma retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp :
    ((coproducts.{t} W).pushouts.transfiniteCompositionsOfShape J).retracts ≤ W.rlp.llp := by
  rw [le_llp_iff_le_rlp, rlp_retracts, ← le_llp_iff_le_rlp]
  apply transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp
/-
**CategoryTheory.MorphismProperty.transfiniteCompositions_le_llp_rlp** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：transfiniteCompositions_le_llp_rlp : transfiniteCompositions.{w} W <= W.rl
p.llp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositions_iff`：transfinite
Compositions_iff {X Y : C} (f : X ⟶ Y) : transfiniteCompositions.{w} W f ↔ exist
s (J : Type w) (_ : LinearOrder J) (_ : SuccOrder…
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le_llp_rl
p`：transfiniteCompositionsOfShape_le_llp_rlp : W.transfiniteCompositionsOfShape 
J <= W.rlp.llp
-/
lemma transfiniteCompositions_le_llp_rlp :
    transfiniteCompositions.{w} W ≤ W.rlp.llp := by
  intro _ _ f hf
  rw [transfiniteCompositions_iff] at hf
  obtain ⟨_, _, _, _, _, hf⟩ := hf
  exact W.transfiniteCompositionsOfShape_le_llp_rlp _ _ hf
/-
**CategoryTheory.MorphismProperty.transfiniteCompositions_pushouts_coproducts_le
_llp_rlp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：transfiniteCompositions_pushouts_coproducts_le_llp_rlp : (transfiniteCompo
sitions.{w} (coproducts.{w} W).pushouts) <= W.rlp.llp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderTransfiniteCompositionL
lp`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory
.MorphismProperty C),   W.llp.IsStableUnderTransfiniteCompositio…
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderCoproductsLlp`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (T : CategoryTheory.MorphismPro
perty C),   CategoryTheory.MorphismProperty.IsStable…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.rlp_pushouts`：rlp_pushouts : T.pushouts.
rlp = T.rlp
· 使用引理 `CategoryTheory.MorphismProperty.rlp_coproducts`：rlp_coproducts : (coprod
ucts.{w} T).rlp = T.rlp
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositions_le_llp_rlp`：tran
sfiniteCompositions_le_llp_rlp : transfiniteCompositions.{w} W <= W.rlp.llp
-/
lemma transfiniteCompositions_pushouts_coproducts_le_llp_rlp :
    (transfiniteCompositions.{w} (coproducts.{w} W).pushouts) ≤ W.rlp.llp := by
  simpa using transfiniteCompositions_le_llp_rlp.{w} (coproducts.{w} W).pushouts
/-
**CategoryTheory.MorphismProperty.retracts_transfiniteComposition_pushouts_copro
ducts_le_llp_rlp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：retracts_transfiniteComposition_pushouts_coproducts_le_llp_rlp : (transfin
iteCompositions.{w} (coproducts.{w} W).pushouts).retracts <= W.rlp.llp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.le_llp_iff_le_rlp`：le_llp_iff_le_rlp (T'
 : MorphismProperty C) : T <= T'.llp ↔ T' <= T.rlp
· 使用引理 `CategoryTheory.MorphismProperty.rlp_retracts`：rlp_retracts : T.retracts.
rlp = T.rlp
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositions_pushouts_coprodu
cts_le_llp_rlp`：transfiniteCompositions_pushouts_coproducts_le_llp_rlp : (transf
initeCompositions.{w} (coproducts.{w} W).pushouts) <= W.rlp.llp
-/
lemma retracts_transfiniteComposition_pushouts_coproducts_le_llp_rlp :
    (transfiniteCompositions.{w} (coproducts.{w} W).pushouts).retracts ≤ W.rlp.llp := by
  rw [le_llp_iff_le_rlp, rlp_retracts, ← le_llp_iff_le_rlp]
  apply transfiniteCompositions_pushouts_coproducts_le_llp_rlp

end MorphismProperty

end CategoryTheory

