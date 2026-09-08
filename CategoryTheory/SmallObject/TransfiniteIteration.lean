/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.SmallObject.Iteration.Nonempty
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous

/-!
# The transfinite iteration of a successor structure

Given a successor structure `Φ : SuccStruct C`
(see the file `Mathlib/CategoryTheory/SmallObject/Iteration/Basic.lean`)
and a well-ordered type `J`, we define the iteration `Φ.iteration J : C`. It is
defined as the colimit of a functor `Φ.iterationFunctor J : J ⥤ C`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory.SmallObject.SuccStruct

open Category Limits

variable {C : Type u} [Category.{v} C] (Φ : SuccStruct C)
  (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasIterationOfShape J C]

variable {J} in
/-- Given `Φ : SuccStruct C` and an element `j : J` in a well-ordered type,
this is the unique element in `Φ.Iteration j`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.iter** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.SmallObject.SuccStruct`。
形式化陈述：iter (j : J) : Φ.Iteration j
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `Φ : SuccStruct C` and an element `j : J` in a well-ordered type,
this is the unique element in `Φ.Iteration j`.
-/
noncomputable def iter (j : J) : Φ.Iteration j := Classical.arbitrary _

set_option backward.isDefEq.respectTransparency.types false in
/-- Given `Φ : SuccStruct C` and a well-ordered type `J`, this
is the functor `J ⥤ C` which gives the iterations of `Φ` indexed by `J`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.iterationFunctor** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：iterationFunctor : J ⥤ C where obj j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `Φ : SuccStruct C` and a well-ordered type `J`, this
is the functor `J ⥤ C` which gives the iterations of `Φ` indexed by `J`.
-/
noncomputable def iterationFunctor : J ⥤ C where
  obj j := (Φ.iter j).F.obj ⟨j, by simp⟩
  map f := Iteration.mapObj _ _ (leOfHom f) _ _ (leOfHom f)

/-- Given `Φ : SuccStruct C` and a well-ordered type `J`,
this is an object of `C` which is the iteration of `Φ` to the power `J`:
it is defined as the colimit of the functor `Φ.iterationFunctor J : J ⥤ C`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.iteration** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.SmallObject.SuccStruct`。
形式化陈述：iteration : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `Φ : SuccStruct C` and a well-ordered type `J`,
this is an object of `C` which is the iteration of `Φ` to the power `J`:
it is defined as the colimit of the functor `Φ.iterationFunctor J : J ⥤ C`.
-/
noncomputable def iteration : C := colimit (Φ.iterationFunctor J)

/-- The colimit cocone expressing that `Φ.iteration J` is the colimit
of `Φ.iterationFunctor J`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.iterationCocone** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：iterationCocone : Cocone (Φ.iterationFunctor J)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit cocone expressing that `Φ.iteration J` is the colimit
of `Φ.iterationFunctor J`.
-/
noncomputable def iterationCocone : Cocone (Φ.iterationFunctor J) :=
  colimit.cocone _

@[simp]
/-
**CategoryTheory.SmallObject.SuccStruct.iterationCocone_pt** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：iterationCocone_pt : (Φ.iterationCocone J).pt = Φ.iteration J
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iterationCocone_pt : (Φ.iterationCocone J).pt = Φ.iteration J := rfl

/-- `Φ.iteration J` identifies to the colimit of `Φ.iterationFunctor J`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.isColimitIterationCocone** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：isColimitIterationCocone : IsColimit (Φ.iterationCocone J)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Φ.iteration J` identifies to the colimit of `Φ.iterationFunctor J`.
-/
noncomputable def isColimitIterationCocone : IsColimit (Φ.iterationCocone J) :=
  colimit.isColimit _

variable {J}

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.SmallObject.SuccStruct.iterationFunctor_obj** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：iterationFunctor_obj (i : J) {j : J} (iter : Φ.Iteration j) (hi : i <= j) 
: (Φ.iterationFunctor J).obj i = iter.F.obj ⟨i, hi⟩
参数：i : J；iter : Φ.Iteration j；hi : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.Iteration.congr_obj`：congr_obj {j₁
 j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂) (k : J) (h₁ : k <= j₁
) (h₂ : k <= j₂) : iter₁.F.obj ⟨k, h₁⟩ = iter₂.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma iterationFunctor_obj (i : J) {j : J} (iter : Φ.Iteration j) (hi : i ≤ j) :
    (Φ.iterationFunctor J).obj i = iter.F.obj ⟨i, hi⟩ :=
  Iteration.congr_obj (Φ.iter i) iter i (by simp) hi

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.SmallObject.SuccStruct.arrowMk_iterationFunctor_map** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：arrowMk_iterationFunctor_map (i₁ i₂ : J) (h₁₂ : i₁ <= i₂) {j : J} (iter : 
Φ.Iteration j) (hj : i₂ <= j) : Arrow.mk ((Φ.iterationFunctor J).map (homOfLE h₁
₂)) = Arrow.mk (iter.F.map (homOfLE h₁₂ : ⟨i₁, h₁₂.trans hj⟩ ⟶ ⟨i₂, hj⟩))
参数：i₁ i₂ : J；h₁₂ : i₁ <= i₂；iter : Φ.Iteration j；hj : i₂ <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.Iteration.arrow_mk_mapObj`：arrow_m
k_mapObj {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂) {k₁ k₂ : 
J} (h₁₂ : k₁ <= k₂) (h₁ : k₁ <= j₁) (h₂ : k₂ <= j₂) (…
· 使用引理 `CategoryTheory.Arrow.ext`：ext {f g : Arrow T} (h₁ : f.left = g.left) (h₂
 : f.right = g.right) (h₃ : f.hom = eqToHom h₁ ≫ g.hom ≫ eqToHom h₂.symm) : f = 
g
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.Iteration.congr_obj`：congr_obj {j₁
 j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂) (k : J) (h₁ : k <= j₁
) (h₂ : k <= j₂) : iter₁.F.obj ⟨k, h₁⟩ = iter₂.…
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.Iteration.congr_map`：congr_map {j₁
 j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂) {k₁ k₂ : J} (h : k₁ <
= k₂) (h₁ : k₂ <= j₁) (h₂ : k₂ <= j₂) : iter₁.F…
-/
lemma arrowMk_iterationFunctor_map (i₁ i₂ : J) (h₁₂ : i₁ ≤ i₂)
    {j : J} (iter : Φ.Iteration j) (hj : i₂ ≤ j) :
    Arrow.mk ((Φ.iterationFunctor J).map (homOfLE h₁₂)) =
      Arrow.mk (iter.F.map (homOfLE h₁₂ : ⟨i₁, h₁₂.trans hj⟩ ⟶ ⟨i₂, hj⟩)) := by
  dsimp [iterationFunctor]
  rw [Iteration.arrow_mk_mapObj]
  exact Arrow.ext (Iteration.congr_obj _ _ _ _ _)
    (Iteration.congr_obj _ _ _ _ _) (Iteration.congr_map _ _ _ _ _)

variable (J)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.SmallObject.SuccStruct.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.SmallObject.SuccStruct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Φ.iterationFunctor J).IsWellOrderContinuous where
  nonempty_isColimit i hi := ⟨by
    let e : (Set.principalSegIio i).monotone.functor ⋙
      (Φ.iterationFunctor J) ≅ restrictionLT (Φ.iter i).F (by simp) :=
      NatIso.ofComponents (fun _ ↦ eqToIso (Φ.iterationFunctor_obj _ _ _)) (by
        rintro ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ f
        apply Arrow.mk_injective
        simpa using! Φ.arrowMk_iterationFunctor_map k₁ k₂ (leOfHom f) (Φ.iter i) h₂.le)
    refine (IsColimit.precomposeInvEquiv e _).1 ?_
    refine IsColimit.ofIsoColimit ((Φ.iter i).isColimit i hi (by simp)) ?_
    refine Cocone.ext (eqToIso (Φ.iterationFunctor_obj i (Φ.iter i) (by simp)).symm) ?_
    rintro ⟨k, hk⟩
    apply Arrow.mk_injective
    simp [Φ.arrowMk_iterationFunctor_map k i hk.le (Φ.iter i) (by simp), e]⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism `(Φ.iterationFunctor J).obj ⊥ ≅ Φ.X₀`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.iterationFunctorObjBotIso** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：iterationFunctorObjBotIso : (Φ.iterationFunctor J).obj ⊥ ≅ Φ.X₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `(Φ.iterationFunctor J).obj ⊥ ≅ Φ.X₀`.
-/
noncomputable def iterationFunctorObjBotIso : (Φ.iterationFunctor J).obj ⊥ ≅ Φ.X₀ :=
  eqToIso (Φ.iter ⊥).obj_bot

set_option backward.defeqAttrib.useBackward true in
/-- The natural map `Φ.X₀ ⟶ (Φ.iterationFunctor J).obj j`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.SmallObject.SuccStruct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map `Φ.X₀ ⟶ (Φ.iterationFunctor J).obj j`.
-/
noncomputable def ιIterationFunctor :
    (Functor.const _).obj Φ.X₀ ⟶ Φ.iterationFunctor J where
  app j := (Φ.iterationFunctorObjBotIso J).inv ≫
    (Φ.iterationFunctor J).map (homOfLE bot_le : ⊥ ⟶ j)
  naturality _ _ f := by
    dsimp
    rw [id_comp, assoc, ← Functor.map_comp]
    rfl

/-- The canonical map `Φ.X₀ ⟶ Φ.iteration J` which is the `J`th-transfinite composition
of maps `Φ.toSucc`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.SmallObject.SuccStruct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `Φ.X₀ ⟶ Φ.iteration J` which is the `J`th-transfinite composit
ion
of maps `Φ.toSucc`.
-/
noncomputable def ιIteration : Φ.X₀ ⟶ Φ.iteration J :=
  (Φ.iterationFunctorObjBotIso J).inv ≫ colimit.ι _ ⊥

/-- The inclusion `Φ.ιIteration J` is a transfinite composition of
shape `J` of morphisms in `Φ.prop`. -/
@[simps]
/-
**CategoryTheory.SmallObject.SuccStruct.transfiniteCompositionOfShape** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `Φ.ιIteration J` is a transfinite composition of
shape `J` of morphisms in `Φ.prop`.
-/
noncomputable def transfiniteCompositionOfShapeιIteration :
    Φ.prop.TransfiniteCompositionOfShape J (Φ.ιIteration J) where
  isoBot := Φ.iterationFunctorObjBotIso J
  map_mem j hj := by
    have := (Φ.iter (Order.succ j)).prop_map_succ j (Order.lt_succ_of_not_isMax hj)
    rw [prop_iff] at this ⊢
    simp only [Φ.iterationFunctor_obj j (Φ.iter (Order.succ j)) (Order.le_succ j),
      Φ.arrowMk_iterationFunctor_map _ _ (Order.le_succ j) (Φ.iter (Order.succ j)) (by simp),
      this]
  F := Φ.iterationFunctor J
  incl := (Φ.iterationCocone J).ι
  isColimit := Φ.isColimitIterationCocone J

variable {J}
/-
**CategoryTheory.SmallObject.SuccStruct.prop_iterationFunctor_map_succ** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：prop_iterationFunctor_map_succ (j : J) (hj : ¬ IsMax j) : Φ.prop ((Φ.itera
tionFunctor J).map (homOfLE (Order.le_succ j)))
参数：j : J；hj : ¬ IsMax j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.map_mem`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheory.Morp
hismProperty C} {J : Type w}   [inst_1 : LinearOrder J] [in…
-/
lemma prop_iterationFunctor_map_succ (j : J) (hj : ¬ IsMax j) :
    Φ.prop ((Φ.iterationFunctor J).map (homOfLE (Order.le_succ j))) :=
  (Φ.transfiniteCompositionOfShapeιIteration J).map_mem j hj

/-- When `j` is not a maximal element, then
`(Φ.iterationFunctor J).obj (Order.succ j)` is isomorphic to
`Φ.succ ((Φ.iterationFunctor J).obj j)`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.iterationFunctorObjSuccIso** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：iterationFunctorObjSuccIso (j : J) (hj : ¬ IsMax j) : (Φ.iterationFunctor 
J).obj (Order.succ j) ≅ Φ.succ ((Φ.iterationFunctor J).obj j)
参数：j : J；hj : ¬ IsMax j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `j` is not a maximal element, then
`(Φ.iterationFunctor J).obj (Order.succ j)` is isomorphic to
`Φ.succ ((Φ.iterationFunctor J).obj j)`.
-/
noncomputable def iterationFunctorObjSuccIso (j : J) (hj : ¬ IsMax j) :
    (Φ.iterationFunctor J).obj (Order.succ j) ≅
      Φ.succ ((Φ.iterationFunctor J).obj j) :=
  eqToIso ((Φ.prop_iterationFunctor_map_succ j hj).succ_eq.symm)

@[reassoc]
/-
**CategoryTheory.SmallObject.SuccStruct.iterationFunctor_map_succ** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct`。
形式化陈述：iterationFunctor_map_succ (j : J) (hj : ¬ IsMax j) : (Φ.iterationFunctor J
).map (homOfLE (Order.le_succ j)) = Φ.toSucc _ ≫ (Φ.iterationFunctorObjSuccIso j
 hj).inv
参数：j : J；hj : ¬ IsMax j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SmallObject.SuccStruct.prop.fac`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {Φ : CategoryTheory.SmallObject.SuccStruct C} {
X Y : C}   {f : X ⟶ Y} (hf : Φ.prop …
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.prop_iterationFunctor_map_succ`：pr
op_iterationFunctor_map_succ (j : J) (hj : ¬ IsMax j) : Φ.prop ((Φ.iterationFunc
tor J).map (homOfLE (Order.le_succ j)))
-/
lemma iterationFunctor_map_succ (j : J) (hj : ¬ IsMax j) :
    (Φ.iterationFunctor J).map (homOfLE (Order.le_succ j)) =
      Φ.toSucc _ ≫ (Φ.iterationFunctorObjSuccIso j hj).inv :=
  (Φ.prop_iterationFunctor_map_succ j hj).fac

end CategoryTheory.SmallObject.SuccStruct

