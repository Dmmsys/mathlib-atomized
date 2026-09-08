/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.SmallObject.Iteration.Basic
public import Mathlib.CategoryTheory.SmallObject.Iteration.ExtendToSucc
public import Mathlib.CategoryTheory.SmallObject.Iteration.FunctorOfCocone

/-!
# Existence of the iteration of a successor structure

Given `Φ : SuccStruct C`, we show by transfinite induction
that for any element `j` in a well-ordered set `J`,
the type `Φ.Iteration j` is nonempty.

-/

@[expose] public section

universe u

namespace CategoryTheory

namespace SmallObject

namespace SuccStruct

open Category Limits

variable {C : Type*} [Category* C] (Φ : SuccStruct C)
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasIterationOfShape J C]

namespace Iteration

variable (J) in
/-- The obvious term in `Φ.Iteration ε ⊥` that is given by `Φ.X₀`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.mkOfBot** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration`。
形式化陈述：mkOfBot : Φ.Iteration (⊥ : J) where F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious term in `Φ.Iteration ε ⊥` that is given by `Φ.X₀`.
-/
def mkOfBot : Φ.Iteration (⊥ : J) where
  F := (Functor.const _).obj Φ.X₀
  obj_bot := rfl
  arrowSucc_eq _ h := by simp at h
  arrowMap_limit _ h₁ h₂ := (h₁.not_isMin (by simpa using h₂)).elim

variable {Φ}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When `j : J` is not maximal, this is the extension in `Φ.Iteration (Order.succ j)`
of any `iter : Φ.Iteration j`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.mkOfSucc** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration`。
形式化陈述：mkOfSucc {j : J} (hj : ¬IsMax j) (iter : Φ.Iteration j) : Φ.Iteration (Ord
er.succ j) where F
参数：hj : ¬IsMax j；iter : Φ.Iteration j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `j : J` is not maximal, this is the extension in `Φ.Iteration (Order.succ j
)`
of any `iter : Φ.Iteration j`.
-/
noncomputable def mkOfSucc {j : J} (hj : ¬IsMax j) (iter : Φ.Iteration j) :
    Φ.Iteration (Order.succ j) where
  F := extendToSucc hj iter.F (Φ.toSucc _)
  obj_bot := by rw [extendToSucc_obj_eq _ _ _ _ bot_le, obj_bot]
  arrowSucc_eq i hi₁ := by
    rw [Order.lt_succ_iff_of_not_isMax hj] at hi₁
    obtain hi₁ | rfl := hi₁.lt_or_eq
    · rw [arrowSucc_def, arrowMap_extendToSucc _ _ _ _ _ _ (Order.succ_le_of_lt hi₁),
        ← arrowSucc_def _ _ hi₁, iter.arrowSucc_eq i hi₁,
        extendToSucc_obj_eq hj iter.F (Φ.toSucc _) i hi₁.le]
    · rw [arrowSucc_extendToSucc, toSuccArrow,
        extendToSucc_obj_eq hj iter.F (Φ.toSucc _) i]
  arrowMap_limit i hi hij k hk := by
    have hij' := (Order.IsSuccLimit.le_succ_iff hi).1 hij
    rw [arrowMap_extendToSucc _ _ _ _ _ _ hij', arrowMap_limit _ _ hi _ _ hk]
    congr 1
    apply Arrow.functor_ext
    rintro ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ f
    dsimp
    rw [← arrowMap, ← arrowMap, arrowMap_extendToSucc]
    rfl

namespace mkOfLimit


variable {j : J} (hj : Order.IsSuccLimit j) (iter : ∀ (i : J), i < j → Φ.Iteration i)

/-- Assuming `j : J` is a limit element and that we have `∀ (i : J), i < j → Φ.Iteration i`,
this is the inductive system `Set.Iio j ⥤ C` which sends `⟨i, _⟩` to
`(iter i _).F.obj ⟨i, _⟩`. -/
@[simps]
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.mkOfLimit.inductiveSystem** 是 
Mathlib 中的一个定义，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration.mkOfLimit
`。
形式化陈述：inductiveSystem : Set.Iio j ⥤ C where obj i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assuming `j : J` is a limit element and that we have `∀ (i : J), i < j → Φ.Itera
tion i`,
this is the inductive system `Set.Iio j ⥤ C` which sends `⟨i, _⟩` to
`(iter i _).F.obj ⟨i, _⟩`.
-/
noncomputable def inductiveSystem : Set.Iio j ⥤ C where
  obj i := (iter i.1 i.2).F.obj ⟨i.1, by simp⟩
  map {i₁ i₂} f := mapObj (iter i₁.1 i₁.2) (iter i₂.1 i₂.2) (leOfHom f)
    (by simp) (by simp) (leOfHom f)

/-- The extension of `inductiveSystem iter` to a functor `Set.Iic j ⥤ C` which
sends the top element to the colimit of `inductiveSystem iter`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.mkOfLimit.functor** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration.mkOfLimit`。
形式化陈述：functor : Set.Iic j ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension of `inductiveSystem iter` to a functor `Set.Iic j ⥤ C` which
sends the top element to the colimit of `inductiveSystem iter`.
-/
noncomputable def functor : Set.Iic j ⥤ C :=
  letI := hasColimitsOfShape_of_isSuccLimit C j hj
  ofCocone (colimit.cocone (inductiveSystem iter))
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.mkOfLimit.functor_obj** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration.mkOfLimit`。
形式化陈述：functor_obj (i : J) (hi : i < j) {k : J} (iter' : Φ.Iteration k) (hk : i <
= k) : (functor hj iter).obj ⟨i, hi.le⟩ = iter'.F.obj ⟨i, hk⟩
参数：i : J；hi : i < j；iter' : Φ.Iteration k；hk : i <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.ofCocone_obj_eq`：ofCocone_obj_eq (
i : J) (hi : i < j) : (ofCocone c).obj ⟨i, hi.le⟩ = F.obj ⟨i, hi⟩
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.Iteration.congr_obj`：congr_obj {j₁
 j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂) (k : J) (h₁ : k <= j₁
) (h₂ : k <= j₂) : iter₁.F.obj ⟨k, h₁⟩ = iter₂.…
-/
lemma functor_obj (i : J) (hi : i < j) {k : J} (iter' : Φ.Iteration k) (hk : i ≤ k) :
    (functor hj iter).obj ⟨i, hi.le⟩ = iter'.F.obj ⟨i, hk⟩ := by
  dsimp only [functor]
  rw [ofCocone_obj_eq _ _ hi]
  apply congr_obj
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.mkOfLimit.arrowMap_functor** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration.mkOfLimi
t`。
形式化陈述：arrowMap_functor (i₁ i₂ : J) (h₁₂ : i₁ <= i₂) (h₂ : i₂ < j) : arrowMap (fu
nctor hj iter) i₁ i₂ h₁₂ h₂.le = Arrow.mk (mapObj (iter i₁ (lt_of_le_of_lt h₁₂ h
₂)) (iter i₂ h₂) h₁₂ (by simp) (by simp) h₁₂)
参数：i₁ i₂ : J；h₁₂ : i₁ <= i₂；h₂ : i₂ < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.arrowMap_ofCocone`：arrowMap_ofCoco
ne (i₁ i₂ : J) (h₁₂ : i₁ <= i₂) (h₂ : i₂ < j) : arrowMap (ofCocone c) i₁ i₂ h₁₂ 
h₂.le = Arrow.mk (F.map (homOfLE h₁₂ : ⟨i₁, l…
-/
lemma arrowMap_functor (i₁ i₂ : J) (h₁₂ : i₁ ≤ i₂) (h₂ : i₂ < j) :
    arrowMap (functor hj iter) i₁ i₂ h₁₂ h₂.le =
      Arrow.mk (mapObj (iter i₁ (lt_of_le_of_lt h₁₂ h₂)) (iter i₂ h₂) h₁₂
        (by simp) (by simp) h₁₂) :=
  arrowMap_ofCocone _ _ _ _ h₂
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.mkOfLimit.arrowMap_functor_to_
top** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration.m
kOfLimit`。
形式化陈述：arrowMap_functor_to_top (i : J) (hi : i < j) : letI
参数：i : J；hi : i < j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.arrowMap_ofCocone_to_top`：arrowMap
_ofCocone_to_top (i : J) (hi : i < j) : arrowMap (ofCocone c) i j hi.le (by simp
) = Arrow.mk (c.ι.app ⟨i, hi⟩)
-/
lemma arrowMap_functor_to_top (i : J) (hi : i < j) :
    letI := hasColimitsOfShape_of_isSuccLimit C j hj
    arrowMap (functor hj iter) i j hi.le (by simp) =
      Arrow.mk (colimit.ι (inductiveSystem iter) ⟨i, hi⟩) :=
  arrowMap_ofCocone_to_top _ _ _

end mkOfLimit

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open mkOfLimit in
/-- When `j` is a limit element, this is the element in `Φ.Iteration j`
that is constructed from elements in `Φ.Iteration i` for all `i < j`. -/
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.mkOfLimit** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration`。
形式化陈述：mkOfLimit {j : J} (hj : Order.IsSuccLimit j) (iter : forall (i : J), i < j
 -> Φ.Iteration i) : Φ.Iteration j where F
参数：hj : Order.IsSuccLimit j；iter : forall (i : J), i < j -> Φ.Iteration i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `j` is a limit element, this is the element in `Φ.Iteration j`
that is constructed from elements in `Φ.Iteration i` for all `i < j`.
-/
noncomputable def mkOfLimit {j : J} (hj : Order.IsSuccLimit j)
    (iter : ∀ (i : J), i < j → Φ.Iteration i) :
    Φ.Iteration j where
  F := functor hj iter
  obj_bot := functor_obj hj iter ⊥ (Order.IsSuccLimit.bot_lt hj) (mkOfBot Φ J) (by rfl)
  arrowSucc_eq i hi := by
    rw [arrowSucc_def, arrowMap_functor _ _ _ _ (Order.le_succ i)
        ((Order.IsSuccLimit.succ_lt_iff hj).2 hi), arrow_mk_mapObj,
      ← arrowSucc_def _ _ ((Order.lt_succ_of_le_of_not_isMax (by rfl) (not_isMax_of_lt hi))),
      arrowSucc_eq, functor_obj _ _ _ hi]
  arrowMap_limit i hi hij k hk := by
    obtain hij | rfl := hij.lt_or_eq
    · rw [arrowMap_functor _ _ _ _ _ hij, arrow_mk_mapObj,
        arrowMap_limit _ _ hi _ _ hk]
      congr 1
      apply Arrow.functor_ext
      rintro ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩ f
      dsimp
      generalize_proofs
      rw [← arrowMap, ← arrowMap, arrowMap_functor hj iter l₁ l₂ _ (hl₂.trans hij),
        arrow_mk_mapObj]
      apply congr_arrowMap
    · rw [arrowMap_functor_to_top _ _ _ hk, ← arrowι_def _ hi]
      congr 1
      apply Arrow.functor_ext
      rintro ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩ f
      dsimp
      generalize_proofs
      rw [← arrowMap, arrow_mk_mapObj, arrowMap_functor _ _ _ _ _ hl₂, arrow_mk_mapObj]

variable (Φ)
/-
**CategoryTheory.SmallObject.SuccStruct.Iteration.nonempty** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.SmallObject.SuccStruct.Iteration`。
形式化陈述：nonempty (j : J) : Nonempty (Φ.Iteration j)
参数：j : J。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance nonempty (j : J) : Nonempty (Φ.Iteration j) := by
  induction j using SuccOrder.limitRecOn with
  | isMin i hi =>
      obtain rfl : i = ⊥ := by simpa using hi
      exact ⟨mkOfBot Φ J⟩
  | succ i hi hi' => exact ⟨mkOfSucc hi hi'.some⟩
  | isSuccLimit i hi hi' => exact ⟨mkOfLimit hi (fun a ha ↦ (hi' a ha).some)⟩

end Iteration

end SuccStruct

end SmallObject

end CategoryTheory

