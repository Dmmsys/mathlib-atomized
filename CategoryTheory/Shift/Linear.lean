/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Localization.Linear

/-!
# Localization of the linearity of the shift functors

If `L : C ⥤ D` is a localization functor with respect to `W : MorphismProperty C`
and both `C` and `D` have been equipped with `R`-linear category structures
such that `L` is `R`-linear and the shift functors on `C` are `R`-linear,
then the shift functors on `D` are `R`-linear.

-/

public section

namespace CategoryTheory

namespace Shift

variable (R : Type*) [Ring R] {C : Type _} [Category* C] [Preadditive C] [Linear R C]
  {D : Type*} [Category* D] [Preadditive D] [Linear R D]
  {M : Type*} [AddMonoid M] [HasShift C M]
  [∀ (n : M), (shiftFunctor C n).Linear R]
  (L : C ⥤ D) (W : MorphismProperty C)

/-
**CategoryTheory.Shift.linear_of_localization** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Shift`。
形式化陈述：linear_of_localization [L.IsLocalization W] [L.Linear R] [HasShift D M] [L
.CommShift M] (n : M) : (shiftFunctor D n).Linear R
参数：n : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Localization.functor_linear_iff`：functor_linear_iff (F : 
C ⥤ E) (G : D ⥤ E) [Lifting L W F G] : F.Linear R ↔ G.Linear R
· 使用定理 `CategoryTheory.Functor.instLinearComp`：∀ {R : Type u_1} [inst : Semiring
 R] {C : Type u_2} {D : Type u_3} [inst_1 : CategoryTheory.Category.{v_1, u_2} C
]   [inst_2 : CategoryTheor…
-/
lemma linear_of_localization [L.IsLocalization W] [L.Linear R] [HasShift D M]
    [L.CommShift M] (n : M) : (shiftFunctor D n).Linear R := by
  have : Localization.Lifting L W (shiftFunctor C n ⋙ L) (shiftFunctor D n) :=
    ⟨(L.commShiftIso n).symm⟩
  rw [← Localization.functor_linear_iff L W R (shiftFunctor C n ⋙ L) (shiftFunctor D n)]
  infer_instance
/-
**CategoryTheory.Shift.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Shift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasShift W.Localization M] [W.Q.CommShift M] [Preadditive W.Localization]
    [Linear R W.Localization] [W.Q.Linear R] (n : M) :
    (shiftFunctor W.Localization n).Linear R := linear_of_localization _ W.Q W _
/-
**CategoryTheory.Shift.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Shift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : M) [W.HasLocalization] [HasShift W.Localization' M] [W.Q'.CommShift M]
    [Preadditive W.Localization'] [Linear R W.Localization'] [W.Q'.Linear R] :
    (shiftFunctor W.Localization' n).Linear R :=
  linear_of_localization _ W.Q' W _

end Shift

end CategoryTheory

