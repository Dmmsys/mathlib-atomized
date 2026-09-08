/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Miscellany about preservation of (co)limits in monoidal categories

This file records some `PreservesColimits` instances on tensor products in monoidal categories. -/

public section

namespace CategoryTheory.MonoidalCategory.Limits
open _root_.CategoryTheory.Limits

variable {C : Type*} [Category* C] [MonoidalCategory C]
  {J : Type*} [Category* J] (F : J ⥤ C)

section Colimits

/-- When `C` is braided and `tensorLeft c` preserves a colimit, then so does `tensorRight k`. -/
/-
**CategoryTheory.MonoidalCategory.Limits.preservesColimit_of_braided_and_preserv
esColimit_tensor_left** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonoidalCategory
.Limits`。
形式化陈述：preservesColimit_of_braided_and_preservesColimit_tensor_left [BraidedCateg
ory C] (c : C) [PreservesColimit F (tensorLeft c)] : PreservesColimit F (tensorR
ight c)
参数：c : C；tensorLeft c。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_natIso`：preservesColimit_of_na
tIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesColimit K F] : PreservesCol
imit K G where preserves t

--- 原说明 ---
When `C` is braided and `tensorLeft c` preserves a colimit, then so does `tensor
Right k`.
-/
instance preservesColimit_of_braided_and_preservesColimit_tensor_left
    [BraidedCategory C] (c : C)
    [PreservesColimit F (tensorLeft c)] :
    PreservesColimit F (tensorRight c) :=
  preservesColimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c)

/-- When `C` is braided and `tensorRight c` preserves a colimit, then so does `tensorLeft k`.
We are not making this an instance to avoid an instance loop with
`preservesColimit_of_braided_and_preservesColimit_tensor_left`. -/
/-
**CategoryTheory.MonoidalCategory.Limits.preservesColimit_of_braided_and_preserv
esColimit_tensor_right** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategor
y.Limits`。
形式化陈述：preservesColimit_of_braided_and_preservesColimit_tensor_right [BraidedCate
gory C] (c : C) [PreservesColimit F (tensorRight c)] : PreservesColimit F (tenso
rLeft c)
参数：c : C；tensorRight c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_natIso`：preservesColimit_of_na
tIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesColimit K F] : PreservesCol
imit K G where preserves t

--- 原说明 ---
When `C` is braided and `tensorRight c` preserves a colimit, then so does `tenso
rLeft k`.
We are not making this an instance to avoid an instance loop with
`preservesColimit_of_braided_and_preservesColimit_tensor_left`.
-/
lemma preservesColimit_of_braided_and_preservesColimit_tensor_right
    [BraidedCategory C] (c : C)
    [PreservesColimit F (tensorRight c)] :
    PreservesColimit F (tensorLeft c) :=
  preservesColimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c).symm
/-
**CategoryTheory.MonoidalCategory.Limits.preservesCoLimit_curriedTensor** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.Limits`。
形式化陈述：preservesCoLimit_curriedTensor [h : forall c : C, PreservesColimit F (tens
orRight c)] : PreservesColimit F (curriedTensor C)
参数：tensorRight c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_evaluation`：preservesColimit_o
f_evaluation (F : D ⥤ K ⥤ C) (G : J ⥤ D) (H : forall k, PreservesColimit G (F ⋙ 
(evaluation K C).obj k)) : PreservesColimi…
-/
lemma preservesCoLimit_curriedTensor [h : ∀ c : C, PreservesColimit F (tensorRight c)] :
    PreservesColimit F (curriedTensor C) :=
  preservesColimit_of_evaluation _ _
    (fun c ↦ inferInstanceAs (PreservesColimit F (tensorRight c)))

end Colimits

section Limits

/-- When `C` is braided and `tensorLeft c` preserves a limit, then so does `tensorRight k`. -/
/-
**CategoryTheory.MonoidalCategory.Limits.preservesLimit_of_braided_and_preserves
Limit_tensor_left** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonoidalCategory.Lim
its`。
形式化陈述：preservesLimit_of_braided_and_preservesLimit_tensor_left [BraidedCategory 
C] (c : C) [PreservesLimit F (tensorLeft c)] : PreservesLimit F (tensorRight c)
参数：c : C；tensorLeft c。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_natIso`：preservesLimit_of_natIso
 (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesLimit K F] : PreservesLimit K G
 where preserves t

--- 原说明 ---
When `C` is braided and `tensorLeft c` preserves a limit, then so does `tensorRi
ght k`.
-/
instance preservesLimit_of_braided_and_preservesLimit_tensor_left
    [BraidedCategory C] (c : C)
    [PreservesLimit F (tensorLeft c)] :
    PreservesLimit F (tensorRight c) :=
  preservesLimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c)

/-- When `C` is braided and `tensorRight c` preserves a limit, then so does `tensorLeft k`.
We are not making this an instance to avoid an instance loop with
`preservesLimit_of_braided_and_preservesLimit_tensor_left`. -/
/-
**CategoryTheory.MonoidalCategory.Limits.preservesLimit_of_braided_and_preserves
Limit_tensor_right** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.Li
mits`。
形式化陈述：preservesLimit_of_braided_and_preservesLimit_tensor_right [BraidedCategory
 C] (c : C) [PreservesLimit F (tensorRight c)] : PreservesLimit F (tensorLeft c)
参数：c : C；tensorRight c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_natIso`：preservesLimit_of_natIso
 (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesLimit K F] : PreservesLimit K G
 where preserves t

--- 原说明 ---
When `C` is braided and `tensorRight c` preserves a limit, then so does `tensorL
eft k`.
We are not making this an instance to avoid an instance loop with
`preservesLimit_of_braided_and_preservesLimit_tensor_left`.
-/
lemma preservesLimit_of_braided_and_preservesLimit_tensor_right
    [BraidedCategory C] (c : C)
    [PreservesLimit F (tensorRight c)] :
    PreservesLimit F (tensorLeft c) :=
  preservesLimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c).symm
/-
**CategoryTheory.MonoidalCategory.Limits.preservesLimit_curriedTensor** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.Limits`。
形式化陈述：preservesLimit_curriedTensor [h : forall c : C, PreservesLimit F (tensorRi
ght c)] : PreservesLimit F (curriedTensor C)
参数：tensorRight c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_evaluation`：preservesLimit_of_ev
aluation (F : D ⥤ K ⥤ C) (G : J ⥤ D) (H : forall k : K, PreservesLimit G (F ⋙ (e
valuation K C).obj k : D ⥤ C)) : Preserv…
-/
lemma preservesLimit_curriedTensor [h : ∀ c : C, PreservesLimit F (tensorRight c)] :
    PreservesLimit F (curriedTensor C) :=
  preservesLimit_of_evaluation _ _ <| fun c ↦ inferInstanceAs (PreservesLimit F (tensorRight c))

end Limits

end CategoryTheory.MonoidalCategory.Limits

