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

/--
Instance `preservesColimit_of_braided_and_preservesColimit_tensor_left` / 实例 `preservesColimit_of_braided_and_preservesColimit_tensor_left`

English:
instance preservesColimit_of_braided_and_preservesColimit_tensor_left
  body: preservesColimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c)

中文:
实例 preservesColimit_of_braided_and_preservesColimit_tensor_left
  定义体: preservesColimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c)

Depends on / 依赖: BraidedCategory, BraidedCategory.tensorLeftIsoTensorRight, preservesColimit_of_natIso, tensorLeftIsoTensorRight
-/
instance preservesColimit_of_braided_and_preservesColimit_tensor_left
    [BraidedCategory C] (c : C)
    [PreservesColimit F (tensorLeft c)] :
    PreservesColimit F (tensorRight c) :=
  preservesColimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c)

/--
lemma `preservesColimit_of_braided_and_preservesColimit_tensor_right` / 引理 `preservesColimit_of_braided_and_preservesColimit_tensor_right`

English:
lemma preservesColimit_of_braided_and_preservesColimit_tensor_right
  proof: preservesColimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c).symm

中文:
引理 preservesColimit_of_braided_and_preservesColimit_tensor_right
  证明: preservesColimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c).symm

Depends on / 依赖: BraidedCategory, BraidedCategory.tensorLeftIsoTensorRight, preservesColimit_of_natIso, tensorLeftIsoTensorRight
-/
lemma preservesColimit_of_braided_and_preservesColimit_tensor_right
    [BraidedCategory C] (c : C)
    [PreservesColimit F (tensorRight c)] :
    PreservesColimit F (tensorLeft c) :=
  preservesColimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c).symm

/--
lemma `preservesCoLimit_curriedTensor` / 引理 `preservesCoLimit_curriedTensor`

English:
lemma preservesCoLimit_curriedTensor
  given: [h : forall c : C, PreservesColimit F (tensorRight c)]
  proof: preservesColimit_of_evaluation _ _
    (fun c => inferInstanceAs (PreservesColimit F (tensorRight c)))

中文:
引理 preservesCoLimit_curriedTensor
  条件: [h : 对任意 c : C, PreservesColimit F (tensorRight c)]
  证明: preservesColimit_of_evaluation _ _
    (fun c => inferInstanceAs (PreservesColimit F (tensorRight c)))

Depends on / 依赖: PreservesColimit, preservesColimit_of_evaluation, tensorRight
-/
lemma preservesCoLimit_curriedTensor [h : forall c : C, PreservesColimit F (tensorRight c)] :
    PreservesColimit F (curriedTensor C) :=
  preservesColimit_of_evaluation _ _
    (fun c => inferInstanceAs (PreservesColimit F (tensorRight c)))

end Colimits

section Limits

/--
Instance `preservesLimit_of_braided_and_preservesLimit_tensor_left` / 实例 `preservesLimit_of_braided_and_preservesLimit_tensor_left`

English:
instance preservesLimit_of_braided_and_preservesLimit_tensor_left
  body: preservesLimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c)

中文:
实例 preservesLimit_of_braided_and_preservesLimit_tensor_left
  定义体: preservesLimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c)

Depends on / 依赖: BraidedCategory, BraidedCategory.tensorLeftIsoTensorRight, preservesLimit_of_natIso, tensorLeftIsoTensorRight
-/
instance preservesLimit_of_braided_and_preservesLimit_tensor_left
    [BraidedCategory C] (c : C)
    [PreservesLimit F (tensorLeft c)] :
    PreservesLimit F (tensorRight c) :=
  preservesLimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c)

/--
lemma `preservesLimit_of_braided_and_preservesLimit_tensor_right` / 引理 `preservesLimit_of_braided_and_preservesLimit_tensor_right`

English:
lemma preservesLimit_of_braided_and_preservesLimit_tensor_right
  proof: preservesLimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c).symm

中文:
引理 preservesLimit_of_braided_and_preservesLimit_tensor_right
  证明: preservesLimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c).symm

Depends on / 依赖: BraidedCategory, BraidedCategory.tensorLeftIsoTensorRight, preservesLimit_of_natIso, tensorLeftIsoTensorRight
-/
lemma preservesLimit_of_braided_and_preservesLimit_tensor_right
    [BraidedCategory C] (c : C)
    [PreservesLimit F (tensorRight c)] :
    PreservesLimit F (tensorLeft c) :=
  preservesLimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c).symm

/--
lemma `preservesLimit_curriedTensor` / 引理 `preservesLimit_curriedTensor`

English:
lemma preservesLimit_curriedTensor
  given: [h : forall c : C, PreservesLimit F (tensorRight c)]
  proof: preservesLimit_of_evaluation _ _ fun c => inferInstanceAs (PreservesLimit F (tensorRight c))

中文:
引理 preservesLimit_curriedTensor
  条件: [h : 对任意 c : C, PreservesLimit F (tensorRight c)]
  证明: preservesLimit_of_evaluation _ _ fun c => inferInstanceAs (PreservesLimit F (tensorRight c))

Depends on / 依赖: PreservesLimit, preservesLimit_of_evaluation, tensorRight
-/
lemma preservesLimit_curriedTensor [h : forall c : C, PreservesLimit F (tensorRight c)] :
    PreservesLimit F (curriedTensor C) :=
preservesLimit_of_evaluation _ _ fun c => inferInstanceAs (PreservesLimit F (tensorRight c))

end Limits

end CategoryTheory.MonoidalCategory.Limits
