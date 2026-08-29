/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.CategoryTheory.Monoidal.Widesubcategory

/-!
# Copy-discard structures on wide subcategories

Given a monoidal category `C`, a morphism property `P : MorphismProperty C` satisfying
`P.IsMonoidalStable` and a comonoid object `c : C`, we introduce a condition `P.
IsStableUnderComonoid c` saying that `c` inherits a comonoid object structure in the category of
`WideSubcategory P`. If `C` is a copy-discard category, if `P` is also stable under braiding and
that this condition `P. IsStableUnderComonoid` holds for all objects `c : C`, we show that
`WideSubcategory P` is also a copy-discard category.
-/

public section

namespace CategoryTheory.MorphismProperty

open scoped ComonObj

variable {C : Type*} [Category* C] (P : MorphismProperty C) [MonoidalCategory C]

/--
Definition of `IsStableUnderComonoid` / `IsStableUnderComonoid` 的定义

English:
class IsStableUnderComonoid
  parameters: (P : MorphismProperty C) (c : C) [ComonObj c]
  axioms and operations (2):
    - counit_mem((P)) : P ε[c]
    - comul_mem((P)) : P Δ[c]

中文:
类 IsStableUnderComonoid
  参数: (P : Morphism命题erty C) (c : C) [ComonObj c]
  公理与运算 (2 个):
    - counit_mem((P)) : P ε[c]
    - comul_mem((P)) : P Δ[c]
-/
class IsStableUnderComonoid (P : MorphismProperty C) (c : C) [ComonObj c] : Prop where
  counit_mem (P) : P ε[c]
  comul_mem (P) : P Δ[c]

export IsStableUnderComonoid (counit_mem comul_mem)

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsMonoidalStable]
  signature: (c : WideSubcategory P) [ComonObj c.obj]
  body: ⟨ε[c.obj], P.counit_mem⟩
  comul := ⟨Δ[c.obj], P.comul_mem⟩

中文:
实例 [P.IsMonoidalStable]
  签名: (c : WideSubcategory P) [ComonObj c.obj]
  定义体: ⟨ε[c.obj], P.counit_mem⟩
  comul := ⟨Δ[c.obj], P.comul_mem⟩

Depends on / 依赖: P.counit_mem, c.obj, counit_mem
-/
instance [P.IsMonoidalStable] (c : WideSubcategory P) [ComonObj c.obj]
    [P.IsStableUnderComonoid c.obj] : ComonObj c where
  counit := ⟨ε[c.obj], P.counit_mem⟩
  comul := ⟨Δ[c.obj], P.comul_mem⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [BraidedCategory
  signature: C] [P.IsStableUnderBraiding] (c
  body: by
    ext
    exact IsCommComonObj.comul_comm _

中文:
实例 [BraidedCategory
  签名: C] [P.IsStableUnderBraiding] (c
  定义体: by
    ext
    exact IsCommComonObj.comul_comm _

Depends on / 依赖: IsCommComonObj, IsCommComonObj.comul_comm, comul_comm
-/
instance [BraidedCategory C] [P.IsStableUnderBraiding] (c : WideSubcategory P) [ComonObj c.obj]
    [IsCommComonObj c.obj] [P.IsStableUnderComonoid c.obj] : IsCommComonObj c where
  comul_comm := by
    ext
    exact IsCommComonObj.comul_comm _

open CopyDiscardCategory in
attribute [local simp] copy_tensor discard_tensor copy_unit discard_unit in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CopyDiscardCategory
  signature: C] [P.IsStableUnderBraiding] [forall c, P.IsStableUnderComonoid c] :

中文:
实例 [CopyDiscardCategory
  签名: C] [P.IsStableUnderBraiding] [对任意 c, P.IsStableUnderComonoid c] :
-/
instance [CopyDiscardCategory C] [P.IsStableUnderBraiding] [forall c, P.IsStableUnderComonoid c] :
    CopyDiscardCategory (WideSubcategory P) where

end CategoryTheory.MorphismProperty
