/-
Copyright (c) 2026 Dénes Pápai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dénes Pápai
-/
module

public import Mathlib.CategoryTheory.Adhesive.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Adhesive structure on slice categories

The slice category `Over B` inherits the property of being adhesive from the
base category.

## TODO
- The dual result for `Under B`.
-/

public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

/--
Instance `adhesive_over` / 实例 `adhesive_over`

English:
instance adhesive_over
  signature: [Adhesive C] [HasPullbacks C] [HasPushouts C] (B : C)
  body: adhesive_of_preserves_and_reflects_isomorphism (Over.forget B)

中文:
实例 adhesive_over
  签名: [Adhesive C] [有Pullbacks C] [有Pushouts C] (B : C)
  定义体: adhesive_of_preserves_and_reflects_isomorphism (Over.forget B)

Depends on / 依赖: Over.forget, adhesive_of_preserves_and_reflects_isomorphism, forget
-/
instance adhesive_over [Adhesive C] [HasPullbacks C] [HasPushouts C] (B : C) :
    Adhesive (Over B) :=
  adhesive_of_preserves_and_reflects_isomorphism (Over.forget B)

end CategoryTheory
