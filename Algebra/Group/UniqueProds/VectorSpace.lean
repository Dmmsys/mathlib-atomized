/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.UniqueProds.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# A `ℚ`-vector space has `TwoUniqueSums`.
-/

public section

variable {G : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommGroup
  signature: G] [Module Rat G] : TwoUniqueSums G
  body: TwoUniqueSums.of_injective_addHom _ (Module.Basis.ofVectorSpace Rat G).repr.injective inferInstance

中文:
实例 [AddCommGroup
  签名: G] [Module Rat G] : TwoUniqueSums G
  定义体: TwoUniqueSums.of_injective_addHom _ (Module.Basis.ofVectorSpace Rat G).repr.injective inferInstance

Depends on / 依赖: Module, Module.Basis.ofVectorSpace, TwoUniqueSums, TwoUniqueSums.of_injective_addHom, injective, ofVectorSpace, of_injective_addHom, repr.injective
-/
instance [AddCommGroup G] [Module Rat G] : TwoUniqueSums G :=
  TwoUniqueSums.of_injective_addHom _ (Module.Basis.ofVectorSpace Rat G).repr.injective inferInstance
