/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Mathlib.LinearAlgebra.Dimension.Finrank

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.GroupTheory.MonoidLocalization.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Affine monoids embed into `ℤⁿ`

This file proves that finitely generated cancellative torsion-free commutative monoids embed into
`ℤⁿ` for some `n`.
-/

public section

open Algebra AddLocalization Function

variable {M : Type*} [AddCancelCommMonoid M] [AddMonoid.FG M] [IsAddTorsionFree M]

namespace AffineAddMonoid

variable (M) in
/--
Definition of `dim` / `dim` 的定义

English:
abbreviation dim
  body: Module.finrank Int GrothendieckAddGroup M

中文:
缩写 dim
  定义体: Module.finrank Int GrothendieckAddGroup M

Depends on / 依赖: GrothendieckAddGroup, Module, Module.finrank, finrank
-/
noncomputable abbrev dim := Module.finrank Int GrothendieckAddGroup M

variable (M) in
/--
Definition of `embedding` / `embedding` 的定义

English:
definition embedding
  signature: : M ->+ FreeAbelianGroup (Fin (dim M))
  body: .comp (FreeAbelianGroup.equivFinsupp _).symm.toAddMonoidHom
    .comp (Module.finBasis Int _).repr.toAddMonoidHom
      (addMonoidOf ⊤).toAddMonoidHom

中文:
定义 embedding
  签名: : M ->+ 自由交换群 (有限集 (dim M))
  定义体: .comp (FreeAbelianGroup.equivFinsupp _).symm.toAddMonoidHom
    .comp (Module.finBasis Int _).repr.toAddMonoidHom
      (addMonoidOf ⊤).toAddMonoidHom

Depends on / 依赖: FreeAbelianGroup, FreeAbelianGroup.equivFinsupp, Module, Module.finBasis, addMonoidOf, equivFinsupp, finBasis, repr.toAddMonoidHom, symm.toAddMonoidHom, toAddMonoidHom
-/
noncomputable def embedding : M ->+ FreeAbelianGroup (Fin (dim M)) :=
.comp (FreeAbelianGroup.equivFinsupp _).symm.toAddMonoidHom
    .comp (Module.finBasis Int _).repr.toAddMonoidHom
      (addMonoidOf ⊤).toAddMonoidHom

/--
lemma `embedding_injective` / 引理 `embedding_injective`

English:
lemma embedding_injective
  statement: Injective (embedding M)
  proof: by
  simpa [embedding] using! mk_left_injective 0

中文:
引理 embedding_injective
  结论: 单射 (embedding M)
  证明: by
  simpa [embedding] using! mk_left_injective 0

Depends on / 依赖: embedding, mk_left_injective
-/
lemma embedding_injective : Injective (embedding M) := by
  simpa [embedding] using! mk_left_injective 0

end AffineAddMonoid
