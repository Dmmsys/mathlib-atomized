/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# `LiesOver` instances for completions of number fields

If `L` and `K` are number fields such that `Algebra K L` then this algebra extends
naturally to the completions of `K` and `L` at places, whenever the place of `L` lies
over the place of `K`. This file contains the relevant instances and properties of this extension
as `scoped` instances. These are scoped because they create non-defeq instance diamonds when
`K = L`.
-/

public section

namespace NumberField.LiesOver

open InfinitePlace InfinitePlace.Completion

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K} {w : InfinitePlace L}
variable [w.LiesOver v]

/--
Definition of `completionMap` / `completionMap` 的定义

English:
definition completionMap
  signature: : v.Completion ->+* w.Completion
  body: ((Completion.equiv w).symm.toRingHom.comp
    (LiesOver.isometry_algebraMap w v).mapRingHom).comp (Completion.equiv v).toRingHom

中文:
定义 completionMap
  签名: : v.完备化 ->+* w.完备化
  定义体: ((Completion.equiv w).symm.toRingHom.comp
    (LiesOver.isometry_algebraMap w v).mapRingHom).comp (Completion.equiv v).toRingHom

Depends on / 依赖: Completion, Completion.equiv, LiesOver, LiesOver.isometry_algebraMap, isometry_algebraMap, mapRingHom, symm.toRingHom.comp, toRingHom
-/
noncomputable def completionMap : v.Completion ->+* w.Completion :=
  ((Completion.equiv w).symm.toRingHom.comp
    (LiesOver.isometry_algebraMap w v).mapRingHom).comp (Completion.equiv v).toRingHom

/--
theorem `continuous_completionMap` / 定理 `continuous_completionMap`

English:
theorem continuous_completionMap
  statement: Continuous (completionMap (v := v) (w := w))
  proof: (continuous_ofCompletion w).comp
    UniformSpace.Completion.continuous_map.comp (continuous_toCompletion v)

中文:
定理 continuous_completionMap
  结论: 连续 (completionMap (v := v) (w := w))
  证明: (continuous_ofCompletion w).comp
    UniformSpace.Completion.continuous_map.comp (continuous_toCompletion v)
-/
theorem continuous_completionMap : Continuous (completionMap (v := v) (w := w)) :=
(continuous_ofCompletion w).comp
    UniformSpace.Completion.continuous_map.comp (continuous_toCompletion v)

/--
theorem `completionMap_coe` / 定理 `completionMap_coe`

English:
theorem completionMap_coe
  given: (x : WithAbs v.1)
  proof: Completion.ext (LiesOver.isometry_algebraMap w v).mapRingHom_coe x

中文:
定理 completionMap_coe
  条件: (x : WithAbs v.1)
  证明: Completion.ext (LiesOver.isometry_algebraMap w v).mapRingHom_coe x

Depends on / 依赖: Completion, Completion.ext, LiesOver, LiesOver.isometry_algebraMap, isometry_algebraMap, mapRingHom_coe
-/
theorem completionMap_coe (x : WithAbs v.1) :
    completionMap (x : v.Completion) = ((algebraMap (WithAbs v.1) (WithAbs w.1) x : WithAbs w.1) :
      w.Completion) :=
Completion.ext (LiesOver.isometry_algebraMap w v).mapRingHom_coe x

/-- If `w` lies over `v`, then `w.Completion` is a `v.Completion`-algebra. -/
noncomputable scoped instance : Algebra v.Completion w.Completion := completionMap.toAlgebra

scoped instance : IsScalarTower K v.Completion w.Completion :=
  .of_algebraMap_eq fun x => by
    have h : algebraMap K v.Completion x = ((WithAbs.toAbs v.1 x : WithAbs v.1) : v.Completion) :=
      rfl
    rw [RingHom.algebraMap_toAlgebra]; rw [h]; rw [completionMap_coe]
    apply Completion.ext
    rw [Completion.algebraMap_toCompletion]; rw [UniformSpace.Completion.algebraMap_def]
    simp [WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply]

scoped instance : ContinuousSMul v.Completion w.Completion where
  continuous_smul := (continuous_completionMap.comp continuous_fst).mul continuous_snd

end NumberField.LiesOver
