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

/-- The ring homomorphism `v.Completion →+* w.Completion` induced by `algebraMap K L`, when `w`
lies over `v`. -/
/-
**NumberField.LiesOver.completionMap** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Lies
Over`。
形式化陈述：completionMap : v.Completion ->+* w.Completion
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.instCompletableTopFieldWithAbsRealValAbsoluteV
alueExistsRingHomComplexEqPlace`：∀ {K : Type u_1} [inst : Field K] (v : NumberFi
eld.InfinitePlace K), CompletableTopField (WithAbs ↑v)
· 使用定理 `NumberField.InfinitePlace.LiesOver.isometry_algebraMap`：isometry_algebra
Map : Isometry (algebraMap (WithAbs v.1) (WithAbs w.1))

--- 原说明 ---
The ring homomorphism `v.Completion →+* w.Completion` induced by `algebraMap K L
`, when `w`
lies over `v`.
-/
noncomputable def completionMap : v.Completion →+* w.Completion :=
  ((Completion.equiv w).symm.toRingHom.comp
    (LiesOver.isometry_algebraMap w v).mapRingHom).comp (Completion.equiv v).toRingHom
/-
**NumberField.LiesOver.continuous_completionMap** 是 Mathlib 中的一个定理，位于命名空间 `Numbe
rField.LiesOver`。
形式化陈述：continuous_completionMap : Continuous (completionMap (v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `NumberField.InfinitePlace.instCompletableTopFieldWithAbsRealValAbsoluteV
alueExistsRingHomComplexEqPlace`：∀ {K : Type u_1} [inst : Field K] (v : NumberFi
eld.InfinitePlace K), CompletableTopField (WithAbs ↑v)
· 使用定理 `NumberField.InfinitePlace.LiesOver.isometry_algebraMap`：isometry_algebra
Map : Isometry (algebraMap (WithAbs v.1) (WithAbs w.1))
· 使用定理 `NumberField.InfinitePlace.Completion.continuous_ofCompletion`：continuous
_ofCompletion : Continuous (ofCompletion (v
· 使用定理 `UniformSpace.Completion.continuous_map`：continuous_map : Continuous (Com
pletion.map f)
· 使用定理 `NumberField.InfinitePlace.Completion.continuous_toCompletion`：continuous
_toCompletion : Continuous (toCompletion (v
-/
theorem continuous_completionMap : Continuous (completionMap (v := v) (w := w)) :=
  (continuous_ofCompletion w).comp <|
    UniformSpace.Completion.continuous_map.comp (continuous_toCompletion v)
/-
**NumberField.LiesOver.completionMap_coe** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.
LiesOver`。
形式化陈述：completionMap_coe (x : WithAbs v.1) : completionMap (x : v.Completion) = (
(algebraMap (WithAbs v.1) (WithAbs w.1) x : WithAbs w.1) : w.Completion)
参数：x : WithAbs v.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.Completion.ext`：∀ {K : Type u_1} [inst : Field
 K] {v : NumberField.InfinitePlace K} {x y : v.Completion},   x.toCompletion = y
.toCompletion → x = y
· 使用定理 `Isometry.mapRingHom_coe`：Isometry.mapRingHom_coe {f : α ->+* β} (h : Iso
metry f) (x : α) : h.mapRingHom x = f x
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `NumberField.InfinitePlace.LiesOver.isometry_algebraMap`：isometry_algebra
Map : Isometry (algebraMap (WithAbs v.1) (WithAbs w.1))
-/
theorem completionMap_coe (x : WithAbs v.1) :
    completionMap (x : v.Completion) = ((algebraMap (WithAbs v.1) (WithAbs w.1) x : WithAbs w.1) :
      w.Completion) :=
  Completion.ext <| (LiesOver.isometry_algebraMap w v).mapRingHom_coe x

/-- If `w` lies over `v`, then `w.Completion` is a `v.Completion`-algebra. -/
/-
**NumberField.LiesOver.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.LiesOver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `w` lies over `v`, then `w.Completion` is a `v.Completion`-algebra.
-/
noncomputable scoped instance : Algebra v.Completion w.Completion := completionMap.toAlgebra
/-
**NumberField.LiesOver.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.LiesOver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance : IsScalarTower K v.Completion w.Completion :=
  .of_algebraMap_eq fun x ↦ by
    have h : algebraMap K v.Completion x = ((WithAbs.toAbs v.1 x : WithAbs v.1) : v.Completion) :=
      rfl
    rw [RingHom.algebraMap_toAlgebra, h, completionMap_coe]
    apply Completion.ext
    rw [Completion.algebraMap_toCompletion, UniformSpace.Completion.algebraMap_def]
    simp [WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply]
/-
**NumberField.LiesOver.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.LiesOver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance : ContinuousSMul v.Completion w.Completion where
  continuous_smul := (continuous_completionMap.comp continuous_fst).mul continuous_snd

end NumberField.LiesOver

