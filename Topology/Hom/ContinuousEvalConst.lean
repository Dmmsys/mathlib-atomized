/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Constructions

/-!
# Bundled morphisms with continuous evaluation at a point

In this file we define a typeclass
saying that `F` is a type of bundled morphisms (in the sense of `DFunLike`)
with a topology on `F` such that evaluation at a point is continuous in `f : F`.

## Implementation Notes

For now, we define the typeclass for non-dependent bundled functions only.
Whenever we add a type of bundled dependent functions with a topology having this property,
we may decide to generalize from `FunLike` to `DFunLike`.
-/

public section

open scoped Topology
open Filter

/--
Definition of `ContinuousEvalConst` / `ContinuousEvalConst` 的定义

English:
class ContinuousEvalConst
  parameters: (F : Type*) (α X : outParam Type*) [FunLike F α X]
  axioms and operations (1):
    - continuous_eval_const((x : α)) : Continuous fun f : F => f x

中文:
类 余ntinuousEvalConst
  参数: (F : 类型) (α X : outParam 类型) [函数状 F α X]
  公理与运算 (1 个):
    - continuous_eval_const((x : α)) : 连续 fun f : F => f x
-/
class ContinuousEvalConst (F : Type*) (α X : outParam Type*) [FunLike F α X]
    [TopologicalSpace F] [TopologicalSpace X] : Prop where
  continuous_eval_const (x : α) : Continuous fun f : F => f x

export ContinuousEvalConst (continuous_eval_const)

section ContinuousEvalConst

variable {F α X Z : Type*} [FunLike F α X] [TopologicalSpace F] [TopologicalSpace X]
  [ContinuousEvalConst F α X] [TopologicalSpace Z] {f : Z -> F} {s : Set Z} {z : Z}

/--
theorem `ContinuousEvalConst.of_continuous_forget` / 定理 `ContinuousEvalConst.of_continuous_forget`

English:
theorem ContinuousEvalConst.of_continuous_forget
  statement: {F' : Type*} [FunLike F' α X] [TopologicalSpace F']
  proof: by simpa only [← hf] using! (continuous_eval_const x).comp hc

@[continuity, fun_prop]

中文:
定理 余ntinuousEvalConst.of_continuous_forget
  结论: {F' : 类型} [函数状 F' α X] [拓扑空间 F']
  证明: by simpa only [← hf] using! (continuous_eval_const x).comp hc

@[continuity, fun_prop]

Depends on / 依赖: ContinuousEvalConst, continuous_eval_const
-/
theorem ContinuousEvalConst.of_continuous_forget {F' : Type*} [FunLike F' α X] [TopologicalSpace F']
    {f : F' -> F} (hc : Continuous f) (hf : forall g, ⇑(f g) = g := by intro; rfl) :
    ContinuousEvalConst F' α X where
  continuous_eval_const x := by simpa only [← hf] using! (continuous_eval_const x).comp hc

@[continuity, fun_prop]
/--
theorem `Continuous.eval_const` / 定理 `Continuous.eval_const`

English:
theorem Continuous.eval_const
  given: (hf : Continuous f) (x : α)
  statement: Continuous (f · x)
  proof: (continuous_eval_const x).comp hf

中文:
定理 连续.eval_const
  条件: (hf : 连续 f) (x : α)
  结论: 连续 (f · x)
  证明: (continuous_eval_const x).comp hf
-/
protected theorem Continuous.eval_const (hf : Continuous f) (x : α) : Continuous (f · x) :=
  (continuous_eval_const x).comp hf

/--
theorem `continuous_coeFun` / 定理 `continuous_coeFun`

English:
theorem continuous_coeFun
  statement: Continuous (DFunLike.coe : F -> α -> X)
  proof: continuous_pi continuous_eval_const

中文:
定理 continuous_coeFun
  结论: 连续 (依赖函数状.coe : F -> α -> X)
  证明: continuous_pi continuous_eval_const

Depends on / 依赖: continuous_eval_const, continuous_pi
-/
theorem continuous_coeFun : Continuous (DFunLike.coe : F -> α -> X) :=
  continuous_pi continuous_eval_const

/--
theorem `Continuous.coeFun` / 定理 `Continuous.coeFun`

English:
theorem Continuous.coeFun
  given: (hf : Continuous f)
  statement: Continuous fun z => ⇑(f z)
  proof: continuous_pi hf.eval_const

中文:
定理 连续.coeFun
  条件: (hf : 连续 f)
  结论: 连续 fun z => ⇑(f z)
  证明: continuous_pi hf.eval_const
-/
protected theorem Continuous.coeFun (hf : Continuous f) : Continuous fun z => ⇑(f z) :=
  continuous_pi hf.eval_const

/--
theorem `Filter.Tendsto.eval_const` / 定理 `Filter.Tendsto.eval_const`

English:
theorem Filter.Tendsto.eval_const
  statement: {ι : Type*} {l : Filter ι} {f : ι -> F} {g : F}
  proof: ((continuous_id.eval_const a).tendsto _).comp hf

中文:
定理 滤子.收敛.eval_const
  结论: {ι : 类型} {l : 滤子 ι} {f : ι -> F} {g : F}
  证明: ((continuous_id.eval_const a).tendsto _).comp hf
-/
protected theorem Filter.Tendsto.eval_const {ι : Type*} {l : Filter ι} {f : ι -> F} {g : F}
    (hf : Tendsto f l (𝓝 g)) (a : α) : Tendsto (f · a) l (𝓝 (g a)) :=
  ((continuous_id.eval_const a).tendsto _).comp hf

/--
theorem `Filter.Tendsto.coeFun` / 定理 `Filter.Tendsto.coeFun`

English:
theorem Filter.Tendsto.coeFun
  statement: {ι : Type*} {l : Filter ι} {f : ι -> F} {g : F}
  proof: (continuous_id.coeFun.tendsto _).comp hf

protected nonrec theorem ContinuousAt.eval_const (hf : ContinuousAt f z) (x : α) :
    ContinuousAt (f · x) z :=
  hf.eval_const x

protected nonrec theorem ContinuousAt.coeFun (hf : ContinuousAt f z) :
    ContinuousAt (fun z => ⇑(f z)) z :=
  hf.coeFun

pr

中文:
定理 滤子.收敛.coeFun
  结论: {ι : 类型} {l : 滤子 ι} {f : ι -> F} {g : F}
  证明: (continuous_id.coeFun.tendsto _).comp hf

protected nonrec theorem ContinuousAt.eval_const (hf : ContinuousAt f z) (x : α) :
    ContinuousAt (f · x) z :=
  hf.eval_const x

protected nonrec theorem ContinuousAt.coeFun (hf : ContinuousAt f z) :
    ContinuousAt (fun z => ⇑(f z)) z :=
  hf.coeFun

pr
-/
protected theorem Filter.Tendsto.coeFun {ι : Type*} {l : Filter ι} {f : ι -> F} {g : F}
    (hf : Tendsto f l (𝓝 g)) : Tendsto (fun i => ⇑(f i)) l (𝓝 ⇑g) :=
  (continuous_id.coeFun.tendsto _).comp hf

protected nonrec theorem ContinuousAt.eval_const (hf : ContinuousAt f z) (x : α) :
    ContinuousAt (f · x) z :=
  hf.eval_const x

protected nonrec theorem ContinuousAt.coeFun (hf : ContinuousAt f z) :
    ContinuousAt (fun z => ⇑(f z)) z :=
  hf.coeFun

protected nonrec theorem ContinuousWithinAt.eval_const (hf : ContinuousWithinAt f s z) (x : α) :
    ContinuousWithinAt (f · x) s z :=
  hf.eval_const x

protected nonrec theorem ContinuousWithinAt.coeFun (hf : ContinuousWithinAt f s z) :
    ContinuousWithinAt (fun z => ⇑(f z)) s z :=
  hf.coeFun

/--
theorem `ContinuousOn.eval_const` / 定理 `ContinuousOn.eval_const`

English:
theorem ContinuousOn.eval_const
  given: (hf : ContinuousOn f s) (x : α)
  proof: fun z hz => (hf z hz).eval_const x

中文:
定理 ContinuousOn.eval_const
  条件: (hf : ContinuousOn f s) (x : α)
  证明: fun z hz => (hf z hz).eval_const x
-/
protected theorem ContinuousOn.eval_const (hf : ContinuousOn f s) (x : α) :
    ContinuousOn (f · x) s :=
  fun z hz => (hf z hz).eval_const x

/--
theorem `ContinuousOn.coeFun` / 定理 `ContinuousOn.coeFun`

English:
theorem ContinuousOn.coeFun
  given: (hf : ContinuousOn f s) (x : α)
  statement: ContinuousOn (f · x) s
  proof: fun z hz => (hf z hz).eval_const x

中文:
定理 ContinuousOn.coeFun
  条件: (hf : ContinuousOn f s) (x : α)
  结论: ContinuousOn (f · x) s
  证明: fun z hz => (hf z hz).eval_const x
-/
protected theorem ContinuousOn.coeFun (hf : ContinuousOn f s) (x : α) : ContinuousOn (f · x) s :=
  fun z hz => (hf z hz).eval_const x

end ContinuousEvalConst
