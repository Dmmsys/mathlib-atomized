/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Hom.ContinuousEvalConst
public import Mathlib.Topology.ContinuousMap.Defs

/-!
# Bundled maps with evaluation continuous in both variables

In this file we define a class `ContinuousEval F X Y`
saying that `F` is a bundled morphism class (in the sense of `FunLike`)
with a topology such that `fun (f, x) : F × X ↦ f x` is a continuous function.
-/

public section

open scoped Topology
open Filter

/--
Definition of `ContinuousEval` / `ContinuousEval` 的定义

English:
class ContinuousEval
  parameters: (F : Type*) (X Y : outParam Type*) [FunLike F X Y]
  axioms and operations (1):
    - continuous_eval : Continuous fun fx : F × X => fx.1 fx.2

中文:
类 ContinuousEval
  参数: (F : 类型) (X Y : outParam 类型) [FunLike F X Y]
  公理与运算 (1 个):
    - continuous_eval : Continuous fun fx : F × X => fx.1 fx.2
-/
class ContinuousEval (F : Type*) (X Y : outParam Type*) [FunLike F X Y]
    [TopologicalSpace F] [TopologicalSpace X] [TopologicalSpace Y] : Prop where
  /-- Evaluation of a bundled morphism at a point is continuous in both variables. -/
  continuous_eval : Continuous fun fx : F × X => fx.1 fx.2

export ContinuousEval (continuous_eval)

variable {F X Y Z : Type*} [FunLike F X Y]
  [TopologicalSpace F] [TopologicalSpace X] [TopologicalSpace Y] [ContinuousEval F X Y]
  [TopologicalSpace Z] {f : Z -> F} {g : Z -> X} {s : Set Z} {z : Z}

@[continuity, fun_prop]
/--
theorem `Continuous.eval` / 定理 `Continuous.eval`

English:
theorem Continuous.eval
  given: (hf : Continuous f) (hg : Continuous g)
  proof: continuous_eval.comp (hf.prodMk hg)

中文:
定理 Continuous.eval
  条件: (hf : Continuous f) (hg : Continuous g)
  证明: continuous_eval.comp (hf.prodMk hg)
-/
protected theorem Continuous.eval (hf : Continuous f) (hg : Continuous g) :
    Continuous fun z => f z (g z) :=
  continuous_eval.comp (hf.prodMk hg)

/--
theorem `ContinuousEval.of_continuous_forget` / 定理 `ContinuousEval.of_continuous_forget`

English:
theorem ContinuousEval.of_continuous_forget
  statement: {F' : Type*} [FunLike F' X Y] [TopologicalSpace F']
  proof: by simpa only [← hf] using hc.fst'.eval continuous_snd

中文:
定理 ContinuousEval.of_continuous_forget
  结论: {F' : 类型} [FunLike F' X Y] [TopologicalSpace F']
  证明: by simpa only [← hf] using hc.fst'.eval continuous_snd

Depends on / 依赖: ContinuousEval, continuous_eval, continuous_snd, hc.fst
-/
theorem ContinuousEval.of_continuous_forget {F' : Type*} [FunLike F' X Y] [TopologicalSpace F']
    {f : F' -> F} (hc : Continuous f) (hf : forall g, ⇑(f g) = g := by intro; rfl) :
    ContinuousEval F' X Y where
  continuous_eval := by simpa only [← hf] using hc.fst'.eval continuous_snd

instance (priority := 100) ContinuousEval.toContinuousMapClass : ContinuousMapClass F X Y where
  map_continuous _ := continuous_const.eval continuous_id

instance (priority := 100) ContinuousEval.toContinuousEvalConst : ContinuousEvalConst F X Y where
  continuous_eval_const _ := continuous_id.eval continuous_const

/--
theorem `Filter.Tendsto.eval` / 定理 `Filter.Tendsto.eval`

English:
theorem Filter.Tendsto.eval
  statement: {α : Type*} {l : Filter α} {f : α -> F} {f₀ : F}
  proof: (ContinuousEval.continuous_eval.tendsto _).comp (hf.prodMk_nhds hg)

protected nonrec theorem ContinuousAt.eval (hf : ContinuousAt f z) (hg : ContinuousAt g z) :
    ContinuousAt (fun z => f z (g z)) z :=
  hf.eval hg

protected nonrec theorem ContinuousWithinAt.eval (hf : ContinuousWithinAt f s z)


中文:
定理 Filter.Tendsto.eval
  结论: {α : 类型} {l : Filter α} {f : α -> F} {f₀ : F}
  证明: (ContinuousEval.continuous_eval.tendsto _).comp (hf.prodMk_nhds hg)

protected nonrec theorem ContinuousAt.eval (hf : ContinuousAt f z) (hg : ContinuousAt g z) :
    ContinuousAt (fun z => f z (g z)) z :=
  hf.eval hg

protected nonrec theorem ContinuousWithinAt.eval (hf : ContinuousWithinAt f s z)

-/
protected theorem Filter.Tendsto.eval {α : Type*} {l : Filter α} {f : α -> F} {f₀ : F}
    {g : α -> X} {x₀ : X} (hf : Tendsto f l (𝓝 f₀)) (hg : Tendsto g l (𝓝 x₀)) :
    Tendsto (fun a => f a (g a)) l (𝓝 (f₀ x₀)) :=
  (ContinuousEval.continuous_eval.tendsto _).comp (hf.prodMk_nhds hg)

protected nonrec theorem ContinuousAt.eval (hf : ContinuousAt f z) (hg : ContinuousAt g z) :
    ContinuousAt (fun z => f z (g z)) z :=
  hf.eval hg

protected nonrec theorem ContinuousWithinAt.eval (hf : ContinuousWithinAt f s z)
    (hg : ContinuousWithinAt g s z) : ContinuousWithinAt (fun z => f z (g z)) s z :=
  hf.eval hg

/--
theorem `ContinuousOn.eval` / 定理 `ContinuousOn.eval`

English:
theorem ContinuousOn.eval
  given: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  proof: fun z hz => (hf z hz).eval (hg z hz)

中文:
定理 ContinuousOn.eval
  条件: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  证明: fun z hz => (hf z hz).eval (hg z hz)
-/
protected theorem ContinuousOn.eval (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun z => f z (g z)) s :=
  fun z hz => (hf z hz).eval (hg z hz)
