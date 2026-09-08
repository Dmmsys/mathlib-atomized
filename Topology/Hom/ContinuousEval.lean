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

/-- A typeclass saying that `F` is a bundled morphism class (in the sense of `FunLike`)
with a topology such that `fun (f, x) : F × X ↦ f x` is a continuous function. -/
/-
**ContinuousEval** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   (X : outParam (Type u_2)) →     (Y : outParam (Type u_3
)) →       [FunLike F X Y] → [TopologicalSpace F] → [TopologicalSpace X] → [Topo
logicalSpace Y] → Prop
参数：Type u_2；Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass saying that `F` is a bundled morphism class (in the sense of `FunLik
e`)
with a topology such that `fun (f, x) : F × X ↦ f x` is a continuous function.
-/
class ContinuousEval (F : Type*) (X Y : outParam Type*) [FunLike F X Y]
    [TopologicalSpace F] [TopologicalSpace X] [TopologicalSpace Y] : Prop where
  /-- Evaluation of a bundled morphism at a point is continuous in both variables. -/
  continuous_eval : Continuous fun fx : F × X ↦ fx.1 fx.2

export ContinuousEval (continuous_eval)

variable {F X Y Z : Type*} [FunLike F X Y]
  [TopologicalSpace F] [TopologicalSpace X] [TopologicalSpace Y] [ContinuousEval F X Y]
  [TopologicalSpace Z] {f : Z → F} {g : Z → X} {s : Set Z} {z : Z}

@[continuity, fun_prop]
/-
**Continuous.eval** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {F : Type u_1} {X : Type u_2} {Y : Type u_3} {Z : Type u_4} [inst : FunL
ike F X Y] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace X] [inst_3
 : TopologicalSpace Y] [ContinuousEval F X Y] [inst_5 : TopologicalSpace Z]   {f
 : Z → F} {g : Z → X}, Continuous f → Continuous g → Continuous fun z => (f z) (
g z)
参数：f z；g z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousEval.continuous_eval`：∀ {F : Type u_1} {X : outParam (Type u_2
)} {Y : outParam (Type u_3)} {inst : FunLike F X Y}   {inst_1 : TopologicalSpace
 F} {inst_2 : Topolo…
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
-/
protected theorem Continuous.eval (hf : Continuous f) (hg : Continuous g) :
    Continuous fun z ↦ f z (g z) :=
  continuous_eval.comp (hf.prodMk hg)

/-- If a type `F'` of bundled morphisms admits a continuous projection
to a type satisfying `ContinuousEval`,
then `F'` satisfies this predicate too.

The word "forget" in the name is motivated by the term "forgetful functor". -/
/-
**ContinuousEval.of_continuous_forget** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousEval.of_continuous_forget {F' : Type*} [FunLike F' X Y] [Topolog
icalSpace F'] {f : F' -> F} (hc : Continuous f) (hf : forall g, ⇑(f g) = g
参数：hc : Continuous f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Continuous.eval`：∀ {F : Type u_1} {X : Type u_2} {Y : Type u_3} {Z : Typ
e u_4} [inst : FunLike F X Y] [inst_1 : TopologicalSpace F]   [inst_2 : Topologi
calSp…
· 使用定理 `Continuous.fst'`：Continuous.fst' {f : X -> Z} (hf : Continuous f) : Cont
inuous fun x : X × Y => f x.fst
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)

--- 原说明 ---
If a type `F'` of bundled morphisms admits a continuous projection
to a type satisfying `ContinuousEval`,
then `F'` satisfies this predicate too.

The word "forget" in the name is motivated by the term "forgetful functor".
-/
theorem ContinuousEval.of_continuous_forget {F' : Type*} [FunLike F' X Y] [TopologicalSpace F']
    {f : F' → F} (hc : Continuous f) (hf : ∀ g, ⇑(f g) = g := by intro; rfl) :
    ContinuousEval F' X Y where
  continuous_eval := by simpa only [← hf] using hc.fst'.eval continuous_snd
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) ContinuousEval.toContinuousMapClass : ContinuousMapClass F X Y where
  map_continuous _ := continuous_const.eval continuous_id
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) ContinuousEval.toContinuousEvalConst : ContinuousEvalConst F X Y where
  continuous_eval_const _ := continuous_id.eval continuous_const
/-
**Filter.Tendsto.eval** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {F : Type u_1} {X : Type u_2} {Y : Type u_3} [inst : FunLike F X Y] [ins
t_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace X] [inst_3 : TopologicalS
pace Y] [ContinuousEval F X Y] {α : Type u_5} {l : Filter α}   {f : α → F} {f₀ :
 F} {g : α → X} {x₀ : X},   Filter.Tendsto f l (nhds f₀) → Filter.Tendsto g l (n
hds x₀) → Filter.Tendsto (fun a => (f a) (g a)) l (nhds (f₀ x₀))
参数：nhds f₀；nhds x₀；fun a => (f a) (g a)；nhds (f₀ x₀)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousEval.continuous_eval`：∀ {F : Type u_1} {X : outParam (Type u_2
)} {Y : outParam (Type u_3)} {inst : FunLike F X Y}   {inst_1 : TopologicalSpace
 F} {inst_2 : Topolo…
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
protected theorem Filter.Tendsto.eval {α : Type*} {l : Filter α} {f : α → F} {f₀ : F}
    {g : α → X} {x₀ : X} (hf : Tendsto f l (𝓝 f₀)) (hg : Tendsto g l (𝓝 x₀)) :
    Tendsto (fun a ↦ f a (g a)) l (𝓝 (f₀ x₀)) :=
  (ContinuousEval.continuous_eval.tendsto _).comp (hf.prodMk_nhds hg)

protected nonrec theorem ContinuousAt.eval (hf : ContinuousAt f z) (hg : ContinuousAt g z) :
    ContinuousAt (fun z ↦ f z (g z)) z :=
  hf.eval hg

protected nonrec theorem ContinuousWithinAt.eval (hf : ContinuousWithinAt f s z)
    (hg : ContinuousWithinAt g s z) : ContinuousWithinAt (fun z ↦ f z (g z)) s z :=
  hf.eval hg
/-
**ContinuousOn.eval** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {F : Type u_1} {X : Type u_2} {Y : Type u_3} {Z : Type u_4} [inst : FunL
ike F X Y] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace X] [inst_3
 : TopologicalSpace Y] [ContinuousEval F X Y] [inst_5 : TopologicalSpace Z]   {f
 : Z → F} {g : Z → X} {s : Set Z}, ContinuousOn f s → ContinuousOn g s → Continu
ousOn (fun z => (f z) (g z)) s
参数：fun z => (f z) (g z)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.eval`：∀ {F : Type u_1} {X : Type u_2} {Y : Type u_3} 
{Z : Type u_4} [inst : FunLike F X Y] [inst_1 : TopologicalSpace F]   [inst_2 : 
TopologicalSp…
-/
protected theorem ContinuousOn.eval (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun z ↦ f z (g z)) s :=
  fun z hz ↦ (hf z hz).eval (hg z hz)
