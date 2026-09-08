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

/-- A typeclass saying that `F` is a type of bundled morphisms (in the sense of `DFunLike`)
with a topology on `F` such that evaluation at a point is continuous in `f : F`. -/
/-
**ContinuousEvalConst** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   (α : outParam (Type u_2)) →     (X : outParam (Type u_3
)) → [FunLike F α X] → [TopologicalSpace F] → [TopologicalSpace X] → Prop
参数：Type u_2；Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass saying that `F` is a type of bundled morphisms (in the sense of `DFu
nLike`)
with a topology on `F` such that evaluation at a point is continuous in `f : F`.
-/
class ContinuousEvalConst (F : Type*) (α X : outParam Type*) [FunLike F α X]
    [TopologicalSpace F] [TopologicalSpace X] : Prop where
  continuous_eval_const (x : α) : Continuous fun f : F ↦ f x

export ContinuousEvalConst (continuous_eval_const)

section ContinuousEvalConst

variable {F α X Z : Type*} [FunLike F α X] [TopologicalSpace F] [TopologicalSpace X]
  [ContinuousEvalConst F α X] [TopologicalSpace Z] {f : Z → F} {s : Set Z} {z : Z}

/-- If a type `F'` of bundled morphisms admits a continuous projection
to a type satisfying `ContinuousEvalConst`,
then `F'` satisfies this predicate too.

The word "forget" in the name is motivated by the term "forgetful functor". -/
/-
**ContinuousEvalConst.of_continuous_forget** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousEvalConst.of_continuous_forget {F' : Type*} [FunLike F' α X] [To
pologicalSpace F'] {f : F' -> F} (hc : Continuous f) (hf : forall g, ⇑(f g) = g
参数：hc : Continuous f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousEvalConst.continuous_eval_const`：∀ {F : Type u_1} {α : outPara
m (Type u_2)} {X : outParam (Type u_3)} {inst : FunLike F α X}   {inst_1 : Topol
ogicalSpace F} {inst_2 : Topolo…

--- 原说明 ---
If a type `F'` of bundled morphisms admits a continuous projection
to a type satisfying `ContinuousEvalConst`,
then `F'` satisfies this predicate too.

The word "forget" in the name is motivated by the term "forgetful functor".
-/
theorem ContinuousEvalConst.of_continuous_forget {F' : Type*} [FunLike F' α X] [TopologicalSpace F']
    {f : F' → F} (hc : Continuous f) (hf : ∀ g, ⇑(f g) = g := by intro; rfl) :
    ContinuousEvalConst F' α X where
  continuous_eval_const x := by simpa only [← hf] using! (continuous_eval_const x).comp hc

@[continuity, fun_prop]
/-
**Continuous.eval_const** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {F : Type u_1} {α : Type u_2} {X : Type u_3} {Z : Type u_4} [inst : FunL
ike F α X] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace X] [Contin
uousEvalConst F α X] [inst_4 : TopologicalSpace Z] {f : Z → F},   Continuous f →
 ∀ (x : α), Continuous fun x_1 => (f x_1) x
参数：x : α；f x_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousEvalConst.continuous_eval_const`：∀ {F : Type u_1} {α : outPara
m (Type u_2)} {X : outParam (Type u_3)} {inst : FunLike F α X}   {inst_1 : Topol
ogicalSpace F} {inst_2 : Topolo…
-/
protected theorem Continuous.eval_const (hf : Continuous f) (x : α) : Continuous (f · x) :=
  (continuous_eval_const x).comp hf
/-
**continuous_coeFun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_coeFun : Continuous (DFunLike.coe : F -> α -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `ContinuousEvalConst.continuous_eval_const`：∀ {F : Type u_1} {α : outPara
m (Type u_2)} {X : outParam (Type u_3)} {inst : FunLike F α X}   {inst_1 : Topol
ogicalSpace F} {inst_2 : Topolo…
-/
theorem continuous_coeFun : Continuous (DFunLike.coe : F → α → X) :=
  continuous_pi continuous_eval_const
/-
**Continuous.coeFun** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {F : Type u_1} {α : Type u_2} {X : Type u_3} {Z : Type u_4} [inst : FunL
ike F α X] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace X] [Contin
uousEvalConst F α X] [inst_4 : TopologicalSpace Z] {f : Z → F},   Continuous f →
 Continuous fun z => ⇑(f z)
参数：f z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.eval_const`：∀ {F : Type u_1} {α : Type u_2} {X : Type u_3} {Z
 : Type u_4} [inst : FunLike F α X] [inst_1 : TopologicalSpace F]   [inst_2 : To
pologicalSp…
-/
protected theorem Continuous.coeFun (hf : Continuous f) : Continuous fun z ↦ ⇑(f z) :=
  continuous_pi hf.eval_const
/-
**Filter.Tendsto.eval_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {F : Type u_1} {α : Type u_2} {X : Type u_3} [inst : FunLike F α X] [ins
t_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace X] [ContinuousEvalConst F
 α X] {ι : Type u_5} {l : Filter ι} {f : ι → F} {g : F},   Filter.Tendsto f l (n
hds g) → ∀ (a : α), Filter.Tendsto (fun x => (f x) a) l (nhds (g a))
参数：nhds g；a : α；fun x => (f x) a；nhds (g a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Continuous.eval_const`：∀ {F : Type u_1} {α : Type u_2} {X : Type u_3} {Z
 : Type u_4} [inst : FunLike F α X] [inst_1 : TopologicalSpace F]   [inst_2 : To
pologicalSp…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
protected theorem Filter.Tendsto.eval_const {ι : Type*} {l : Filter ι} {f : ι → F} {g : F}
    (hf : Tendsto f l (𝓝 g)) (a : α) : Tendsto (f · a) l (𝓝 (g a)) :=
  ((continuous_id.eval_const a).tendsto _).comp hf
/-
**Filter.Tendsto.coeFun** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {F : Type u_1} {α : Type u_2} {X : Type u_3} [inst : FunLike F α X] [ins
t_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace X] [ContinuousEvalConst F
 α X] {ι : Type u_5} {l : Filter ι} {f : ι → F} {g : F},   Filter.Tendsto f l (n
hds g) → Filter.Tendsto (fun i => ⇑(f i)) l (nhds ⇑g)
参数：nhds g；fun i => ⇑(f i)；nhds ⇑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Continuous.coeFun`：∀ {F : Type u_1} {α : Type u_2} {X : Type u_3} {Z : T
ype u_4} [inst : FunLike F α X] [inst_1 : TopologicalSpace F]   [inst_2 : Topolo
gicalSp…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
protected theorem Filter.Tendsto.coeFun {ι : Type*} {l : Filter ι} {f : ι → F} {g : F}
    (hf : Tendsto f l (𝓝 g)) : Tendsto (fun i ↦ ⇑(f i)) l (𝓝 ⇑g) :=
  (continuous_id.coeFun.tendsto _).comp hf

protected nonrec theorem ContinuousAt.eval_const (hf : ContinuousAt f z) (x : α) :
    ContinuousAt (f · x) z :=
  hf.eval_const x

protected nonrec theorem ContinuousAt.coeFun (hf : ContinuousAt f z) :
    ContinuousAt (fun z ↦ ⇑(f z)) z :=
  hf.coeFun

protected nonrec theorem ContinuousWithinAt.eval_const (hf : ContinuousWithinAt f s z) (x : α) :
    ContinuousWithinAt (f · x) s z :=
  hf.eval_const x

protected nonrec theorem ContinuousWithinAt.coeFun (hf : ContinuousWithinAt f s z) :
    ContinuousWithinAt (fun z ↦ ⇑(f z)) s z :=
  hf.coeFun
/-
**ContinuousOn.eval_const** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {F : Type u_1} {α : Type u_2} {X : Type u_3} {Z : Type u_4} [inst : FunL
ike F α X] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace X] [Contin
uousEvalConst F α X] [inst_4 : TopologicalSpace Z] {f : Z → F} {s : Set Z},   Co
ntinuousOn f s → ∀ (x : α), ContinuousOn (fun x_1 => (f x_1) x) s
参数：x : α；fun x_1 => (f x_1) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.eval_const`：∀ {F : Type u_1} {α : Type u_2} {X : Type
 u_3} {Z : Type u_4} [inst : FunLike F α X] [inst_1 : TopologicalSpace F]   [ins
t_2 : TopologicalSp…
-/
protected theorem ContinuousOn.eval_const (hf : ContinuousOn f s) (x : α) :
    ContinuousOn (f · x) s :=
  fun z hz ↦ (hf z hz).eval_const x
/-
**ContinuousOn.coeFun** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {F : Type u_1} {α : Type u_2} {X : Type u_3} {Z : Type u_4} [inst : FunL
ike F α X] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace X] [Contin
uousEvalConst F α X] [inst_4 : TopologicalSpace Z] {f : Z → F} {s : Set Z},   Co
ntinuousOn f s → ∀ (x : α), ContinuousOn (fun x_1 => (f x_1) x) s
参数：x : α；fun x_1 => (f x_1) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.eval_const`：∀ {F : Type u_1} {α : Type u_2} {X : Type
 u_3} {Z : Type u_4} [inst : FunLike F α X] [inst_1 : TopologicalSpace F]   [ins
t_2 : TopologicalSp…
-/
protected theorem ContinuousOn.coeFun (hf : ContinuousOn f s) (x : α) : ContinuousOn (f · x) s :=
  fun z hz ↦ (hf z hz).eval_const x

end ContinuousEvalConst

