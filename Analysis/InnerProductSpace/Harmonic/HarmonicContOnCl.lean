/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus, based on code by Yury Kudryashov
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Functions Harmonic on a Domain and Continuous on Its Closure

Many theorems in harmonic analysis assume that a function is harmonic on a domain and is continuous
on its closure. In this file we define a predicate `HarmonicContOnCl` that expresses this property
and prove basic facts about this predicate.
-/

public section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f f₁ f₂ : E → F}
  {x : E} {s : Set E} {c : ℝ}

open Laplacian Metric Topology

namespace InnerProductSpace

/--
A predicate saying that a function is harmonic on a set and is continuous on its closure. This is a
common assumption in harmonic analysis.
-/
/-
**InnerProductSpace.HarmonicContOnCl** 是 Mathlib 中的一个归纳类型，位于命名空间 `InnerProductSp
ace`。
形式化陈述：{E : Type u_1} →   [inst : NormedAddCommGroup E] →     [inst_1 : InnerProd
uctSpace ℝ E] →       [FiniteDimensional ℝ E] →         {F : Type u_2} → [inst :
 NormedAddCommGroup F] → [NormedSpace ℝ F] → (E → F) → Set E → Prop
参数：E → F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate saying that a function is harmonic on a set and is continuous on its
 closure. This is a
common assumption in harmonic analysis.
-/
structure HarmonicContOnCl (f : E → F) (s : Set E) : Prop where
  protected harmonicOnNhd : HarmonicOnNhd f s
  protected continuousOn : ContinuousOn f (closure s)
/-
**InnerProductSpace.HarmonicOnNhd.harmonicContOnCl** 是 Mathlib 中的一个定理，位于命名空间 `In
nerProductSpace.HarmonicOnNhd`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f : E → F} {s : Set E},   InnerProductSpace.
HarmonicOnNhd f (closure s) → InnerProductSpace.HarmonicContOnCl f s
参数：closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicOnNhd.mono`：∀ {E : Type u_1} [inst : NormedAdd
CommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]  
 {F : Type u_2} [inst_3 : …
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `InnerProductSpace.HarmonicOnNhd.continuousOn`：∀ {E : Type u_1} [inst : N
ormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensiona
l ℝ E]   {F : Type u_2} [inst_3 : …
-/
theorem HarmonicOnNhd.harmonicContOnCl (h : HarmonicOnNhd f (closure s)) :
    HarmonicContOnCl f s :=
  ⟨h.mono subset_closure, h.continuousOn⟩
/-
**InnerProductSpace.IsClosed.harmonicContOnCl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Inn
erProductSpace.IsClosed`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f : E → F} {s : Set E},   IsClosed s → (Inne
rProductSpace.HarmonicContOnCl f s ↔ InnerProductSpace.HarmonicOnNhd f s)
参数：InnerProductSpace.HarmonicContOnCl f s ↔ InnerProductSpace.HarmonicOnNhd f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicContOnCl.harmonicOnNhd`：∀ {E : Type u_1} [inst
 : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimens
ional ℝ E]   {F : Type u_2} [inst_3 : …
· 使用定理 `InnerProductSpace.HarmonicOnNhd.harmonicContOnCl`：∀ {E : Type u_1} [inst
 : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimens
ional ℝ E]   {F : Type u_2} [inst_3 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
-/
theorem IsClosed.harmonicContOnCl_iff (hs : IsClosed s) :
    HarmonicContOnCl f s ↔ HarmonicOnNhd f s where
  mp := (·.1 · ·)
  mpr h := by
    rw [← hs.closure_eq] at h
    exact h.harmonicContOnCl
/-
**InnerProductSpace.harmonicContOnCl_const** 是 Mathlib 中的一个定理，位于命名空间 `InnerProdu
ctSpace`。
形式化陈述：harmonicContOnCl_const {c : F} : HarmonicContOnCl (fun _ : E => c) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.harmonicOnNhd_const`：∀ {E : Type u_1} [inst : NormedAd
dCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E] 
  {F : Type u_2} [inst_3 : …
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
-/
theorem harmonicContOnCl_const {c : F} : HarmonicContOnCl (fun _ : E ↦ c) s :=
  ⟨harmonicOnNhd_const c, continuousOn_const⟩

namespace HarmonicContOnCl

/-
**InnerProductSpace.HarmonicContOnCl.continuousOn_ball** 是 Mathlib 中的一个定理，位于命名空间
 `InnerProductSpace.HarmonicContOnCl`。
形式化陈述：continuousOn_ball {x : E} {r : Real} (h : HarmonicContOnCl f (ball x r)) :
 ContinuousOn f (closedBall x r)
参数：h : HarmonicContOnCl f (ball x r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.closedBall_zero`：∀ {γ : Type w} [inst : MetricSpace γ] {x : γ}, M
etric.closedBall x 0 = {x}
· 使用定理 `continuousOn_singleton`：continuousOn_singleton (f : α -> β) (a : α) : Co
ntinuousOn f {a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_ball`：closure_ball (x : E) {r : Real} (hr : r != 0) : closure (b
all x r) = closedBall x r
· 使用定理 `InnerProductSpace.HarmonicContOnCl.continuousOn`：∀ {E : Type u_1} [inst 
: NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensi
onal ℝ E]   {F : Type u_2} [inst_3 : …
-/
theorem continuousOn_ball {x : E} {r : ℝ} (h : HarmonicContOnCl f (ball x r)) :
    ContinuousOn f (closedBall x r) := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero]
    exact continuousOn_singleton f x
  · rw [← closure_ball x hr]
    exact h.continuousOn
/-
**InnerProductSpace.HarmonicContOnCl.mk_ball** 是 Mathlib 中的一个定理，位于命名空间 `InnerPro
ductSpace.HarmonicContOnCl`。
形式化陈述：mk_ball {x : E} {r : Real} (hd : HarmonicOnNhd f (ball x r)) (hc : Continu
ousOn f (closedBall x r)) : HarmonicContOnCl f (ball x r)
参数：hd : HarmonicOnNhd f (ball x r)；hc : ContinuousOn f (closedBall x r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用引理 `Metric.closure_ball_subset_closedBall`：closure_ball_subset_closedBall : 
closure (ball x ε) subseteq closedBall x ε
-/
theorem mk_ball {x : E} {r : ℝ} (hd : HarmonicOnNhd f (ball x r))
    (hc : ContinuousOn f (closedBall x r)) :
    HarmonicContOnCl f (ball x r) :=
  ⟨hd, hc.mono <| closure_ball_subset_closedBall⟩
/-
**InnerProductSpace.HarmonicContOnCl.contDiffAt** 是 Mathlib 中的一个定理，位于命名空间 `Inner
ProductSpace.HarmonicContOnCl`。
形式化陈述：contDiffAt (h : HarmonicContOnCl f s) (hx : x in s) : ContDiffAt Real 2 f 
x
参数：h : HarmonicContOnCl f s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `InnerProductSpace.HarmonicContOnCl.harmonicOnNhd`：∀ {E : Type u_1} [inst
 : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimens
ional ℝ E]   {F : Type u_2} [inst_3 : …
-/
theorem contDiffAt (h : HarmonicContOnCl f s) (hx : x ∈ s) :
    ContDiffAt ℝ 2 f x := (h.1 x hx).1
/-
**InnerProductSpace.HarmonicContOnCl.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 
`InnerProductSpace.HarmonicContOnCl`。
形式化陈述：differentiableAt (h : HarmonicContOnCl f s) (hx : x in s) : Differentiable
At Real f x
参数：h : HarmonicContOnCl f s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.differentiableAt`：ContDiffAt.differentiableAt (h : ContDiffAt
 𝕜 n f x) (hn : n != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `InnerProductSpace.HarmonicContOnCl.contDiffAt`：contDiffAt (h : HarmonicC
ontOnCl f s) (hx : x in s) : ContDiffAt Real 2 f x
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem differentiableAt (h : HarmonicContOnCl f s) (hx : x ∈ s) :
    DifferentiableAt ℝ f x := (h.contDiffAt hx).differentiableAt two_ne_zero
/-
**InnerProductSpace.HarmonicContOnCl.mono** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduc
tSpace.HarmonicContOnCl`。
形式化陈述：mono {t : Set E} (h : HarmonicContOnCl f s) (ht : t subseteq s) : Harmonic
ContOnCl f t
参数：h : HarmonicContOnCl f s；ht : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicOnNhd.mono`：∀ {E : Type u_1} [inst : NormedAdd
CommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]  
 {F : Type u_2} [inst_3 : …
· 使用定理 `InnerProductSpace.HarmonicContOnCl.harmonicOnNhd`：∀ {E : Type u_1} [inst
 : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimens
ional ℝ E]   {F : Type u_2} [inst_3 : …
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `InnerProductSpace.HarmonicContOnCl.continuousOn`：∀ {E : Type u_1} [inst 
: NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensi
onal ℝ E]   {F : Type u_2} [inst_3 : …
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
theorem mono {t : Set E} (h : HarmonicContOnCl f s) (ht : t ⊆ s) :
    HarmonicContOnCl f t := ⟨h.harmonicOnNhd.mono ht, h.continuousOn.mono (closure_mono ht)⟩
/-
**InnerProductSpace.HarmonicContOnCl.add** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduct
Space.HarmonicContOnCl`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f₁ f₂ : E → F} {s : Set E},   InnerProductSp
ace.HarmonicContOnCl f₁ s →     InnerProductSpace.HarmonicContOnCl f₂ s → InnerP
roductSpace.HarmonicContOnCl (f₁ + f₂) s
参数：f₁ + f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicOnNhd.add`：∀ {E : Type u_1} [inst : NormedAddC
ommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   
{F : Type u_2} [inst_3 : …
· 使用定理 `InnerProductSpace.HarmonicContOnCl.harmonicOnNhd`：∀ {E : Type u_1} [inst
 : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimens
ional ℝ E]   {F : Type u_2} [inst_3 : …
· 使用定理 `ContinuousOn.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 :
 Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : 
X → M}…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `InnerProductSpace.HarmonicContOnCl.continuousOn`：∀ {E : Type u_1} [inst 
: NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensi
onal ℝ E]   {F : Type u_2} [inst_3 : …
-/
@[to_fun] theorem add (hf₁ : HarmonicContOnCl f₁ s) (hf₂ : HarmonicContOnCl f₂ s) :
    HarmonicContOnCl (f₁ + f₂) s := ⟨hf₁.1.add hf₂.1, hf₁.2.add hf₂.2⟩
/-
**InnerProductSpace.HarmonicContOnCl.add_const** 是 Mathlib 中的一个定理，位于命名空间 `InnerP
roductSpace.HarmonicContOnCl`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f : E → F} {s : Set E},   InnerProductSpace.
HarmonicContOnCl f s → ∀ (c : F), InnerProductSpace.HarmonicContOnCl (f + fun x 
=> c) s
参数：c : F；f + fun x => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicContOnCl.add`：∀ {E : Type u_1} [inst : NormedA
ddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]
   {F : Type u_2} [inst_3 : …
· 使用定理 `InnerProductSpace.harmonicContOnCl_const`：harmonicContOnCl_const {c : F}
 : HarmonicContOnCl (fun _ : E => c) s
-/
@[to_fun] theorem add_const (hf : HarmonicContOnCl f s) (c : F) :
    HarmonicContOnCl (f + fun _ ↦ c) s := hf.add harmonicContOnCl_const
/-
**InnerProductSpace.HarmonicContOnCl.const_add** 是 Mathlib 中的一个定理，位于命名空间 `InnerP
roductSpace.HarmonicContOnCl`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f : E → F} {s : Set E},   InnerProductSpace.
HarmonicContOnCl f s → ∀ (c : F), InnerProductSpace.HarmonicContOnCl ((fun x => 
c) + f) s
参数：c : F；(fun x => c) + f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicContOnCl.add`：∀ {E : Type u_1} [inst : NormedA
ddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]
   {F : Type u_2} [inst_3 : …
· 使用定理 `InnerProductSpace.harmonicContOnCl_const`：harmonicContOnCl_const {c : F}
 : HarmonicContOnCl (fun _ : E => c) s
-/
@[to_fun] theorem const_add (hf : HarmonicContOnCl f s) (c : F) :
  HarmonicContOnCl ((fun _ ↦ c) + f) s := harmonicContOnCl_const.add hf
/-
**InnerProductSpace.HarmonicContOnCl.neg** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduct
Space.HarmonicContOnCl`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f : E → F} {s : Set E},   InnerProductSpace.
HarmonicContOnCl f s → InnerProductSpace.HarmonicContOnCl (-f) s
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicOnNhd.neg`：∀ {E : Type u_1} [inst : NormedAddC
ommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   
{F : Type u_2} [inst_3 : …
· 使用定理 `InnerProductSpace.HarmonicContOnCl.harmonicOnNhd`：∀ {E : Type u_1} [inst
 : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimens
ional ℝ E]   {F : Type u_2} [inst_3 : …
· 使用定理 `ContinuousOn.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : X 
→ G} {…
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `InnerProductSpace.HarmonicContOnCl.continuousOn`：∀ {E : Type u_1} [inst 
: NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensi
onal ℝ E]   {F : Type u_2} [inst_3 : …
-/
@[to_fun] theorem neg (hf : HarmonicContOnCl f s) :
    HarmonicContOnCl (-f) s := ⟨hf.1.neg, hf.2.neg⟩
/-
**InnerProductSpace.HarmonicContOnCl.sub** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduct
Space.HarmonicContOnCl`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f₁ f₂ : E → F} {s : Set E},   InnerProductSp
ace.HarmonicContOnCl f₁ s →     InnerProductSpace.HarmonicContOnCl f₂ s → InnerP
roductSpace.HarmonicContOnCl (f₁ - f₂) s
参数：f₁ - f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicOnNhd.sub`：∀ {E : Type u_1} [inst : NormedAddC
ommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   
{F : Type u_2} [inst_3 : …
· 使用定理 `InnerProductSpace.HarmonicContOnCl.harmonicOnNhd`：∀ {E : Type u_1} [inst
 : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimens
ional ℝ E]   {F : Type u_2} [inst_3 : …
· 使用定理 `ContinuousOn.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `InnerProductSpace.HarmonicContOnCl.continuousOn`：∀ {E : Type u_1} [inst 
: NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensi
onal ℝ E]   {F : Type u_2} [inst_3 : …
-/
@[to_fun] theorem sub (hf₁ : HarmonicContOnCl f₁ s) (hf₂ : HarmonicContOnCl f₂ s) :
    HarmonicContOnCl (f₁ - f₂) s := ⟨hf₁.1.sub hf₂.1, hf₁.2.sub hf₂.2⟩
/-
**InnerProductSpace.HarmonicContOnCl.sub_const** 是 Mathlib 中的一个定理，位于命名空间 `InnerP
roductSpace.HarmonicContOnCl`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f : E → F} {s : Set E},   InnerProductSpace.
HarmonicContOnCl f s → ∀ (c : F), InnerProductSpace.HarmonicContOnCl (f - fun x 
=> c) s
参数：c : F；f - fun x => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicContOnCl.sub`：∀ {E : Type u_1} [inst : NormedA
ddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]
   {F : Type u_2} [inst_3 : …
· 使用定理 `InnerProductSpace.harmonicContOnCl_const`：harmonicContOnCl_const {c : F}
 : HarmonicContOnCl (fun _ : E => c) s
-/
@[to_fun] theorem sub_const (hf : HarmonicContOnCl f s) (c : F) :
    HarmonicContOnCl (f - fun _ ↦ c) s := hf.sub harmonicContOnCl_const
/-
**InnerProductSpace.HarmonicContOnCl.const_sub** 是 Mathlib 中的一个定理，位于命名空间 `InnerP
roductSpace.HarmonicContOnCl`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f : E → F} {s : Set E},   InnerProductSpace.
HarmonicContOnCl f s → ∀ (c : F), InnerProductSpace.HarmonicContOnCl ((fun x => 
c) - f) s
参数：c : F；(fun x => c) - f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicContOnCl.sub`：∀ {E : Type u_1} [inst : NormedA
ddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]
   {F : Type u_2} [inst_3 : …
· 使用定理 `InnerProductSpace.harmonicContOnCl_const`：harmonicContOnCl_const {c : F}
 : HarmonicContOnCl (fun _ : E => c) s
-/
@[to_fun] theorem const_sub (hf : HarmonicContOnCl f s) (c : F) :
    HarmonicContOnCl ((fun _ ↦ c) - f) s := harmonicContOnCl_const.sub hf
/-
**InnerProductSpace.HarmonicContOnCl.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `Inner
ProductSpace.HarmonicContOnCl`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f : E → F} {s : Set E},   InnerProductSpace.
HarmonicContOnCl f s → ∀ (c : ℝ), InnerProductSpace.HarmonicContOnCl (c • f) s
参数：c : ℝ；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicOnNhd.const_smul`：∀ {E : Type u_1} [inst : Nor
medAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional 
ℝ E]   {F : Type u_2} [inst_3 : …
· 使用定理 `InnerProductSpace.HarmonicContOnCl.harmonicOnNhd`：∀ {E : Type u_1} [inst
 : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimens
ional ℝ E]   {F : Type u_2} [inst_3 : …
· 使用定理 `ContinuousOn.const_smul`：ContinuousOn.const_smul (hg : ContinuousOn g s)
 (c : M) : ContinuousOn (c • g) s
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `InnerProductSpace.HarmonicContOnCl.continuousOn`：∀ {E : Type u_1} [inst 
: NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensi
onal ℝ E]   {F : Type u_2} [inst_3 : …
-/
@[to_fun] theorem const_smul (hf : HarmonicContOnCl f s) (c : ℝ) :
    HarmonicContOnCl (c • f) s := ⟨hf.1.const_smul, hf.2.const_smul c⟩

end HarmonicContOnCl

end InnerProductSpace

