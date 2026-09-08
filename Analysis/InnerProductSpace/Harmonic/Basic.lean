/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Harmonic Functions

This file defines harmonic functions on real, finite-dimensional, inner product spaces `E`.
-/

@[expose] public section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f f₁ f₂ : E → F}
  {x : E} {s t : Set E} {c : ℝ}

open Topology Laplacian

namespace InnerProductSpace

/-!
## Definition
-/

variable (f x) in
/--
Let `E` be a real, finite-dimensional, inner product space and `x` be a point of `E`. A function `f`
on `E` is harmonic at `x` if it is two times continuously `ℝ`-differentiable and if its Laplacian
vanishes in a neighborhood of `x`.
-/
/-
**InnerProductSpace.HarmonicAt** 是 Mathlib 中的一个定义，位于命名空间 `InnerProductSpace`。
形式化陈述：HarmonicAt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `E` be a real, finite-dimensional, inner product space and `x` be a point of
 `E`. A function `f`
on `E` is harmonic at `x` if it is two times continuously `ℝ`-differentiable and
 if its Laplacian
vanishes in a neighborhood of `x`.
-/
def HarmonicAt := (ContDiffAt ℝ 2 f x) ∧ (Δ f =ᶠ[𝓝 x] 0)

variable (f s) in
/--
Let `E` be a real, finite-dimensional, inner product space and `s` be a subset of `E`. A function
`f` on `E` is harmonic in a neighborhood of `s` if it is harmonic at every point of `s`.
-/
/-
**InnerProductSpace.HarmonicOnNhd** 是 Mathlib 中的一个定义，位于命名空间 `InnerProductSpace`。
形式化陈述：HarmonicOnNhd
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `E` be a real, finite-dimensional, inner product space and `s` be a subset o
f `E`. A function
`f` on `E` is harmonic in a neighborhood of `s` if it is harmonic at every point
 of `s`.
-/
def HarmonicOnNhd := ∀ x ∈ s, HarmonicAt f x

/--
Harmonic functions are two times continuously differentiable.
-/
/-
**InnerProductSpace.HarmonicOnNhd.contDiffOn** 是 Mathlib 中的一个定理，位于命名空间 `InnerPro
ductSpace.HarmonicOnNhd`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f : E → F} {s : Set E},   InnerProductSpace.
HarmonicOnNhd f s → ContDiffOn ℝ 2 f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Harmonic functions are two times continuously differentiable.
-/
lemma HarmonicOnNhd.contDiffOn (hf : HarmonicOnNhd f s) : ContDiffOn ℝ 2 f s :=
  fun x hx ↦ (hf x hx).1.contDiffWithinAt

/-!
## Elementary Properties
-/

/--
If two functions agree in a neighborhood of `x`, then one is harmonic at `x` iff so is the other.
-/
/-
**InnerProductSpace.harmonicAt_congr_nhds** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduc
tSpace`。
形式化陈述：harmonicAt_congr_nhds {f₁ f₂ : E -> F} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂) : Harmo
nicAt f₁ x ↔ HarmonicAt f₂ x
参数：h : f₁ =ᶠ[𝓝 x] f₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.congr_of_eventuallyEq`：ContDiffAt.congr_of_eventuallyEq (h : 
ContDiffAt 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x] f) : ContDiffAt 𝕜 n f₁ x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `InnerProductSpace.laplacian_congr_nhds`：laplacian_congr_nhds (h : f₁ =ᶠ[
𝓝 x] f₂) : Δ f₁ =ᶠ[𝓝 x] Δ f₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If two functions agree in a neighborhood of `x`, then one is harmonic at `x` iff
 so is the other.
-/
theorem harmonicAt_congr_nhds {f₁ f₂ : E → F} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂) :
    HarmonicAt f₁ x ↔ HarmonicAt f₂ x := by
  constructor <;> intro hf
  · exact ⟨hf.1.congr_of_eventuallyEq h.symm, (laplacian_congr_nhds h.symm).trans hf.2⟩
  · exact ⟨hf.1.congr_of_eventuallyEq h, (laplacian_congr_nhds h).trans hf.2⟩

/--
If `f` is harmonic at `x`, then it is harmonic at all points in a neighborhood of `x`.
-/
/-
**InnerProductSpace.HarmonicAt.eventually** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduc
tSpace.HarmonicAt`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f : E → F} {x : E},   InnerProductSpace.Harm
onicAt f x → ∀ᶠ (y : E) in nhds x, InnerProductSpace.HarmonicAt f y
参数：y : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Eventually.eventually_nhds`：Filter.Eventually.eventually_nhds {p 
: X -> Prop} (h : forallᶠ y in 𝓝 x, p y) : forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p
 x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContDiffAt.eventually`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type uF} […
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
If `f` is harmonic at `x`, then it is harmonic at all points in a neighborhood o
f `x`.
-/
theorem HarmonicAt.eventually {f : E → F} {x : E} (h : HarmonicAt f x) :
    ∀ᶠ y in 𝓝 x, HarmonicAt f y := by
  filter_upwards [h.1.eventually (by simp), h.2.eventually_nhds] with a h₁a h₂a
  exact ⟨h₁a, h₂a⟩

/--
Constant functions are harmonic
-/
/-
**InnerProductSpace.harmonicAt_const** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpac
e`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {x : E} (c : F),   InnerProductSpace.Harmonic
At (fun x => c) x
参数：c : F；fun x => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffAt_const`：contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E =
> c) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.laplacian_const`：∀ {E : Type u_2} [inst : NormedAddCom
mGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F
 : Type u_3} [inst_3 : …

--- 原说明 ---
Constant functions are harmonic
-/
@[simp] theorem harmonicAt_const (c : F) :
    HarmonicAt (fun _ ↦ c) x := ⟨by fun_prop, by simp⟩

/--
Constant functions are harmonic
-/
/-
**InnerProductSpace.harmonicOnNhd_const** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductS
pace`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {s : Set E} (c : F),   InnerProductSpace.Harm
onicOnNhd (fun x => c) s
参数：c : F；fun x => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
Constant functions are harmonic
-/
@[simp] theorem harmonicOnNhd_const (c : F) :
    HarmonicOnNhd (fun _ ↦ c) s := fun _ _ ↦ by simp

variable (f) in
/--
Harmonicity is an open property.
-/
/-
**InnerProductSpace.isOpen_setOfPred_harmonicAt** 是 Mathlib 中的一个定理，位于命名空间 `Inner
ProductSpace`。
形式化陈述：isOpen_setOfPred_harmonicAt : IsOpen { x : E | HarmonicAt f x }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `InnerProductSpace.HarmonicAt.eventually`：∀ {E : Type u_1} [inst : Normed
AddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E
]   {F : Type u_2} [inst_3 : …

--- 原说明 ---
Harmonicity is an open property.
-/
theorem isOpen_setOfPred_harmonicAt : IsOpen { x : E | HarmonicAt f x } :=
  isOpen_iff_mem_nhds.2 (fun _ hx ↦ hx.eventually)

@[deprecated (since := "2026-07-09")] alias isOpen_setOf_harmonicAt := isOpen_setOfPred_harmonicAt

/--
If `f` is harmonic in a neighborhood of `s`, it is harmonic in a neighborhood of every subset.
-/
/-
**InnerProductSpace.HarmonicOnNhd.mono** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSp
ace.HarmonicOnNhd`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f : E → F} {s t : Set E},   InnerProductSpac
e.HarmonicOnNhd f s → t ⊆ s → InnerProductSpace.HarmonicOnNhd f t
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is harmonic in a neighborhood of `s`, it is harmonic in a neighborhood of
 every subset.
-/
lemma HarmonicOnNhd.mono (h : HarmonicOnNhd f s) (hst : t ⊆ s) :
    HarmonicOnNhd f t := fun x hx ↦ h x (hst hx)

/--
Harmonic functions are continuous.
-/
/-
**InnerProductSpace.HarmonicOnNhd.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `InnerP
roductSpace.HarmonicOnNhd`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f : E → F} {s : Set E},   InnerProductSpace.
HarmonicOnNhd f s → ContinuousOn f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `ContDiffAt.continuousAt`：ContDiffAt.continuousAt (h : ContDiffAt 𝕜 n f x
) : ContinuousAt f x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Harmonic functions are continuous.
-/
@[fun_prop] theorem HarmonicOnNhd.continuousOn (h : HarmonicOnNhd f s) :
    ContinuousOn f s :=
  fun x hx ↦ (h x hx).1.continuousAt.continuousWithinAt (s := s)

/-!
## Vector Space Structure
-/

/--
Sums of harmonic functions are harmonic.
-/
/-
**InnerProductSpace.HarmonicAt.add** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpace.
HarmonicAt`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f₁ f₂ : E → F} {x : E},   InnerProductSpace.
HarmonicAt f₁ x → InnerProductSpace.HarmonicAt f₂ x → InnerProductSpace.Harmonic
At (f₁ + f₂) x
参数：f₁ + f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.add`：ContDiffAt.add {f g : E -> F} (hf : ContDiffAt 𝕜 n f x) 
(hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => f x + g x) x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContDiffAt.laplacian_add_nhds`：∀ {E : Type u_2} [inst : NormedAddCommGro
up E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : T
ype u_3} [inst_3 : …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Sums of harmonic functions are harmonic.
-/
theorem HarmonicAt.add (h₁ : HarmonicAt f₁ x) (h₂ : HarmonicAt f₂ x) :
    HarmonicAt (f₁ + f₂) x := by
  constructor
  · exact h₁.1.add h₂.1
  · filter_upwards [h₁.1.laplacian_add_nhds h₂.1, h₁.2, h₂.2]
    simp_all

/--
Differences of harmonic functions are harmonic.
-/
/-
**InnerProductSpace.HarmonicAt.sub** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpace.
HarmonicAt`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f₁ f₂ : E → F} {x : E},   InnerProductSpace.
HarmonicAt f₁ x → InnerProductSpace.HarmonicAt f₂ x → InnerProductSpace.Harmonic
At (f₁ - f₂) x
参数：f₁ - f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.sub`：ContDiffAt.sub {f g : E -> F} (hf : ContDiffAt 𝕜 n f x) 
(hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => f x - g x) x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContDiffAt.laplacian_sub_nhds`：∀ {E : Type u_2} [inst : NormedAddCommGro
up E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : T
ype u_3} [inst_3 : …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Differences of harmonic functions are harmonic.
-/
theorem HarmonicAt.sub (h₁ : HarmonicAt f₁ x) (h₂ : HarmonicAt f₂ x) :
    HarmonicAt (f₁ - f₂) x := by
  constructor
  · exact h₁.1.sub h₂.1
  · filter_upwards [h₁.1.laplacian_sub_nhds h₂.1, h₁.2, h₂.2]
    simp_all

/--
Sums of harmonic functions are harmonic.
-/
/-
**InnerProductSpace.HarmonicOnNhd.add** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpa
ce.HarmonicOnNhd`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f₁ f₂ : E → F} {s : Set E},   InnerProductSp
ace.HarmonicOnNhd f₁ s →     InnerProductSpace.HarmonicOnNhd f₂ s → InnerProduct
Space.HarmonicOnNhd (f₁ + f₂) s
参数：f₁ + f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicAt.add`：∀ {E : Type u_1} [inst : NormedAddComm
Group E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F 
: Type u_2} [inst_3 : …

--- 原说明 ---
Sums of harmonic functions are harmonic.
-/
theorem HarmonicOnNhd.add (h₁ : HarmonicOnNhd f₁ s) (h₂ : HarmonicOnNhd f₂ s) :
    HarmonicOnNhd (f₁ + f₂) s := fun x hx ↦ (h₁ x hx).add (h₂ x hx)

/--
Differences of harmonic functions are harmonic.
-/
/-
**InnerProductSpace.HarmonicOnNhd.sub** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpa
ce.HarmonicOnNhd`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f₁ f₂ : E → F} {s : Set E},   InnerProductSp
ace.HarmonicOnNhd f₁ s →     InnerProductSpace.HarmonicOnNhd f₂ s → InnerProduct
Space.HarmonicOnNhd (f₁ - f₂) s
参数：f₁ - f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicAt.sub`：∀ {E : Type u_1} [inst : NormedAddComm
Group E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F 
: Type u_2} [inst_3 : …

--- 原说明 ---
Differences of harmonic functions are harmonic.
-/
theorem HarmonicOnNhd.sub (h₁ : HarmonicOnNhd f₁ s) (h₂ : HarmonicOnNhd f₂ s) :
    HarmonicOnNhd (f₁ - f₂) s := fun x hx ↦ (h₁ x hx).sub (h₂ x hx)

/--
The negative of a harmonic function is harmonic.
-/
/-
**InnerProductSpace.HarmonicAt.neg** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpace.
HarmonicAt`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f : E → F} {x : E},   InnerProductSpace.Harm
onicAt f x → InnerProductSpace.HarmonicAt (-f) x
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.neg`：ContDiffAt.neg {f : E -> F} (hf : ContDiffAt 𝕜 n f x) : 
ContDiffAt 𝕜 n (fun x => -f x) x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `InnerProductSpace.laplacian_neg`：laplacian_neg : Δ (-f) = -(Δ f)
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The negative of a harmonic function is harmonic.
-/
theorem HarmonicAt.neg (h : HarmonicAt f x) :
    HarmonicAt (-f) x := by
  constructor
  · simpa using! h.1.neg
  · filter_upwards [h.2] with x hx
    simp_all [laplacian_neg]

/--
The negative of a harmonic function is harmonic.
-/
/-
**InnerProductSpace.HarmonicOnNhd.neg** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpa
ce.HarmonicOnNhd`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f : E → F} {s : Set E},   InnerProductSpace.
HarmonicOnNhd f s → InnerProductSpace.HarmonicOnNhd (-f) s
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicAt.neg`：∀ {E : Type u_1} [inst : NormedAddComm
Group E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F 
: Type u_2} [inst_3 : …

--- 原说明 ---
The negative of a harmonic function is harmonic.
-/
theorem HarmonicOnNhd.neg (h : HarmonicOnNhd f s) :
    HarmonicOnNhd (-f) s := fun x hx ↦ (h x hx).neg

/--
Scalar multiples of harmonic functions are harmonic.
-/
/-
**InnerProductSpace.HarmonicAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduc
tSpace.HarmonicAt`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f : E → F} {x : E} {c : ℝ},   InnerProductSp
ace.HarmonicAt f x → InnerProductSpace.HarmonicAt (c • f) x
参数：c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.const_smul`：ContDiffAt.const_smul {f : E -> F} {x : E} (c : R
) (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (fun y => c • f y) x
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `InnerProductSpace.laplacian_smul_nhds`：laplacian_smul_nhds (v : 𝕜) (h : 
ContDiffAt Real 2 f x) : Δ (v • f) =ᶠ[𝓝 x] v • (Δ f)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Scalar multiples of harmonic functions are harmonic.
-/
theorem HarmonicAt.const_smul (h : HarmonicAt f x) :
    HarmonicAt (c • f) x := by
  constructor
  · exact h.1.const_smul c
  · filter_upwards [laplacian_smul_nhds c h.1, h.2]
    simp_all

/--
Scalar multiples of harmonic functions are harmonic.
-/
/-
**InnerProductSpace.HarmonicOnNhd.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `InnerPro
ductSpace.HarmonicOnNhd`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {f : E → F} {s : Set E} {c : ℝ},   InnerProdu
ctSpace.HarmonicOnNhd f s → InnerProductSpace.HarmonicOnNhd (c • f) s
参数：c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicAt.const_smul`：∀ {E : Type u_1} [inst : Normed
AddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E
]   {F : Type u_2} [inst_3 : …

--- 原说明 ---
Scalar multiples of harmonic functions are harmonic.
-/
theorem HarmonicOnNhd.const_smul (h : HarmonicOnNhd f s) :
    HarmonicOnNhd (c • f) s := fun x hx ↦ (h x hx).const_smul

/-!
## Compatibility with Linear Maps
-/

/--
Compositions of continuous `ℝ`-linear maps with harmonic functions are harmonic.
-/
/-
**InnerProductSpace.HarmonicAt.comp_CLM** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductS
pace.HarmonicAt`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {G : Type u_3}   [inst_5 : NormedAddCommGroup
 G] [inst_6 : NormedSpace ℝ G] {f : E → F} {x : E},   InnerProductSpace.Harmonic
At f x → ∀ (l : F →L[ℝ] G), InnerProductSpace.HarmonicAt (⇑l ∘ f) x
参数：l : F →L[ℝ] G；⇑l ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.continuousLinearMap_comp`：ContDiffAt.continuousLinearMap_comp
 (g : F ->L[𝕜] G) (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (g ∘ f) x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContDiffAt.laplacian_CLM_comp_left_nhds`：∀ {E : Type u_2} [inst : Normed
AddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E
]   {F : Type u_3} [inst_3 : …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Compositions of continuous `ℝ`-linear maps with harmonic functions are harmonic.
-/
theorem HarmonicAt.comp_CLM (h : HarmonicAt f x) (l : F →L[ℝ] G) :
    HarmonicAt (l ∘ f) x := by
  constructor
  · exact h.1.continuousLinearMap_comp l
  · filter_upwards [h.1.laplacian_CLM_comp_left_nhds (l := l), h.2]
    simp_all

/--
Compositions of continuous linear maps with harmonic functions are harmonic.
-/
/-
**InnerProductSpace.HarmonicOnNhd.comp_CLM** 是 Mathlib 中的一个定理，位于命名空间 `InnerProdu
ctSpace.HarmonicOnNhd`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {G : Type u_3}   [inst_5 : NormedAddCommGroup
 G] [inst_6 : NormedSpace ℝ G] {f : E → F} {s : Set E},   InnerProductSpace.Harm
onicOnNhd f s → ∀ (l : F →L[ℝ] G), InnerProductSpace.HarmonicOnNhd (⇑l ∘ f) s
参数：l : F →L[ℝ] G；⇑l ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicAt.comp_CLM`：∀ {E : Type u_1} [inst : NormedAd
dCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E] 
  {F : Type u_2} [inst_3 : …

--- 原说明 ---
Compositions of continuous linear maps with harmonic functions are harmonic.
-/
theorem HarmonicOnNhd.comp_CLM (h : HarmonicOnNhd f s) (l : F →L[ℝ] G) :
    HarmonicOnNhd (l ∘ f) s := fun x hx ↦ (h x hx).comp_CLM l

/--
Functions are harmonic iff their compositions with continuous linear equivalences are harmonic.
-/
/-
**InnerProductSpace.harmonicAt_comp_CLE_iff** 是 Mathlib 中的一个定理，位于命名空间 `InnerProd
uctSpace`。
形式化陈述：harmonicAt_comp_CLE_iff (l : F ≃L[Real] G) : HarmonicAt (l ∘ f) x ↔ Harmon
icAt f x
参数：l : F ≃L[Real] G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicAt.congr_simp`：∀ {E : Type u_1} [inst : Normed
AddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E
]   {F : Type u_2} [inst_3 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `InnerProductSpace.HarmonicAt.comp_CLM`：∀ {E : Type u_1} [inst : NormedAd
dCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E] 
  {F : Type u_2} [inst_3 : …

--- 原说明 ---
Functions are harmonic iff their compositions with continuous linear equivalence
s are harmonic.
-/
theorem harmonicAt_comp_CLE_iff (l : F ≃L[ℝ] G) :
    HarmonicAt (l ∘ f) x ↔ HarmonicAt f x := by
  constructor <;> intro h
  · simpa [Function.comp_def] using h.comp_CLM l.symm.toContinuousLinearMap
  · exact h.comp_CLM l.toContinuousLinearMap

/--
Functions are harmonic iff their compositions with continuous linear equivalences are harmonic.
-/
/-
**InnerProductSpace.harmonicOnNhd_comp_CLE_iff** 是 Mathlib 中的一个定理，位于命名空间 `InnerP
roductSpace`。
形式化陈述：harmonicOnNhd_comp_CLE_iff (l : F ≃L[Real] G) : HarmonicOnNhd (l ∘ f) s ↔ 
HarmonicOnNhd f s
参数：l : F ≃L[Real] G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `InnerProductSpace.harmonicAt_comp_CLE_iff`：harmonicAt_comp_CLE_iff (l : 
F ≃L[Real] G) : HarmonicAt (l ∘ f) x ↔ HarmonicAt f x

--- 原说明 ---
Functions are harmonic iff their compositions with continuous linear equivalence
s are harmonic.
-/
theorem harmonicOnNhd_comp_CLE_iff (l : F ≃L[ℝ] G) :
    HarmonicOnNhd (l ∘ f) s ↔ HarmonicOnNhd f s :=
  forall₂_congr fun _ _ ↦ harmonicAt_comp_CLE_iff l

end InnerProductSpace

