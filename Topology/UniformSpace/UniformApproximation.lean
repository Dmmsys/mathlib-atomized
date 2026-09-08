/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Uniform approximation

In this file, we give lemmas ensuring that a function is continuous if it can be approximated
uniformly by continuous functions. We give various versions, within a set or the whole space, at
a single point or at all points, with locally uniform approximation or uniform approximation. All
the statements are derived from a statement about locally uniform approximation within a set at
a point, called `continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt`.

## Implementation notes

Most results hold under weaker assumptions of locally uniform approximation. In a first section,
we prove the results under these weaker assumptions. Then, we derive the results on uniform
convergence from them.

## Tags

Uniform limit, uniform convergence, tends uniformly to
-/

public section


noncomputable section

open Topology Uniformity Filter SetRel Set Uniform

variable {α β ι : Type*} [TopologicalSpace α] [UniformSpace β]
variable {F : ι → α → β} {f : α → β} {s s' : Set α} {x : α} {p : Filter ι} {g : ι → α}

/-- A function which can be locally uniformly approximated by functions which are continuous
within a set at a point is continuous within this set at this point. -/
/-
**continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt** 是 Mathlib
 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt (hx : x
 in s) (L : forall u in 𝓤 β, exists t in 𝓝[s] x, exists F : α -> β, ContinuousWi
thinAt F s x ∧ forall y in t, (f y, F y) in u) : ContinuousWithinAt f s x
参数：hx : x in s；L : forall u in 𝓤 β, exists t in 𝓝[s] x, exists F : α -> β, Conti
nuousWithinAt F s x ∧ forall y in t, (f y, F y) in u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Uniform.continuousWithinAt_iff'_left`：∀ {α : Type ua} {β : Type ub} [ins
t : UniformSpace α] [inst_1 : TopologicalSpace β] {f : β → α} {b : β} {s : Set β
},   ContinuousWithinAt f …
· 使用定理 `comp_mem_uniformity_sets`：comp_mem_uniformity_sets {s : SetRel α α} (hs 
: s in 𝓤 α) : exists t in 𝓤 α, t ○ t subseteq s
· 使用定理 `comp_symm_of_uniformity`：comp_symm_of_uniformity {s : SetRel α α} (hs : 
s in 𝓤 α) : exists t in 𝓤 α, (forall {a b}, (a, b) in t -> (b, a) in t) ∧ t ○ t 
subseteq s
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用引理 `SetRel.prodMk_mem_comp`：prodMk_mem_comp (hab : a ~[R] b) (hbc : b ~[S] c
) : a ~[R ○ S] c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `refl_mem_uniformity`：refl_mem_uniformity {x : α} {s : SetRel α α} (h : s
 in 𝓤 α) : (x, x) in s
· 使用定理 `Filter.Eventually.self_of_nhdsWithin`：Filter.Eventually.self_of_nhdsWith
in {p : α -> Prop} {s : Set α} {x : α} (h : forallᶠ y in 𝓝[s] x, p y) (hx : x in
 s) : p x

--- 原说明 ---
A function which can be locally uniformly approximated by functions which are co
ntinuous
within a set at a point is continuous within this set at this point.
-/
theorem continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt (hx : x ∈ s)
    (L : ∀ u ∈ 𝓤 β, ∃ t ∈ 𝓝[s] x, ∃ F : α → β, ContinuousWithinAt F s x ∧ ∀ y ∈ t, (f y, F y) ∈ u) :
    ContinuousWithinAt f s x := by
  refine Uniform.continuousWithinAt_iff'_left.2 fun u₀ hu₀ => ?_
  obtain ⟨u₁, h₁, u₁₀⟩ : ∃ u ∈ 𝓤 β, u ○ u ⊆ u₀ := comp_mem_uniformity_sets hu₀
  obtain ⟨u₂, h₂, hsymm, u₂₁⟩ : ∃ u ∈ 𝓤 β, (∀ {a b}, (a, b) ∈ u → (b, a) ∈ u) ∧ u ○ u ⊆ u₁ :=
    comp_symm_of_uniformity h₁
  rcases L u₂ h₂ with ⟨t, tx, F, hFc, hF⟩
  have A : ∀ᶠ y in 𝓝[s] x, (f y, F y) ∈ u₂ := Eventually.mono tx hF
  have B : ∀ᶠ y in 𝓝[s] x, (F y, F x) ∈ u₂ := Uniform.continuousWithinAt_iff'_left.1 hFc h₂
  have C : ∀ᶠ y in 𝓝[s] x, (f y, F x) ∈ u₁ :=
    (A.and B).mono fun y hy => u₂₁ (prodMk_mem_comp hy.1 hy.2)
  have : (F x, f x) ∈ u₁ :=
    u₂₁ (prodMk_mem_comp (refl_mem_uniformity h₂) (hsymm (A.self_of_nhdsWithin hx)))
  exact C.mono fun y hy => u₁₀ <| prodMk_mem_comp hy this

/-- A function which can be locally uniformly approximated by functions which are continuous at
a point is continuous at this point. -/
/-
**continuousAt_of_locally_uniform_approx_of_continuousAt** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：continuousAt_of_locally_uniform_approx_of_continuousAt (L : forall u in 𝓤 
β, exists t in 𝓝 x, exists F, ContinuousAt F x ∧ forall y in t, (f y, F y) in u)
 : ContinuousAt f x
参数：L : forall u in 𝓤 β, exists t in 𝓝 x, exists F, ContinuousAt F x ∧ forall y i
n t, (f y, F y) in u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt`：cont
inuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt (hx : x in s) (L 
: forall u in 𝓤 β, exists t in 𝓝[s] x, exists F : α -> β…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a

--- 原说明 ---
A function which can be locally uniformly approximated by functions which are co
ntinuous at
a point is continuous at this point.
-/
theorem continuousAt_of_locally_uniform_approx_of_continuousAt
    (L : ∀ u ∈ 𝓤 β, ∃ t ∈ 𝓝 x, ∃ F, ContinuousAt F x ∧ ∀ y ∈ t, (f y, F y) ∈ u) :
    ContinuousAt f x := by
  rw [← continuousWithinAt_univ]
  apply continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt (mem_univ _) _
  simpa only [exists_prop, nhdsWithin_univ, continuousWithinAt_univ] using L

/-- A function which can be locally uniformly approximated by functions which are continuous
on a set is continuous on this set. -/
/-
**continuousOn_of_locally_uniform_approx_of_continuousWithinAt** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：continuousOn_of_locally_uniform_approx_of_continuousWithinAt (L : forall x
 in s, forall u in 𝓤 β, exists t in 𝓝[s] x, exists F, ContinuousWithinAt F s x ∧
 forall y in t, (f y, F y) in u) : ContinuousOn f s
参数：L : forall x in s, forall u in 𝓤 β, exists t in 𝓝[s] x, exists F, ContinuousW
ithinAt F s x ∧ forall y in t, (f y, F y) in u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt`：cont
inuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt (hx : x in s) (L 
: forall u in 𝓤 β, exists t in 𝓝[s] x, exists F : α -> β…

--- 原说明 ---
A function which can be locally uniformly approximated by functions which are co
ntinuous
on a set is continuous on this set.
-/
theorem continuousOn_of_locally_uniform_approx_of_continuousWithinAt
    (L : ∀ x ∈ s, ∀ u ∈ 𝓤 β, ∃ t ∈ 𝓝[s] x, ∃ F,
      ContinuousWithinAt F s x ∧ ∀ y ∈ t, (f y, F y) ∈ u) :
    ContinuousOn f s := fun x hx =>
  continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt hx (L x hx)

/-- A function which can be uniformly approximated by functions which are continuous on a set
is continuous on this set. -/
/-
**continuousOn_of_uniform_approx_of_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_of_uniform_approx_of_continuousOn (L : forall u in 𝓤 β, exist
s F, ContinuousOn F s ∧ forall y in s, (f y, F y) in u) : ContinuousOn f s
参数：L : forall u in 𝓤 β, exists F, ContinuousOn F s ∧ forall y in s, (f y, F y) i
n u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousOn_of_locally_uniform_approx_of_continuousWithinAt`：continuous
On_of_locally_uniform_approx_of_continuousWithinAt (L : forall x in s, forall u 
in 𝓤 β, exists t in 𝓝[s] x, exists F, ContinuousWi…
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `ContinuousOn.continuousWithinAt`：ContinuousOn.continuousWithinAt (hf : C
ontinuousOn f s) (hx : x in s) : ContinuousWithinAt f s x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A function which can be uniformly approximated by functions which are continuous
 on a set
is continuous on this set.
-/
theorem continuousOn_of_uniform_approx_of_continuousOn
    (L : ∀ u ∈ 𝓤 β, ∃ F, ContinuousOn F s ∧ ∀ y ∈ s, (f y, F y) ∈ u) : ContinuousOn f s :=
  continuousOn_of_locally_uniform_approx_of_continuousWithinAt fun _x hx u hu =>
    ⟨s, self_mem_nhdsWithin, (L u hu).imp fun _F hF => ⟨hF.1.continuousWithinAt hx, hF.2⟩⟩

/-- A function which can be locally uniformly approximated by continuous functions is continuous. -/
/-
**continuous_of_locally_uniform_approx_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：continuous_of_locally_uniform_approx_of_continuousAt (L : forall x : α, fo
rall u in 𝓤 β, exists t in 𝓝 x, exists F, ContinuousAt F x ∧ forall y in t, (f y
, F y) in u) : Continuous f
参数：L : forall x : α, forall u in 𝓤 β, exists t in 𝓝 x, exists F, ContinuousAt F 
x ∧ forall y in t, (f y, F y) in u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `continuousAt_of_locally_uniform_approx_of_continuousAt`：continuousAt_of_
locally_uniform_approx_of_continuousAt (L : forall u in 𝓤 β, exists t in 𝓝 x, ex
ists F, ContinuousAt F x ∧ forall y in t, (f…

--- 原说明 ---
A function which can be locally uniformly approximated by continuous functions i
s continuous.
-/
theorem continuous_of_locally_uniform_approx_of_continuousAt
    (L : ∀ x : α, ∀ u ∈ 𝓤 β, ∃ t ∈ 𝓝 x, ∃ F, ContinuousAt F x ∧ ∀ y ∈ t, (f y, F y) ∈ u) :
    Continuous f :=
  continuous_iff_continuousAt.2 fun x =>
    continuousAt_of_locally_uniform_approx_of_continuousAt (L x)

/-- A function which can be uniformly approximated by continuous functions is continuous. -/
/-
**continuous_of_uniform_approx_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_of_uniform_approx_of_continuous (L : forall u in 𝓤 β, exists F,
 Continuous F ∧ forall y, (f y, F y) in u) : Continuous f
参数：L : forall u in 𝓤 β, exists F, Continuous F ∧ forall y, (f y, F y) in u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `continuousOn_of_uniform_approx_of_continuousOn`：continuousOn_of_uniform_
approx_of_continuousOn (L : forall u in 𝓤 β, exists F, ContinuousOn F s ∧ forall
 y in s, (f y, F y) in u) : Continuo…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
A function which can be uniformly approximated by continuous functions is contin
uous.
-/
theorem continuous_of_uniform_approx_of_continuous
    (L : ∀ u ∈ 𝓤 β, ∃ F, Continuous F ∧ ∀ y, (f y, F y) ∈ u) : Continuous f :=
  continuousOn_univ.mp <|
    continuousOn_of_uniform_approx_of_continuousOn <| by
      simpa [continuousOn_univ] using L

/-!
### Uniform limits

From the previous statements on uniform approximation, we deduce continuity results for uniform
limits.
-/


/-- A locally uniform limit on a set of functions which are continuous on this set is itself
continuous on this set. -/
/-
**TendstoLocallyUniformlyOn.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `TendstoLocal
lyUniformlyOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} [inst : TopologicalSpace α]
 [inst_1 : UniformSpace β] {F : ι → α → β}   {f : α → β} {s : Set α} {p : Filter
 ι},   TendstoLocallyUniformlyOn F f p s → (∃ᶠ (n : ι) in p, ContinuousOn (F n) 
s) → ContinuousOn f s
参数：∃ᶠ (n : ι) in p, ContinuousOn (F n) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousOn_of_locally_uniform_approx_of_continuousWithinAt`：continuous
On_of_locally_uniform_approx_of_continuousWithinAt (L : forall x in s, forall u 
in 𝓤 β, exists t in 𝓝[s] x, exists F, ContinuousWi…
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `ContinuousOn.continuousWithinAt`：ContinuousOn.continuousWithinAt (hf : C
ontinuousOn f s) (hx : x in s) : ContinuousWithinAt f s x

--- 原说明 ---
A locally uniform limit on a set of functions which are continuous on this set i
s itself
continuous on this set.
-/
protected theorem TendstoLocallyUniformlyOn.continuousOn (h : TendstoLocallyUniformlyOn F f p s)
    (hc : ∃ᶠ n in p, ContinuousOn (F n) s) : ContinuousOn f s := by
  refine continuousOn_of_locally_uniform_approx_of_continuousWithinAt fun x hx u hu => ?_
  rcases h u hu x hx with ⟨t, ht, H⟩
  rcases (hc.and_eventually H).exists with ⟨n, hFc, hF⟩
  exact ⟨t, ht, ⟨F n, hFc.continuousWithinAt hx, hF⟩⟩

/-- A uniform limit on a set of functions which are continuous on this set is itself continuous
on this set. -/
/-
**TendstoUniformlyOn.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `TendstoUniformlyOn`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} [inst : TopologicalSpace α]
 [inst_1 : UniformSpace β] {F : ι → α → β}   {f : α → β} {s : Set α} {p : Filter
 ι},   TendstoUniformlyOn F f p s → (∃ᶠ (n : ι) in p, ContinuousOn (F n) s) → Co
ntinuousOn f s
参数：∃ᶠ (n : ι) in p, ContinuousOn (F n) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformlyOn.continuousOn`：∀ {α : Type u_1} {β : Type u_2} 
{ι : Type u_3} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {F : ι → α 
→ β}   {f : α → β} {s : Set …
· 使用定理 `TendstoUniformlyOn.tendstoLocallyUniformlyOn`：∀ {α : Type u_1} {β : Type
 u_2} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {F : 
ι → α → β}   {f : α → β} {s : Set …

--- 原说明 ---
A uniform limit on a set of functions which are continuous on this set is itself
 continuous
on this set.
-/
protected theorem TendstoUniformlyOn.continuousOn (h : TendstoUniformlyOn F f p s)
    (hc : ∃ᶠ n in p, ContinuousOn (F n) s) : ContinuousOn f s :=
  h.tendstoLocallyUniformlyOn.continuousOn hc

/-- A locally uniform limit of continuous functions is continuous. -/
/-
**TendstoLocallyUniformly.continuous** 是 Mathlib 中的一个定理，位于命名空间 `TendstoLocallyUn
iformly`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} [inst : TopologicalSpace α]
 [inst_1 : UniformSpace β] {F : ι → α → β}   {f : α → β} {p : Filter ι}, Tendsto
LocallyUniformly F f p → (∃ᶠ (n : ι) in p, Continuous (F n)) → Continuous f
参数：∃ᶠ (n : ι) in p, Continuous (F n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `TendstoLocallyUniformlyOn.continuousOn`：∀ {α : Type u_1} {β : Type u_2} 
{ι : Type u_3} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {F : ι → α 
→ β}   {f : α → β} {s : Set …
· 使用定理 `TendstoLocallyUniformly.tendstoLocallyUniformlyOn`：∀ {α : Type u_1} {β :
 Type u_2} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] 
{F : ι → α → β}   {f : α → β} {s : Set …
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s

--- 原说明 ---
A locally uniform limit of continuous functions is continuous.
-/
protected theorem TendstoLocallyUniformly.continuous (h : TendstoLocallyUniformly F f p)
    (hc : ∃ᶠ n in p, Continuous (F n)) : Continuous f :=
  continuousOn_univ.mp <|
    h.tendstoLocallyUniformlyOn.continuousOn <| hc.mono fun _n hn => hn.continuousOn

/-- A uniform limit of continuous functions is continuous. -/
/-
**TendstoUniformly.continuous** 是 Mathlib 中的一个定理，位于命名空间 `TendstoUniformly`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} [inst : TopologicalSpace α]
 [inst_1 : UniformSpace β] {F : ι → α → β}   {f : α → β} {p : Filter ι}, Tendsto
Uniformly F f p → (∃ᶠ (n : ι) in p, Continuous (F n)) → Continuous f
参数：∃ᶠ (n : ι) in p, Continuous (F n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformly.continuous`：∀ {α : Type u_1} {β : Type u_2} {ι :
 Type u_3} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {F : ι → α → β}
   {f : α → β} {p : Filt…
· 使用定理 `TendstoUniformly.tendstoLocallyUniformly`：∀ {α : Type u_1} {β : Type u_2
} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {F : ι → 
α → β}   {f : α → β} {p : Filt…

--- 原说明 ---
A uniform limit of continuous functions is continuous.
-/
protected theorem TendstoUniformly.continuous (h : TendstoUniformly F f p)
    (hc : ∃ᶠ n in p, Continuous (F n)) : Continuous f :=
  h.tendstoLocallyUniformly.continuous hc

/-!
### Composing limits under uniform convergence

In general, if `Fₙ` converges pointwise to a function `f`, and `gₙ` tends to `x`, it is not true
that `Fₙ gₙ` tends to `f x`. It is true however if the convergence of `Fₙ` to `f` is uniform. In
this paragraph, we prove variations around this statement.
-/


/-- If `Fₙ` converges locally uniformly on a neighborhood of `x` within a set `s` to a function `f`
which is continuous at `x` within `s`, and `gₙ` tends to `x` within `s`, then `Fₙ (gₙ)` tends
to `f x`. -/
/-
**tendsto_comp_of_locally_uniform_limit_within** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_comp_of_locally_uniform_limit_within (h : ContinuousWithinAt f s x
) (hg : Tendsto g p (𝓝[s] x)) (hunif : forall u in 𝓤 β, exists t in 𝓝[s] x, fora
llᶠ n in p, forall y in t, (f y, F n y) in u) : Tendsto (fun n => F n (g n)) p (
𝓝 (f x))
参数：h : ContinuousWithinAt f s x；hg : Tendsto g p (𝓝[s] x)；hunif : forall u in 𝓤 
β, exists t in 𝓝[s] x, forallᶠ n in p, forall y in t, (f y, F n y) in u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Uniform.tendsto_nhds_right`：tendsto_nhds_right {f : Filter β} {u : β -> 
α} {a : α} : Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (a, u x)) f (𝓤 α)
· 使用定理 `comp_mem_uniformity_sets`：comp_mem_uniformity_sets {s : SetRel α α} (hs 
: s in 𝓤 α) : exists t in 𝓤 α, t ○ t subseteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Uniform.continuousWithinAt_iff'_right`：∀ {α : Type ua} {β : Type ub} [in
st : UniformSpace α] [inst_1 : TopologicalSpace β] {f : β → α} {b : β} {s : Set 
β},   ContinuousWithinAt f …
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `SetRel.prodMk_mem_comp`：prodMk_mem_comp (hab : a ~[R] b) (hbc : b ~[S] c
) : a ~[R ○ S] c

--- 原说明 ---
If `Fₙ` converges locally uniformly on a neighborhood of `x` within a set `s` to
 a function `f`
which is continuous at `x` within `s`, and `gₙ` tends to `x` within `s`, then `F
ₙ (gₙ)` tends
to `f x`.
-/
theorem tendsto_comp_of_locally_uniform_limit_within (h : ContinuousWithinAt f s x)
    (hg : Tendsto g p (𝓝[s] x))
    (hunif : ∀ u ∈ 𝓤 β, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, (f y, F n y) ∈ u) :
    Tendsto (fun n => F n (g n)) p (𝓝 (f x)) := by
  refine Uniform.tendsto_nhds_right.2 fun u₀ hu₀ => ?_
  obtain ⟨u₁, h₁, u₁₀⟩ : ∃ u ∈ 𝓤 β, u ○ u ⊆ u₀ := comp_mem_uniformity_sets hu₀
  rcases hunif u₁ h₁ with ⟨s, sx, hs⟩
  have A : ∀ᶠ n in p, g n ∈ s := hg sx
  have B : ∀ᶠ n in p, (f x, f (g n)) ∈ u₁ := hg (Uniform.continuousWithinAt_iff'_right.1 h h₁)
  exact B.mp <| A.mp <| hs.mono fun y H1 H2 H3 => u₁₀ <| prodMk_mem_comp H3 <| H1 _ H2

/-- If `Fₙ` converges locally uniformly on a neighborhood of `x` to a function `f` which is
continuous at `x`, and `gₙ` tends to `x`, then `Fₙ (gₙ)` tends to `f x`. -/
/-
**tendsto_comp_of_locally_uniform_limit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_comp_of_locally_uniform_limit (h : ContinuousAt f x) (hg : Tendsto
 g p (𝓝 x)) (hunif : forall u in 𝓤 β, exists t in 𝓝 x, forallᶠ n in p, forall y 
in t, (f y, F n y) in u) : Tendsto (fun n => F n (g n)) p (𝓝 (f x))
参数：h : ContinuousAt f x；hg : Tendsto g p (𝓝 x)；hunif : forall u in 𝓤 β, exists t
 in 𝓝 x, forallᶠ n in p, forall y in t, (f y, F n y) in u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_comp_of_locally_uniform_limit_within`：tendsto_comp_of_locally_un
iform_limit_within (h : ContinuousWithinAt f s x) (hg : Tendsto g p (𝓝[s] x)) (h
unif : forall u in 𝓤 β, exists t i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a

--- 原说明 ---
If `Fₙ` converges locally uniformly on a neighborhood of `x` to a function `f` w
hich is
continuous at `x`, and `gₙ` tends to `x`, then `Fₙ (gₙ)` tends to `f x`.
-/
theorem tendsto_comp_of_locally_uniform_limit (h : ContinuousAt f x) (hg : Tendsto g p (𝓝 x))
    (hunif : ∀ u ∈ 𝓤 β, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, (f y, F n y) ∈ u) :
    Tendsto (fun n => F n (g n)) p (𝓝 (f x)) := by
  rw [← continuousWithinAt_univ] at h
  rw [← nhdsWithin_univ] at hunif hg
  exact tendsto_comp_of_locally_uniform_limit_within h hg hunif

/-- If `Fₙ` tends locally uniformly to `f` on a set `s`, and `gₙ` tends to `x` within `s`, then
`Fₙ gₙ` tends to `f x` if `f` is continuous at `x` within `s` and `x ∈ s`. -/
/-
**TendstoLocallyUniformlyOn.tendsto_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformlyOn.tendsto_comp (h : TendstoLocallyUniformlyOn F f 
p s) (hf : ContinuousWithinAt f s x) (hx : x in s) (hg : Tendsto g p (𝓝[s] x)) :
 Tendsto (fun n => F n (g n)) p (𝓝 (f x))
参数：h : TendstoLocallyUniformlyOn F f p s；hf : ContinuousWithinAt f s x；hx : x in
 s；hg : Tendsto g p (𝓝[s] x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_comp_of_locally_uniform_limit_within`：tendsto_comp_of_locally_un
iform_limit_within (h : ContinuousWithinAt f s x) (hg : Tendsto g p (𝓝[s] x)) (h
unif : forall u in 𝓤 β, exists t i…

--- 原说明 ---
If `Fₙ` tends locally uniformly to `f` on a set `s`, and `gₙ` tends to `x` withi
n `s`, then
`Fₙ gₙ` tends to `f x` if `f` is continuous at `x` within `s` and `x ∈ s`.
-/
theorem TendstoLocallyUniformlyOn.tendsto_comp (h : TendstoLocallyUniformlyOn F f p s)
    (hf : ContinuousWithinAt f s x) (hx : x ∈ s) (hg : Tendsto g p (𝓝[s] x)) :
    Tendsto (fun n => F n (g n)) p (𝓝 (f x)) :=
  tendsto_comp_of_locally_uniform_limit_within hf hg fun u hu => h u hu x hx

/-- If `Fₙ` tends uniformly to `f` on a set `s`, and `gₙ` tends to `x` within `s`, then `Fₙ gₙ`
tends to `f x` if `f` is continuous at `x` within `s`. -/
/-
**TendstoUniformlyOn.tendsto_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOn.tendsto_comp (h : TendstoUniformlyOn F f p s) (hf : Con
tinuousWithinAt f s x) (hg : Tendsto g p (𝓝[s] x)) : Tendsto (fun n => F n (g n)
) p (𝓝 (f x))
参数：h : TendstoUniformlyOn F f p s；hf : ContinuousWithinAt f s x；hg : Tendsto g p
 (𝓝[s] x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_comp_of_locally_uniform_limit_within`：tendsto_comp_of_locally_un
iform_limit_within (h : ContinuousWithinAt f s x) (hg : Tendsto g p (𝓝[s] x)) (h
unif : forall u in 𝓤 β, exists t i…
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a

--- 原说明 ---
If `Fₙ` tends uniformly to `f` on a set `s`, and `gₙ` tends to `x` within `s`, t
hen `Fₙ gₙ`
tends to `f x` if `f` is continuous at `x` within `s`.
-/
theorem TendstoUniformlyOn.tendsto_comp (h : TendstoUniformlyOn F f p s)
    (hf : ContinuousWithinAt f s x) (hg : Tendsto g p (𝓝[s] x)) :
    Tendsto (fun n => F n (g n)) p (𝓝 (f x)) :=
  tendsto_comp_of_locally_uniform_limit_within hf hg fun u hu => ⟨s, self_mem_nhdsWithin, h u hu⟩

/-- If `Fₙ` tends locally uniformly to `f`, and `gₙ` tends to `x`, then `Fₙ gₙ` tends to `f x`. -/
/-
**TendstoLocallyUniformly.tendsto_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformly.tendsto_comp (h : TendstoLocallyUniformly F f p) (
hf : ContinuousAt f x) (hg : Tendsto g p (𝓝 x)) : Tendsto (fun n => F n (g n)) p
 (𝓝 (f x))
参数：h : TendstoLocallyUniformly F f p；hf : ContinuousAt f x；hg : Tendsto g p (𝓝 x
)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_comp_of_locally_uniform_limit`：tendsto_comp_of_locally_uniform_l
imit (h : ContinuousAt f x) (hg : Tendsto g p (𝓝 x)) (hunif : forall u in 𝓤 β, e
xists t in 𝓝 x, forallᶠ n i…

--- 原说明 ---
If `Fₙ` tends locally uniformly to `f`, and `gₙ` tends to `x`, then `Fₙ gₙ` tend
s to `f x`.
-/
theorem TendstoLocallyUniformly.tendsto_comp (h : TendstoLocallyUniformly F f p)
    (hf : ContinuousAt f x) (hg : Tendsto g p (𝓝 x)) : Tendsto (fun n => F n (g n)) p (𝓝 (f x)) :=
  tendsto_comp_of_locally_uniform_limit hf hg fun u hu => h u hu x

/-- If `Fₙ` tends uniformly to `f`, and `gₙ` tends to `x`, then `Fₙ gₙ` tends to `f x`. -/
/-
**TendstoUniformly.tendsto_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformly.tendsto_comp (h : TendstoUniformly F f p) (hf : Continuou
sAt f x) (hg : Tendsto g p (𝓝 x)) : Tendsto (fun n => F n (g n)) p (𝓝 (f x))
参数：h : TendstoUniformly F f p；hf : ContinuousAt f x；hg : Tendsto g p (𝓝 x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformly.tendsto_comp`：TendstoLocallyUniformly.tendsto_co
mp (h : TendstoLocallyUniformly F f p) (hf : ContinuousAt f x) (hg : Tendsto g p
 (𝓝 x)) : Tendsto (fun n =…
· 使用定理 `TendstoUniformly.tendstoLocallyUniformly`：∀ {α : Type u_1} {β : Type u_2
} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {F : ι → 
α → β}   {f : α → β} {p : Filt…

--- 原说明 ---
If `Fₙ` tends uniformly to `f`, and `gₙ` tends to `x`, then `Fₙ gₙ` tends to `f 
x`.
-/
theorem TendstoUniformly.tendsto_comp (h : TendstoUniformly F f p) (hf : ContinuousAt f x)
    (hg : Tendsto g p (𝓝 x)) : Tendsto (fun n => F n (g n)) p (𝓝 (f x)) :=
  h.tendstoLocallyUniformly.tendsto_comp hf hg

/-!
### Uniform approximation and limit of uniformly continuous functions.
-/
section UniformContinuous
variable {α β ι : Type*} [UniformSpace α] [UniformSpace β]
variable {F : ι → α → β} {f : α → β} {s : Set α} {p : Filter ι}

/-- A function which can be uniformly approximated by functions which are uniformly continuous on a
set is uniformly continuous on this set. -/
/-
**uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn (h : forall u
 in 𝓤 β, exists F : α -> β, UniformContinuousOn F s ∧ forall y in s, (f y, F y) 
in u) : UniformContinuousOn f s
参数：h : forall u in 𝓤 β, exists F : α -> β, UniformContinuousOn F s ∧ forall y in
 s, (f y, F y) in u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comp_comp_symm_mem_uniformity_sets`：comp_comp_symm_mem_uniformity_sets {
s : SetRel α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t ○ t s
ubseteq s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `SetRel.prodMk_mem_comp`：prodMk_mem_comp (hab : a ~[R] b) (hbc : b ~[S] c
) : a ~[R ○ S] c
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Std.Symm.symm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Symm r] (a 
b : α), r a b → r b a

--- 原说明 ---
A function which can be uniformly approximated by functions which are uniformly 
continuous on a
set is uniformly continuous on this set.
-/
theorem uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn
    (h : ∀ u ∈ 𝓤 β, ∃ F : α → β, UniformContinuousOn F s ∧ ∀ y ∈ s, (f y, F y) ∈ u) :
    UniformContinuousOn f s := by
  simp_rw [uniformContinuousOn_iff_restrict, uniformContinuous_def] at h ⊢
  intro u hu
  obtain ⟨v, hv, hvsymm, hvu⟩ := comp_comp_symm_mem_uniformity_sets hu
  obtain ⟨F, hF, hFv⟩ := h v hv
  filter_upwards [hF v hv] with x hx
  exact hvu <| prodMk_mem_comp (prodMk_mem_comp (hFv _ x.1.prop) hx)
      <| hvsymm.symm (f x.2) (F x.2) <| hFv _ x.2.prop

/-- A function which can be uniformly approximated by uniformly continuous functions is uniformly
continuous. -/
/-
**uniformContinuous_of_uniform_approx_of_uniformContinuous** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：uniformContinuous_of_uniform_approx_of_uniformContinuous (h : forall u in 
𝓤 β, exists F : α -> β, UniformContinuous F ∧ forall y, (f y, F y) in u) : Unifo
rmContinuous f
参数：h : forall u in 𝓤 β, exists F : α -> β, UniformContinuous F ∧ forall y, (f y,
 F y) in u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `uniformContinuousOn_univ`：uniformContinuousOn_univ {f : α -> β} : Unifor
mContinuousOn f univ ↔ UniformContinuous f
· 使用定理 `uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn`：uniformCon
tinuousOn_of_uniform_approx_of_uniformContinuousOn (h : forall u in 𝓤 β, exists 
F : α -> β, UniformContinuousOn F s ∧ forall y in …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
A function which can be uniformly approximated by uniformly continuous functions
 is uniformly
continuous.
-/
theorem uniformContinuous_of_uniform_approx_of_uniformContinuous
    (h : ∀ u ∈ 𝓤 β, ∃ F : α → β, UniformContinuous F ∧ ∀ y, (f y, F y) ∈ u) :
    UniformContinuous f :=
  uniformContinuousOn_univ.mp <| uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn
    <| by simpa [uniformContinuousOn_univ] using h

/-- A uniform limit on a set of functions which are uniformly continuous on this set is itself
uniformly continuous on this set. -/
/-
**TendstoUniformlyOn.uniformContinuousOn** 是 Mathlib 中的一个定理，位于命名空间 `TendstoUnifo
rmlyOn`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {ι : Type u_6} [inst : UniformSpace α] [in
st_1 : UniformSpace β] {F : ι → α → β}   {f : α → β} {s : Set α} {p : Filter ι},
   TendstoUniformlyOn F f p s → (∃ᶠ (n : ι) in p, UniformContinuousOn (F n) s) →
 UniformContinuousOn f s
参数：∃ᶠ (n : ι) in p, UniformContinuousOn (F n) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn`：uniformCon
tinuousOn_of_uniform_approx_of_uniformContinuousOn (h : forall u in 𝓤 β, exists 
F : α -> β, UniformContinuousOn F s ∧ forall y in …
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x

--- 原说明 ---
A uniform limit on a set of functions which are uniformly continuous on this set
 is itself
uniformly continuous on this set.
-/
protected theorem TendstoUniformlyOn.uniformContinuousOn (h : TendstoUniformlyOn F f p s)
    (hc : ∃ᶠ n in p, UniformContinuousOn (F n) s) : UniformContinuousOn f s :=
  uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn fun u hu ↦
    let ⟨i, hF⟩ := (hc.and_eventually (h u hu)).exists
    ⟨F i, hF⟩

/-- A uniform limit of uniformly continuous functions is uniformly continuous. -/
/-
**TendstoUniformly.uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 `TendstoUniformly
`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {ι : Type u_6} [inst : UniformSpace α] [in
st_1 : UniformSpace β] {F : ι → α → β}   {f : α → β} {p : Filter ι}, TendstoUnif
ormly F f p → (∃ᶠ (n : ι) in p, UniformContinuous (F n)) → UniformContinuous f
参数：∃ᶠ (n : ι) in p, UniformContinuous (F n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_of_uniform_approx_of_uniformContinuous`：uniformContinu
ous_of_uniform_approx_of_uniformContinuous (h : forall u in 𝓤 β, exists F : α ->
 β, UniformContinuous F ∧ forall y, (f y, F y)…
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x

--- 原说明 ---
A uniform limit of uniformly continuous functions is uniformly continuous.
-/
protected theorem TendstoUniformly.uniformContinuous (h : TendstoUniformly F f p)
    (hc : ∃ᶠ n in p, UniformContinuous (F n)) : UniformContinuous f :=
  uniformContinuous_of_uniform_approx_of_uniformContinuous fun u hu ↦
    let ⟨i, hF⟩ := (hc.and_eventually (h u hu)).exists
    ⟨F i, hF⟩

end UniformContinuous

