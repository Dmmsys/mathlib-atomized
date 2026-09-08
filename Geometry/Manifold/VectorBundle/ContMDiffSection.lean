/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.Notation

/-!
# `C^n` sections

In this file we define the type `ContMDiffSection` of `n` times continuously differentiable
sections of a vector bundle over a manifold `M` and prove that it's a module over the base field.

In passing, we prove that binary and finite sums, differences and scalar products of `C^n`
sections are `C^n`.

-/

@[expose] public section


open Bundle Filter Function

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : ℕ∞ω)
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  -- `V` vector bundle
  [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]

-- Binary and finite sums, negative, differences and scalar products of smooth sections are smooth
section operations

-- Let V be a vector bundle
variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

variable {I F n V}

variable {f : M → 𝕜} {a : 𝕜} {s t : Π x : M, V x} {u : Set M} {x₀ : M}

/-
**ContMDiffWithinAt.add_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.add_section (hs : CMDiffAt[u] n (T% s) x₀) (ht : CMDiffA
t[u] n (T% t) x₀) : CMDiffAt[u] n (T% (s + t)) x₀
参数：hs : CMDiffAt[u] n (T% s) x₀；ht : CMDiffAt[u] n (T% t) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.contMDiffWithinAt_section`：contMDiffWithinAt_section {s : forall 
x, E x} {a : Set B} {x₀ : B} : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n (fun x =
> TotalSpace.mk' F x (…
· 使用定理 `ContMDiffWithinAt.congr_of_eventuallyEq`：ContMDiffWithinAt.congr_of_even
tuallyEq (h : ContMDiffWithinAt I I' n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x 
= f x) : ContMDiffWithinAt I …
· 使用定理 `ContMDiffWithinAt.add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 : Norme
dAddCommGro…
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt`：mem_baseSet_trivializationAt :
 b in (trivializationAt F E b).baseSet
· 使用定理 `IsLinearMap.map_add`：∀ {R : Type u} {M : Type v} {M₂ : Type w} [inst : S
emiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 : _r
oot_.Modu…
· 使用定理 `Bundle.Trivialization.linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type 
u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace F]   [ins
t_2 : TopologicalS…
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt'`：∀ {B : Type u_2} {F : Type u_
3} {inst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5} 
  {inst_2 : TopologicalSpace (B…
-/
lemma ContMDiffWithinAt.add_section (hs : CMDiffAt[u] n (T% s) x₀) (ht : CMDiffAt[u] n (T% t) x₀) :
    CMDiffAt[u] n (T% (s + t)) x₀ := by
  rw [contMDiffWithinAt_section] at hs ht ⊢
  set e := trivializationAt F V x₀
  refine (hs.add ht).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx
      apply (e.linear 𝕜 hx).1
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).1
/-
**ContMDiffAt.add_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffAt.add_section (hs : CMDiffAt n (T% s) x₀) (ht : CMDiffAt n (T% t
) x₀) : CMDiffAt n (T% (s + t)) x₀
参数：hs : CMDiffAt n (T% s) x₀；ht : CMDiffAt n (T% t) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffWithinAt_univ`：contMDiffWithinAt_univ : ContMDiffWithinAt I I' 
n f univ x ↔ ContMDiffAt I I' n f x
· 使用引理 `ContMDiffWithinAt.add_section`：ContMDiffWithinAt.add_section (hs : CMDif
fAt[u] n (T% s) x₀) (ht : CMDiffAt[u] n (T% t) x₀) : CMDiffAt[u] n (T% (s + t)) 
x₀
-/
lemma ContMDiffAt.add_section (hs : CMDiffAt n (T% s) x₀) (ht : CMDiffAt n (T% t) x₀) :
    CMDiffAt n (T% (s + t)) x₀ := by
  rw [← contMDiffWithinAt_univ] at hs ⊢
  exact hs.add_section ht
/-
**ContMDiffOn.add_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffOn.add_section (hs : CMDiff[u] n (T% s)) (ht : CMDiff[u] n (T% t)
) : CMDiff[u] n (T% (s + t))
参数：hs : CMDiff[u] n (T% s)；ht : CMDiff[u] n (T% t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffWithinAt.add_section`：ContMDiffWithinAt.add_section (hs : CMDif
fAt[u] n (T% s) x₀) (ht : CMDiffAt[u] n (T% t) x₀) : CMDiffAt[u] n (T% (s + t)) 
x₀
-/
lemma ContMDiffOn.add_section (hs : CMDiff[u] n (T% s)) (ht : CMDiff[u] n (T% t)) :
    CMDiff[u] n (T% (s + t)) :=
  fun x₀ hx₀ ↦ (hs x₀ hx₀).add_section (ht x₀ hx₀)
/-
**ContMDiff.add_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.add_section (hs : CMDiff n (T% s)) (ht : CMDiff n (T% t)) : CMDi
ff n (T% (s + t))
参数：hs : CMDiff n (T% s)；ht : CMDiff n (T% t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffAt.add_section`：ContMDiffAt.add_section (hs : CMDiffAt n (T% s)
 x₀) (ht : CMDiffAt n (T% t) x₀) : CMDiffAt n (T% (s + t)) x₀
-/
lemma ContMDiff.add_section (hs : CMDiff n (T% s)) (ht : CMDiff n (T% t)) :
    CMDiff n (T% (s + t)) :=
  fun x₀ ↦ (hs x₀).add_section (ht x₀)
/-
**ContMDiffWithinAt.neg_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.neg_section (hs : CMDiffAt[u] n (T% s) x₀) : CMDiffAt[u]
 n (T% (-s)) x₀
参数：hs : CMDiffAt[u] n (T% s) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.contMDiffWithinAt_section`：contMDiffWithinAt_section {s : forall 
x, E x} {a : Set B} {x₀ : B} : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n (fun x =
> TotalSpace.mk' F x (…
· 使用定理 `ContMDiffWithinAt.congr_of_eventuallyEq`：ContMDiffWithinAt.congr_of_even
tuallyEq (h : ContMDiffWithinAt I I' n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x 
= f x) : ContMDiffWithinAt I …
· 使用定理 `ContMDiffWithinAt.neg`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 : Norme
dAddCommGro…
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt`：mem_baseSet_trivializationAt :
 b in (trivializationAt F E b).baseSet
· 使用定理 `IsLinearMap.map_neg`：map_neg {f : M -> M₂} (lin : IsLinearMap R f) (x : 
M) : f (-x) = -f x
· 使用定理 `Bundle.Trivialization.linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type 
u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace F]   [ins
t_2 : TopologicalS…
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt'`：∀ {B : Type u_2} {F : Type u_
3} {inst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5} 
  {inst_2 : TopologicalSpace (B…
-/
lemma ContMDiffWithinAt.neg_section
    (hs : CMDiffAt[u] n (T% s) x₀) : CMDiffAt[u] n (T% (-s)) x₀ := by
  rw [contMDiffWithinAt_section] at hs ⊢
  set e := trivializationAt F V x₀
  refine hs.neg.congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx
      apply (e.linear 𝕜 hx).map_neg
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).map_neg
/-
**ContMDiffAt.neg_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffAt.neg_section (hs : CMDiffAt n (T% s) x₀) : CMDiffAt n (T% (-s))
 x₀
参数：hs : CMDiffAt n (T% s) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffWithinAt_univ`：contMDiffWithinAt_univ : ContMDiffWithinAt I I' 
n f univ x ↔ ContMDiffAt I I' n f x
· 使用引理 `ContMDiffWithinAt.neg_section`：ContMDiffWithinAt.neg_section (hs : CMDif
fAt[u] n (T% s) x₀) : CMDiffAt[u] n (T% (-s)) x₀
-/
lemma ContMDiffAt.neg_section (hs : CMDiffAt n (T% s) x₀) : CMDiffAt n (T% (-s)) x₀ := by
  rw [← contMDiffWithinAt_univ] at hs ⊢
  exact hs.neg_section
/-
**ContMDiffOn.neg_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffOn.neg_section (hs : CMDiff[u] n (T% s)) : CMDiff[u] n (T% (-s))
参数：hs : CMDiff[u] n (T% s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffWithinAt.neg_section`：ContMDiffWithinAt.neg_section (hs : CMDif
fAt[u] n (T% s) x₀) : CMDiffAt[u] n (T% (-s)) x₀
-/
lemma ContMDiffOn.neg_section (hs : CMDiff[u] n (T% s)) : CMDiff[u] n (T% (-s)) :=
  fun x₀ hx₀ ↦ (hs x₀ hx₀).neg_section
/-
**ContMDiff.neg_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.neg_section (hs : CMDiff n (T% s)) : CMDiff n (T% (-s))
参数：hs : CMDiff n (T% s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffAt.neg_section`：ContMDiffAt.neg_section (hs : CMDiffAt n (T% s)
 x₀) : CMDiffAt n (T% (-s)) x₀
-/
lemma ContMDiff.neg_section (hs : CMDiff n (T% s)) : CMDiff n (T% (-s)) :=
  fun x₀ ↦ (hs x₀).neg_section
/-
**ContMDiffWithinAt.sub_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.sub_section (hs : CMDiffAt[u] n (T% s) x₀) (ht : CMDiffA
t[u] n (T% t) x₀) : CMDiffAt[u] n (T% (s - t)) x₀
参数：hs : CMDiffAt[u] n (T% s) x₀；ht : CMDiffAt[u] n (T% t) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `ContMDiffWithinAt.add_section`：ContMDiffWithinAt.add_section (hs : CMDif
fAt[u] n (T% s) x₀) (ht : CMDiffAt[u] n (T% t) x₀) : CMDiffAt[u] n (T% (s + t)) 
x₀
· 使用引理 `ContMDiffWithinAt.neg_section`：ContMDiffWithinAt.neg_section (hs : CMDif
fAt[u] n (T% s) x₀) : CMDiffAt[u] n (T% (-s)) x₀
-/
lemma ContMDiffWithinAt.sub_section (hs : CMDiffAt[u] n (T% s) x₀) (ht : CMDiffAt[u] n (T% t) x₀) :
    CMDiffAt[u] n (T% (s - t)) x₀ := by
  rw [sub_eq_add_neg]
  exact hs.add_section ht.neg_section
/-
**ContMDiffAt.sub_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffAt.sub_section (hs : CMDiffAt n (T% s) x₀) (ht : CMDiffAt n (T% t
) x₀) : CMDiffAt n (T% (s - t)) x₀
参数：hs : CMDiffAt n (T% s) x₀；ht : CMDiffAt n (T% t) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `ContMDiffAt.add_section`：ContMDiffAt.add_section (hs : CMDiffAt n (T% s)
 x₀) (ht : CMDiffAt n (T% t) x₀) : CMDiffAt n (T% (s + t)) x₀
· 使用引理 `ContMDiffAt.neg_section`：ContMDiffAt.neg_section (hs : CMDiffAt n (T% s)
 x₀) : CMDiffAt n (T% (-s)) x₀
-/
lemma ContMDiffAt.sub_section (hs : CMDiffAt n (T% s) x₀) (ht : CMDiffAt n (T% t) x₀) :
    CMDiffAt n (T% (s - t)) x₀ := by
  rw [sub_eq_add_neg]
  apply hs.add_section ht.neg_section
/-
**ContMDiffOn.sub_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffOn.sub_section (hs : CMDiff[u] n (T% s)) (ht : CMDiff[u] n (T% t)
) : CMDiff[u] n (T% (s - t))
参数：hs : CMDiff[u] n (T% s)；ht : CMDiff[u] n (T% t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffWithinAt.sub_section`：ContMDiffWithinAt.sub_section (hs : CMDif
fAt[u] n (T% s) x₀) (ht : CMDiffAt[u] n (T% t) x₀) : CMDiffAt[u] n (T% (s - t)) 
x₀
-/
lemma ContMDiffOn.sub_section (hs : CMDiff[u] n (T% s)) (ht : CMDiff[u] n (T% t)) :
    CMDiff[u] n (T% (s - t)) :=
  fun x₀ hx₀ ↦ (hs x₀ hx₀).sub_section (ht x₀ hx₀)
/-
**ContMDiff.sub_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.sub_section (hs : CMDiff n (T% s)) (ht : CMDiff n (T% t)) : CMDi
ff n (T% (s - t))
参数：hs : CMDiff n (T% s)；ht : CMDiff n (T% t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffAt.sub_section`：ContMDiffAt.sub_section (hs : CMDiffAt n (T% s)
 x₀) (ht : CMDiffAt n (T% t) x₀) : CMDiffAt n (T% (s - t)) x₀
-/
lemma ContMDiff.sub_section (hs : CMDiff n (T% s)) (ht : CMDiff n (T% t)) : CMDiff n (T% (s - t)) :=
  fun x₀ ↦ (hs x₀).sub_section (ht x₀)
/-
**ContMDiffWithinAt.smul_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.smul_section (hf : CMDiffAt[u] n f x₀) (hs : CMDiffAt[u]
 n (T% s) x₀) : CMDiffAt[u] n (T% (f • s)) x₀
参数：hf : CMDiffAt[u] n f x₀；hs : CMDiffAt[u] n (T% s) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.contMDiffWithinAt_section`：contMDiffWithinAt_section {s : forall 
x, E x} {a : Set B} {x₀ : B} : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n (fun x =
> TotalSpace.mk' F x (…
· 使用定理 `ContMDiffWithinAt.congr_of_eventuallyEq`：ContMDiffWithinAt.congr_of_even
tuallyEq (h : ContMDiffWithinAt I I' n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x 
= f x) : ContMDiffWithinAt I …
· 使用定理 `ContMDiffWithinAt.smul`：ContMDiffWithinAt.smul (hf : CMDiffAt[s] n f x) 
(hg : CMDiffAt[s] n g x) : CMDiffAt[s] n (f • g) x
· 使用定理 `instContMDiffSMulModelWithCornersSelf`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {n : WithTop…
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt`：mem_baseSet_trivializationAt :
 b in (trivializationAt F E b).baseSet
· 使用定理 `IsLinearMap.map_smul`：∀ {R : Type u} {M : Type v} {M₂ : Type w} [inst : 
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 : _
root_.Modu…
· 使用定理 `Bundle.Trivialization.linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type 
u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace F]   [ins
t_2 : TopologicalS…
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt'`：∀ {B : Type u_2} {F : Type u_
3} {inst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5} 
  {inst_2 : TopologicalSpace (B…
-/
lemma ContMDiffWithinAt.smul_section (hf : CMDiffAt[u] n f x₀) (hs : CMDiffAt[u] n (T% s) x₀) :
    CMDiffAt[u] n (T% (f • s)) x₀ := by
  rw [contMDiffWithinAt_section] at hs ⊢
  set e := trivializationAt F V x₀
  refine (hf.smul hs).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx
      apply (e.linear 𝕜 hx).2
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).2
/-
**ContMDiffAt.smul_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffAt.smul_section (hf : CMDiffAt n f x₀) (hs : CMDiffAt n (T% s) x₀
) : CMDiffAt n (T% (f • s)) x₀
参数：hf : CMDiffAt n f x₀；hs : CMDiffAt n (T% s) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffWithinAt_univ`：contMDiffWithinAt_univ : ContMDiffWithinAt I I' 
n f univ x ↔ ContMDiffAt I I' n f x
· 使用引理 `ContMDiffWithinAt.smul_section`：ContMDiffWithinAt.smul_section (hf : CMD
iffAt[u] n f x₀) (hs : CMDiffAt[u] n (T% s) x₀) : CMDiffAt[u] n (T% (f • s)) x₀
-/
lemma ContMDiffAt.smul_section (hf : CMDiffAt n f x₀) (hs : CMDiffAt n (T% s) x₀) :
    CMDiffAt n (T% (f • s)) x₀ := by
  rw [← contMDiffWithinAt_univ] at hs ⊢
  exact .smul_section hf hs
/-
**ContMDiffOn.smul_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffOn.smul_section (hf : CMDiff[u] n f) (hs : CMDiff[u] n (T% s)) : 
CMDiff[u] n (T% (f • s))
参数：hf : CMDiff[u] n f；hs : CMDiff[u] n (T% s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffWithinAt.smul_section`：ContMDiffWithinAt.smul_section (hf : CMD
iffAt[u] n f x₀) (hs : CMDiffAt[u] n (T% s) x₀) : CMDiffAt[u] n (T% (f • s)) x₀
-/
lemma ContMDiffOn.smul_section (hf : CMDiff[u] n f) (hs : CMDiff[u] n (T% s)) :
    CMDiff[u] n (T% (f • s)) :=
  fun x₀ hx₀ ↦ (hf x₀ hx₀).smul_section (hs x₀ hx₀)
/-
**ContMDiff.smul_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.smul_section (hf : CMDiff n f) (hs : CMDiff n (T% s)) : CMDiff n
 (T% (f • s))
参数：hf : CMDiff n f；hs : CMDiff n (T% s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffAt.smul_section`：ContMDiffAt.smul_section (hf : CMDiffAt n f x₀
) (hs : CMDiffAt n (T% s) x₀) : CMDiffAt n (T% (f • s)) x₀
-/
lemma ContMDiff.smul_section (hf : CMDiff n f) (hs : CMDiff n (T% s)) : CMDiff n (T% (f • s)) :=
  fun x₀ ↦ (hf x₀).smul_section (hs x₀)
/-
**ContMDiffWithinAt.const_smul_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.const_smul_section (hs : CMDiffAt[u] n (T% s) x₀) : CMDi
ffAt[u] n (T% (a • s)) x₀
参数：hs : CMDiffAt[u] n (T% s) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffWithinAt.smul_section`：ContMDiffWithinAt.smul_section (hf : CMD
iffAt[u] n f x₀) (hs : CMDiffAt[u] n (T% s) x₀) : CMDiffAt[u] n (T% (f • s)) x₀
· 使用定理 `contMDiffWithinAt_const`：contMDiffWithinAt_const : ContMDiffWithinAt I I
' n (fun _ : M => c) s x
-/
lemma ContMDiffWithinAt.const_smul_section
    (hs : CMDiffAt[u] n (T% s) x₀) : CMDiffAt[u] n (T% (a • s)) x₀ :=
  contMDiffWithinAt_const.smul_section hs
/-
**ContMDiffAt.const_smul_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffAt.const_smul_section (hs : CMDiffAt n (T% s) x₀) : CMDiffAt n (T
% (a • s)) x₀
参数：hs : CMDiffAt n (T% s) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffAt.smul_section`：ContMDiffAt.smul_section (hf : CMDiffAt n f x₀
) (hs : CMDiffAt n (T% s) x₀) : CMDiffAt n (T% (f • s)) x₀
· 使用定理 `contMDiffAt_const`：contMDiffAt_const : ContMDiffAt I I' n (fun _ : M => 
c) x
-/
lemma ContMDiffAt.const_smul_section (hs : CMDiffAt n (T% s) x₀) : CMDiffAt n (T% (a • s)) x₀ :=
  contMDiffAt_const.smul_section hs
/-
**ContMDiffOn.const_smul_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffOn.const_smul_section (hs : CMDiff[u] n (T% s)) : CMDiff[u] n (T%
 (a • s))
参数：hs : CMDiff[u] n (T% s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffOn.smul_section`：ContMDiffOn.smul_section (hf : CMDiff[u] n f) 
(hs : CMDiff[u] n (T% s)) : CMDiff[u] n (T% (f • s))
· 使用定理 `contMDiffOn_const`：contMDiffOn_const : ContMDiffOn I I' n (fun _ : M => 
c) s
-/
lemma ContMDiffOn.const_smul_section (hs : CMDiff[u] n (T% s)) : CMDiff[u] n (T% (a • s)) :=
  contMDiffOn_const.smul_section hs
/-
**ContMDiff.const_smul_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.const_smul_section (hs : CMDiff n (T% s)) : CMDiff n (T% (a • s)
)
参数：hs : CMDiff n (T% s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffAt.const_smul_section`：ContMDiffAt.const_smul_section (hs : CMD
iffAt n (T% s) x₀) : CMDiffAt n (T% (a • s)) x₀
-/
lemma ContMDiff.const_smul_section (hs : CMDiff n (T% s)) : CMDiff n (T% (a • s)) :=
  fun x₀ ↦ (hs x₀).const_smul_section

variable {ι : Type*} {t : ι → (x : M) → V x}
/-
**ContMDiffWithinAt.sum_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.sum_section {s : Finset ι} (hs : forall i in s, CMDiffAt
[u] n (T% (t i ·)) x₀) : CMDiffAt[u] n (T% (fun x => (∑ i in s, (t i x)))) x₀
参数：hs : forall i in s, CMDiffAt[u] n (T% (t i ·)) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `Bundle.contMDiffWithinAt_zeroSection`：contMDiffWithinAt_zeroSection {t :
 Set B} {x : B} : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n (zeroSection F E) t x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用引理 `ContMDiffWithinAt.add_section`：ContMDiffWithinAt.add_section (hs : CMDif
fAt[u] n (T% s) x₀) (ht : CMDiffAt[u] n (T% t) x₀) : CMDiffAt[u] n (T% (s + t)) 
x₀
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
-/
lemma ContMDiffWithinAt.sum_section {s : Finset ι}
    (hs : ∀ i ∈ s, CMDiffAt[u] n (T% (t i ·)) x₀) :
    CMDiffAt[u] n (T% (fun x ↦ (∑ i ∈ s, (t i x)))) x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using! contMDiffWithinAt_zeroSection ..
  | insert i s hi h =>
    simp only [Finset.sum_insert hi]
    apply (hs _ (s.mem_insert_self i)).add_section
    exact h fun i a ↦ hs _ (s.mem_insert_of_mem a)
/-
**ContMDiffAt.sum_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffAt.sum_section {s : Finset ι} (hs : forall i in s, CMDiffAt n (T%
 (t i ·)) x₀) : CMDiffAt n (T% (fun x => (∑ i in s, (t i x)))) x₀
参数：hs : forall i in s, CMDiffAt n (T% (t i ·)) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffWithinAt.sum_section`：ContMDiffWithinAt.sum_section {s : Finset
 ι} (hs : forall i in s, CMDiffAt[u] n (T% (t i ·)) x₀) : CMDiffAt[u] n (T% (fun
 x => (∑ i in s, (t…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma ContMDiffAt.sum_section {s : Finset ι}
    (hs : ∀ i ∈ s, CMDiffAt n (T% (t i ·)) x₀) :
    CMDiffAt n (T% (fun x ↦ (∑ i ∈ s, (t i x)))) x₀ := by
  simp_rw [← contMDiffWithinAt_univ] at hs ⊢
  exact .sum_section hs
/-
**ContMDiffOn.sum_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffOn.sum_section {s : Finset ι} (hs : forall i in s, CMDiff[u] n (T
% (t i ·))) : CMDiff[u] n (T% (fun x => (∑ i in s, (t i x))))
参数：hs : forall i in s, CMDiff[u] n (T% (t i ·))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffWithinAt.sum_section`：ContMDiffWithinAt.sum_section {s : Finset
 ι} (hs : forall i in s, CMDiffAt[u] n (T% (t i ·)) x₀) : CMDiffAt[u] n (T% (fun
 x => (∑ i in s, (t…
-/
lemma ContMDiffOn.sum_section {s : Finset ι}
    (hs : ∀ i ∈ s, CMDiff[u] n (T% (t i ·))) :
    CMDiff[u] n (T% (fun x ↦ (∑ i ∈ s, (t i x)))) :=
  fun x₀ hx₀ ↦ .sum_section fun i hi ↦ hs i hi x₀ hx₀
/-
**ContMDiff.sum_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.sum_section {s : Finset ι} (hs : forall i in s, CMDiff n (T% (t 
i ·))) : CMDiff n (T% (fun x => (∑ i in s, (t i x))))
参数：hs : forall i in s, CMDiff n (T% (t i ·))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffAt.sum_section`：ContMDiffAt.sum_section {s : Finset ι} (hs : fo
rall i in s, CMDiffAt n (T% (t i ·)) x₀) : CMDiffAt n (T% (fun x => (∑ i in s, (
t i x)))) x₀
-/
lemma ContMDiff.sum_section {s : Finset ι} (hs : ∀ i ∈ s, CMDiff n (T% (t i ·))) :
    CMDiff n (T% (fun x ↦ (∑ i ∈ s, (t i x)))) :=
  fun x₀ ↦ .sum_section fun i hi ↦ (hs i hi) x₀

/-- The scalar product `ψ • s` of a `C^k` function `ψ : M → 𝕜` and a section `s` of a vector
bundle `V → M` is `C^k` once `s` is `C^k` on an open set containing `tsupport ψ`.

This is a vector bundle analogue of `contMDiff_of_tsupport`. -/
/-
**ContMDiffOn.smul_section_of_tsupport** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffOn.smul_section_of_tsupport {s : Π (x : M), V x} {ψ : M -> 𝕜} (hψ
 : CMDiff[u] n ψ) (ht : IsOpen u) (ht' : tsupport ψ subseteq u) (hs : CMDiff[u] 
n (T% s)) : CMDiff n (T% (ψ • s))
参数：x : M；hψ : CMDiff[u] n ψ；ht : IsOpen u；ht' : tsupport ψ subseteq u；hs : CMDif
f[u] n (T% s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `contMDiff_of_contMDiffOn_union_of_isOpen`：contMDiff_of_contMDiffOn_union
_of_isOpen (hf : ContMDiffOn I I' n f s) (hf' : ContMDiffOn I I' n f t) (hst : s
 union t = univ) (hs : IsOpen …
· 使用引理 `ContMDiffOn.smul_section`：ContMDiffOn.smul_section (hf : CMDiff[u] n f) 
(hs : CMDiff[u] n (T% s)) : CMDiff[u] n (T% (f • s))
· 使用定理 `ContMDiffOn.congr`：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : 
forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁ s
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `Bundle.contMDiff_zeroSection`：contMDiff_zeroSection : ContMDiff IB (IB.p
rod 𝓘(𝕜, F)) n (zeroSection F E)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `image_eq_zero_of_notMem_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst 
: Zero α] [inst_1 : TopologicalSpace X] {f : X → α} {x : X},   x ∉ tsupport f → 
f x = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.compl_subset_iff_union`：compl_subset_iff_union {s t : Set α} : sᶜ su
bseteq t ↔ s union t = univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `isClosed_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [inst
_1 : TopologicalSpace X] (f : X → α), IsClosed (tsupport f)

--- 原说明 ---
The scalar product `ψ • s` of a `C^k` function `ψ : M → 𝕜` and a section `s` of 
a vector
bundle `V → M` is `C^k` once `s` is `C^k` on an open set containing `tsupport ψ`
.

This is a vector bundle analogue of `contMDiff_of_tsupport`.
-/
lemma ContMDiffOn.smul_section_of_tsupport {s : Π (x : M), V x} {ψ : M → 𝕜} (hψ : CMDiff[u] n ψ)
    (ht : IsOpen u) (ht' : tsupport ψ ⊆ u) (hs : CMDiff[u] n (T% s)) :
    CMDiff n (T% (ψ • s)) := by
  apply contMDiff_of_contMDiffOn_union_of_isOpen (hψ.smul_section hs) ?_ ?_ ht
      (isOpen_compl_iff.mpr <| isClosed_tsupport ψ)
  · apply ((contMDiff_zeroSection _ _).contMDiffOn (s := (tsupport ψ)ᶜ)).congr
    intro y hy
    simp [image_eq_zero_of_notMem_tsupport hy, zeroSection]
  · exact Set.compl_subset_iff_union.mp <| Set.compl_subset_compl.mpr ht'

/-- The sum of a locally finite collection of sections is `C^k` iff each section is.
Version at a point within a set. -/
/-
**ContMDiffWithinAt.sum_section_of_locallyFinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.sum_section_of_locallyFinite (ht : LocallyFinite fun i =
> {x : M | t i x != 0}) (ht' : forall i, CMDiffAt[u] n (T% (t i ·)) x₀) : CMDiff
At[u] n (T% (fun x => ∑' i, (t i x))) x₀
参数：ht : LocallyFinite fun i => {x : M | t i x != 0}；ht' : forall i, CMDiffAt[u] 
n (T% (t i ·)) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffWithinAt.sum_section`：ContMDiffWithinAt.sum_section {s : Finset
 ι} (hs : forall i in s, CMDiffAt[u] n (T% (t i ·)) x₀) : CMDiffAt[u] n (T% (fun
 x => (∑ i in s, (t…
· 使用定理 `ContMDiffWithinAt.mono`：ContMDiffWithinAt.mono (hf : ContMDiffWithinAt I
 I' n f s x) (hts : t subseteq s) : ContMDiffWithinAt I I' n f t x
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contMDiffWithinAt_inter`：contMDiffWithinAt_inter (ht : t in 𝓝 x) : ContM
DiffWithinAt I I' n f (s inter t) x ↔ ContMDiffWithinAt I I' n f s x
· 使用定理 `ContMDiffWithinAt.congr`：ContMDiffWithinAt.congr (h : ContMDiffWithinAt 
I I' n f s x) (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x) : ContMDiffWith
inAt I I' n f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.TotalSpace.mk_inj`：∀ {B : Type u_1} {F : Type u_2} {E : B → Type 
u_3} {b : B} {y y' : E b}, ⟨b, y⟩ = ⟨b, y'⟩ ↔ y = y'
· 使用定理 `tsum_eq_sum'`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [L.LeAtTop] {
s …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.support_subset_iff'`：∀ {ι : Type u_1} {M : Type u_3} [inst : Ze
ro M] {f : ι → M} {s : Set ι}, Function.support f ⊆ s ↔ ∀ x ∉ s, f x = 0
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `Set.mem_of_mem_inter_right`：mem_of_mem_inter_right {x : α} {a b : Set α}
 (h : x in a inter b) : x in b
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s

--- 原说明 ---
The sum of a locally finite collection of sections is `C^k` iff each section is.
Version at a point within a set.
-/
lemma ContMDiffWithinAt.sum_section_of_locallyFinite
    (ht : LocallyFinite fun i ↦ {x : M | t i x ≠ 0})
    (ht' : ∀ i, CMDiffAt[u] n (T% (t i ·)) x₀) :
    CMDiffAt[u] n (T% (fun x ↦ ∑' i, (t i x))) x₀ := by
  obtain ⟨u', hu', hfin⟩ := ht x₀
  -- All sections `t i` but a finite set `s` vanish near `x₀`: choose a neighbourhood `u` of `x₀`
  -- and a finite set `s` of sections which don't vanish.
  let s := {i | ((fun i ↦ {x | t i x ≠ 0}) i ∩ u').Nonempty}
  have := hfin.fintype
  have : CMDiffAt[u ∩ u'] n (T% (fun x ↦ (∑ i ∈ s, (t i x)))) x₀ :=
    .sum_section fun i hi ↦ ((ht' i).mono Set.inter_subset_left)
  apply (contMDiffWithinAt_inter hu').mp
  apply this.congr fun y hy ↦ ?_
  · rw [TotalSpace.mk_inj, tsum_eq_sum']
    refine support_subset_iff'.mpr fun i hi ↦ ?_
    by_contra! h
    have : i ∈ s.toFinset := by
      refine Set.mem_toFinset.mpr ?_
      simp only [s, ne_eq, Set.mem_ofPred_eq]
      use x₀
      simpa using ⟨h, mem_of_mem_nhds hu'⟩
    exact hi this
  rw [TotalSpace.mk_inj, tsum_eq_sum']
  refine support_subset_iff'.mpr fun i hi ↦ ?_
  by_contra! h
  have : i ∈ s.toFinset := by
    refine Set.mem_toFinset.mpr ?_
    simp only [s, ne_eq, Set.mem_ofPred_eq]
    use y
    simpa using ⟨h, Set.mem_of_mem_inter_right hy⟩
  exact hi this

/-- The sum of a locally finite collection of sections is `C^k` at `x` iff each section is. -/
/-
**ContMDiffAt.sum_section_of_locallyFinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffAt.sum_section_of_locallyFinite (ht : LocallyFinite fun i => {x :
 M | t i x != 0}) (ht' : forall i, CMDiffAt n (T% (t i ·)) x₀) : CMDiffAt n (T% 
(fun x => (∑' i, (t i x)))) x₀
参数：ht : LocallyFinite fun i => {x : M | t i x != 0}；ht' : forall i, CMDiffAt n (
T% (t i ·)) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffWithinAt.sum_section_of_locallyFinite`：ContMDiffWithinAt.sum_se
ction_of_locallyFinite (ht : LocallyFinite fun i => {x : M | t i x != 0}) (ht' :
 forall i, CMDiffAt[u] n (T% (t i ·)…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
The sum of a locally finite collection of sections is `C^k` at `x` iff each sect
ion is.
-/
lemma ContMDiffAt.sum_section_of_locallyFinite (ht : LocallyFinite fun i ↦ {x : M | t i x ≠ 0})
    (ht' : ∀ i, CMDiffAt n (T% (t i ·)) x₀) :
    CMDiffAt n (T% (fun x ↦ (∑' i, (t i x)))) x₀ := by
  simp_rw [← contMDiffWithinAt_univ] at ht' ⊢
  exact .sum_section_of_locallyFinite ht ht'

/-- The sum of a locally finite collection of sections is `C^k` on a set `u` iff each section is. -/
/-
**ContMDiffOn.sum_section_of_locallyFinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffOn.sum_section_of_locallyFinite (ht : LocallyFinite fun i => {x :
 M | t i x != 0}) (ht' : forall i, CMDiff[u] n (T% (t i ·))) : CMDiff[u] n (T% (
fun x => ∑' i, (t i x)))
参数：ht : LocallyFinite fun i => {x : M | t i x != 0}；ht' : forall i, CMDiff[u] n 
(T% (t i ·))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffWithinAt.sum_section_of_locallyFinite`：ContMDiffWithinAt.sum_se
ction_of_locallyFinite (ht : LocallyFinite fun i => {x : M | t i x != 0}) (ht' :
 forall i, CMDiffAt[u] n (T% (t i ·)…

--- 原说明 ---
The sum of a locally finite collection of sections is `C^k` on a set `u` iff eac
h section is.
-/
lemma ContMDiffOn.sum_section_of_locallyFinite (ht : LocallyFinite fun i ↦ {x : M | t i x ≠ 0})
    (ht' : ∀ i, CMDiff[u] n (T% (t i ·))) :
    CMDiff[u] n (T% (fun x ↦ ∑' i, (t i x))) :=
  fun x hx ↦ .sum_section_of_locallyFinite ht (ht' · x hx)

/-- The sum of a locally finite collection of sections is `C^k` iff each section is. -/
/-
**ContMDiff.sum_section_of_locallyFinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.sum_section_of_locallyFinite (ht : LocallyFinite fun i => {x : M
 | t i x != 0}) (ht' : forall i, CMDiff n (T% (t i ·))) : CMDiff n (T% (fun x =>
 ∑' i, (t i x)))
参数：ht : LocallyFinite fun i => {x : M | t i x != 0}；ht' : forall i, CMDiff n (T%
 (t i ·))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffAt.sum_section_of_locallyFinite`：ContMDiffAt.sum_section_of_loc
allyFinite (ht : LocallyFinite fun i => {x : M | t i x != 0}) (ht' : forall i, C
MDiffAt n (T% (t i ·)) x₀) : C…

--- 原说明 ---
The sum of a locally finite collection of sections is `C^k` iff each section is.
-/
lemma ContMDiff.sum_section_of_locallyFinite (ht : LocallyFinite fun i ↦ {x : M | t i x ≠ 0})
    (ht' : ∀ i, CMDiff n (T% (t i ·))) :
    CMDiff n (T% (fun x ↦ ∑' i, (t i x))) :=
  fun x ↦ .sum_section_of_locallyFinite ht fun i ↦ ht' i x

-- Future: the next four lemmas can presumably be generalised, but some hypotheses on the supports
-- of the sections `t i` are necessary.
/-
**ContMDiffWithinAt.finsum_section_of_locallyFinite** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：ContMDiffWithinAt.finsum_section_of_locallyFinite (ht : LocallyFinite fun 
i => {x : M | t i x != 0}) (ht' : forall i, CMDiffAt[u] n (T% (t i ·)) x₀) : CMD
iffAt[u] n (T% (fun x => ∑ᶠ i, t i x)) x₀
参数：ht : LocallyFinite fun i => {x : M | t i x != 0}；ht' : forall i, CMDiffAt[u] 
n (T% (t i ·)) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.congr'`：ContMDiffWithinAt.congr' (h : ContMDiffWithinA
t I I' n f s x) (h₁ : forall y in t, f₁ y = f y) (hst : s subseteq t) (hxt : x i
n t) : ContMDi…
· 使用引理 `ContMDiffWithinAt.sum_section_of_locallyFinite`：ContMDiffWithinAt.sum_se
ction_of_locallyFinite (ht : LocallyFinite fun i => {x : M | t i x != 0}) (ht' :
 forall i, CMDiffAt[u] n (T% (t i ·)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsum_eq_finsum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [L.LeAtTop]
, Fu…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `trivial`：True
-/
lemma ContMDiffWithinAt.finsum_section_of_locallyFinite
    (ht : LocallyFinite fun i ↦ {x : M | t i x ≠ 0})
    (ht' : ∀ i, CMDiffAt[u] n (T% (t i ·)) x₀) :
    CMDiffAt[u] n (T% (fun x ↦ ∑ᶠ i, t i x)) x₀ := by
  apply (ContMDiffWithinAt.sum_section_of_locallyFinite ht ht').congr' (t := Set.univ)
      (fun y hy ↦ ?_) (by grind) trivial
  rw [← tsum_eq_finsum (L := SummationFilter.unconditional ι)]
  choose U hu hfin using ht y
  have : {x | t x y ≠ 0} ⊆ {i | ((fun i ↦ {x | t i x ≠ 0}) i ∩ U).Nonempty} := by
    intro x hx
    rw [Set.mem_ofPred] at hx ⊢
    use y
    simpa using ⟨hx, mem_of_mem_nhds hu⟩
  exact Set.Finite.subset hfin this
/-
**ContMDiffAt.finsum_section_of_locallyFinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffAt.finsum_section_of_locallyFinite (ht : LocallyFinite fun i => {
x : M | t i x != 0}) (ht' : forall i, CMDiffAt n (T% (t i ·)) x₀) : CMDiffAt n (
T% (fun x => ∑ᶠ i, t i x)) x₀
参数：ht : LocallyFinite fun i => {x : M | t i x != 0}；ht' : forall i, CMDiffAt n (
T% (t i ·)) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffWithinAt.finsum_section_of_locallyFinite`：ContMDiffWithinAt.fin
sum_section_of_locallyFinite (ht : LocallyFinite fun i => {x : M | t i x != 0}) 
(ht' : forall i, CMDiffAt[u] n (T% (t i…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma ContMDiffAt.finsum_section_of_locallyFinite
    (ht : LocallyFinite fun i ↦ {x : M | t i x ≠ 0})
    (ht' : ∀ i, CMDiffAt n (T% (t i ·)) x₀) :
    CMDiffAt n (T% (fun x ↦ ∑ᶠ i, t i x)) x₀ := by
  simp_rw [← contMDiffWithinAt_univ] at ht' ⊢
  exact .finsum_section_of_locallyFinite ht ht'
/-
**ContMDiffOn.finsum_section_of_locallyFinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffOn.finsum_section_of_locallyFinite (ht : LocallyFinite fun i => {
x : M | t i x != 0}) (ht' : forall i, CMDiff[u] n (T% (t i ·))) : CMDiff[u] n (T
% (fun x => ∑ᶠ i, t i x))
参数：ht : LocallyFinite fun i => {x : M | t i x != 0}；ht' : forall i, CMDiff[u] n 
(T% (t i ·))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffWithinAt.finsum_section_of_locallyFinite`：ContMDiffWithinAt.fin
sum_section_of_locallyFinite (ht : LocallyFinite fun i => {x : M | t i x != 0}) 
(ht' : forall i, CMDiffAt[u] n (T% (t i…
-/
lemma ContMDiffOn.finsum_section_of_locallyFinite
    (ht : LocallyFinite fun i ↦ {x : M | t i x ≠ 0})
    (ht' : ∀ i, CMDiff[u] n (T% (t i ·))) :
    CMDiff[u] n (T% (fun x ↦ ∑ᶠ i, t i x)) :=
  fun x hx ↦ .finsum_section_of_locallyFinite ht fun i ↦ ht' i x hx
/-
**ContMDiff.finsum_section_of_locallyFinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.finsum_section_of_locallyFinite (ht : LocallyFinite fun i => {x 
: M | t i x != 0}) (ht' : forall i, CMDiff n (T% (t i ·))) : CMDiff n (T% (fun x
 => ∑ᶠ i, t i x))
参数：ht : LocallyFinite fun i => {x : M | t i x != 0}；ht' : forall i, CMDiff n (T%
 (t i ·))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffAt.finsum_section_of_locallyFinite`：ContMDiffAt.finsum_section_
of_locallyFinite (ht : LocallyFinite fun i => {x : M | t i x != 0}) (ht' : foral
l i, CMDiffAt n (T% (t i ·)) x₀) …
-/
lemma ContMDiff.finsum_section_of_locallyFinite (ht : LocallyFinite fun i ↦ {x : M | t i x ≠ 0})
    (ht' : ∀ i, CMDiff n (T% (t i ·))) :
    CMDiff n (T% (fun x ↦ ∑ᶠ i, t i x)) :=
  fun x ↦ .finsum_section_of_locallyFinite ht fun i ↦ ht' i x

end operations

/-- Bundled `n` times continuously differentiable sections of a vector bundle.
Denoted as `Cₛ^n⟮I; F, V⟯` within the `Manifold` namespace. -/
/-
**ContMDiffSection** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {H : Type u_3} →             [inst_3 : TopologicalSpace H] →          
     ModelWithCorners 𝕜 E H →                 {M : Type u_4} →                  
 [inst_4 : TopologicalSpace M] →                     [ChartedSpace H M] →       
                (F : Type u_5) →                         [inst_6 : NormedAddComm
Group F] →                           [NormedSpace 𝕜 F] →                        
     WithTop ℕ∞ →                               (V : M → Type u_6) →            
                     [inst : TopologicalSpace (Bundle.TotalSpace F V)] →        
                           [inst_7 : (x : M) → TopologicalSpace (V x)] → [FiberB
undle F V] → Type (max u_4 u_6)
参数：F : Type u_5；V : M → Type u_6；Bundle.TotalSpace F V；x : M；V x；max u_4 u_6。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundled `n` times continuously differentiable sections of a vector bundle.
Denoted as `Cₛ^n⟮I; F, V⟯` within the `Manifold` namespace.
-/
structure ContMDiffSection where
  /-- the underlying function of this section -/
  protected toFun : ∀ x, V x
  /-- proof that this section is `C^n` -/
  protected contMDiff_toFun : CMDiff n (T% toFun)

@[inherit_doc] scoped[Manifold] notation "Cₛ^" n "⟮" I "; " F ", " V "⟯" => ContMDiffSection I F n V

namespace ContMDiffSection

variable {I} {n} {F} {V}

/-
**ContMDiffSection.** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffSection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DFunLike Cₛ^n⟮I; F, V⟯ M V where
  coe := ContMDiffSection.toFun
  coe_injective := by rintro ⟨⟩ ⟨⟩ h; congr

variable {s t : Cₛ^n⟮I; F, V⟯}

@[simp]
/-
**ContMDiffSection.coeFn_mk** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffSection`。
形式化陈述：coeFn_mk (s : forall x, V x) (hs : CMDiff n (T% s)) : (mk s hs : forall x,
 V x) = s
参数：s : forall x, V x；hs : CMDiff n (T% s)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_mk (s : ∀ x, V x) (hs : CMDiff n (T% s)) : (mk s hs : ∀ x, V x) = s := rfl
/-
**ContMDiffSection.contMDiff** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffSection`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {F : Type u_5} [inst_6 : NormedAddCom
mGroup F]   [inst_7 : NormedSpace 𝕜 F] {n : WithTop ℕ∞} {V : M → Type u_6} [inst
_8 : TopologicalSpace (Bundle.TotalSpace F V)]   [inst_9 : (x : M) → Topological
Space (V x)] [inst_10 : FiberBundle F V] (s : ContMDiffSection I F n V),   ContM
Diff I (I.prod (modelWithCornersSelf 𝕜 F)) n fun x => ⟨x, s x⟩
参数：Bundle.TotalSpace F V；x : M；V x；s : ContMDiffSection I F n V；I.prod (modelWit
hCornersSelf 𝕜 F)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffSection.contMDiff_toFun`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
-/
protected theorem contMDiff (s : Cₛ^n⟮I; F, V⟯) : CMDiff n (T% fun x ↦ s x) :=
  s.contMDiff_toFun
/-
**ContMDiffSection.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffSection`。
形式化陈述：coe_inj ⦃s t : Cₛ^n⟮I; F, V⟯⦄ (h : (s : forall x, V x) = t) : s = t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem coe_inj ⦃s t : Cₛ^n⟮I; F, V⟯⦄ (h : (s : ∀ x, V x) = t) : s = t :=
  DFunLike.ext' h
/-
**ContMDiffSection.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffSection`。
形式化陈述：coe_injective : Injective ((↑) : Cₛ^n⟮I; F, V⟯ -> forall x, V x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffSection.coe_inj`：coe_inj ⦃s t : Cₛ^n⟮I; F, V⟯⦄ (h : (s : forall
 x, V x) = t) : s = t
-/
theorem coe_injective : Injective ((↑) : Cₛ^n⟮I; F, V⟯ → ∀ x, V x) :=
  coe_inj

@[ext]
/-
**ContMDiffSection.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffSection`。
形式化陈述：ext (h : forall x, s x = t x) : s = t
参数：h : forall x, s x = t x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext (h : ∀ x, s x = t x) : s = t := DFunLike.ext _ _ h

section
variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

/-
**ContMDiffSection.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffSection`。
形式化陈述：instAdd : Add Cₛ^n⟮I; F, V⟯
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd : Add Cₛ^n⟮I; F, V⟯ :=
  ⟨fun s t ↦ ⟨s + t, s.contMDiff.add_section t.contMDiff⟩⟩

@[simp]
/-
**ContMDiffSection.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffSection`。
形式化陈述：coe_add (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s + t) = ⇑s + t
参数：s t : Cₛ^n⟮I; F, V⟯。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s + t) = ⇑s + t :=
  rfl
/-
**ContMDiffSection.instSub** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffSection`。
形式化陈述：instSub : Sub Cₛ^n⟮I; F, V⟯
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSub : Sub Cₛ^n⟮I; F, V⟯ :=
  ⟨fun s t ↦ ⟨s - t, s.contMDiff.sub_section t.contMDiff⟩⟩

@[simp]
/-
**ContMDiffSection.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffSection`。
形式化陈述：coe_sub (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s - t) = s - t
参数：s t : Cₛ^n⟮I; F, V⟯。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s - t) = s - t :=
  rfl
/-
**ContMDiffSection.instZero** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffSection`。
形式化陈述：instZero : Zero Cₛ^n⟮I; F, V⟯
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero : Zero Cₛ^n⟮I; F, V⟯ :=
  ⟨⟨fun _ => 0, (contMDiff_zeroSection 𝕜 V).of_le le_top⟩⟩
/-
**ContMDiffSection.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffSection`。
形式化陈述：inhabited : Inhabited Cₛ^n⟮I; F, V⟯
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited : Inhabited Cₛ^n⟮I; F, V⟯ :=
  ⟨0⟩

@[simp]
/-
**ContMDiffSection.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffSection`。
形式化陈述：coe_zero : ⇑(0 : Cₛ^n⟮I; F, V⟯) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ⇑(0 : Cₛ^n⟮I; F, V⟯) = 0 :=
  rfl
/-
**ContMDiffSection.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffSection`。
形式化陈述：instNeg : Neg Cₛ^n⟮I; F, V⟯
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNeg : Neg Cₛ^n⟮I; F, V⟯ :=
  ⟨fun s ↦ ⟨-s, s.contMDiff.neg_section⟩⟩

@[simp]
/-
**ContMDiffSection.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffSection`。
形式化陈述：coe_neg (s : Cₛ^n⟮I; F, V⟯) : ⇑(-s : Cₛ^n⟮I; F, V⟯) = -s
参数：s : Cₛ^n⟮I; F, V⟯。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg (s : Cₛ^n⟮I; F, V⟯) : ⇑(-s : Cₛ^n⟮I; F, V⟯) = -s :=
  rfl
/-
**ContMDiffSection.instNSMul** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffSection`。
形式化陈述：instNSMul : SMul Nat Cₛ^n⟮I; F, V⟯
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNSMul : SMul ℕ Cₛ^n⟮I; F, V⟯ :=
  ⟨nsmulRec⟩

@[simp]
/-
**ContMDiffSection.coe_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffSection`。
形式化陈述：coe_nsmul (s : Cₛ^n⟮I; F, V⟯) (k : Nat) : ⇑(k • s : Cₛ^n⟮I; F, V⟯) = k • ⇑
s
参数：s : Cₛ^n⟮I; F, V⟯；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coe_nsmul (s : Cₛ^n⟮I; F, V⟯) (k : ℕ) : ⇑(k • s : Cₛ^n⟮I; F, V⟯) = k • ⇑s := by
  induction k with
  | zero => simp_rw [zero_smul]; rfl
  | succ k ih => simp_rw [succ_nsmul, ← ih]; rfl
/-
**ContMDiffSection.instZSMul** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffSection`。
形式化陈述：instZSMul : SMul Int Cₛ^n⟮I; F, V⟯
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZSMul : SMul ℤ Cₛ^n⟮I; F, V⟯ :=
  ⟨zsmulRec⟩

@[simp]
/-
**ContMDiffSection.coe_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffSection`。
形式化陈述：coe_zsmul (s : Cₛ^n⟮I; F, V⟯) (z : Int) : ⇑(z • s : Cₛ^n⟮I; F, V⟯) = z • ⇑
s
参数：s : Cₛ^n⟮I; F, V⟯；z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContMDiffSection.coe_nsmul`：coe_nsmul (s : Cₛ^n⟮I; F, V⟯) (k : Nat) : ⇑(
k • s : Cₛ^n⟮I; F, V⟯) = k • ⇑s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `negSucc_zsmul`：negSucc_zsmul {G} [SubNegMonoid G] (a : G) (n : Nat) : In
t.negSucc n • a = -((n + 1) • a)
-/
theorem coe_zsmul (s : Cₛ^n⟮I; F, V⟯) (z : ℤ) : ⇑(z • s : Cₛ^n⟮I; F, V⟯) = z • ⇑s := by
  rcases z with n | n
  · refine (coe_nsmul s n).trans ?_
    simp only [Int.ofNat_eq_natCast, natCast_zsmul]
  · refine (congr_arg Neg.neg (coe_nsmul s (n + 1))).trans ?_
    simp only [negSucc_zsmul]
/-
**ContMDiffSection.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffSection`
。
形式化陈述：instAddCommGroup : AddCommGroup Cₛ^n⟮I; F, V⟯
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffSection.coe_injective`：coe_injective : Injective ((↑) : Cₛ^n⟮I;
 F, V⟯ -> forall x, V x)
· 使用定理 `ContMDiffSection.coe_zero`：coe_zero : ⇑(0 : Cₛ^n⟮I; F, V⟯) = 0
· 使用定理 `ContMDiffSection.coe_add`：coe_add (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s + t) = ⇑s 
+ t
· 使用定理 `ContMDiffSection.coe_neg`：coe_neg (s : Cₛ^n⟮I; F, V⟯) : ⇑(-s : Cₛ^n⟮I; F
, V⟯) = -s
· 使用定理 `ContMDiffSection.coe_sub`：coe_sub (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s - t) = s -
 t
· 使用定理 `ContMDiffSection.coe_nsmul`：coe_nsmul (s : Cₛ^n⟮I; F, V⟯) (k : Nat) : ⇑(
k • s : Cₛ^n⟮I; F, V⟯) = k • ⇑s
· 使用定理 `ContMDiffSection.coe_zsmul`：coe_zsmul (s : Cₛ^n⟮I; F, V⟯) (z : Int) : ⇑(
z • s : Cₛ^n⟮I; F, V⟯) = z • ⇑s
-/
instance instAddCommGroup : AddCommGroup Cₛ^n⟮I; F, V⟯ :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul
/-
**ContMDiffSection.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffSection`。
形式化陈述：instSMul : SMul 𝕜 Cₛ^n⟮I; F, V⟯
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul : SMul 𝕜 Cₛ^n⟮I; F, V⟯ :=
  ⟨fun c s ↦ ⟨c • ⇑s, s.contMDiff.const_smul_section⟩⟩

@[simp]
/-
**ContMDiffSection.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffSection`。
形式化陈述：coe_smul (r : 𝕜) (s : Cₛ^n⟮I; F, V⟯) : ⇑(r • s : Cₛ^n⟮I; F, V⟯) = r • ⇑s
参数：r : 𝕜；s : Cₛ^n⟮I; F, V⟯。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul (r : 𝕜) (s : Cₛ^n⟮I; F, V⟯) : ⇑(r • s : Cₛ^n⟮I; F, V⟯) = r • ⇑s :=
  rfl

variable (I F V n) in
/-- The additive morphism from `C^n` sections to dependent maps. -/
/-
**ContMDiffSection.coeAddHom** 是 Mathlib 中的一个定义，位于命名空间 `ContMDiffSection`。
形式化陈述：coeAddHom : Cₛ^n⟮I; F, V⟯ ->+ forall x, V x where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffSection.coe_zero`：coe_zero : ⇑(0 : Cₛ^n⟮I; F, V⟯) = 0
· 使用定理 `ContMDiffSection.coe_add`：coe_add (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s + t) = ⇑s 
+ t

--- 原说明 ---
The additive morphism from `C^n` sections to dependent maps.
-/
def coeAddHom : Cₛ^n⟮I; F, V⟯ →+ ∀ x, V x where
  toFun := (↑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
/-
**ContMDiffSection.coeAddHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffSection`。
形式化陈述：coeAddHom_apply (s : Cₛ^n⟮I; F, V⟯) : coeAddHom I F n V s = s
参数：s : Cₛ^n⟮I; F, V⟯。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeAddHom_apply (s : Cₛ^n⟮I; F, V⟯) : coeAddHom I F n V s = s := rfl
/-
**ContMDiffSection.instModule** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffSection`。
形式化陈述：instModule : Module 𝕜 Cₛ^n⟮I; F, V⟯
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffSection.coe_injective`：coe_injective : Injective ((↑) : Cₛ^n⟮I;
 F, V⟯ -> forall x, V x)
· 使用定理 `ContMDiffSection.coe_smul`：coe_smul (r : 𝕜) (s : Cₛ^n⟮I; F, V⟯) : ⇑(r • 
s : Cₛ^n⟮I; F, V⟯) = r • ⇑s
-/
instance instModule : Module 𝕜 Cₛ^n⟮I; F, V⟯ :=
  coe_injective.module 𝕜 (coeAddHom I F n V) coe_smul

end

/-
**ContMDiffSection.mdifferentiable'** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffSection`
。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {F : Type u_5} [inst_6 : NormedAddCom
mGroup F]   [inst_7 : NormedSpace 𝕜 F] {n : WithTop ℕ∞} {V : M → Type u_6} [inst
_8 : TopologicalSpace (Bundle.TotalSpace F V)]   [inst_9 : (x : M) → Topological
Space (V x)] [inst_10 : FiberBundle F V] (s : ContMDiffSection I F n V),   n ≠ 0
 → MDiff fun x => ⟨x, s x⟩
参数：Bundle.TotalSpace F V；x : M；V x；s : ContMDiffSection I F n V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.mdifferentiable`：ContMDiff.mdifferentiable (hf : CMDiff n f) (
hn : n != 0) : MDiff f
· 使用定理 `ContMDiffSection.contMDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
-/
protected theorem mdifferentiable' (s : Cₛ^n⟮I; F, V⟯) (hn : n ≠ 0) : MDiff (T% fun x ↦ s x) :=
  s.contMDiff.mdifferentiable hn
/-
**ContMDiffSection.mdifferentiable** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffSection`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {F : Type u_5} [inst_6 : NormedAddCom
mGroup F]   [inst_7 : NormedSpace 𝕜 F] {V : M → Type u_6} [inst_8 : TopologicalS
pace (Bundle.TotalSpace F V)]   [inst_9 : (x : M) → TopologicalSpace (V x)] [ins
t_10 : FiberBundle F V] (s : ContMDiffSection I F (↑⊤) V),   MDiff fun x => ⟨x, 
s x⟩
参数：Bundle.TotalSpace F V；x : M；V x；s : ContMDiffSection I F (↑⊤) V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.mdifferentiable`：ContMDiff.mdifferentiable (hf : CMDiff n f) (
hn : n != 0) : MDiff f
· 使用定理 `ContMDiffSection.contMDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
protected theorem mdifferentiable (s : Cₛ^∞⟮I; F, V⟯) : MDiff (T% fun x ↦ s x) :=
  s.contMDiff.mdifferentiable (by simp)
/-
**ContMDiffSection.mdifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffSection
`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {F : Type u_5} [inst_6 : NormedAddCom
mGroup F]   [inst_7 : NormedSpace 𝕜 F] {V : M → Type u_6} [inst_8 : TopologicalS
pace (Bundle.TotalSpace F V)]   [inst_9 : (x : M) → TopologicalSpace (V x)] [ins
t_10 : FiberBundle F V] (s : ContMDiffSection I F (↑⊤) V) {x : M},   (MDiffAt fu
n x => ⟨x, s x⟩) x
参数：Bundle.TotalSpace F V；x : M；V x；s : ContMDiffSection I F (↑⊤) V；MDiffAt fun x
 => ⟨x, s x⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffSection.mdifferentiable`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
-/
protected theorem mdifferentiableAt (s : Cₛ^∞⟮I; F, V⟯) {x} : MDiffAt (T% fun x ↦ s x) x :=
  s.mdifferentiable x

end ContMDiffSection

