/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Defs
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.Calculus.TangentCone.Basic

/-!
# Product of sets with unique differentiability property

In this file we prove that the product of two sets with unique differentiability property
has the same property, see `UniqueDiffOn.prod`.
-/

public section

open Filter Set
open scoped Topology

variable {𝕜 E F : Type*} [Semiring 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F] [ContinuousConstSMul 𝕜 F]
  {x : E} {s : Set E} {y : F} {t : Set F}

/-- The tangent cone of a product contains the tangent cone of its left factor. -/
/-
**subset_tangentConeAt_prod_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_tangentConeAt_prod_left (ht : y in closure t) : LinearMap.inl 𝕜 E F
 '' tangentConeAt 𝕜 s x subseteq tangentConeAt 𝕜 (s ×ˢ t) (x, y)
参数：ht : y in closure t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tangentConeAt_closure`：tangentConeAt_closure : tangentConeAt 𝕜 (closure 
s) x = tangentConeAt 𝕜 s x
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `closure_prod_eq`：closure_prod_eq {s : Set X} {t : Set Y} : closure (s ×ˢ
 t) = closure s ×ˢ closure t
· 使用定理 `exists_fun_of_mem_tangentConeAt`：exists_fun_of_mem_tangentConeAt (h : y 
in tangentConeAt R s x) : exists (α : Type (max u v)) (l : Filter α) (_hl : l.Ne
Bot) (c : α -> R) (d …
· 使用定理 `mem_tangentConeAt_of_seq`：mem_tangentConeAt_of_seq {α : Type*} (l : Filt
er α) [l.NeBot] (c : α -> R) (d : α -> E) (hd₀ : Tendsto d l (𝓝 0)) (hds : foral
lᶠ n in l, x +…
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0

--- 原说明 ---
The tangent cone of a product contains the tangent cone of its left factor.
-/
theorem subset_tangentConeAt_prod_left (ht : y ∈ closure t) :
    LinearMap.inl 𝕜 E F '' tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜 (s ×ˢ t) (x, y) := by
  rw [← tangentConeAt_closure (s := s ×ˢ t), closure_prod_eq]
  rintro _ ⟨z, hz, rfl⟩
  rcases exists_fun_of_mem_tangentConeAt hz with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  refine mem_tangentConeAt_of_seq l c (fun n ↦ (d n, 0)) (hd₀.prodMk_nhds tendsto_const_nhds)
    (hds.mono fun n hn ↦ by simp [ht, subset_closure hn]) ?_
  simpa using hcd.prodMk_nhds tendsto_const_nhds

/-- The tangent cone of a product contains the tangent cone of its right factor. -/
/-
**subset_tangentConeAt_prod_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_tangentConeAt_prod_right (hs : x in closure s) : LinearMap.inr 𝕜 E 
F '' tangentConeAt 𝕜 t y subseteq tangentConeAt 𝕜 (s ×ˢ t) (x, y)
参数：hs : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tangentConeAt_closure`：tangentConeAt_closure : tangentConeAt 𝕜 (closure 
s) x = tangentConeAt 𝕜 s x
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `closure_prod_eq`：closure_prod_eq {s : Set X} {t : Set Y} : closure (s ×ˢ
 t) = closure s ×ˢ closure t
· 使用定理 `exists_fun_of_mem_tangentConeAt`：exists_fun_of_mem_tangentConeAt (h : y 
in tangentConeAt R s x) : exists (α : Type (max u v)) (l : Filter α) (_hl : l.Ne
Bot) (c : α -> R) (d …
· 使用定理 `mem_tangentConeAt_of_seq`：mem_tangentConeAt_of_seq {α : Type*} (l : Filt
er α) [l.NeBot] (c : α -> R) (d : α -> E) (hd₀ : Tendsto d l (𝓝 0)) (hds : foral
lᶠ n in l, x +…
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0

--- 原说明 ---
The tangent cone of a product contains the tangent cone of its right factor.
-/
theorem subset_tangentConeAt_prod_right (hs : x ∈ closure s) :
    LinearMap.inr 𝕜 E F '' tangentConeAt 𝕜 t y ⊆ tangentConeAt 𝕜 (s ×ˢ t) (x, y) := by
  rw [← tangentConeAt_closure (s := s ×ˢ t), closure_prod_eq]
  rintro _ ⟨z, hz, rfl⟩
  rcases exists_fun_of_mem_tangentConeAt hz with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  refine mem_tangentConeAt_of_seq l c (fun n ↦ (0, d n)) (tendsto_const_nhds.prodMk_nhds hd₀)
    (hds.mono fun n hn ↦ by simp [hs, subset_closure hn]) ?_
  simpa using tendsto_const_nhds.prodMk_nhds hcd

/-- The product of two sets of unique differentiability at points `x` and `y` has unique
differentiability at `(x, y)`. -/
/-
**UniqueDiffWithinAt.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffWithinAt.prod (hs : UniqueDiffWithinAt 𝕜 s x) (ht : UniqueDiffWi
thinAt 𝕜 t y) : UniqueDiffWithinAt 𝕜 (s ×ˢ t) (x, y)
参数：hs : UniqueDiffWithinAt 𝕜 s x；ht : UniqueDiffWithinAt 𝕜 t y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniqueDiffWithinAt_iff`：∀ (R : Type u) {E : Type v} [inst : Semiring R] 
[inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   [inst_3 : TopologicalSp
ace E] (s : …
· 使用定理 `closure_prod_eq`：closure_prod_eq {s : Set X} {t : Set Y} : closure (s ×ˢ
 t) = closure s ×ˢ closure t
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `subset_tangentConeAt_prod_left`：subset_tangentConeAt_prod_left (ht : y i
n closure t) : LinearMap.inl 𝕜 E F '' tangentConeAt 𝕜 s x subseteq tangentConeAt
 𝕜 (s ×ˢ t) (x, y)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `subset_tangentConeAt_prod_right`：subset_tangentConeAt_prod_right (hs : x
 in closure s) : LinearMap.inr 𝕜 E F '' tangentConeAt 𝕜 t y subseteq tangentCone
At 𝕜 (s ×ˢ t) (x, y)
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `LinearMap.span_inl_union_inr`：span_inl_union_inr {s : Set M} {t : Set M₂
} : span R (inl R M M₂ '' s union inr R M M₂ '' t) = (span R s).prod (span R t)
· 使用定理 `Dense.prod`：Dense.prod {s : Set X} {t : Set Y} (hs : Dense s) (ht : Dens
e t) : Dense (s ×ˢ t)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
The product of two sets of unique differentiability at points `x` and `y` has un
ique
differentiability at `(x, y)`.
-/
theorem UniqueDiffWithinAt.prod (hs : UniqueDiffWithinAt 𝕜 s x)
    (ht : UniqueDiffWithinAt 𝕜 t y) : UniqueDiffWithinAt 𝕜 (s ×ˢ t) (x, y) := by
  rw [uniqueDiffWithinAt_iff] at hs ht ⊢
  rw [closure_prod_eq]
  refine ⟨?_, hs.2, ht.2⟩
  have : _ ≤ Submodule.span 𝕜 (tangentConeAt 𝕜 (s ×ˢ t) (x, y)) := Submodule.span_mono
    (union_subset (subset_tangentConeAt_prod_left ht.2) (subset_tangentConeAt_prod_right hs.2))
  rw [LinearMap.span_inl_union_inr, SetLike.le_def] at this
  exact (hs.1.prod ht.1).mono this

/-- The product of two sets of unique differentiability is a set of unique differentiability. -/
/-
**UniqueDiffOn.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffOn.prod (hs : UniqueDiffOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t) : Unique
DiffOn 𝕜 (s ×ˢ t)
参数：hs : UniqueDiffOn 𝕜 s；ht : UniqueDiffOn 𝕜 t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffWithinAt.prod`：UniqueDiffWithinAt.prod (hs : UniqueDiffWithinA
t 𝕜 s x) (ht : UniqueDiffWithinAt 𝕜 t y) : UniqueDiffWithinAt 𝕜 (s ×ˢ t) (x, y)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The product of two sets of unique differentiability is a set of unique different
iability.
-/
theorem UniqueDiffOn.prod (hs : UniqueDiffOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t) :
    UniqueDiffOn 𝕜 (s ×ˢ t) :=
  fun ⟨x, y⟩ h => UniqueDiffWithinAt.prod (hs x h.1) (ht y h.2)
