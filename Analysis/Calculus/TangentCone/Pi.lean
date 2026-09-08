/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Indexed product of sets with unique differentiability property

In this file we prove that the indexed product
of a family sets with unique differentiability property
has the same property, see `UniqueDiffOn.pi` and  `UniqueDiffOn.univ_pi`.
-/

public section

open Filter Set
open scoped Topology

section Semiring

variable {𝕜 : Type*} [Semiring 𝕜]
  {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [∀ i, TopologicalSpace (E i)] [∀ i, ContinuousAdd (E i)] [∀ i, ContinuousConstSMul 𝕜 (E i)]
  {s : ∀ i, Set (E i)} {x : ∀ i, E i}

/-- The tangent cone of a product contains the tangent cone of each factor. -/
/-
**mapsTo_tangentConeAt_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapsTo_tangentConeAt_pi [DecidableEq ι] {i : ι} (hi : forall j != i, x j i
n closure (s j)) : MapsTo (Pi.single i) (tangentConeAt 𝕜 (s i) (x i)) (tangentCo
neAt 𝕜 (Set.pi univ s) x)
参数：hi : forall j != i, x j in closure (s j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tangentConeAt_closure`：tangentConeAt_closure : tangentConeAt 𝕜 (closure 
s) x = tangentConeAt 𝕜 s x
· 使用定理 `Pi.continuousAdd`：∀ {ι : Type u_1} {C : ι → Type u_6} [inst : (i : ι) → 
TopologicalSpace (C i)] [inst_1 : (i : ι) → Add (C i)]   [∀ (i : ι), ContinuousA
dd (C …
· 使用定理 `instContinuousConstSMulForall`：∀ {M : Type u_1} {ι : Type u_4} {γ : ι → 
Type u_5} [inst : (i : ι) → TopologicalSpace (γ i)]   [inst_1 : (i : ι) → SMul M
 (γ i)] [∀ (i : ι),…
· 使用定理 `exists_fun_of_mem_tangentConeAt`：exists_fun_of_mem_tangentConeAt (h : y 
in tangentConeAt R s x) : exists (α : Type (max u v)) (l : Filter α) (_hl : l.Ne
Bot) (c : α -> R) (d …
· 使用定理 `mem_tangentConeAt_of_seq`：mem_tangentConeAt_of_seq {α : Type*} (l : Filt
er α) [l.NeBot] (c : α -> R) (d : α -> E) (hd₀ : Tendsto d l (𝓝 0)) (hds : foral
lᶠ n in l, x +…
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `closure_pi_set`：closure_pi_set {ι : Type*} {α : ι -> Type*} [forall i, T
opologicalSpace (α i)] (I : Set ι) (s : forall i, Set (α i)) : closure (pi I s) 
= pi…
· 使用定理 `Set.mem_univ_pi`：mem_univ_pi : f in pi univ t ↔ forall i, f i in t i
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0

--- 原说明 ---
The tangent cone of a product contains the tangent cone of each factor.
-/
theorem mapsTo_tangentConeAt_pi [DecidableEq ι] {i : ι} (hi : ∀ j ≠ i, x j ∈ closure (s j)) :
    MapsTo (Pi.single i) (tangentConeAt 𝕜 (s i) (x i)) (tangentConeAt 𝕜 (Set.pi univ s) x) := by
  rw [← tangentConeAt_closure (s := .pi _ _)]
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  apply mem_tangentConeAt_of_seq l c (fun n ↦ Pi.single i (d n))
  · rw [tendsto_pi_nhds]
    intro j
    rcases eq_or_ne j i with rfl | hj <;> simp [*, tendsto_const_nhds]
  · refine hds.mono fun n hn ↦ ?_
    rw [closure_pi_set, mem_univ_pi]
    intro j
    rcases eq_or_ne j i with rfl | hj <;> simp [*, subset_closure hn]
  · rw [tendsto_pi_nhds]
    intro j
    rcases eq_or_ne j i with rfl | hj <;> simp [*, tendsto_const_nhds]
/-
**UniqueDiffWithinAt.univ_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffWithinAt.univ_pi {s : forall i, Set (E i)} {x : forall i, E i} (
h : forall i, UniqueDiffWithinAt 𝕜 (s i) (x i)) : UniqueDiffWithinAt 𝕜 (Set.pi u
niv s) x
参数：E i；h : forall i, UniqueDiffWithinAt 𝕜 (s i) (x i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `closure_pi_set`：closure_pi_set {ι : Type*} {α : ι -> Type*} [forall i, T
opologicalSpace (α i)] (I : Set ι) (s : forall i, Set (α i)) : closure (pi I s) 
= pi…
· 使用定理 `Dense.of_closure`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense (closure s) → Dense s
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `SetLike.coe_mono`：coe_mono : Monotone (SetLike.coe : A -> Set B)
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `mapsTo_tangentConeAt_pi`：mapsTo_tangentConeAt_pi [DecidableEq ι] {i : ι}
 (hi : forall j != i, x j in closure (s j)) : MapsTo (Pi.single i) (tangentConeA
t 𝕜 (s i) (x …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Dense.closure`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}, D
ense s → Dense (closure s)
· 使用定理 `dense_pi`：dense_pi {ι : Type*} {α : ι -> Type*} [forall i, TopologicalSp
ace (α i)] {s : forall i, Set (α i)} (I : Set ι) (hs : forall i in I, Dense (s…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem UniqueDiffWithinAt.univ_pi {s : ∀ i, Set (E i)} {x : ∀ i, E i}
    (h : ∀ i, UniqueDiffWithinAt 𝕜 (s i) (x i)) : UniqueDiffWithinAt 𝕜 (Set.pi univ s) x := by
  classical
  simp only [uniqueDiffWithinAt_iff, closure_pi_set] at h ⊢
  refine ⟨.of_closure <| (dense_pi univ fun i _ ↦ (h i).1).closure.mono ?_, fun i _ => (h i).2⟩
  simp only [closure_pi_set, ← Submodule.closure_coe_iSup_map_single, Submodule.map_span]
  gcongr
  refine iSup_le fun i ↦ ?_
  gcongr
  exact mapsTo_tangentConeAt_pi (fun j _ ↦ (h j).2) |>.image_subset

/-- The product of a family of sets of unique differentiability is a set of unique
differentiability. -/
/-
**UniqueDiffOn.univ_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffOn.univ_pi {s : forall i, Set (E i)} (h : forall i, UniqueDiffOn
 𝕜 (s i)) : UniqueDiffOn 𝕜 (Set.pi univ s)
参数：E i；h : forall i, UniqueDiffOn 𝕜 (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffWithinAt.univ_pi`：UniqueDiffWithinAt.univ_pi {s : forall i, Se
t (E i)} {x : forall i, E i} (h : forall i, UniqueDiffWithinAt 𝕜 (s i) (x i)) : 
UniqueDiffWithin…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The product of a family of sets of unique differentiability is a set of unique
differentiability.
-/
theorem UniqueDiffOn.univ_pi {s : ∀ i, Set (E i)} (h : ∀ i, UniqueDiffOn 𝕜 (s i)) :
    UniqueDiffOn 𝕜 (Set.pi univ s) :=
  fun _x hx ↦ .univ_pi fun i ↦ h i _ <| hx i (mem_univ i)

end Semiring

variable {𝕜 : Type*} [DivisionSemiring 𝕜]
  {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [TopologicalSpace 𝕜] [(𝓝[≠] (0 : 𝕜)).NeBot]
  [∀ i, TopologicalSpace (E i)] [∀ i, ContinuousAdd (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]
  {s : ∀ i, Set (E i)} {x : ∀ i, E i} {I : Set ι}

/-
**UniqueDiffWithinAt.pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffWithinAt.pi (h : forall i in I, UniqueDiffWithinAt 𝕜 (s i) (x i)
) : UniqueDiffWithinAt 𝕜 (Set.pi I s) x
参数：h : forall i in I, UniqueDiffWithinAt 𝕜 (s i) (x i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_pi_piecewise_univ`：univ_pi_piecewise_univ {ι : Type*} {α : ι ->
 Type*} (s : Set ι) (t : forall i, Set (α i)) [forall x, Decidable (x in s)] : p
i univ (s.piecew…
· 使用定理 `UniqueDiffWithinAt.univ_pi`：UniqueDiffWithinAt.univ_pi {s : forall i, Se
t (E i)} {x : forall i, E i} (h : forall i, UniqueDiffWithinAt 𝕜 (s i) (x i)) : 
UniqueDiffWithin…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem UniqueDiffWithinAt.pi (h : ∀ i ∈ I, UniqueDiffWithinAt 𝕜 (s i) (x i)) :
    UniqueDiffWithinAt 𝕜 (Set.pi I s) x := by
  classical
  rw [← Set.univ_pi_piecewise_univ]
  refine UniqueDiffWithinAt.univ_pi fun i => ?_
  by_cases hi : i ∈ I <;> simp [*, uniqueDiffWithinAt_univ]

/-- The product of a family of sets of unique differentiability is a set of unique
differentiability. -/
/-
**UniqueDiffOn.pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffOn.pi (h : forall i in I, UniqueDiffOn 𝕜 (s i)) : UniqueDiffOn 𝕜
 (Set.pi I s)
参数：h : forall i in I, UniqueDiffOn 𝕜 (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffWithinAt.pi`：UniqueDiffWithinAt.pi (h : forall i in I, UniqueD
iffWithinAt 𝕜 (s i) (x i)) : UniqueDiffWithinAt 𝕜 (Set.pi I s) x

--- 原说明 ---
The product of a family of sets of unique differentiability is a set of unique
differentiability.
-/
theorem UniqueDiffOn.pi (h : ∀ i ∈ I, UniqueDiffOn 𝕜 (s i)) : UniqueDiffOn 𝕜 (Set.pi I s) :=
  fun x hx => UniqueDiffWithinAt.pi fun i hi => h i hi (x i) (hx i hi)
