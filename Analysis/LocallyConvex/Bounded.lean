/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.GroupTheory.GroupAction.Pointwise
public import Mathlib.Analysis.LocallyConvex.Basic
public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Analysis.Seminorm
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Von Neumann Boundedness

This file defines natural or von Neumann bounded sets and proves elementary properties.

## Main declarations

* `Bornology.IsVonNBounded`: A set `s` is von Neumann-bounded if every neighborhood of zero
  absorbs `s`.
* `Bornology.vonNBornology`: The bornology made of the von Neumann-bounded sets.

## Main results

* `Bornology.IsVonNBounded.of_topologicalSpace_le`: A coarser topology admits more
  von Neumann-bounded sets.
* `Bornology.IsVonNBounded.image`: A continuous linear image of a bounded set is bounded.
* `Bornology.isVonNBounded_iff_smul_tendsto_zero`: Given any sequence `ε` of scalars which tends
  to `𝓝[≠] 0`, we have that a set `S` is bounded if and only if for any sequence `x : ℕ → S`,
  `ε • x` tends to 0. This shows that bounded sets are completely determined by sequences, which is
  the key fact for proving that sequential continuity implies continuity for linear maps defined on
  a bornological space

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

-/

@[expose] public section


variable {𝕜 𝕜' E F ι : Type*}

open Set Filter Function
open scoped Topology Pointwise


namespace Bornology

section SeminormedRing

section Zero

variable (𝕜)
variable [SeminormedRing 𝕜] [SMul 𝕜 E] [Zero E]
variable [TopologicalSpace E]

/-- A set `s` is von Neumann bounded if every neighborhood of 0 absorbs `s`. -/
/-
**Bornology.IsVonNBounded** 是 Mathlib 中的一个定义，位于命名空间 `Bornology`。
形式化陈述：IsVonNBounded (s : Set E) : Prop
参数：s : Set E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is von Neumann bounded if every neighborhood of 0 absorbs `s`.
-/
def IsVonNBounded (s : Set E) : Prop :=
  ∀ ⦃V⦄, V ∈ 𝓝 (0 : E) → Absorbs 𝕜 V s

variable (E)

@[simp]
/-
**Bornology.isVonNBounded_empty** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isVonNBounded_empty : IsVonNBounded 𝕜 (∅ : Set E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Absorbs.empty`：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M] [ins
t_1 : SMul M α] {s : Set α}, Absorbs M s ∅
-/
theorem isVonNBounded_empty : IsVonNBounded 𝕜 (∅ : Set E) := fun _ _ => Absorbs.empty

variable {𝕜 E}
/-
**Bornology.isVonNBounded_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isVonNBounded_iff (s : Set E) : IsVonNBounded 𝕜 s ↔ forall V in 𝓝 (0 : E),
 Absorbs 𝕜 V s
参数：s : Set E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isVonNBounded_iff (s : Set E) : IsVonNBounded 𝕜 s ↔ ∀ V ∈ 𝓝 (0 : E), Absorbs 𝕜 V s :=
  Iff.rfl
/-
**Bornology._root_.Filter.HasBasis.isVonNBounded_iff** 是 Mathlib 中的一个定理，位于命名空间 `
Bornology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.HasBasis.isVonNBounded_iff {q : ι → Prop} {s : ι → Set E} {A : Set E}
    (h : (𝓝 (0 : E)).HasBasis q s) : IsVonNBounded 𝕜 A ↔ ∀ i, q i → Absorbs 𝕜 (s i) A := by
  refine ⟨fun hA i hi => hA (h.mem_of_mem hi), fun hA V hV => ?_⟩
  rcases h.mem_iff.mp hV with ⟨i, hi, hV⟩
  exact (hA i hi).mono_left hV

/-- Subsets of bounded sets are bounded. -/
/-
**Bornology.IsVonNBounded.subset** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsVonNBoun
ded`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : SeminormedRing 𝕜] [inst_1 : SMul 𝕜
 E] [inst_2 : Zero E]   [inst_3 : TopologicalSpace E] {s₁ s₂ : Set E}, s₁ ⊆ s₂ →
 Bornology.IsVonNBounded 𝕜 s₂ → Bornology.IsVonNBounded 𝕜 s₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Absorbs.mono_right`：mono_right (h : Absorbs M s t₁) (ht : t₂ subseteq t₁
) : Absorbs M s t₂

--- 原说明 ---
Subsets of bounded sets are bounded.
-/
theorem IsVonNBounded.subset {s₁ s₂ : Set E} (h : s₁ ⊆ s₂) (hs₂ : IsVonNBounded 𝕜 s₂) :
    IsVonNBounded 𝕜 s₁ := fun _ hV => (hs₂ hV).mono_right h

@[simp]
/-
**Bornology.isVonNBounded_union** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isVonNBounded_union {s t : Set E} : IsVonNBounded 𝕜 (s union t) ↔ IsVonNBo
unded 𝕜 s ∧ IsVonNBounded 𝕜 t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isVonNBounded_union {s t : Set E} :
    IsVonNBounded 𝕜 (s ∪ t) ↔ IsVonNBounded 𝕜 s ∧ IsVonNBounded 𝕜 t := by
  simp only [IsVonNBounded, absorbs_union, forall_and]

/-- The union of two bounded sets is bounded. -/
/-
**Bornology.IsVonNBounded.union** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsVonNBound
ed`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : SeminormedRing 𝕜] [inst_1 : SMul 𝕜
 E] [inst_2 : Zero E]   [inst_3 : TopologicalSpace E] {s₁ s₂ : Set E},   Bornolo
gy.IsVonNBounded 𝕜 s₁ → Bornology.IsVonNBounded 𝕜 s₂ → Bornology.IsVonNBounded 𝕜
 (s₁ ∪ s₂)
参数：s₁ ∪ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bornology.isVonNBounded_union`：isVonNBounded_union {s t : Set E} : IsVon
NBounded 𝕜 (s union t) ↔ IsVonNBounded 𝕜 s ∧ IsVonNBounded 𝕜 t

--- 原说明 ---
The union of two bounded sets is bounded.
-/
theorem IsVonNBounded.union {s₁ s₂ : Set E} (hs₁ : IsVonNBounded 𝕜 s₁) (hs₂ : IsVonNBounded 𝕜 s₂) :
    IsVonNBounded 𝕜 (s₁ ∪ s₂) := isVonNBounded_union.2 ⟨hs₁, hs₂⟩

@[nontriviality]
/-
**Bornology.IsVonNBounded.of_boundedSpace** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.I
sVonNBounded`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : SeminormedRing 𝕜] [inst_1 : SMul 𝕜
 E] [inst_2 : Zero E]   [inst_3 : TopologicalSpace E] [BoundedSpace 𝕜] {s : Set 
E}, Bornology.IsVonNBounded 𝕜 s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Absorbs.of_boundedSpace`：∀ {M : Type u_1} {α : Type u_2} [inst : Bornolo
gy M] [inst_1 : SMul M α] {s t : Set α} [BoundedSpace M], Absorbs M s t
-/
theorem IsVonNBounded.of_boundedSpace [BoundedSpace 𝕜] {s : Set E} : IsVonNBounded 𝕜 s := fun _ _ ↦
  .of_boundedSpace

@[nontriviality]
/-
**Bornology.IsVonNBounded.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.I
sVonNBounded`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : SeminormedRing 𝕜] [inst_1 : SMul 𝕜
 E] [inst_2 : Zero E]   [inst_3 : TopologicalSpace E] [Subsingleton E] {s : Set 
E}, Bornology.IsVonNBounded 𝕜 s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.eq_univ_of_nonempty`：eq_univ_of_nonempty {s : Set α} : s.No
nempty -> s = univ
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
-/
theorem IsVonNBounded.of_subsingleton [Subsingleton E] {s : Set E} : IsVonNBounded 𝕜 s :=
  fun U hU ↦ .of_forall fun c ↦ calc
    s ⊆ univ := subset_univ s
    _ = c • U := .symm <| Subsingleton.eq_univ_of_nonempty <| (Filter.nonempty_of_mem hU).image _

@[simp]
/-
**Bornology.isVonNBounded_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isVonNBounded_iUnion {ι : Sort*} [Finite ι] {s : ι -> Set E} : IsVonNBound
ed 𝕜 (⋃ i, s i) ↔ forall i, IsVonNBounded 𝕜 (s i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isVonNBounded_iUnion {ι : Sort*} [Finite ι] {s : ι → Set E} :
    IsVonNBounded 𝕜 (⋃ i, s i) ↔ ∀ i, IsVonNBounded 𝕜 (s i) := by
  simp only [IsVonNBounded, absorbs_iUnion, @forall_comm ι]
/-
**Bornology.isVonNBounded_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isVonNBounded_biUnion {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι -> Se
t E} : IsVonNBounded 𝕜 (⋃ i in I, s i) ↔ forall i in I, IsVonNBounded 𝕜 (s i)
参数：hI : I.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `Bornology.isVonNBounded_iUnion`：isVonNBounded_iUnion {ι : Sort*} [Finite
 ι] {s : ι -> Set E} : IsVonNBounded 𝕜 (⋃ i, s i) ↔ forall i, IsVonNBounded 𝕜 (s
 i)
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isVonNBounded_biUnion {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι → Set E} :
    IsVonNBounded 𝕜 (⋃ i ∈ I, s i) ↔ ∀ i ∈ I, IsVonNBounded 𝕜 (s i) := by
  have _ := hI.to_subtype
  rw [biUnion_eq_iUnion, isVonNBounded_iUnion, Subtype.forall]
/-
**Bornology.isVonNBounded_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isVonNBounded_sUnion {S : Set (Set E)} (hS : S.Finite) : IsVonNBounded 𝕜 (
⋃₀ S) ↔ forall s in S, IsVonNBounded 𝕜 s
参数：Set E；hS : S.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `Bornology.isVonNBounded_biUnion`：isVonNBounded_biUnion {ι : Type*} {I : 
Set ι} (hI : I.Finite) {s : ι -> Set E} : IsVonNBounded 𝕜 (⋃ i in I, s i) ↔ fora
ll i in I, IsVonNBoun…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isVonNBounded_sUnion {S : Set (Set E)} (hS : S.Finite) :
    IsVonNBounded 𝕜 (⋃₀ S) ↔ ∀ s ∈ S, IsVonNBounded 𝕜 s := by
  rw [sUnion_eq_biUnion, isVonNBounded_biUnion hS]

end Zero

section ContinuousAdd

variable [SeminormedRing 𝕜] [AddZeroClass E] [TopologicalSpace E] [ContinuousAdd E]
  [DistribSMul 𝕜 E] {s t : Set E}

/-
**Bornology.IsVonNBounded.add** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsVonNBounded
`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : SeminormedRing 𝕜] [inst_1 : AddZer
oClass E] [inst_2 : TopologicalSpace E]   [ContinuousAdd E] [inst_4 : DistribSMu
l 𝕜 E] {s t : Set E},   Bornology.IsVonNBounded 𝕜 s → Bornology.IsVonNBounded 𝕜 
t → Bornology.IsVonNBounded 𝕜 (s + t)
参数：s + t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_open_nhds_zero_add_subset`：∀ {M : Type u_3} [inst : TopologicalSp
ace M] [inst_1 : AddZeroClass M] [ContinuousAdd M] {U : Set M},   U ∈ nhds 0 → ∃
 V, IsOpen V ∧ 0 ∈ V ∧…
· 使用引理 `Absorbs.mono_left`：mono_left (h : Absorbs M s₁ t) (hs : s₁ subseteq s₂) 
: Absorbs M s₂ t
· 使用定理 `Absorbs.add`：∀ {M : Type u_1} {E : Type u_2} [inst : Bornology M] {s₁ s₂
 t₁ t₂ : Set E} [inst_1 : AddZeroClass E]   [inst_2 : DistribSMul M E], Absorbs 
M…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
protected theorem IsVonNBounded.add (hs : IsVonNBounded 𝕜 s) (ht : IsVonNBounded 𝕜 t) :
    IsVonNBounded 𝕜 (s + t) := fun U hU ↦ by
  rcases exists_open_nhds_zero_add_subset hU with ⟨V, hVo, hV, hVU⟩
  exact ((hs <| hVo.mem_nhds hV).add (ht <| hVo.mem_nhds hV)).mono_left hVU

end ContinuousAdd

section IsTopologicalAddGroup

variable [SeminormedRing 𝕜] [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [DistribMulAction 𝕜 E] {s t : Set E}

/-
**Bornology.IsVonNBounded.neg** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsVonNBounded
`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : SeminormedRing 𝕜] [inst_1 : AddGro
up E] [inst_2 : TopologicalSpace E]   [IsTopologicalAddGroup E] [inst_4 : Distri
bMulAction 𝕜 E] {s : Set E},   Bornology.IsVonNBounded 𝕜 s → Bornology.IsVonNBou
nded 𝕜 (-s)
参数：-s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Absorbs.neg_neg`：∀ {M : Type u_1} {E : Type u_2} [inst : Monoid M] [inst
_1 : AddGroup E] [inst_2 : DistribMulAction M E]   [inst_3 : Bornology M] {s t :
 Set …
· 使用定理 `neg_mem_nhds_zero`：∀ (G : Type w) [inst : TopologicalSpace G] [inst_1 : 
AddGroup G] [IsTopologicalAddGroup G] {S : Set G},   S ∈ nhds 0 → -S ∈ nhds 0
-/
protected theorem IsVonNBounded.neg (hs : IsVonNBounded 𝕜 s) : IsVonNBounded 𝕜 (-s) := fun U hU ↦ by
  rw [← neg_neg U]
  exact (hs <| neg_mem_nhds_zero _ hU).neg_neg

@[simp]
/-
**Bornology.isVonNBounded_neg** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isVonNBounded_neg : IsVonNBounded 𝕜 (-s) ↔ IsVonNBounded 𝕜 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsVonNBounded.neg`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Sem
inormedRing 𝕜] [inst_1 : AddGroup E] [inst_2 : TopologicalSpace E]   [IsTopologi
calAddGroup E] [i…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem isVonNBounded_neg : IsVonNBounded 𝕜 (-s) ↔ IsVonNBounded 𝕜 s :=
  ⟨fun h ↦ neg_neg s ▸ h.neg, fun h ↦ h.neg⟩

alias ⟨IsVonNBounded.of_neg, _⟩ := isVonNBounded_neg
/-
**Bornology.IsVonNBounded.sub** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsVonNBounded
`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : SeminormedRing 𝕜] [inst_1 : AddGro
up E] [inst_2 : TopologicalSpace E]   [IsTopologicalAddGroup E] [inst_4 : Distri
bMulAction 𝕜 E] {s t : Set E},   Bornology.IsVonNBounded 𝕜 s → Bornology.IsVonNB
ounded 𝕜 t → Bornology.IsVonNBounded 𝕜 (s - t)
参数：s - t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Bornology.IsVonNBounded.add`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Sem
inormedRing 𝕜] [inst_1 : AddZeroClass E] [inst_2 : TopologicalSpace E]   [Contin
uousAdd E] [inst_…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Bornology.IsVonNBounded.neg`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Sem
inormedRing 𝕜] [inst_1 : AddGroup E] [inst_2 : TopologicalSpace E]   [IsTopologi
calAddGroup E] [i…
-/
protected theorem IsVonNBounded.sub (hs : IsVonNBounded 𝕜 s) (ht : IsVonNBounded 𝕜 t) :
    IsVonNBounded 𝕜 (s - t) := by
  rw [sub_eq_add_neg]
  exact hs.add ht.neg

end IsTopologicalAddGroup

end SeminormedRing

section MultipleTopologies

variable [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- If a topology `t'` is coarser than `t`, then any set `s` that is bounded with respect to
`t` is bounded with respect to `t'`. -/
/-
**Bornology.IsVonNBounded.of_topologicalSpace_le** 是 Mathlib 中的一个定理，位于命名空间 `Born
ology.IsVonNBounded`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : SeminormedRing 𝕜] [inst_1 : AddCom
mGroup E] [inst_2 : _root_.Module 𝕜 E]   {t t' : TopologicalSpace E}, t ≤ t' → ∀
 {s : Set E}, Bornology.IsVonNBounded 𝕜 s → Bornology.IsVonNBounded 𝕜 s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iff_nhds`：le_iff_nhds {α : Type*} (t t' : TopologicalSpace α) : t <= 
t' ↔ forall x, @nhds α t x <= @nhds α t' x

--- 原说明 ---
If a topology `t'` is coarser than `t`, then any set `s` that is bounded with re
spect to
`t` is bounded with respect to `t'`.
-/
theorem IsVonNBounded.of_topologicalSpace_le {t t' : TopologicalSpace E} (h : t ≤ t') {s : Set E}
    (hs : @IsVonNBounded 𝕜 E _ _ _ t s) : @IsVonNBounded 𝕜 E _ _ _ t' s := fun _ hV =>
  hs <| (le_iff_nhds t t').mp h 0 hV

end MultipleTopologies

/-
**Bornology.isVonNBounded_iff_tendsto_smallSets_nhds** 是 Mathlib 中的一个引理，位于命名空间 `
Bornology`。
形式化陈述：isVonNBounded_iff_tendsto_smallSets_nhds {𝕜 E : Type*} [NormedDivisionRing
 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] {S : Set E} : IsVonNBound
ed 𝕜 S ↔ Tendsto (· • S : 𝕜 -> Set E) (𝓝 0) (𝓝 0).smallSets
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_smallSets_iff`：tendsto_smallSets_iff {f : α -> Set β} : T
endsto f la lb.smallSets ↔ forall t in lb, forallᶠ x in la, f x subseteq t
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `absorbs_iff_eventually_nhds_zero`：absorbs_iff_eventually_nhds_zero (h₀ :
 0 in s) : Absorbs 𝕜 s t ↔ forallᶠ c : 𝕜 in 𝓝 0, MapsTo (c • ·) t s
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isVonNBounded_iff_tendsto_smallSets_nhds {𝕜 E : Type*} [NormedDivisionRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] {S : Set E} :
    IsVonNBounded 𝕜 S ↔ Tendsto (· • S : 𝕜 → Set E) (𝓝 0) (𝓝 0).smallSets := by
  rw [tendsto_smallSets_iff]
  refine forall₂_congr fun V hV ↦ ?_
  simp only [absorbs_iff_eventually_nhds_zero (mem_of_mem_nhds hV), mapsTo_iff_image_subset,
    image_smul]

alias ⟨IsVonNBounded.tendsto_smallSets_nhds, _⟩ := isVonNBounded_iff_tendsto_smallSets_nhds
/-
**Bornology.isVonNBounded_iff_absorbing_le** 是 Mathlib 中的一个引理，位于命名空间 `Bornology`
。
形式化陈述：isVonNBounded_iff_absorbing_le {𝕜 E : Type*} [NormedDivisionRing 𝕜] [AddCo
mmGroup E] [Module 𝕜 E] [TopologicalSpace E] {S : Set E} : IsVonNBounded 𝕜 S ↔ F
ilter.absorbing 𝕜 S <= 𝓝 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isVonNBounded_iff_absorbing_le {𝕜 E : Type*} [NormedDivisionRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] {S : Set E} :
    IsVonNBounded 𝕜 S ↔ Filter.absorbing 𝕜 S ≤ 𝓝 0 :=
  .rfl
/-
**Bornology.isVonNBounded_pi_iff** 是 Mathlib 中的一个引理，位于命名空间 `Bornology`。
形式化陈述：isVonNBounded_pi_iff {𝕜 ι : Type*} {E : ι -> Type*} [NormedDivisionRing 𝕜]
 [forall i, AddCommGroup (E i)] [forall i, Module 𝕜 (E i)] [forall i, Topologica
lSpace (E i)] {S : Set (forall i, E i)} : IsVonNBounded 𝕜 S ↔ forall i, IsVonNBo
unded 𝕜 (eval i '' S)
参数：E i；E i；E i；forall i, E i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `Filter.smallSets_iInf`：smallSets_iInf {f : ι -> Filter α} : (iInf f).sma
llSets = ⨅ i, (f i).smallSets
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.smallSets_comap_eq_comap_image`：smallSets_comap_eq_comap_image (l
 : Filter β) (f : α -> β) : (comap f l).smallSets = comap (image f) l.smallSets
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isVonNBounded_pi_iff {𝕜 ι : Type*} {E : ι → Type*} [NormedDivisionRing 𝕜]
    [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
    {S : Set (∀ i, E i)} : IsVonNBounded 𝕜 S ↔ ∀ i, IsVonNBounded 𝕜 (eval i '' S) := by
  simp_rw [isVonNBounded_iff_tendsto_smallSets_nhds, nhds_pi, Filter.pi, smallSets_iInf,
    smallSets_comap_eq_comap_image, tendsto_iInf, tendsto_comap_iff, Function.comp_def,
    ← image_smul, image_image, eval, Pi.smul_apply, Pi.zero_apply]

section Image

variable {𝕜₁ 𝕜₂ : Type*} [NormedDivisionRing 𝕜₁] [NormedDivisionRing 𝕜₂] [AddCommGroup E]
  [Module 𝕜₁ E] [AddCommGroup F] [Module 𝕜₂ F] [TopologicalSpace E] [TopologicalSpace F]

/-- A continuous linear image of a bounded set is bounded. -/
/-
**Bornology.IsVonNBounded.image** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsVonNBound
ed`。
形式化陈述：∀ {E : Type u_3} {F : Type u_4} {𝕜₁ : Type u_6} {𝕜₂ : Type u_7} [inst : No
rmedDivisionRing 𝕜₁]   [inst_1 : NormedDivisionRing 𝕜₂] [inst_2 : AddCommGroup E
] [inst_3 : _root_.Module 𝕜₁ E] [inst_4 : AddCommGroup F]   [inst_5 : _root_.Mod
ule 𝕜₂ F] [inst_6 : TopologicalSpace E] [inst_7 : TopologicalSpace F] {σ : 𝕜₁ →+
* 𝕜₂}   [RingHomSurjective σ] [RingHomIsometric σ] {s : Set E},   Bornology.IsVo
nNBounded 𝕜₁ s → ∀ (f : E →SL[σ] F), Bornology.IsVonNBounded 𝕜₂ (⇑f '' s)
参数：f : E →SL[σ] F；⇑f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f : X
 → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEm
bedding f → ∀ (x : X),…
· 使用定理 `Isometry.isEmbedding`：isEmbedding (hf : Isometry f) : IsEmbedding f
· 使用引理 `RingHom.isometry`：RingHom.isometry {𝕜₁ 𝕜₂ : Type*} [SeminormedRing 𝕜₁] [
SeminormedRing 𝕜₂] (σ : 𝕜₁ ->+* 𝕜₂) [RingHomIsometric σ] : Isometry σ
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `RingHom.surjective`：RingHom.surjective (σ : R₁ ->+* R₂) [t : RingHomSurj
ective σ] : Function.Surjective σ
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `image_smul_setₛₗ`：image_smul_setₛₗ (f : F) (c : M) (s : Set α) : f '' (c
 • s) = σ c • f '' s
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.image_smallSets`：∀ {α : Type u_1} {β : Type u_2} {la : Fi
lter α} {lb : Filter β} {f : α → β},   Filter.Tendsto f la lb → Filter.Tendsto (
fun x => f '' x) la.…

--- 原说明 ---
A continuous linear image of a bounded set is bounded.
-/
protected theorem IsVonNBounded.image {σ : 𝕜₁ →+* 𝕜₂} [RingHomSurjective σ] [RingHomIsometric σ]
    {s : Set E} (hs : IsVonNBounded 𝕜₁ s) (f : E →SL[σ] F) : IsVonNBounded 𝕜₂ (f '' s) := by
  have : map σ (𝓝 0) = 𝓝 0 := by
    rw [σ.isometry.isEmbedding.map_nhds_eq, σ.surjective.range_eq, nhdsWithin_univ, map_zero]
  have hf₀ : Tendsto f (𝓝 0) (𝓝 0) := f.continuous.tendsto' 0 0 (map_zero f)
  simp only [isVonNBounded_iff_tendsto_smallSets_nhds, ← this, tendsto_map'_iff] at hs ⊢
  simpa only [comp_def, image_smul_setₛₗ] using hf₀.image_smallSets.comp hs

end Image

section sequence

/-
**Bornology.IsVonNBounded.smul_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 `Bornology
.IsVonNBounded`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} {ι : Type u_5} [inst : NormedField 𝕜] [ins
t_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace 
E] {S : Set E} {ε : ι → 𝕜} {x : ι → E} {l : Filter ι},   Bornology.IsVonNBounded
 𝕜 S →     (∀ᶠ (n : ι) in l, x n ∈ S) → Filter.Tendsto ε l (nhds 0) → Filter.Ten
dsto (ε • x) l (nhds 0)
参数：∀ᶠ (n : ι) in l, x n ∈ S；nhds 0；ε • x；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.of_smallSets`：∀ {α : Type u_1} {β : Type u_2} {la : Filte
r α} {lb : Filter β} {s : α → Set β} {f : α → β},   Filter.Tendsto s la lb.small
Sets → (∀ᶠ (x : α…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Bornology.IsVonNBounded.tendsto_smallSets_nhds`：∀ {𝕜 : Type u_6} {E : Ty
pe u_7} [inst : NormedDivisionRing 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_
.Module 𝕜 E]   [inst_3 : Topological…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
theorem IsVonNBounded.smul_tendsto_zero [NormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    {S : Set E} {ε : ι → 𝕜} {x : ι → E} {l : Filter ι}
    (hS : IsVonNBounded 𝕜 S) (hxS : ∀ᶠ n in l, x n ∈ S) (hε : Tendsto ε l (𝓝 0)) :
    Tendsto (ε • x) l (𝓝 0) :=
  (hS.tendsto_smallSets_nhds.comp hε).of_smallSets <| hxS.mono fun _ ↦ smul_mem_smul_set

variable [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousSMul 𝕜 E]
/-
**Bornology.isVonNBounded_of_smul_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 `Bornol
ogy`。
形式化陈述：isVonNBounded_of_smul_tendsto_zero {ε : ι -> 𝕜} {l : Filter ι} [l.NeBot] (
hε : forallᶠ n in l, ε n != 0) {S : Set E} (H : forall x : ι -> E, (forall n, x 
n in S) -> Tendsto (ε • x) l (𝓝 0)) : IsVonNBounded 𝕜 S
参数：hε : forallᶠ n in l, ε n != 0；H : forall x : ι -> E, (forall n, x n in S) -> 
Tendsto (ε • x) l (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.isVonNBounded_iff`：∀ {𝕜 : Type u_1} {E : Type u_3} {ι : 
Type u_5} [inst : SeminormedRing 𝕜] [inst_1 : SMul 𝕜 E] [inst_2 : Zero E]   [ins
t_3 : TopologicalSpace …
· 使用定理 `nhds_basis_balanced`：nhds_basis_balanced : (𝓝 (0 : E)).HasBasis (fun s :
 Set E => s in 𝓝 (0 : E) ∧ Balanced 𝕜 s) id
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `absorbs_iff_norm`：absorbs_iff_norm : Absorbs 𝕜 A B ↔ exists r, forall c 
: 𝕜, r <= ‖c‖ -> B subseteq c • A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用定理 `Balanced.smul_mono`：Balanced.smul_mono (hs : Balanced 𝕝 s) {a : 𝕝} (h : 
‖a‖ <= ‖b‖) : a • s subseteq b • s
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.mem_inv_smul_set_iff₀`：mem_inv_smul_set_iff₀ (ha : a != 0) (A : Set 
β) (x : β) : x in a⁻¹ • A ↔ a • x in A
· 使用定理 `Filter.Eventually.choice`：∀ {α : Type u} {β : Type v} {r : α → β → Prop}
 {l : Filter α} [l.NeBot],   (∀ᶠ (x : α) in l, ∃ y, r x y) → ∃ f, ∀ᶠ (x : α) in 
l, r x (f x)
· 使用定理 `Filter.frequently_false`：frequently_false (f : Filter α) : ¬existsᶠ _ in
 f, False
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_mem_set`：eventually_mem_set {s : Set α} {l : Filter α}
 : (forallᶠ x in l, x in s) ↔ s in l
-/
theorem isVonNBounded_of_smul_tendsto_zero {ε : ι → 𝕜} {l : Filter ι} [l.NeBot]
    (hε : ∀ᶠ n in l, ε n ≠ 0) {S : Set E}
    (H : ∀ x : ι → E, (∀ n, x n ∈ S) → Tendsto (ε • x) l (𝓝 0)) : IsVonNBounded 𝕜 S := by
  rw [(nhds_basis_balanced 𝕜 E).isVonNBounded_iff]
  by_contra! ⟨V, ⟨hV, hVb⟩, hVS⟩
  have : ∀ᶠ n in l, ∃ x : S, ε n • (x : E) ∉ V := by
    filter_upwards [hε] with n hn
    rw [absorbs_iff_norm] at hVS
    push Not at hVS
    rcases hVS ‖(ε n)⁻¹‖ with ⟨a, haε, haS⟩
    rcases Set.not_subset.mp haS with ⟨x, hxS, hx⟩
    refine ⟨⟨x, hxS⟩, fun hnx => ?_⟩
    rw [← Set.mem_inv_smul_set_iff₀ hn] at hnx
    exact hx (hVb.smul_mono haε hnx)
  rcases this.choice with ⟨x, hx⟩
  refine Filter.frequently_false l (Filter.Eventually.frequently ?_)
  filter_upwards [hx,
    (H (_ ∘ x) fun n => (x n).2).eventually (eventually_mem_set.mpr hV)] using fun n => id

/-- Given any sequence `ε` of scalars which tends to `𝓝[≠] 0`, we have that a set `S` is bounded
  if and only if for any sequence `x : ℕ → S`, `ε • x` tends to 0. This actually works for any
  indexing type `ι`, but in the special case `ι = ℕ` we get the important fact that convergent
  sequences fully characterize bounded sets. -/
/-
**Bornology.isVonNBounded_iff_smul_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 `Borno
logy`。
形式化陈述：isVonNBounded_iff_smul_tendsto_zero {ε : ι -> 𝕜} {l : Filter ι} [l.NeBot] 
(hε : Tendsto ε l (𝓝[!=] 0)) {S : Set E} : IsVonNBounded 𝕜 S ↔ forall x : ι -> E
, (forall n, x n in S) -> Tendsto (ε • x) l (𝓝 0)
参数：hε : Tendsto ε l (𝓝[!=] 0)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsVonNBounded.smul_tendsto_zero`：∀ {𝕜 : Type u_1} {E : Type u_
3} {ι : Type u_5} [inst : NormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _
root_.Module 𝕜 E] [inst_3 : Top…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Bornology.isVonNBounded_of_smul_tendsto_zero`：isVonNBounded_of_smul_tend
sto_zero {ε : ι -> 𝕜} {l : Filter ι} [l.NeBot] (hε : forallᶠ n in l, ε n != 0) {
S : Set E} (H : forall x : ι -> E,…
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a

--- 原说明 ---
Given any sequence `ε` of scalars which tends to `𝓝[≠] 0`, we have that a set `S
` is bounded
  if and only if for any sequence `x : ℕ → S`, `ε • x` tends to 0. This actually
 works for any
  indexing type `ι`, but in the special case `ι = ℕ` we get the important fact t
hat convergent
  sequences fully characterize bounded sets.
-/
theorem isVonNBounded_iff_smul_tendsto_zero {ε : ι → 𝕜} {l : Filter ι} [l.NeBot]
    (hε : Tendsto ε l (𝓝[≠] 0)) {S : Set E} :
    IsVonNBounded 𝕜 S ↔ ∀ x : ι → E, (∀ n, x n ∈ S) → Tendsto (ε • x) l (𝓝 0) :=
  ⟨fun hS _ hxS => hS.smul_tendsto_zero (Eventually.of_forall hxS) (le_trans hε nhdsWithin_le_nhds),
    isVonNBounded_of_smul_tendsto_zero (by exact hε self_mem_nhdsWithin)⟩

end sequence

/-- If a set is von Neumann bounded with respect to a smaller field,
then it is also von Neumann bounded with respect to a larger field.
See also `Bornology.IsVonNBounded.restrict_scalars` below. -/
/-
**Bornology.IsVonNBounded.extend_scalars** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.Is
VonNBounded`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_6} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] (𝕝 : Type u_7) [inst_3 : Nontr
iviallyNormedField 𝕝] [inst_4 : NormedAlgebra 𝕜 𝕝]   [inst_5 : _root_.Module 𝕝 E
] [inst_6 : TopologicalSpace E] [ContinuousSMul 𝕝 E] [IsScalarTower 𝕜 𝕝 E] {s : 
Set E},   Bornology.IsVonNBounded 𝕜 s → Bornology.IsVonNBounded 𝕝 s
参数：𝕝 : Type u_7。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.exists_seq_tendsto`：exists_seq_tendsto (f : Filter α) [IsCountabl
yGenerated f] [NeBot f] : exists x : Nat -> α, Tendsto x atTop f
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `Bornology.isVonNBounded_of_smul_tendsto_zero`：isVonNBounded_of_smul_tend
sto_zero {ε : ι -> 𝕜} {l : Filter ι} [l.NeBot] (hε : forallᶠ n in l, ε n != 0) {
S : Set E} (H : forall x : ι -> E,…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Bornology.IsVonNBounded.smul_tendsto_zero`：∀ {𝕜 : Type u_1} {E : Type u_
3} {ι : Type u_5} [inst : NormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _
root_.Module 𝕜 E] [inst_3 : Top…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y

--- 原说明 ---
If a set is von Neumann bounded with respect to a smaller field,
then it is also von Neumann bounded with respect to a larger field.
See also `Bornology.IsVonNBounded.restrict_scalars` below.
-/
theorem IsVonNBounded.extend_scalars [NontriviallyNormedField 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E]
    (𝕝 : Type*) [NontriviallyNormedField 𝕝] [NormedAlgebra 𝕜 𝕝]
    [Module 𝕝 E] [TopologicalSpace E] [ContinuousSMul 𝕝 E] [IsScalarTower 𝕜 𝕝 E]
    {s : Set E} (h : IsVonNBounded 𝕜 s) : IsVonNBounded 𝕝 s := by
  obtain ⟨ε, hε, hε₀⟩ : ∃ ε : ℕ → 𝕜, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ n in atTop, ε n ≠ 0 := by
    simpa only [tendsto_nhdsWithin_iff] using! exists_seq_tendsto (𝓝[≠] (0 : 𝕜))
  refine isVonNBounded_of_smul_tendsto_zero (ε := (ε · • 1)) (by simpa) fun x hx ↦ ?_
  have := h.smul_tendsto_zero (.of_forall hx) hε
  simpa only [Pi.smul_def', smul_one_smul]

section NormedField

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E]

/-- The closure of a bounded set is bounded. -/
/-
**Bornology.IsVonNBounded.closure** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsVonNBou
nded`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : NormedField 𝕜] [inst_1 : AddCommGr
oup E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : TopologicalSpace E] [T1Space E] 
[RegularSpace E] [ContinuousConstSMul 𝕜 E] {a : Set E},   Bornology.IsVonNBounde
d 𝕜 a → Bornology.IsVonNBounded 𝕜 (closure a)
参数：closure a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_mem_nhds_isClosed_subset`：exists_mem_nhds_isClosed_subset {x : X}
 {s : Set X} (h : s in 𝓝 x) : exists t in 𝓝 x, IsClosed t ∧ t subseteq s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_smul₀`：closure_smul₀ {E} [Zero E] [MulActionWithZero G₀ E] [Topo
logicalSpace E] [T1Space E] [ContinuousConstSMul G₀ E] (c : G₀) (s : Set E) : cl
osu…
· 使用定理 `Set.smul_set_mono`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s 
t : Set β} {a : α}, s ⊆ t → a • s ⊆ a • t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `closure_subset_iff_isClosed`：closure_subset_iff_isClosed : closure s sub
seteq s ↔ IsClosed s

--- 原说明 ---
The closure of a bounded set is bounded.
-/
theorem IsVonNBounded.closure [T1Space E] [RegularSpace E] [ContinuousConstSMul 𝕜 E]
    {a : Set E} (ha : IsVonNBounded 𝕜 a) : IsVonNBounded 𝕜 (closure a) := by
  intro V hV
  rcases exists_mem_nhds_isClosed_subset hV with ⟨W, hW₁, hW₂, hW₃⟩
  specialize ha hW₁
  filter_upwards [ha] with b ha'
  grw [ha', closure_smul₀ b, closure_subset_iff_isClosed.mpr hW₂, hW₃]

variable [ContinuousSMul 𝕜 E]

/-- Singletons are bounded. -/
/-
**Bornology.isVonNBounded_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isVonNBounded_singleton (x : E) : IsVonNBounded 𝕜 ({x} : Set E)
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Absorbent.absorbs`：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M] 
[inst_1 : SMul M α] {s : Set α},   Absorbent M s → ∀ {x : α}, Absorbs M s {x}
· 使用定理 `absorbent_nhds_zero`：absorbent_nhds_zero (hA : A in 𝓝 (0 : E)) : Absorbe
nt 𝕜 A

--- 原说明 ---
Singletons are bounded.
-/
theorem isVonNBounded_singleton (x : E) : IsVonNBounded 𝕜 ({x} : Set E) := fun _ hV =>
  (absorbent_nhds_zero hV).absorbs

@[simp]
/-
**Bornology.isVonNBounded_insert** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isVonNBounded_insert (x : E) {s : Set E} : IsVonNBounded 𝕜 (insert x s) ↔ 
IsVonNBounded 𝕜 s
参数：x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isVonNBounded_insert (x : E) {s : Set E} :
    IsVonNBounded 𝕜 (insert x s) ↔ IsVonNBounded 𝕜 s := by
  simp only [← singleton_union, isVonNBounded_union, isVonNBounded_singleton, true_and]

protected alias ⟨_, IsVonNBounded.insert⟩ := isVonNBounded_insert

/-- Finite sets are bounded. -/
/-
**Bornology._root_.Set.Finite.isVonNBounded** 是 Mathlib 中的一个定理，位于命名空间 `Bornology
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finite sets are bounded.
-/
theorem _root_.Set.Finite.isVonNBounded {s : Set E} (hs : s.Finite) :
    IsVonNBounded 𝕜 s := fun _ hV ↦
  (absorbent_nhds_zero hV).absorbs_finite hs

section ContinuousAdd

variable [ContinuousAdd E] {s t : Set E}

/-
**Bornology.IsVonNBounded.vadd** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsVonNBounde
d`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : NormedField 𝕜] [inst_1 : AddCommGr
oup E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : TopologicalSpace E] [ContinuousS
Mul 𝕜 E] [ContinuousAdd E] {s : Set E},   Bornology.IsVonNBounded 𝕜 s → ∀ (x : E
), Bornology.IsVonNBounded 𝕜 (x +ᵥ s)
参数：x : E；x +ᵥ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.singleton_vadd`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] {t
 : Set β} {a : α}, {a} +ᵥ t = a +ᵥ t
· 使用定理 `Bornology.IsVonNBounded.add`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Sem
inormedRing 𝕜] [inst_1 : AddZeroClass E] [inst_2 : TopologicalSpace E]   [Contin
uousAdd E] [inst_…
· 使用定理 `Bornology.isVonNBounded_singleton`：isVonNBounded_singleton (x : E) : IsV
onNBounded 𝕜 ({x} : Set E)
-/
protected theorem IsVonNBounded.vadd (hs : IsVonNBounded 𝕜 s) (x : E) :
    IsVonNBounded 𝕜 (x +ᵥ s) := by
  rw [← singleton_vadd]
  -- TODO: dot notation timeouts in the next line
  exact IsVonNBounded.add (isVonNBounded_singleton x) hs

@[simp]
/-
**Bornology.isVonNBounded_vadd** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isVonNBounded_vadd (x : E) : IsVonNBounded 𝕜 (x +ᵥ s) ↔ IsVonNBounded 𝕜 s
参数：x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_vadd_vadd`：∀ {G : Type u_3} {α : Type u_5} [inst : AddGroup G] [inst
_1 : AddAction G α] (g : G) (a : α), -g +ᵥ g +ᵥ a = a
· 使用定理 `Bornology.IsVonNBounded.vadd`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : No
rmedField 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : 
TopologicalSpace E…
-/
theorem isVonNBounded_vadd (x : E) : IsVonNBounded 𝕜 (x +ᵥ s) ↔ IsVonNBounded 𝕜 s :=
  ⟨fun h ↦ by simpa using h.vadd (-x), fun h ↦ h.vadd x⟩
/-
**Bornology.IsVonNBounded.of_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsVo
nNBounded`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : NormedField 𝕜] [inst_1 : AddCommGr
oup E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : TopologicalSpace E] [ContinuousS
Mul 𝕜 E] [ContinuousAdd E] {s t : Set E},   Bornology.IsVonNBounded 𝕜 (s + t) → 
s.Nonempty → Bornology.IsVonNBounded 𝕜 t
参数：s + t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bornology.isVonNBounded_vadd`：isVonNBounded_vadd (x : E) : IsVonNBounded
 𝕜 (x +ᵥ s) ↔ IsVonNBounded 𝕜 s
· 使用定理 `Bornology.IsVonNBounded.subset`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : 
SeminormedRing 𝕜] [inst_1 : SMul 𝕜 E] [inst_2 : Zero E]   [inst_3 : TopologicalS
pace E] {s₁ s₂ : Set…
· 使用定理 `Set.image_subset_image2_right`：image_subset_image2_right (ha : a in s) :
 f a '' t subseteq image2 f s t
-/
theorem IsVonNBounded.of_add_right (hst : IsVonNBounded 𝕜 (s + t)) (hs : s.Nonempty) :
    IsVonNBounded 𝕜 t :=
  let ⟨x, hx⟩ := hs
  (isVonNBounded_vadd x).mp <| hst.subset <| image_subset_image2_right hx
/-
**Bornology.IsVonNBounded.of_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsVon
NBounded`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : NormedField 𝕜] [inst_1 : AddCommGr
oup E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : TopologicalSpace E] [ContinuousS
Mul 𝕜 E] [ContinuousAdd E] {s t : Set E},   Bornology.IsVonNBounded 𝕜 (s + t) → 
t.Nonempty → Bornology.IsVonNBounded 𝕜 s
参数：s + t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsVonNBounded.of_add_right`：∀ {𝕜 : Type u_1} {E : Type u_3} [i
nst : NormedField 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   [i
nst_3 : TopologicalSpace E…
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem IsVonNBounded.of_add_left (hst : IsVonNBounded 𝕜 (s + t)) (ht : t.Nonempty) :
    IsVonNBounded 𝕜 s :=
  ((add_comm s t).subst hst).of_add_right ht
/-
**Bornology.isVonNBounded_add_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isVonNBounded_add_of_nonempty (hs : s.Nonempty) (ht : t.Nonempty) : IsVonN
Bounded 𝕜 (s + t) ↔ IsVonNBounded 𝕜 s ∧ IsVonNBounded 𝕜 t
参数：hs : s.Nonempty；ht : t.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsVonNBounded.of_add_left`：∀ {𝕜 : Type u_1} {E : Type u_3} [in
st : NormedField 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   [in
st_3 : TopologicalSpace E…
· 使用定理 `Bornology.IsVonNBounded.of_add_right`：∀ {𝕜 : Type u_1} {E : Type u_3} [i
nst : NormedField 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   [i
nst_3 : TopologicalSpace E…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_imp`：∀ {a b c : Prop}, a ∧ b → c ↔ a → b → c
· 使用定理 `Bornology.IsVonNBounded.add`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Sem
inormedRing 𝕜] [inst_1 : AddZeroClass E] [inst_2 : TopologicalSpace E]   [Contin
uousAdd E] [inst_…
-/
theorem isVonNBounded_add_of_nonempty (hs : s.Nonempty) (ht : t.Nonempty) :
    IsVonNBounded 𝕜 (s + t) ↔ IsVonNBounded 𝕜 s ∧ IsVonNBounded 𝕜 t :=
  ⟨fun h ↦ ⟨h.of_add_left ht, h.of_add_right hs⟩, and_imp.2 IsVonNBounded.add⟩
/-
**Bornology.isVonNBounded_add** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isVonNBounded_add : IsVonNBounded 𝕜 (s + t) ↔ s = ∅ ∨ t = ∅ ∨ IsVonNBounde
d 𝕜 s ∧ IsVonNBounded 𝕜 t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.empty_add`：∀ {α : Type u_2} [inst : Add α] {s : Set α}, ∅ + s = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.add_empty`：∀ {α : Type u_2} [inst : Add α] {s : Set α}, s + ∅ = ∅
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Bornology.isVonNBounded_add_of_nonempty`：isVonNBounded_add_of_nonempty (
hs : s.Nonempty) (ht : t.Nonempty) : IsVonNBounded 𝕜 (s + t) ↔ IsVonNBounded 𝕜 s
 ∧ IsVonNBounded 𝕜 t
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem isVonNBounded_add :
    IsVonNBounded 𝕜 (s + t) ↔ s = ∅ ∨ t = ∅ ∨ IsVonNBounded 𝕜 s ∧ IsVonNBounded 𝕜 t := by
  rcases s.eq_empty_or_nonempty with rfl | hs; · simp
  rcases t.eq_empty_or_nonempty with rfl | ht; · simp
  simp [hs.ne_empty, ht.ne_empty, isVonNBounded_add_of_nonempty hs ht]

@[simp]
/-
**Bornology.isVonNBounded_add_self** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isVonNBounded_add_self : IsVonNBounded 𝕜 (s + s) ↔ IsVonNBounded 𝕜 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.add_empty`：∀ {α : Type u_2} [inst : Add α] {s : Set α}, s + ∅ = ∅
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem isVonNBounded_add_self : IsVonNBounded 𝕜 (s + s) ↔ IsVonNBounded 𝕜 s := by
  rcases s.eq_empty_or_nonempty with rfl | hs <;> simp [isVonNBounded_add_of_nonempty, *]
/-
**Bornology.IsVonNBounded.of_sub_left** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsVon
NBounded`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : NormedField 𝕜] [inst_1 : AddCommGr
oup E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : TopologicalSpace E] [ContinuousS
Mul 𝕜 E] [ContinuousAdd E] {s t : Set E},   Bornology.IsVonNBounded 𝕜 (s - t) → 
t.Nonempty → Bornology.IsVonNBounded 𝕜 s
参数：s - t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsVonNBounded.of_add_left`：∀ {𝕜 : Type u_1} {E : Type u_3} [in
st : NormedField 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   [in
st_3 : TopologicalSpace E…
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Set.Nonempty.neg`：∀ {α : Type u_2} [inst : InvolutiveNeg α] {s : Set α},
 s.Nonempty → (-s).Nonempty
-/
theorem IsVonNBounded.of_sub_left (hst : IsVonNBounded 𝕜 (s - t)) (ht : t.Nonempty) :
    IsVonNBounded 𝕜 s :=
  ((sub_eq_add_neg s t).subst hst).of_add_left ht.neg

end ContinuousAdd

section IsTopologicalAddGroup

variable [IsTopologicalAddGroup E] {s t : Set E}

/-
**Bornology.IsVonNBounded.of_sub_right** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsVo
nNBounded`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : NormedField 𝕜] [inst_1 : AddCommGr
oup E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : TopologicalSpace E] [ContinuousS
Mul 𝕜 E] [IsTopologicalAddGroup E] {s t : Set E},   Bornology.IsVonNBounded 𝕜 (s
 - t) → s.Nonempty → Bornology.IsVonNBounded 𝕜 t
参数：s - t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsVonNBounded.of_neg`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : 
SeminormedRing 𝕜] [inst_1 : AddGroup E] [inst_2 : TopologicalSpace E]   [IsTopol
ogicalAddGroup E] [i…
· 使用定理 `Bornology.IsVonNBounded.of_add_right`：∀ {𝕜 : Type u_1} {E : Type u_3} [i
nst : NormedField 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   [i
nst_3 : TopologicalSpace E…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem IsVonNBounded.of_sub_right (hst : IsVonNBounded 𝕜 (s - t)) (hs : s.Nonempty) :
    IsVonNBounded 𝕜 t :=
  (((sub_eq_add_neg s t).subst hst).of_add_right hs).of_neg
/-
**Bornology.isVonNBounded_sub_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isVonNBounded_sub_of_nonempty (hs : s.Nonempty) (ht : t.Nonempty) : IsVonN
Bounded 𝕜 (s - t) ↔ IsVonNBounded 𝕜 s ∧ IsVonNBounded 𝕜 t
参数：hs : s.Nonempty；ht : t.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isVonNBounded_sub_of_nonempty (hs : s.Nonempty) (ht : t.Nonempty) :
    IsVonNBounded 𝕜 (s - t) ↔ IsVonNBounded 𝕜 s ∧ IsVonNBounded 𝕜 t := by
  simp [sub_eq_add_neg, isVonNBounded_add_of_nonempty, hs, ht]
/-
**Bornology.isVonNBounded_sub** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isVonNBounded_sub : IsVonNBounded 𝕜 (s - t) ↔ s = ∅ ∨ t = ∅ ∨ IsVonNBounde
d 𝕜 s ∧ IsVonNBounded 𝕜 t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isVonNBounded_sub :
    IsVonNBounded 𝕜 (s - t) ↔ s = ∅ ∨ t = ∅ ∨ IsVonNBounded 𝕜 s ∧ IsVonNBounded 𝕜 t := by
  simp [sub_eq_add_neg, isVonNBounded_add]

end IsTopologicalAddGroup

/-- The union of all bounded set is the whole space. -/
/-
**Bornology.sUnion_isVonNBounded_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：sUnion_isVonNBounded_eq_univ : ⋃₀ Set.ofPred (IsVonNBounded 𝕜) = (Set.univ
 : Set E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Set.mem_sUnion`：mem_sUnion {x : α} {S : Set (Set α)} : x in ⋃₀ S ↔ exist
s t in S, x in t
· 使用定理 `Bornology.isVonNBounded_singleton`：isVonNBounded_singleton (x : E) : IsV
onNBounded 𝕜 ({x} : Set E)
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)

--- 原说明 ---
The union of all bounded set is the whole space.
-/
theorem sUnion_isVonNBounded_eq_univ : ⋃₀ Set.ofPred (IsVonNBounded 𝕜) = (Set.univ : Set E) :=
  Set.eq_univ_iff_forall.mpr fun x =>
    Set.mem_sUnion.mpr ⟨{x}, isVonNBounded_singleton _, Set.mem_singleton _⟩

variable (𝕜 E)

-- See note [reducible non-instances]
/-- The von Neumann bornology defined by the von Neumann bounded sets.

Note that this is not registered as an instance, in order to avoid diamonds with the
metric bornology. -/
/-
**Bornology.vonNBornology** 是 Mathlib 中的一个缩写定义，位于命名空间 `Bornology`。
形式化陈述：vonNBornology : Bornology E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.isVonNBounded_singleton`：isVonNBounded_singleton (x : E) : IsV
onNBounded 𝕜 ({x} : Set E)

--- 原说明 ---
The von Neumann bornology defined by the von Neumann bounded sets.

Note that this is not registered as an instance, in order to avoid diamonds with
 the
metric bornology.
-/
abbrev vonNBornology : Bornology E :=
  Bornology.ofBounded (Set.ofPred (IsVonNBounded 𝕜)) (isVonNBounded_empty 𝕜 E)
    (fun _ hs _ ht => hs.subset ht) (fun _ hs _ => hs.union) isVonNBounded_singleton

variable {E}

@[simp]
/-
**Bornology.isBounded_iff_isVonNBounded** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_iff_isVonNBounded {s : Set E} : @IsBounded _ (vonNBornology 𝕜 E)
 s ↔ IsVonNBounded 𝕜 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.isBounded_ofBounded_iff`：isBounded_ofBounded_iff (B : Set (Set
 α)) {empty_mem subset_mem union_mem sUnion_univ} : @IsBounded _ (ofBounded B em
pty_mem subset_mem unio…
· 使用定理 `Bornology.isVonNBounded_singleton`：isVonNBounded_singleton (x : E) : IsV
onNBounded 𝕜 ({x} : Set E)
-/
theorem isBounded_iff_isVonNBounded {s : Set E} :
    @IsBounded _ (vonNBornology 𝕜 E) s ↔ IsVonNBounded 𝕜 s :=
  isBounded_ofBounded_iff _

end NormedField

end Bornology

section IsUniformAddGroup

variable (𝕜) [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]

/-
**TotallyBounded.isVonNBounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TotallyBounded.isVonNBounded {s : Set E} (hs : TotallyBounded s) : Bornolo
gy.IsVonNBounded 𝕜 s
参数：hs : TotallyBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Filter.HasBasis.prod`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {l
b : Filter β} {ι : Type u_6} {ι' : Type u_7} {pa : ι → Prop}   {sa : ι → Set α} 
{pb : ι' →…
· 使用定理 `nhds_basis_balanced`：nhds_basis_balanced : (𝓝 (0 : E)).HasBasis (fun s :
 Set E => s in 𝓝 (0 : E) ∧ Balanced 𝕜 s) id
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `Filter.Tendsto.basis_left`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4
} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α} {lb : Filter β}   {f : α → β}
, Filter.Tendst…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `totallyBounded_iff_subset_finite_iUnion_nhds_zero`：∀ {α : Type u_1} [ins
t : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {s : Set α},   T
otallyBounded s ↔ ∀ U ∈ nhds 0, ∃ t, t.…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Absorbs.mono_right`：mono_right (h : Absorbs M s t₁) (ht : t₂ subseteq t₁
) : Absorbs M s t₂
· 使用定理 `Set.Finite.absorbs_biUnion`：∀ {M : Type u_1} {α : Type u_2} [inst : Born
ology M] [inst_1 : SMul M α] {s : Set α} {ι : Type u_3} {t : ι → Set α}   {I : S
et ι}, I.Finite …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.add_subset_iff`：∀ {α : Type u_2} [inst : Add α] {s t u : Set α}, s +
 t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x + y ∈ u
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t
· 使用引理 `Absorbs.mono_left`：mono_left (h : Absorbs M s₁ t) (hs : s₁ subseteq s₂) 
: Absorbs M s₂ t
· 使用定理 `Absorbent.vadd_absorbs`：vadd_absorbs {M E : Type*} [Bornology M] [AddZer
oClass E] [DistribSMul M E] {s₁ s₂ t : Set E} {x : E} (h₁ : Absorbent M s₁) (h₂ 
: Absorbs M …
· 使用定理 `absorbent_nhds_zero`：absorbent_nhds_zero (hA : A in 𝓝 (0 : E)) : Absorbe
nt 𝕜 A
· 使用定理 `Balanced.absorbs_self`：Balanced.absorbs_self (hs : Balanced 𝕜 s) : Absor
bs 𝕜 s s
· 使用定理 `Metric.isBounded_iff`：isBounded_iff {s : Set α} : IsBounded s ↔ exists C
 : Real, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
（共 32 条，此处仅展示前 30 条）
-/
theorem TotallyBounded.isVonNBounded {s : Set E} (hs : TotallyBounded s) :
    Bornology.IsVonNBounded 𝕜 s := by
  if h : ∃ x : 𝕜, 1 < ‖x‖ then
    let : NontriviallyNormedField 𝕜 := ⟨h⟩
    rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero] at hs
    intro U hU
    have h : Filter.Tendsto (fun x : E × E => x.fst + x.snd) (𝓝 0) (𝓝 0) :=
      continuous_add.tendsto' _ _ (zero_add _)
    have h' := (nhds_basis_balanced 𝕜 E).prod (nhds_basis_balanced 𝕜 E)
    simp_rw [← nhds_prod_eq, id] at h'
    rcases h.basis_left h' U hU with ⟨x, hx, h''⟩
    rcases hs x.snd hx.2.1 with ⟨t, ht, hs⟩
    refine Absorbs.mono_right ?_ hs
    rw [ht.absorbs_biUnion]
    have hx_fstsnd : x.fst + x.snd ⊆ U := add_subset_iff.mpr fun z1 hz1 z2 hz2 ↦
      h'' <| mk_mem_prod hz1 hz2
    refine fun y _ => Absorbs.mono_left ?_ hx_fstsnd
    exact (absorbent_nhds_zero hx.1.1).vadd_absorbs hx.2.2.absorbs_self
  else
    have : BoundedSpace 𝕜 := ⟨Metric.isBounded_iff.2 ⟨1, by simp_all [dist_eq_norm]⟩⟩
    exact Bornology.IsVonNBounded.of_boundedSpace

end IsUniformAddGroup

variable (𝕜) in
/-
**IsCompact.isVonNBounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.isVonNBounded [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Top
ologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] {s : Set E} (hs 
: IsCompact s) : Bornology.IsVonNBounded 𝕜 s
参数：hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TotallyBounded.isVonNBounded`：TotallyBounded.isVonNBounded {s : Set E} (
hs : TotallyBounded s) : Bornology.IsVonNBounded 𝕜 s
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `IsCompact.totallyBounded`：∀ {α : Type u} [uniformSpace : UniformSpace α]
 {s : Set α}, IsCompact s → TotallyBounded s
-/
theorem IsCompact.isVonNBounded [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] {s : Set E}
    (hs : IsCompact s) : Bornology.IsVonNBounded 𝕜 s :=
  letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI := isUniformAddGroup_of_addCommGroup (G := E)
  hs.totallyBounded.isVonNBounded 𝕜

variable (𝕜) in
/-
**Filter.Tendsto.isVonNBounded_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.isVonNBounded_range [NormedField 𝕜] [AddCommGroup E] [Modul
e 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] {f : 
Nat -> E} {x : E} (hf : Tendsto f atTop (𝓝 x)) : Bornology.IsVonNBounded 𝕜 (rang
e f)
参数：hf : Tendsto f atTop (𝓝 x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TotallyBounded.isVonNBounded`：TotallyBounded.isVonNBounded {s : Set E} (
hs : TotallyBounded s) : Bornology.IsVonNBounded 𝕜 s
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `CauchySeq.totallyBounded_range`：CauchySeq.totallyBounded_range {s : Nat 
-> α} (hs : CauchySeq s) : TotallyBounded (range s)
· 使用定理 `Filter.Tendsto.cauchySeq`：Filter.Tendsto.cauchySeq [SemilatticeSup β] [N
onempty β] {f : β -> α} {x} (hx : Tendsto f atTop (𝓝 x)) : CauchySeq f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem Filter.Tendsto.isVonNBounded_range [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    {f : ℕ → E} {x : E} (hf : Tendsto f atTop (𝓝 x)) : Bornology.IsVonNBounded 𝕜 (range f) :=
  letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI := isUniformAddGroup_of_addCommGroup (G := E)
  hf.cauchySeq.totallyBounded_range.isVonNBounded 𝕜

variable (𝕜) in
/-
**Bornology.IsVonNBounded.restrict_scalars_of_nontrivial** 是 Mathlib 中的一个定理，位于命名
空间 `Bornology.IsVonNBounded`。
形式化陈述：∀ (𝕜 : Type u_1) {𝕜' : Type u_2} {E : Type u_3} [inst : NormedField 𝕜] [in
st_1 : NormedRing 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜'] [Nontrivial 𝕜'] [inst_4 : 
Zero E] [inst_5 : TopologicalSpace E] [inst_6 : SMul 𝕜 E]   [inst_7 : MulAction 
𝕜' E] [IsScalarTower 𝕜 𝕜' E] {s : Set E},   Bornology.IsVonNBounded 𝕜' s → Borno
logy.IsVonNBounded 𝕜 s
参数：𝕜 : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Absorbs.restrict_scalars`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_3}
 [inst : Monoid N] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : MulAction
 N α] [IsScala…
· 使用定理 `AntilipschitzWith.tendsto_cobounded`：tendsto_cobounded (hf : Antilipschi
tzWith K f) : Tendsto f (cobounded α) (cobounded β)
· 使用定理 `AntilipschitzWith.of_le_mul_nndist`：∀ {α : Type u_1} {β : Type u_2} [ins
t : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β}
,   (∀ (x y : α), nndist…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nndist_eq_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), nndist a b = ‖a - b‖₊
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `nnnorm_smul`：nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nnnorm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 
‖a‖₊ ≠ 0 ↔ a ≠ 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
protected theorem Bornology.IsVonNBounded.restrict_scalars_of_nontrivial
    [NormedField 𝕜] [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] [Nontrivial 𝕜']
    [Zero E] [TopologicalSpace E]
    [SMul 𝕜 E] [MulAction 𝕜' E] [IsScalarTower 𝕜 𝕜' E] {s : Set E}
    (h : IsVonNBounded 𝕜' s) : IsVonNBounded 𝕜 s := by
  intro V hV
  refine (h hV).restrict_scalars <| AntilipschitzWith.tendsto_cobounded (K := ‖(1 : 𝕜')‖₊⁻¹) ?_
  refine AntilipschitzWith.of_le_mul_nndist fun x y ↦ ?_
  rw [nndist_eq_nnnorm, nndist_eq_nnnorm, ← sub_smul, nnnorm_smul, ← div_eq_inv_mul,
    mul_div_cancel_right₀ _ (nnnorm_ne_zero_iff.2 one_ne_zero)]

variable (𝕜) in
/-
**Bornology.IsVonNBounded.restrict_scalars** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.
IsVonNBounded`。
形式化陈述：∀ (𝕜 : Type u_1) {𝕜' : Type u_2} {E : Type u_3} [inst : NormedField 𝕜] [in
st_1 : NormedRing 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜'] [inst_3 : Zero E] [inst_4 
: TopologicalSpace E] [inst_5 : SMul 𝕜 E]   [inst_6 : MulActionWithZero 𝕜' E] [I
sScalarTower 𝕜 𝕜' E] {s : Set E},   Bornology.IsVonNBounded 𝕜' s → Bornology.IsV
onNBounded 𝕜 s
参数：𝕜 : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `MulActionWithZero.subsingleton`：∀ (M₀ : Type u_2) (A : Type u_7) [inst :
 MonoidWithZero M₀] [inst_1 : Zero A] [MulActionWithZero M₀ A]   [Subsingleton M
₀], Subsingleton A
· 使用定理 `Bornology.IsVonNBounded.of_subsingleton`：∀ {𝕜 : Type u_1} {E : Type u_3}
 [inst : SeminormedRing 𝕜] [inst_1 : SMul 𝕜 E] [inst_2 : Zero E]   [inst_3 : Top
ologicalSpace E] [Subsingleto…
· 使用定理 `Bornology.IsVonNBounded.restrict_scalars_of_nontrivial`：∀ (𝕜 : Type u_1)
 {𝕜' : Type u_2} {E : Type u_3} [inst : NormedField 𝕜] [inst_1 : NormedRing 𝕜'] 
  [inst_2 : NormedAlgebra 𝕜 𝕜'] [Nontrivial …
-/
protected theorem Bornology.IsVonNBounded.restrict_scalars
    [NormedField 𝕜] [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜']
    [Zero E] [TopologicalSpace E]
    [SMul 𝕜 E] [MulActionWithZero 𝕜' E] [IsScalarTower 𝕜 𝕜' E] {s : Set E}
    (h : IsVonNBounded 𝕜' s) : IsVonNBounded 𝕜 s :=
  match subsingleton_or_nontrivial 𝕜' with
  | .inl _ =>
    have : Subsingleton E := MulActionWithZero.subsingleton 𝕜' E
    IsVonNBounded.of_subsingleton
  | .inr _ =>
    h.restrict_scalars_of_nontrivial _

section VonNBornologyEqMetric

namespace NormedSpace

section NormedField

variable (𝕜)
variable [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-
**NormedSpace.isVonNBounded_of_isBounded** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`
。
形式化陈述：isVonNBounded_of_isBounded {s : Set E} (h : Bornology.IsBounded s) : Borno
logy.IsVonNBounded 𝕜 s
参数：h : Bornology.IsBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.subset_ball`：∀ {α : Type u} {s : Set α} [inst : Pseu
doMetricSpace α], Bornology.IsBounded s → ∀ (c : α), ∃ r, s ⊆ Metric.ball c r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.isVonNBounded_iff`：∀ {𝕜 : Type u_1} {E : Type u_3} {ι : 
Type u_5} [inst : SeminormedRing 𝕜] [inst_1 : SMul 𝕜 E] [inst_2 : Zero E]   [ins
t_3 : TopologicalSpace …
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ball_normSeminorm`：ball_normSeminorm : (normSeminorm 𝕜 E).ball = Metric.
ball
· 使用引理 `Absorbs.mono_right`：mono_right (h : Absorbs M s t₁) (ht : t₂ subseteq t₁
) : Absorbs M s t₂
· 使用定理 `Seminorm.ball_zero_absorbs_ball_zero`：ball_zero_absorbs_ball_zero (p : S
eminorm 𝕜 E) {r₁ r₂ : Real} (hr₁ : 0 < r₁) : Absorbs 𝕜 (p.ball 0 r₁) (p.ball 0 r
₂)
-/
theorem isVonNBounded_of_isBounded {s : Set E} (h : Bornology.IsBounded s) :
    Bornology.IsVonNBounded 𝕜 s := by
  rcases h.subset_ball 0 with ⟨r, hr⟩
  rw [Metric.nhds_basis_ball.isVonNBounded_iff]
  rw [← ball_normSeminorm 𝕜 E] at hr ⊢
  exact fun ε hε ↦ ((normSeminorm 𝕜 E).ball_zero_absorbs_ball_zero hε).mono_right hr

variable (E)
/-
**NormedSpace.isVonNBounded_ball** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：isVonNBounded_ball (r : Real) : Bornology.IsVonNBounded 𝕜 (Metric.ball (0 
: E) r)
参数：r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.isVonNBounded_of_isBounded`：isVonNBounded_of_isBounded {s : 
Set E} (h : Bornology.IsBounded s) : Bornology.IsVonNBounded 𝕜 s
· 使用定理 `Metric.isBounded_ball`：isBounded_ball : IsBounded (ball x r)
-/
theorem isVonNBounded_ball (r : ℝ) : Bornology.IsVonNBounded 𝕜 (Metric.ball (0 : E) r) :=
  isVonNBounded_of_isBounded _ Metric.isBounded_ball
/-
**NormedSpace.isVonNBounded_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：isVonNBounded_closedBall (r : Real) : Bornology.IsVonNBounded 𝕜 (Metric.cl
osedBall (0 : E) r)
参数：r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.isVonNBounded_of_isBounded`：isVonNBounded_of_isBounded {s : 
Set E} (h : Bornology.IsBounded s) : Bornology.IsVonNBounded 𝕜 s
· 使用定理 `Metric.isBounded_closedBall`：isBounded_closedBall : IsBounded (closedBal
l x r)
-/
theorem isVonNBounded_closedBall (r : ℝ) :
    Bornology.IsVonNBounded 𝕜 (Metric.closedBall (0 : E) r) :=
  isVonNBounded_of_isBounded _ Metric.isBounded_closedBall

end NormedField

variable (𝕜)
variable [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-
**NormedSpace.isVonNBounded_iff** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：isVonNBounded_iff {s : Set E} : Bornology.IsVonNBounded 𝕜 s ↔ Bornology.Is
Bounded s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Absorbs.exists_pos`：Absorbs.exists_pos (h : Absorbs 𝕜 A B) : exists r > 
0, forall c : 𝕜, r <= ‖c‖ -> B subseteq c • A
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NormedField.exists_lt_norm`：exists_lt_norm (r : Real) : exists x : α, r 
< ‖x‖
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Metric.isBounded_ball`：isBounded_ball : IsBounded (ball x r)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ball_normSeminorm`：ball_normSeminorm : (normSeminorm 𝕜 E).ball = Metric.
ball
· 使用定理 `Seminorm.smul_ball_zero`：smul_ball_zero {p : Seminorm 𝕜 E} {k : 𝕜} {r : 
Real} (hk : k != 0) : k • p.ball 0 r = p.ball 0 (‖k‖ * r)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NormedSpace.isVonNBounded_of_isBounded`：isVonNBounded_of_isBounded {s : 
Set E} (h : Bornology.IsBounded s) : Bornology.IsVonNBounded 𝕜 s
-/
theorem isVonNBounded_iff {s : Set E} : Bornology.IsVonNBounded 𝕜 s ↔ Bornology.IsBounded s := by
  refine ⟨fun h ↦ ?_, isVonNBounded_of_isBounded _⟩
  rcases (h (Metric.ball_mem_nhds 0 zero_lt_one)).exists_pos with ⟨ρ, hρ, hρball⟩
  rcases NormedField.exists_lt_norm 𝕜 ρ with ⟨a, ha⟩
  specialize hρball a ha.le
  rw [← ball_normSeminorm 𝕜 E, Seminorm.smul_ball_zero (norm_pos_iff.1 <| hρ.trans ha),
    ball_normSeminorm] at hρball
  exact Metric.isBounded_ball.subset hρball
/-
**NormedSpace.isVonNBounded_iff'** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：isVonNBounded_iff' {s : Set E} : Bornology.IsVonNBounded 𝕜 s ↔ exists r : 
Real, forall x in s, ‖x‖ <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.isVonNBounded_iff`：isVonNBounded_iff {s : Set E} : Bornology
.IsVonNBounded 𝕜 s ↔ Bornology.IsBounded s
· 使用定理 `isBounded_iff_forall_norm_le`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E] {s : Set E}, Bornology.IsBounded s ↔ ∃ C, ∀ x ∈ s, ‖x‖ ≤ C
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isVonNBounded_iff' {s : Set E} :
    Bornology.IsVonNBounded 𝕜 s ↔ ∃ r : ℝ, ∀ x ∈ s, ‖x‖ ≤ r := by
  rw [NormedSpace.isVonNBounded_iff, isBounded_iff_forall_norm_le]
/-
**NormedSpace.image_isVonNBounded_iff** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：image_isVonNBounded_iff {α : Type*} {f : α -> E} {s : Set α} : Bornology.I
sVonNBounded 𝕜 (f '' s) ↔ exists r : Real, forall x in s, ‖f x‖ <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image_isVonNBounded_iff {α : Type*} {f : α → E} {s : Set α} :
    Bornology.IsVonNBounded 𝕜 (f '' s) ↔ ∃ r : ℝ, ∀ x ∈ s, ‖f x‖ ≤ r := by
  simp_rw [isVonNBounded_iff', Set.forall_mem_image]

/-- In a normed space, the von Neumann bornology (`Bornology.vonNBornology`) is equal to the
metric bornology. -/
/-
**NormedSpace.vonNBornology_eq** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：vonNBornology_eq : Bornology.vonNBornology 𝕜 E = PseudoMetricSpace.toBorno
logy
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bornology.ext_iff_isBounded`：ext_iff_isBounded {t t' : Bornology α} : t 
= t' ↔ forall s, @IsBounded α t s ↔ @IsBounded α t' s
· 使用定理 `Bornology.isBounded_iff_isVonNBounded`：isBounded_iff_isVonNBounded {s : 
Set E} : @IsBounded _ (vonNBornology 𝕜 E) s ↔ IsVonNBounded 𝕜 s
· 使用定理 `NormedSpace.isVonNBounded_iff`：isVonNBounded_iff {s : Set E} : Bornology
.IsVonNBounded 𝕜 s ↔ Bornology.IsBounded s

--- 原说明 ---
In a normed space, the von Neumann bornology (`Bornology.vonNBornology`) is equa
l to the
metric bornology.
-/
theorem vonNBornology_eq : Bornology.vonNBornology 𝕜 E = PseudoMetricSpace.toBornology := by
  rw [Bornology.ext_iff_isBounded]
  intro s
  rw [Bornology.isBounded_iff_isVonNBounded]
  exact isVonNBounded_iff _
/-
**NormedSpace.isBounded_iff_subset_smul_ball** 是 Mathlib 中的一个定理，位于命名空间 `NormedSp
ace`。
形式化陈述：isBounded_iff_subset_smul_ball {s : Set E} : Bornology.IsBounded s ↔ exist
s a : 𝕜, s subseteq a • Metric.ball (0 : E) 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.isVonNBounded_iff`：isVonNBounded_iff {s : Set E} : Bornology
.IsVonNBounded 𝕜 s ↔ Bornology.IsBounded s
· 使用引理 `Absorbs.exists_pos`：Absorbs.exists_pos (h : Absorbs 𝕜 A B) : exists r > 
0, forall c : 𝕜, r <= ‖c‖ -> B subseteq c • A
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NormedField.exists_lt_norm`：exists_lt_norm (r : Real) : exists x : α, r 
< ‖x‖
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Bornology.IsVonNBounded.subset`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : 
SeminormedRing 𝕜] [inst_1 : SMul 𝕜 E] [inst_2 : Zero E]   [inst_3 : TopologicalS
pace E] {s₁ s₂ : Set…
· 使用定理 `Bornology.IsVonNBounded.image`：∀ {E : Type u_3} {F : Type u_4} {𝕜₁ : Typ
e u_6} {𝕜₂ : Type u_7} [inst : NormedDivisionRing 𝕜₁]   [inst_1 : NormedDivision
Ring 𝕜₂] [inst_2 : …
· 使用定理 `NormedSpace.isVonNBounded_ball`：isVonNBounded_ball (r : Real) : Bornolog
y.IsVonNBounded 𝕜 (Metric.ball (0 : E) r)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem isBounded_iff_subset_smul_ball {s : Set E} :
    Bornology.IsBounded s ↔ ∃ a : 𝕜, s ⊆ a • Metric.ball (0 : E) 1 := by
  rw [← isVonNBounded_iff 𝕜]
  constructor
  · intro h
    rcases (h (Metric.ball_mem_nhds 0 zero_lt_one)).exists_pos with ⟨ρ, _, hρball⟩
    rcases NormedField.exists_lt_norm 𝕜 ρ with ⟨a, ha⟩
    exact ⟨a, hρball a ha.le⟩
  · rintro ⟨a, ha⟩
    exact ((isVonNBounded_ball 𝕜 E 1).image (a • (1 : E →L[𝕜] E))).subset ha
/-
**NormedSpace.isBounded_iff_subset_smul_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `No
rmedSpace`。
形式化陈述：isBounded_iff_subset_smul_closedBall {s : Set E} : Bornology.IsBounded s ↔
 exists a : 𝕜, s subseteq a • Metric.closedBall (0 : E) 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.isBounded_iff_subset_smul_ball`：isBounded_iff_subset_smul_ba
ll {s : Set E} : Bornology.IsBounded s ↔ exists a : 𝕜, s subseteq a • Metric.bal
l (0 : E) 1
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.smul_set_mono`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s 
t : Set β} {a : α}, s ⊆ t → a • s ⊆ a • t
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.isVonNBounded_iff`：isVonNBounded_iff {s : Set E} : Bornology
.IsVonNBounded 𝕜 s ↔ Bornology.IsBounded s
· 使用定理 `Bornology.IsVonNBounded.subset`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : 
SeminormedRing 𝕜] [inst_1 : SMul 𝕜 E] [inst_2 : Zero E]   [inst_3 : TopologicalS
pace E] {s₁ s₂ : Set…
· 使用定理 `Bornology.IsVonNBounded.image`：∀ {E : Type u_3} {F : Type u_4} {𝕜₁ : Typ
e u_6} {𝕜₂ : Type u_7} [inst : NormedDivisionRing 𝕜₁]   [inst_1 : NormedDivision
Ring 𝕜₂] [inst_2 : …
· 使用定理 `NormedSpace.isVonNBounded_closedBall`：isVonNBounded_closedBall (r : Real
) : Bornology.IsVonNBounded 𝕜 (Metric.closedBall (0 : E) r)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem isBounded_iff_subset_smul_closedBall {s : Set E} :
    Bornology.IsBounded s ↔ ∃ a : 𝕜, s ⊆ a • Metric.closedBall (0 : E) 1 := by
  constructor
  · rw [isBounded_iff_subset_smul_ball 𝕜]
    exact Exists.imp fun a ha => ha.trans <| Set.smul_set_mono <| Metric.ball_subset_closedBall
  · rw [← isVonNBounded_iff 𝕜]
    rintro ⟨a, ha⟩
    exact ((isVonNBounded_closedBall 𝕜 E 1).image (a • (1 : E →L[𝕜] E))).subset ha

end NormedSpace

end VonNBornologyEqMetric

section QuasiCompleteSpace

/-- A locally convex space is quasi-complete if every closed and von Neumann bounded set is
complete. -/
/-
**QuasiCompleteSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕜 : Type u_6) → (E : Type u_7) → [Zero E] → [UniformSpace E] → [Seminorme
dRing 𝕜] → [SMul 𝕜 E] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A locally convex space is quasi-complete if every closed and von Neumann bounded
 set is
complete.
-/
class QuasiCompleteSpace (𝕜 : Type*) (E : Type*) [Zero E] [UniformSpace E] [SeminormedRing 𝕜]
    [SMul 𝕜 E] : Prop where
  /-- A locally convex space is quasi-complete if every closed and von Neumann bounded set is
  complete. -/
  quasiComplete : ∀ ⦃s : Set E⦄, Bornology.IsVonNBounded 𝕜 s → IsClosed s → IsComplete s

variable {𝕜 : Type*} {E : Type*} [Zero E] [UniformSpace E] [SeminormedRing 𝕜] [SMul 𝕜 E]

/-- A complete space is quasi-complete with respect to any scalar ring. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complete space is quasi-complete with respect to any scalar ring.
-/
instance [CompleteSpace E] : QuasiCompleteSpace 𝕜 E where
  quasiComplete _ _ := IsClosed.isComplete

/-- [Bourbaki, *Topological Vector Spaces*, III §1.6][bourbaki1987] -/
/-
**isCompact_closure_of_totallyBounded_quasiComplete** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：isCompact_closure_of_totallyBounded_quasiComplete {E : Type*} {𝕜 : Type*} 
[NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGrou
p E] [ContinuousSMul 𝕜 E] [QuasiCompleteSpace 𝕜 E] {s : Set E} (hs : TotallyBoun
ded s) : IsCompact (closure s)
参数：hs : TotallyBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TotallyBounded.isCompact_of_isComplete`：TotallyBounded.isCompact_of_isCo
mplete {s : Set α} (ht : TotallyBounded s) (hc : IsComplete s) : IsCompact s
· 使用定理 `TotallyBounded.closure`：TotallyBounded.closure {s : Set α} (h : TotallyB
ounded s) : TotallyBounded (closure s)
· 使用定理 `QuasiCompleteSpace.quasiComplete`：∀ {𝕜 : Type u_6} {E : Type u_7} {inst 
: Zero E} {inst_1 : UniformSpace E} {inst_2 : SeminormedRing 𝕜}   {inst_3 : SMul
 𝕜 E} [self : QuasiCom…
· 使用定理 `TotallyBounded.isVonNBounded`：TotallyBounded.isVonNBounded {s : Set E} (
hs : TotallyBounded s) : Bornology.IsVonNBounded 𝕜 s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)

--- 原说明 ---
[Bourbaki, *Topological Vector Spaces*, III §1.6][bourbaki1987]
-/
theorem isCompact_closure_of_totallyBounded_quasiComplete {E : Type*} {𝕜 : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [QuasiCompleteSpace 𝕜 E] {s : Set E} (hs : TotallyBounded s) : IsCompact (closure s) :=
  hs.closure.isCompact_of_isComplete
    (QuasiCompleteSpace.quasiComplete (TotallyBounded.isVonNBounded 𝕜 (TotallyBounded.closure hs))
    isClosed_closure)

end QuasiCompleteSpace

