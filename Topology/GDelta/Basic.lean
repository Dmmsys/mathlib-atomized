/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.CountableInter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Data.Set.Notation
import Mathlib.Topology.Constructions

/-!
# `Gδ` sets

In this file we define `Gδ` sets and prove their basic properties.

## Main definitions

* `IsGδ`: a set `s` is a `Gδ` set if it can be represented as an intersection
  of countably many open sets;

* `residual`: the σ-filter of residual sets. A set `s` is called *residual* if it includes a
  countable intersection of dense open sets.

* `IsNowhereDense`: a set is called *nowhere dense* iff its closure has empty interior
* `IsMeagre`: a set `s` is called *meagre* iff its complement is residual

## Main results

We prove that finite or countable intersections of Gδ sets are Gδ sets.

- `isClosed_isNowhereDense_iff_compl`: a closed set is nowhere dense iff
  its complement is open and dense
- `isMeagre_iff_countable_union_isNowhereDense`: a set is meagre iff it is contained in a countable
  union of nowhere dense sets
- subsets of meagre sets are meagre; countable unions of meagre sets are meagre

See `Mathlib/Topology/GDelta/MetrizableSpace.lean` for the proof that
continuity set of a function from a topological space to a metrizable space is a Gδ set.

## Tags

Gδ set, residual set, nowhere dense set, meagre set
-/

@[expose] public section

assert_not_exists UniformSpace

noncomputable section

open Topology TopologicalSpace Filter Encodable Set

variable {X Y ι : Type*} {ι' : Sort*}


section IsGδ

variable [TopologicalSpace X]

/-- A Gδ set is a countable intersection of open sets. -/
/-
**IsG** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Gδ set is a countable intersection of open sets.
-/
def IsGδ (s : Set X) : Prop :=
  ∃ T : Set (Set X), (∀ t ∈ T, IsOpen t) ∧ T.Countable ∧ s = ⋂₀ T

/-- An open set is a Gδ set. -/
/-
**IsOpen.isG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open set is a Gδ set.
-/
theorem IsOpen.isGδ {s : Set X} (h : IsOpen s) : IsGδ s :=
  ⟨{s}, by simp [h], countable_singleton _, (Set.sInter_singleton _).symm⟩

@[simp]
/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem IsGδ.empty : IsGδ (∅ : Set X) :=
  isOpen_empty.isGδ


@[simp]
/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem IsGδ.univ : IsGδ (univ : Set X) :=
  isOpen_univ.isGδ
/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsGδ.biInter_of_isOpen {I : Set ι} (hI : I.Countable) {f : ι → Set X}
    (hf : ∀ i ∈ I, IsOpen (f i)) : IsGδ (⋂ i ∈ I, f i) :=
  ⟨f '' I, by rwa [forall_mem_image], hI.image _, by rw [sInter_image]⟩
/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsGδ.iInter_of_isOpen [Countable ι'] {f : ι' → Set X} (hf : ∀ i, IsOpen (f i)) :
    IsGδ (⋂ i, f i) :=
  ⟨range f, by rwa [forall_mem_range], countable_range _, by rw [sInter_range]⟩
/-
**isG** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isGδ_iff_eq_iInter_nat {s : Set X} :
    IsGδ s ↔ ∃ (f : ℕ → Set X), (∀ n, IsOpen (f n)) ∧ s = ⋂ n, f n := by
  refine ⟨?_, ?_⟩
  · rintro ⟨T, hT, T_count, rfl⟩
    rcases Set.eq_empty_or_nonempty T with rfl | hT
    · exact ⟨fun _n ↦ univ, fun _n ↦ isOpen_univ, by simp⟩
    · obtain ⟨f, hf⟩ : ∃ (f : ℕ → Set X), T = range f := Countable.exists_eq_range T_count hT
      exact ⟨f, by simp_all, by simp [hf]⟩
  · rintro ⟨f, hf, rfl⟩
    exact .iInter_of_isOpen hf

alias ⟨IsGδ.eq_iInter_nat, _⟩ := isGδ_iff_eq_iInter_nat

/-- The intersection of an encodable family of Gδ sets is a Gδ set. -/
/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intersection of an encodable family of Gδ sets is a Gδ set.
-/
protected theorem IsGδ.iInter [Countable ι'] {s : ι' → Set X} (hs : ∀ i, IsGδ (s i)) :
    IsGδ (⋂ i, s i) := by
  choose T hTo hTc hTs using hs
  obtain rfl : s = fun i => ⋂₀ T i := funext hTs
  refine ⟨⋃ i, T i, ?_, countable_iUnion hTc, (sInter_iUnion _).symm⟩
  simpa [@forall_comm ι'] using hTo
/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsGδ.biInter {s : Set ι} (hs : s.Countable) {t : ∀ i ∈ s, Set X}
    (ht : ∀ (i) (hi : i ∈ s), IsGδ (t i hi)) : IsGδ (⋂ i ∈ s, t i ‹_›) := by
  rw [biInter_eq_iInter]
  have := hs.to_subtype
  exact .iInter fun x => ht x x.2


/-- A countable intersection of Gδ sets is a Gδ set. -/
/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A countable intersection of Gδ sets is a Gδ set.
-/
theorem IsGδ.sInter {S : Set (Set X)} (h : ∀ s ∈ S, IsGδ s) (hS : S.Countable) : IsGδ (⋂₀ S) := by
  simpa only [sInter_eq_biInter] using IsGδ.biInter hS h
/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsGδ.inter {s t : Set X} (hs : IsGδ s) (ht : IsGδ t) : IsGδ (s ∩ t) := by
  rw [inter_eq_iInter]
  exact .iInter (Bool.forall_bool.2 ⟨ht, hs⟩)

/-- The union of two Gδ sets is a Gδ set. -/
/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The union of two Gδ sets is a Gδ set.
-/
theorem IsGδ.union {s t : Set X} (hs : IsGδ s) (ht : IsGδ t) : IsGδ (s ∪ t) := by
  rcases hs with ⟨S, Sopen, Scount, rfl⟩
  rcases ht with ⟨T, Topen, Tcount, rfl⟩
  rw [sInter_union_sInter]
  refine .biInter_of_isOpen (Scount.prod Tcount) ?_
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  exact (Sopen a ha).union (Topen b hb)

/-- The union of finitely many Gδ sets is a Gδ set, `Set.sUnion` version. -/
/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The union of finitely many Gδ sets is a Gδ set, `Set.sUnion` version.
-/
theorem IsGδ.sUnion {S : Set (Set X)} (hS : S.Finite) (h : ∀ s ∈ S, IsGδ s) : IsGδ (⋃₀ S) := by
  induction S, hS using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp only [forall_mem_insert, sUnion_insert] at *
    exact h.1.union (ih h.2)

/-- The union of finitely many Gδ sets is a Gδ set, bounded indexed union version. -/
/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The union of finitely many Gδ sets is a Gδ set, bounded indexed union version.
-/
theorem IsGδ.biUnion {s : Set ι} (hs : s.Finite) {f : ι → Set X} (h : ∀ i ∈ s, IsGδ (f i)) :
    IsGδ (⋃ i ∈ s, f i) := by
  rw [← sUnion_image]
  exact .sUnion (hs.image _) (forall_mem_image.2 h)

/-- The union of finitely many Gδ sets is a Gδ set, bounded indexed union version. -/
/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The union of finitely many Gδ sets is a Gδ set, bounded indexed union version.
-/
theorem IsGδ.iUnion [Finite ι'] {f : ι' → Set X} (h : ∀ i, IsGδ (f i)) : IsGδ (⋃ i, f i) :=
  .sUnion (finite_range _) <| forall_mem_range.2 h

/-- The preimage of a Gδ set under a continuous map is Gδ. -/
/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a Gδ set under a continuous map is Gδ.
-/
theorem IsGδ.preimage [TopologicalSpace Y] {f : X → Y} {s : Set Y} (hf : Continuous f)
    (hs : IsGδ s) : IsGδ (f ⁻¹' s) := by
  obtain ⟨U, hU1, hU2⟩ := hs.eq_iInter_nat
  simp_all only [preimage_iInter]
  exact IsGδ.iInter_of_isOpen (fun i => hf.isOpen_preimage (U i) (hU1 i))

@[deprecated (since := "2026-05-19")] alias isGδ_induced := IsGδ.preimage

end IsGδ

section residual

variable [TopologicalSpace X]

/-- A set `s` is called *residual* if it includes a countable intersection of dense open sets. -/
/-
**residual** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：residual (X : Type*) [TopologicalSpace X] : Filter X
参数：X : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is called *residual* if it includes a countable intersection of dense 
open sets.
-/
def residual (X : Type*) [TopologicalSpace X] : Filter X :=
  Filter.countableGenerate { t | IsOpen t ∧ Dense t }
/-
**countableInterFilter_residual** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：countableInterFilter_residual : CountableInterFilter (residual X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `residual.eq_1`：∀ (X : Type u_5) [inst : TopologicalSpace X], residual X 
= Filter.countableGenerate {t | IsOpen t ∧ Dense t}
· 使用定理 `Filter.instCountableInterFilterCountableGenerate`：∀ {α : Type u_1} (g : 
Set (Set α)), CountableInterFilter (Filter.countableGenerate g)
-/
instance countableInterFilter_residual : CountableInterFilter (residual X) := by
  rw [residual]; infer_instance

/-- Dense open sets are residual. -/
/-
**residual_of_dense_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：residual_of_dense_open {s : Set X} (ho : IsOpen s) (hd : Dense s) : s in r
esidual X
参数：ho : IsOpen s；hd : Dense s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dense open sets are residual.
-/
theorem residual_of_dense_open {s : Set X} (ho : IsOpen s) (hd : Dense s) : s ∈ residual X :=
  CountableGenerateSets.basic ⟨ho, hd⟩

/-- Dense Gδ sets are residual. -/
/-
**residual_of_dense_G** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dense Gδ sets are residual.
-/
theorem residual_of_dense_Gδ {s : Set X} (ho : IsGδ s) (hd : Dense s) : s ∈ residual X := by
  rcases ho with ⟨T, To, Tct, rfl⟩
  exact
    (countable_sInter_mem Tct).mpr fun t tT =>
      residual_of_dense_open (To t tT) (hd.mono (sInter_subset_of_mem tT))

/-- A set is residual iff it includes a countable intersection of dense open sets. -/
/-
**mem_residual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_residual_iff {s : Set X} : s in residual X ↔ exists S : Set (Set X), (
forall t in S, IsOpen t) ∧ (forall t in S, Dense t) ∧ S.Countable ∧ ⋂₀ S subsete
q s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.mem_countableGenerate_iff`：mem_countableGenerate_iff {s : Set α} 
: s in countableGenerate g ↔ exists S : Set (Set α), S subseteq g ∧ S.Countable 
∧ ⋂₀ S subseteq s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A set is residual iff it includes a countable intersection of dense open sets.
-/
theorem mem_residual_iff {s : Set X} :
    s ∈ residual X ↔
      ∃ S : Set (Set X), (∀ t ∈ S, IsOpen t) ∧ (∀ t ∈ S, Dense t) ∧ S.Countable ∧ ⋂₀ S ⊆ s :=
  mem_countableGenerate_iff.trans <| by simp_rw [subset_def, mem_ofPred, forall_and, and_assoc]

end residual

section IsMeagre
open Function TopologicalSpace Set
variable [TopologicalSpace X]

/-- A set is called **nowhere dense** iff its closure has empty interior. -/
/-
**IsNowhereDense** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsNowhereDense (s : Set X)
参数：s : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set is called **nowhere dense** iff its closure has empty interior.
-/
def IsNowhereDense (s : Set X) := interior (closure s) = ∅

/-- The empty set is nowhere dense. -/
@[simp]
/-
**isNowhereDense_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isNowhereDense_empty : IsNowhereDense (∅ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsNowhereDense.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (s : S
et X), IsNowhereDense s = (interior (closure s) = ∅)
· 使用定理 `closure_empty`：closure_empty : closure (∅ : Set X) = ∅
· 使用定理 `interior_empty`：interior_empty : interior (∅ : Set X) = ∅

--- 原说明 ---
The empty set is nowhere dense.
-/
lemma isNowhereDense_empty : IsNowhereDense (∅ : Set X) := by
  rw [IsNowhereDense, closure_empty, interior_empty]

/-- A subset of a nowhere dense set is nowhere dense. -/
@[gcongr]
/-
**IsNowhereDense.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsNowhereDense.mono {s t : Set X} (ht : t subseteq s) (hs : IsNowhereDense
 s) : IsNowhereDense t
参数：ht : t subseteq s；hs : IsNowhereDense s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_of_subset_empty`：eq_empty_of_subset_empty {s : Set α} : s s
ubseteq ∅ -> s = ∅
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
A subset of a nowhere dense set is nowhere dense.
-/
lemma IsNowhereDense.mono {s t : Set X} (ht : t ⊆ s) (hs : IsNowhereDense s) : IsNowhereDense t :=
  Set.eq_empty_of_subset_empty <| by grw [ht]; rw [hs]

/-- A closed set is nowhere dense iff its interior is empty. -/
/-
**IsClosed.isNowhereDense_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.isNowhereDense_iff {s : Set X} (hs : IsClosed s) : IsNowhereDense
 s ↔ interior s = ∅
参数：hs : IsClosed s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsNowhereDense.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (s : S
et X), IsNowhereDense s = (interior (closure s) = ∅)
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A closed set is nowhere dense iff its interior is empty.
-/
lemma IsClosed.isNowhereDense_iff {s : Set X} (hs : IsClosed s) :
    IsNowhereDense s ↔ interior s = ∅ := by
  rw [IsNowhereDense, IsClosed.closure_eq hs]

/-- If a set `s` is nowhere dense, so is its closure. -/
/-
**IsNowhereDense.closure** 是 Mathlib 中的一个定理，位于命名空间 `IsNowhereDense`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {s : Set X}, IsNowhereDense s
 → IsNowhereDense (closure s)
参数：closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsNowhereDense.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (s : S
et X), IsNowhereDense s = (interior (closure s) = ∅)
· 使用定理 `closure_closure`：closure_closure : closure (closure s) = closure s

--- 原说明 ---
If a set `s` is nowhere dense, so is its closure.
-/
protected lemma IsNowhereDense.closure {s : Set X} (hs : IsNowhereDense s) :
    IsNowhereDense (closure s) := by
  rwa [IsNowhereDense, closure_closure]

/-- A nowhere dense set `s` is contained in a closed nowhere dense set (namely, its closure). -/
/-
**IsNowhereDense.subset_of_closed_isNowhereDense** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsNowhereDense.subset_of_closed_isNowhereDense {s : Set X} (hs : IsNowhere
Dense s) : exists t : Set X, s subseteq t ∧ IsNowhereDense t ∧ IsClosed t
参数：hs : IsNowhereDense s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `IsNowhereDense.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s 
: Set X}, IsNowhereDense s → IsNowhereDense (closure s)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)

--- 原说明 ---
A nowhere dense set `s` is contained in a closed nowhere dense set (namely, its 
closure).
-/
lemma IsNowhereDense.subset_of_closed_isNowhereDense {s : Set X} (hs : IsNowhereDense s) :
    ∃ t : Set X, s ⊆ t ∧ IsNowhereDense t ∧ IsClosed t :=
  ⟨closure s, subset_closure, ⟨hs.closure, isClosed_closure⟩⟩

/-- A set `s` is closed and nowhere dense iff its complement `sᶜ` is open and dense. -/
/-
**isClosed_isNowhereDense_iff_compl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_isNowhereDense_iff_compl {s : Set X} : IsClosed s ∧ IsNowhereDens
e s ↔ IsOpen sᶜ ∧ Dense sᶜ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用引理 `IsClosed.isNowhereDense_iff`：IsClosed.isNowhereDense_iff {s : Set X} (hs
 : IsClosed s) : IsNowhereDense s ↔ interior s = ∅
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `interior_eq_empty_iff_dense_compl`：interior_eq_empty_iff_dense_compl : i
nterior s = ∅ ↔ Dense sᶜ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A set `s` is closed and nowhere dense iff its complement `sᶜ` is open and dense.
-/
lemma isClosed_isNowhereDense_iff_compl {s : Set X} :
    IsClosed s ∧ IsNowhereDense s ↔ IsOpen sᶜ ∧ Dense sᶜ := by
  rw [and_congr_right IsClosed.isNowhereDense_iff,
    isOpen_compl_iff, interior_eq_empty_iff_dense_compl]

/-- To check that `s` is nowhere dense, it suffices to check that no point of `s`
is in the interior of `closure s`. -/
/-
**isNowhereDense_iff_disjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isNowhereDense_iff_disjoint {s : Set X} : IsNowhereDense s ↔ Disjoint s (i
nterior (closure s))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.disjoint_empty`：∀ {α : Type u} (s : Set α), Disjoint s ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Disjoint.eq_bot_of_self`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_
1 : OrderBot α] {a : α}, Disjoint a a → a = ⊥
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Disjoint.closure_left`：Disjoint.closure_left (hd : Disjoint s t) (ht : I
sOpen t) : Disjoint (closure s) t
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)

--- 原说明 ---
To check that `s` is nowhere dense, it suffices to check that no point of `s`
is in the interior of `closure s`.
-/
lemma isNowhereDense_iff_disjoint {s : Set X} :
    IsNowhereDense s ↔ Disjoint s (interior (closure s)) :=
  ⟨fun H ↦ H ▸ disjoint_empty _, fun H ↦
    H.closure_left isOpen_interior |>.mono_left interior_subset |>.eq_bot_of_self⟩

/-- To check that `s` is nowhere dense, it suffices to check that `closure s` is not a
neighborhood of any point of `s`. -/
/-
**isNowhereDense_iff_forall_notMem_nhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isNowhereDense_iff_forall_notMem_nhds {s : Set X} : IsNowhereDense s ↔ for
all x in s, closure s ∉ 𝓝 x
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
To check that `s` is nowhere dense, it suffices to check that `closure s` is not
 a
neighborhood of any point of `s`.
-/
lemma isNowhereDense_iff_forall_notMem_nhds {s : Set X} :
    IsNowhereDense s ↔ ∀ x ∈ s, closure s ∉ 𝓝 x := by
  simp [isNowhereDense_iff_disjoint, disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem,
    mem_interior_iff_mem_nhds]

/-- The image of a nowhere dense set through an inducing map is nowhere dense. -/
/-
**Topology.IsInducing.isNowhereDense_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.isNowhereDense_image [TopologicalSpace Y] {f : X -> Y}
 (hf : Topology.IsInducing f) {s : Set X} (h : IsNowhereDense s) : IsNowhereDens
e (f '' s)
参数：hf : Topology.IsInducing f；h : IsNowhereDense s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isNowhereDense_iff_forall_notMem_nhds`：isNowhereDense_iff_forall_notMem_
nhds {s : Set X} : IsNowhereDense s ↔ forall x in s, closure s ∉ 𝓝 x
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Topology.IsInducing.closure_eq_preimage_closure_image`：closure_eq_preima
ge_closure_image (hf : IsInducing f) (s : Set X) : closure s = f ⁻¹' closure (f 
'' s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g

--- 原说明 ---
The image of a nowhere dense set through an inducing map is nowhere dense.
-/
lemma Topology.IsInducing.isNowhereDense_image [TopologicalSpace Y] {f : X → Y}
    (hf : Topology.IsInducing f) {s : Set X} (h : IsNowhereDense s) : IsNowhereDense (f '' s) := by
  rw [isNowhereDense_iff_forall_notMem_nhds, forall_mem_image] at *
  simp_rw [hf.nhds_eq_comap, hf.closure_eq_preimage_closure_image] at h
  exact fun x x_mem hx ↦ h x x_mem (preimage_mem_comap hx)

/-- A set is nowhere dense if it is nowhere dense in some subspace. -/
/-
**IsNowhereDense.image_val** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsNowhereDense.image_val {Y : Set X} {s : Set Y} (hs : IsNowhereDense s) :
 IsNowhereDense (s : Set X)
参数：hs : IsNowhereDense s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.isNowhereDense_image`：Topology.IsInducing.isNowhereD
ense_image [TopologicalSpace Y] {f : X -> Y} (hf : Topology.IsInducing f) {s : S
et X} (h : IsNowhereDense s) :…
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)

--- 原说明 ---
A set is nowhere dense if it is nowhere dense in some subspace.
-/
lemma IsNowhereDense.image_val {Y : Set X} {s : Set Y}
    (hs : IsNowhereDense s) : IsNowhereDense (s : Set X) :=
  Topology.IsInducing.subtypeVal.isNowhereDense_image hs

/-- A set is called **meagre** iff its complement is a residual (or comeagre) set. -/
/-
**IsMeagre** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsMeagre (s : Set X)
参数：s : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set is called **meagre** iff its complement is a residual (or comeagre) set.
-/
def IsMeagre (s : Set X) := sᶜ ∈ residual X

/-- The empty set is meagre. -/
/-
**IsMeagre.empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMeagre.empty : IsMeagre (∅ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMeagre.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (s : Set X),
 IsMeagre s = (sᶜ ∈ residual X)
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f

--- 原说明 ---
The empty set is meagre.
-/
lemma IsMeagre.empty : IsMeagre (∅ : Set X) := by
  rw [IsMeagre, compl_empty]
  exact Filter.univ_mem

/-- Subsets of meagre sets are meagre. -/
@[gcongr]
/-
**IsMeagre.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMeagre.mono {s t : Set X} (hts : t subseteq s) (hs : IsMeagre s) : IsMea
gre t
参数：hts : t subseteq s；hs : IsMeagre s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s

--- 原说明 ---
Subsets of meagre sets are meagre.
-/
lemma IsMeagre.mono {s t : Set X} (hts : t ⊆ s) (hs : IsMeagre s) : IsMeagre t :=
  Filter.mem_of_superset hs (compl_subset_compl.mpr hts)

/-- An intersection with a meagre set is meagre. -/
/-
**IsMeagre.inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMeagre.inter {s t : Set X} (hs : IsMeagre s) : IsMeagre (s inter t)
参数：hs : IsMeagre s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsMeagre.mono`：IsMeagre.mono {s t : Set X} (hts : t subseteq s) (hs : Is
Meagre s) : IsMeagre t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s

--- 原说明 ---
An intersection with a meagre set is meagre.
-/
lemma IsMeagre.inter {s t : Set X} (hs : IsMeagre s) : IsMeagre (s ∩ t) :=
  hs.mono inter_subset_left

/-- A union of two meagre sets is meagre. -/
/-
**IsMeagre.union** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMeagre.union {s t : Set X} (hs : IsMeagre s) (ht : IsMeagre t) : IsMeagr
e (s union t)
参数：hs : IsMeagre s；ht : IsMeagre t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMeagre.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (s : Set X),
 IsMeagre s = (sᶜ ∈ residual X)
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f

--- 原说明 ---
A union of two meagre sets is meagre.
-/
lemma IsMeagre.union {s t : Set X} (hs : IsMeagre s) (ht : IsMeagre t) : IsMeagre (s ∪ t) := by
  rw [IsMeagre, compl_union]
  exact inter_mem hs ht

/-- A countable union of meagre sets is meagre. -/
/-
**isMeagre_iUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMeagre_iUnion [Countable ι'] {f : ι' -> Set X} (hs : forall i, IsMeagre 
(f i)) : IsMeagre (⋃ i, f i)
参数：hs : forall i, IsMeagre (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMeagre.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (s : Set X),
 IsMeagre s = (sᶜ ∈ residual X)
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `countable_iInter_mem`：countable_iInter_mem [Countable ι] {s : ι -> Set α
} : (⋂ i, s i) in l ↔ forall i, s i in l

--- 原说明 ---
A countable union of meagre sets is meagre.
-/
lemma isMeagre_iUnion [Countable ι'] {f : ι' → Set X} (hs : ∀ i, IsMeagre (f i)) :
    IsMeagre (⋃ i, f i) := by
  rw [IsMeagre, compl_iUnion]
  exact countable_iInter_mem.mpr hs
/-
**isMeagre_biUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMeagre_biUnion {I : Set ι} (c : I.Countable) {f : ι -> Set X} (h : foral
l i in I, IsMeagre (f i)) : IsMeagre (⋃ i in I, f i)
参数：c : I.Countable；h : forall i in I, IsMeagre (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMeagre_iUnion`：isMeagre_iUnion [Countable ι'] {f : ι' -> Set X} (hs : 
forall i, IsMeagre (f i)) : IsMeagre (⋃ i, f i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
lemma isMeagre_biUnion {I : Set ι} (c : I.Countable) {f : ι → Set X}
    (h : ∀ i ∈ I, IsMeagre (f i)) : IsMeagre (⋃ i ∈ I, f i) := by
  suffices IsMeagre (⋃ i : I, f i) by simpa
  have : Countable I := c
  apply isMeagre_iUnion
  intro ⟨i, hi⟩
  exact h i hi

/-- A set is meagre iff it is contained in a countable union of nowhere dense sets. -/
/-
**isMeagre_iff_countable_union_isNowhereDense** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMeagre_iff_countable_union_isNowhereDense {s : Set X} : IsMeagre s ↔ exi
sts S : Set (Set X), (forall t in S, IsNowhereDense t) ∧ S.Countable ∧ s subsete
q ⋃₀ S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMeagre.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (s : Set X),
 IsMeagre s = (sᶜ ∈ residual X)
· 使用定理 `mem_residual_iff`：mem_residual_iff {s : Set X} : s in residual X ↔ exist
s S : Set (Set X), (forall t in S, IsOpen t) ∧ (forall t in S, Dense t) ∧ S.Coun
table …
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `Function.Surjective.image_surjective`：∀ {α : Type u_1} {β : Type u_2} {f
 : α → β}, Function.Surjective f → Function.Surjective (Set.image f)
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `compl_bijective`：compl_bijective : Function.Bijective (compl : α -> α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.compl_compl_image`：compl_compl_image [BooleanAlgebra α] (s : Set α) 
: Compl.compl '' Compl.compl '' s = s
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `IsNowhereDense.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s 
: Set X}, IsNowhereDense s → IsNowhereDense (closure s)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Set.sUnion_mono_subsets`：sUnion_mono_subsets {s : Set (Set α)} {f : Set 
α -> Set α} (hf : forall t : Set α, t subseteq f t) : ⋃₀ s subseteq ⋃₀ (f '' s)
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
A set is meagre iff it is contained in a countable union of nowhere dense sets.
-/
lemma isMeagre_iff_countable_union_isNowhereDense {s : Set X} :
    IsMeagre s ↔ ∃ S : Set (Set X), (∀ t ∈ S, IsNowhereDense t) ∧ S.Countable ∧ s ⊆ ⋃₀ S := by
  rw [IsMeagre, mem_residual_iff, compl_bijective.surjective.image_surjective.exists]
  simp_rw [← and_assoc, ← forall_and, forall_mem_image, ← isClosed_isNowhereDense_iff_compl,
    sInter_image, ← compl_iUnion₂, compl_subset_compl, ← sUnion_eq_biUnion, and_assoc]
  refine ⟨fun ⟨S, hS, hc, hsub⟩ ↦ ⟨S, fun s hs ↦ (hS hs).2, ?_, hsub⟩, ?_⟩
  · rw [← compl_compl_image S]; exact hc.image _
  · intro ⟨S, hS, hc, hsub⟩
    use closure '' S
    rw [forall_mem_image]
    exact ⟨fun s hs ↦ ⟨isClosed_closure, (hS s hs).closure⟩,
      (hc.image _).image _, hsub.trans (sUnion_mono_subsets fun s ↦ subset_closure)⟩

/-- A set of second category (i.e. non-meagre) is nonempty. -/
/-
**nonempty_of_not_isMeagre** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nonempty_of_not_isMeagre {s : Set X} (hs : ¬IsMeagre s) : s.Nonempty
参数：hs : ¬IsMeagre s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsMeagre.empty`：IsMeagre.empty : IsMeagre (∅ : Set X)

--- 原说明 ---
A set of second category (i.e. non-meagre) is nonempty.
-/
lemma nonempty_of_not_isMeagre {s : Set X} (hs : ¬IsMeagre s) : s.Nonempty := by
  contrapose! hs
  simpa [hs] using IsMeagre.empty

/-- A nowhere dense set is meagre. -/
/-
**IsNowhereDense.isMeagre** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsNowhereDense.isMeagre {s : Set X} (h : IsNowhereDense s) : IsMeagre s
参数：h : IsNowhereDense s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isMeagre_iff_countable_union_isNowhereDense`：isMeagre_iff_countable_unio
n_isNowhereDense {s : Set X} : IsMeagre s ↔ exists S : Set (Set X), (forall t in
 S, IsNowhereDense t) ∧ S.Countab…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.sUnion_singleton`：sUnion_singleton (s : Set α) : ⋃₀ {s} = s

--- 原说明 ---
A nowhere dense set is meagre.
-/
lemma IsNowhereDense.isMeagre {s : Set X} (h : IsNowhereDense s) : IsMeagre s := by
  rw [isMeagre_iff_countable_union_isNowhereDense]
  exact ⟨{s}, by simpa, by simp, by simp⟩
/-
**exists_of_not_isMeagre_biUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_of_not_isMeagre_biUnion {I : Set ι} (c : I.Countable) {A : ι -> Set
 X} (h : ¬IsMeagre (⋃ i in I, A i)) : exists i in I, ¬IsMeagre (A i)
参数：c : I.Countable；h : ¬IsMeagre (⋃ i in I, A i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用引理 `isMeagre_biUnion`：isMeagre_biUnion {I : Set ι} (c : I.Countable) {f : ι 
-> Set X} (h : forall i in I, IsMeagre (f i)) : IsMeagre (⋃ i in I, f i)
-/
lemma exists_of_not_isMeagre_biUnion {I : Set ι}
    (c : I.Countable) {A : ι → Set X} (h : ¬IsMeagre (⋃ i ∈ I, A i)) :
    ∃ i ∈ I, ¬IsMeagre (A i) := by
  contrapose! h
  exact isMeagre_biUnion c h

/-- The image of a meagre set through an inducing map is meagre. -/
/-
**Topology.IsInducing.isMeagre_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.isMeagre_image [TopologicalSpace Y] {f : X -> Y} (hf :
 Topology.IsInducing f) {s : Set X} (h : IsMeagre s) : IsMeagre (f '' s)
参数：hf : Topology.IsInducing f；h : IsMeagre s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isMeagre_iff_countable_union_isNowhereDense`：isMeagre_iff_countable_unio
n_isNowhereDense {s : Set X} : IsMeagre s ↔ exists S : Set (Set X), (forall t in
 S, IsNowhereDense t) ∧ S.Countab…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsInducing.isNowhereDense_image`：Topology.IsInducing.isNowhereD
ense_image [TopologicalSpace Y] {f : X -> Y} (hf : Topology.IsInducing f) {s : S
et X} (h : IsNowhereDense s) :…
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `Set.image_sUnion`：image_sUnion {f : α -> β} {s : Set (Set α)} : (f '' ⋃₀
 s) = ⋃₀ (image f '' s)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The image of a meagre set through an inducing map is meagre.
-/
lemma Topology.IsInducing.isMeagre_image [TopologicalSpace Y] {f : X → Y}
    (hf : Topology.IsInducing f) {s : Set X} (h : IsMeagre s) : IsMeagre (f '' s) := by
  rw [isMeagre_iff_countable_union_isNowhereDense] at *
  obtain ⟨T, isNowhereDense, countable, cover⟩ := h
  refine ⟨(Set.image f) '' T, ?isNowhereDense, countable.image _, ?cover⟩
  case isNowhereDense =>
    intro u ⟨t, tT, tu⟩
    rw [← tu]
    apply hf.isNowhereDense_image (isNowhereDense t tT)
  case cover =>
    rw [← Set.image_sUnion]
    grw [cover]

/-- A set is meagre if it is meagre in some subspace. -/
/-
**IsMeagre.image_val** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMeagre.image_val {s : Set X} {m : Set s} (h : IsMeagre (m : Set s)) : Is
Meagre (m : Set X)
参数：h : IsMeagre (m : Set s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.isMeagre_image`：Topology.IsInducing.isMeagre_image [
TopologicalSpace Y] {f : X -> Y} (hf : Topology.IsInducing f) {s : Set X} (h : I
sMeagre s) : IsMeagre (f…
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)

--- 原说明 ---
A set is meagre if it is meagre in some subspace.
-/
lemma IsMeagre.image_val {s : Set X} {m : Set s} (h : IsMeagre (m : Set s)) :
    IsMeagre (m : Set X) := Topology.IsInducing.subtypeVal.isMeagre_image h

end IsMeagre

