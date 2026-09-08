/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yury Kudryashov
-/
module

public import Mathlib.Topology.NhdsSet
public import Mathlib.Topology.Inseparable

/-!
# Neighborhoods kernel of a set

In `Mathlib/Topology/Defs/Filter.lean`, `nhdsKer s` is defined to be the intersection of all
neighborhoods of `s`.
Note that this construction has no standard name in the literature.

In this file we prove basic properties of this operation.
-/

public section

open Set Filter
open scoped Topology

variable {ι : Sort*} {X : Type*} [TopologicalSpace X] {s t : Set X} {x y : X}

/-
**nhdsKer_singleton_eq_ker_nhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsKer_singleton_eq_ker_nhds (x : X) : nhdsKer {x} = (𝓝 x).ker
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nhdsKer_singleton_eq_ker_nhds (x : X) : nhdsKer {x} = (𝓝 x).ker := by simp [nhdsKer]

@[simp]
/-
**mem_nhdsKer_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsKer_singleton : x in nhdsKer {y} ↔ x ⤳ y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `nhdsKer_singleton_eq_ker_nhds`：nhdsKer_singleton_eq_ker_nhds (x : X) : n
hdsKer {x} = (𝓝 x).ker
· 使用定理 `ker_nhds_eq_specializes`：ker_nhds_eq_specializes : (𝓝 x).ker = {y | y ⤳ 
x}
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nhdsKer_singleton : x ∈ nhdsKer {y} ↔ x ⤳ y := by
  rw [nhdsKer_singleton_eq_ker_nhds, ker_nhds_eq_specializes, mem_ofPred]
/-
**nhdsKer_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsKer_def (s : Set X) : nhdsKer s = ⋂₀ {t : Set X | IsOpen t ∧ s subsete
q t}
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.ker`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p :
 ι → Prop} {s : ι → Set α},   l.HasBasis p s → l.ker = ⋂ i, ⋂ (_ : p i), s i
· 使用定理 `hasBasis_nhdsSet`：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U 
=> IsOpen U ∧ s subseteq U) fun U => U
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
-/
lemma nhdsKer_def (s : Set X) : nhdsKer s = ⋂₀ {t : Set X | IsOpen t ∧ s ⊆ t} :=
  (hasBasis_nhdsSet _).ker.trans sInter_eq_biInter.symm
/-
**mem_nhdsKer** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_nhdsKer : x in nhdsKer s ↔ forall U, IsOpen U -> s subseteq U -> x in 
U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `nhdsKer_def`：nhdsKer_def (s : Set X) : nhdsKer s = ⋂₀ {t : Set X | IsOpe
n t ∧ s subseteq t}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_nhdsKer : x ∈ nhdsKer s ↔ ∀ U, IsOpen U → s ⊆ U → x ∈ U := by simp [nhdsKer_def]
/-
**subset_nhdsKer_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：subset_nhdsKer_iff : s subseteq nhdsKer t ↔ forall U, IsOpen U -> t subset
eq U -> s subseteq U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `nhdsKer_def`：nhdsKer_def (s : Set X) : nhdsKer s = ⋂₀ {t : Set X | IsOpe
n t ∧ s subseteq t}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma subset_nhdsKer_iff : s ⊆ nhdsKer t ↔ ∀ U, IsOpen U → t ⊆ U → s ⊆ U := by
  simp [nhdsKer_def]
/-
**subset_nhdsKer** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：subset_nhdsKer : s subseteq nhdsKer s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `subset_nhdsKer_iff`：subset_nhdsKer_iff : s subseteq nhdsKer t ↔ forall U
, IsOpen U -> t subseteq U -> s subseteq U
-/
lemma subset_nhdsKer : s ⊆ nhdsKer s := subset_nhdsKer_iff.2 fun _ _ ↦ id
/-
**nhdsKer_minimal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsKer_minimal (h₁ : s subseteq t) (h₂ : IsOpen t) : nhdsKer s subseteq t
参数：h₁ : s subseteq t；h₂ : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `nhdsKer_def`：nhdsKer_def (s : Set X) : nhdsKer s = ⋂₀ {t : Set X | IsOpe
n t ∧ s subseteq t}
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
-/
lemma nhdsKer_minimal (h₁ : s ⊆ t) (h₂ : IsOpen t) : nhdsKer s ⊆ t := by
  rw [nhdsKer_def]; exact sInter_subset_of_mem ⟨h₂, h₁⟩
/-
**IsOpen.nhdsKer_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpen.nhdsKer_eq (h : IsOpen s) : nhdsKer s = s
参数：h : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `nhdsKer_minimal`：nhdsKer_minimal (h₁ : s subseteq t) (h₂ : IsOpen t) : n
hdsKer s subseteq t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用引理 `subset_nhdsKer`：subset_nhdsKer : s subseteq nhdsKer s
-/
lemma IsOpen.nhdsKer_eq (h : IsOpen s) : nhdsKer s = s :=
  (nhdsKer_minimal Subset.rfl h).antisymm subset_nhdsKer
/-
**IsOpen.nhdsKer_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpen.nhdsKer_subset (ht : IsOpen t) : nhdsKer s subseteq t ↔ s subseteq 
t
参数：ht : IsOpen t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `subset_nhdsKer`：subset_nhdsKer : s subseteq nhdsKer s
· 使用引理 `nhdsKer_minimal`：nhdsKer_minimal (h₁ : s subseteq t) (h₂ : IsOpen t) : n
hdsKer s subseteq t
-/
lemma IsOpen.nhdsKer_subset (ht : IsOpen t) : nhdsKer s ⊆ t ↔ s ⊆ t :=
  ⟨subset_nhdsKer.trans, fun h ↦ nhdsKer_minimal h ht⟩

@[simp]
/-
**nhdsKer_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsKer_iUnion (s : ι -> Set X) : nhdsKer (⋃ i, s i) = ⋃ i, nhdsKer (s i)
参数：s : ι -> Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_iUnion`：nhdsSet_iUnion {ι : Sort*} (s : ι -> Set X) : 𝓝ˢ (⋃ i, s
 i) = ⨆ i, 𝓝ˢ (s i)
· 使用定理 `Filter.ker_iSup`：ker_iSup (f : ι -> Filter α) : ker (⨆ i, f i) = ⋃ i, ke
r (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhdsKer_iUnion (s : ι → Set X) : nhdsKer (⋃ i, s i) = ⋃ i, nhdsKer (s i) := by
  simp only [nhdsKer, nhdsSet_iUnion, ker_iSup]
/-
**nhdsKer_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsKer_biUnion {ι : Type*} (s : Set ι) (t : ι -> Set X) : nhdsKer (⋃ i in
 s, t i) = ⋃ i in s, nhdsKer (t i)
参数：s : Set ι；t : ι -> Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsKer_iUnion`：nhdsKer_iUnion (s : ι -> Set X) : nhdsKer (⋃ i, s i) = ⋃
 i, nhdsKer (s i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhdsKer_biUnion {ι : Type*} (s : Set ι) (t : ι → Set X) :
    nhdsKer (⋃ i ∈ s, t i) = ⋃ i ∈ s, nhdsKer (t i) := by
  simp only [nhdsKer_iUnion]

@[simp]
/-
**nhdsKer_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsKer_union (s t : Set X) : nhdsKer (s union t) = nhdsKer s union nhdsKe
r t
参数：s t : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_union`：nhdsSet_union (s t : Set X) : 𝓝ˢ (s union t) = 𝓝ˢ s ⊔ 𝓝ˢ 
t
· 使用定理 `Filter.ker_sup`：ker_sup (f g : Filter α) : ker (f ⊔ g) = ker f union ker
 g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhdsKer_union (s t : Set X) : nhdsKer (s ∪ t) = nhdsKer s ∪ nhdsKer t := by
  simp only [nhdsKer, nhdsSet_union, ker_sup]

@[simp]
/-
**nhdsKer_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsKer_sUnion (S : Set (Set X)) : nhdsKer (⋃₀ S) = ⋃ s in S, nhdsKer s
参数：S : Set (Set X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `nhdsKer_iUnion`：nhdsKer_iUnion (s : ι -> Set X) : nhdsKer (⋃ i, s i) = ⋃
 i, nhdsKer (s i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhdsKer_sUnion (S : Set (Set X)) : nhdsKer (⋃₀ S) = ⋃ s ∈ S, nhdsKer s := by
  simp only [sUnion_eq_biUnion, nhdsKer_iUnion]
/-
**mem_nhdsKer_iff_specializes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsKer_iff_specializes : x in nhdsKer s ↔ exists y in s, x ⤳ y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `nhdsKer_iUnion`：nhdsKer_iUnion (s : ι -> Set X) : nhdsKer (⋃ i, s i) = ⋃
 i, nhdsKer (s i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
theorem mem_nhdsKer_iff_specializes : x ∈ nhdsKer s ↔ ∃ y ∈ s, x ⤳ y := calc
  x ∈ nhdsKer s ↔ x ∈ nhdsKer (⋃ y ∈ s, {y}) := by simp
  _ ↔ ∃ y ∈ s, x ⤳ y := by
    simp only [nhdsKer_iUnion, mem_nhdsKer_singleton, mem_iUnion₂, exists_prop]
/-
**nhdsKer_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X], Monotone nhdsKer
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.ker_mono`：ker_mono : Monotone (ker : Filter α -> Set α)
· 使用定理 `nhdsSet_mono`：nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t
-/
@[gcongr, mono] lemma nhdsKer_mono : Monotone (nhdsKer : Set X → Set X) :=
  fun _s _t h ↦ ker_mono <| nhdsSet_mono h

/-- This name was used to be used for the `Iff` version,
see `nhdsKer_subset_nhdsKer_iff_nhdsSet`.
-/
/-
**nhdsKer_subset_nhdsKer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X] {s t : Set X}, s ⊆ t → nhdsKe
r s ⊆ nhdsKer t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsKer_mono`：∀ {X : Type u_2} [inst : TopologicalSpace X], Monotone nhd
sKer

--- 原说明 ---
This name was used to be used for the `Iff` version,
see `nhdsKer_subset_nhdsKer_iff_nhdsSet`.
-/
@[gcongr] lemma nhdsKer_subset_nhdsKer (h : s ⊆ t) : nhdsKer s ⊆ nhdsKer t := nhdsKer_mono h
/-
**nhdsKer_subset_nhdsKer_iff_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X] {s t : Set X}, nhdsKer s ⊆ nh
dsKer t ↔ nhdsSet s ≤ nhdsSet t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `hasBasis_nhdsSet`：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U 
=> IsOpen U ∧ s subseteq U) fun U => U
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
This name was used to be used for the `Iff` version,
see `nhdsKer_subset_nhdsKer_iff_nhdsSet`.
-/
@[simp] lemma nhdsKer_subset_nhdsKer_iff_nhdsSet : nhdsKer s ⊆ nhdsKer t ↔ 𝓝ˢ s ≤ 𝓝ˢ t := by
  simp +contextual only [subset_nhdsKer_iff, (hasBasis_nhdsSet _).ge_iff,
    and_imp, IsOpen.mem_nhdsSet, IsOpen.nhdsKer_subset]
/-
**nhdsKer_eq_nhdsKer_iff_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsKer_eq_nhdsKer_iff_nhdsSet : nhdsKer s = nhdsKer t ↔ 𝓝ˢ s = 𝓝ˢ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nhdsKer_eq_nhdsKer_iff_nhdsSet : nhdsKer s = nhdsKer t ↔ 𝓝ˢ s = 𝓝ˢ t := by
  simp [le_antisymm_iff]
/-
**specializes_iff_nhdsKer_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：specializes_iff_nhdsKer_subset : x ⤳ y ↔ nhdsKer {x} subseteq nhdsKer {y}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma specializes_iff_nhdsKer_subset : x ⤳ y ↔ nhdsKer {x} ⊆ nhdsKer {y} := by
  simp [Specializes]
/-
**nhdsKer_iInter_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsKer_iInter_subset {s : ι -> Set X} : nhdsKer (⋂ i, s i) subseteq ⋂ i, 
nhdsKer (s i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_iInf_le`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [in
st : CompleteLattice α] {s : ι → α} [inst_1 : CompleteLattice β]   {f : α → β}, 
Monotone f…
· 使用定理 `nhdsKer_mono`：∀ {X : Type u_2} [inst : TopologicalSpace X], Monotone nhd
sKer
-/
theorem nhdsKer_iInter_subset {s : ι → Set X} : nhdsKer (⋂ i, s i) ⊆ ⋂ i, nhdsKer (s i) :=
  nhdsKer_mono.map_iInf_le
/-
**nhdsKer_inter_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsKer_inter_subset {s t : Set X} : nhdsKer (s inter t) subseteq nhdsKer 
s inter nhdsKer t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_inf_le`：∀ {α : Type u} {β : Type v} [inst : SemilatticeInf 
α] [inst_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (x ⊓ y
) ≤ f x ⊓…
· 使用定理 `nhdsKer_mono`：∀ {X : Type u_2} [inst : TopologicalSpace X], Monotone nhd
sKer
-/
theorem nhdsKer_inter_subset {s t : Set X} : nhdsKer (s ∩ t) ⊆ nhdsKer s ∩ nhdsKer t :=
  nhdsKer_mono.map_inf_le _ _
/-
**nhdsKer_sInter_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsKer_sInter_subset {s : Set (Set X)} : nhdsKer (⋂₀ s) subseteq ⋂ x in s
, nhdsKer x
参数：Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_sInf_le`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLa
ttice α] [inst_1 : CompleteLattice β] {s : Set α} {f : α → β},   Monotone f → f 
(sInf s) ≤…
· 使用定理 `nhdsKer_mono`：∀ {X : Type u_2} [inst : TopologicalSpace X], Monotone nhd
sKer
-/
theorem nhdsKer_sInter_subset {s : Set (Set X)} : nhdsKer (⋂₀ s) ⊆ ⋂ x ∈ s, nhdsKer x :=
  nhdsKer_mono.map_sInf_le
/-
**nhdsKer_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X], nhdsKer ∅ = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsOpen.nhdsKer_eq`：IsOpen.nhdsKer_eq (h : IsOpen s) : nhdsKer s = s
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
-/
@[simp] lemma nhdsKer_empty : nhdsKer (∅ : Set X) = ∅ := isOpen_empty.nhdsKer_eq
/-
**nhdsKer_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X], nhdsKer Set.univ = Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsOpen.nhdsKer_eq`：IsOpen.nhdsKer_eq (h : IsOpen s) : nhdsKer s = s
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
-/
@[simp] lemma nhdsKer_univ : nhdsKer (univ : Set X) = univ := isOpen_univ.nhdsKer_eq
/-
**nhdsKer_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X] {s : Set X}, nhdsKer s = ∅ ↔ 
s = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_bot_mono`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α
] {a b : α}, b ≤ a → a = ⊥ → b = ⊥
· 使用引理 `subset_nhdsKer`：subset_nhdsKer : s subseteq nhdsKer s
· 使用定理 `nhdsKer_empty`：∀ {X : Type u_2} [inst : TopologicalSpace X], nhdsKer ∅ =
 ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma nhdsKer_eq_empty : nhdsKer s = ∅ ↔ s = ∅ :=
  ⟨eq_bot_mono subset_nhdsKer, by rintro rfl; exact nhdsKer_empty⟩
/-
**nhdsSet_nhdsKer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X] (s : Set X), nhdsSet (nhdsKer
 s) = nhdsSet s
参数：s : Set X；nhdsKer s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `hasBasis_nhdsSet`：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U 
=> IsOpen U ∧ s subseteq U) fun U => U
· 使用定理 `IsOpen.mem_nhdsSet`：IsOpen.mem_nhdsSet (hU : IsOpen s) : s in 𝓝ˢ t ↔ t s
ubseteq s
· 使用引理 `IsOpen.nhdsKer_subset`：IsOpen.nhdsKer_subset (ht : IsOpen t) : nhdsKer s
 subseteq t ↔ s subseteq t
· 使用定理 `nhdsSet_mono`：nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t
· 使用引理 `subset_nhdsKer`：subset_nhdsKer : s subseteq nhdsKer s
-/
@[simp] lemma nhdsSet_nhdsKer (s : Set X) : 𝓝ˢ (nhdsKer s) = 𝓝ˢ s := by
  refine le_antisymm ((hasBasis_nhdsSet _).ge_iff.2 ?_) (nhdsSet_mono subset_nhdsKer)
  exact fun U ⟨hUo, hsU⟩ ↦ hUo.mem_nhdsSet.2 <| hUo.nhdsKer_subset.2 hsU
/-
**nhdsKer_nhdsKer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X] (s : Set X), nhdsKer (nhdsKer
 s) = nhdsKer s
参数：s : Set X；nhdsKer s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_nhdsKer`：∀ {X : Type u_2} [inst : TopologicalSpace X] (s : Set X
), nhdsSet (nhdsKer s) = nhdsSet s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma nhdsKer_nhdsKer (s : Set X) : nhdsKer (nhdsKer s) = nhdsKer s := by
  simp only [nhdsKer_eq_nhdsKer_iff_nhdsSet, nhdsSet_nhdsKer]
/-
**nhdsKer_pair** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsKer_pair {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (x : 
X) (y : Y) : nhdsKer {(x, y)} = nhdsKer {x} ×ˢ nhdsKer {y}
参数：x : X；y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `nhdsKer_singleton_eq_ker_nhds`：nhdsKer_singleton_eq_ker_nhds (x : X) : n
hdsKer {x} = (𝓝 x).ker
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Filter.ker_prod`：ker_prod (f : Filter α) (g : Filter β) : ker (f ×ˢ g) =
 ker f ×ˢ ker g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nhdsKer_pair {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) : nhdsKer {(x, y)} = nhdsKer {x} ×ˢ nhdsKer {y} := by
  simp_rw [nhdsKer_singleton_eq_ker_nhds, nhds_prod_eq, ker_prod]
/-
**nhdsKer_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsKer_prod {Y : Type*} [TopologicalSpace Y] (s : Set X) (t : Set Y) : nh
dsKer (s ×ˢ t) = nhdsKer s ×ˢ nhdsKer t
参数：s : Set X；t : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `nhdsKer_biUnion`：nhdsKer_biUnion {ι : Type*} (s : Set ι) (t : ι -> Set X
) : nhdsKer (⋃ i in s, t i) = ⋃ i in s, nhdsKer (t i)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `nhdsKer_pair`：nhdsKer_pair {X Y : Type*} [TopologicalSpace X] [Topologic
alSpace Y] (x : X) (y : Y) : nhdsKer {(x, y)} = nhdsKer {x} ×ˢ nhdsKer {y}
· 使用引理 `Set.biUnion_prod`：biUnion_prod {α β γ} (s : Set α) (t : Set β) (f : α ->
 Set γ) (g : β -> Set δ) : ⋃ x in s ×ˢ t, f x.1 ×ˢ g x.2 = (⋃ x in s, f x) ×ˢ (⋃
 x in …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nhdsKer_prod {Y : Type*} [TopologicalSpace Y] (s : Set X) (t : Set Y) :
    nhdsKer (s ×ˢ t) = nhdsKer s ×ˢ nhdsKer t := calc
  _ = ⋃ (p ∈ s ×ˢ t), nhdsKer {p} := by
    conv_lhs => rw [← biUnion_of_singleton (s ×ˢ t), nhdsKer_biUnion]
  _ = ⋃ (p ∈ s ×ˢ t), nhdsKer {p.1} ×ˢ nhdsKer {p.2} := by
    congr! with ⟨x, y⟩ _; rw [nhdsKer_pair]
  _ = (⋃ x ∈ s, nhdsKer {x}) ×ˢ (⋃ y ∈ t, nhdsKer {y}) :=
    biUnion_prod s t (fun x => nhdsKer {x}) (fun y => nhdsKer {y})
  _ = nhdsKer s ×ˢ nhdsKer t := by
    simp_rw [← nhdsKer_biUnion, biUnion_of_singleton]
/-
**nhdsKer_singleton_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsKer_singleton_pi {ι : Type*} {X : ι -> Type*} [Π (i : ι), TopologicalS
pace (X i)] (p : Π (i : ι), X i) : nhdsKer {p} = univ.pi (fun i => nhdsKer {p i}
)
参数：i : ι；X i；p : Π (i : ι), X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `nhdsKer_singleton_eq_ker_nhds`：nhdsKer_singleton_eq_ker_nhds (x : X) : n
hdsKer {x} = (𝓝 x).ker
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Filter.ker_pi`：ker_pi {ι : Type*} {α : ι -> Type*} (f : (i : ι) -> Filte
r (α i)) : ker (Filter.pi f) = univ.pi (fun i => ker (f i))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nhdsKer_singleton_pi {ι : Type*} {X : ι → Type*} [Π (i : ι), TopologicalSpace (X i)]
    (p : Π (i : ι), X i) : nhdsKer {p} = univ.pi (fun i => nhdsKer {p i}) := by
  simp_rw [nhdsKer_singleton_eq_ker_nhds, nhds_pi, ker_pi]
/-
**nhdsKer_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsKer_pi {ι : Type*} {X : ι -> Type*} [Π (i : ι), TopologicalSpace (X i)
] (s : Π (i : ι), Set (X i)) : nhdsKer (univ.pi s) = univ.pi (fun i => nhdsKer (
s i))
参数：i : ι；X i；s : Π (i : ι), Set (X i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `nhdsKer_biUnion`：nhdsKer_biUnion {ι : Type*} (s : Set ι) (t : ι -> Set X
) : nhdsKer (⋃ i in s, t i) = ⋃ i in s, nhdsKer (t i)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `nhdsKer_singleton_pi`：nhdsKer_singleton_pi {ι : Type*} {X : ι -> Type*} 
[Π (i : ι), TopologicalSpace (X i)] (p : Π (i : ι), X i) : nhdsKer {p} = univ.pi
 (fun i =>…
· 使用定理 `Set.biUnion_univ_pi`：biUnion_univ_pi {ι : α -> Type*} (s : (a : α) -> Se
t (ι a)) (t : (a : α) -> ι a -> Set (π a)) : ⋃ x in univ.pi s, pi univ (fun a =>
 t a (x a…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nhdsKer_pi {ι : Type*} {X : ι → Type*} [Π (i : ι), TopologicalSpace (X i)]
    (s : Π (i : ι), Set (X i)) : nhdsKer (univ.pi s) = univ.pi (fun i => nhdsKer (s i)) := calc
  _ = ⋃ (p ∈ univ.pi s), nhdsKer {p} := by
    conv_lhs => rw [← biUnion_of_singleton (univ.pi s), nhdsKer_biUnion]
  _ = ⋃ (p ∈ univ.pi s), univ.pi fun i => nhdsKer {p i} := by
    congr! with p _; rw [nhdsKer_singleton_pi]
  _ = univ.pi fun i => ⋃ x ∈ s i, nhdsKer {x} :=
    biUnion_univ_pi s fun i x => nhdsKer {x}
  _ = univ.pi (fun i => nhdsKer (s i)) := by
    simp_rw [← nhdsKer_biUnion, biUnion_of_singleton]
