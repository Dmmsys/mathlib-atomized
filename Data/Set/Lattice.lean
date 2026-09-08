/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Logic.Pairwise
public import Mathlib.Data.Set.BooleanAlgebra

/-!
# The set lattice

This file is a collection of results on the complete atomic Boolean algebra structure of `Set α`.
Notation for the complete lattice operations can be found in `Mathlib/Order/SetNotation.lean`.

## Main declarations
* `Set.sInter_eq_biInter`, `Set.sUnion_eq_biInter`: Shows that `⋂₀ s = ⋂ x ∈ s, x` and
  `⋃₀ s = ⋃ x ∈ s, x`.
* `Set.completeAtomicBooleanAlgebra`: `Set α` is a `CompleteAtomicBooleanAlgebra` with `≤ = ⊆`,
  `< = ⊂`, `⊓ = ∩`, `⊔ = ∪`, `⨅ = ⋂`, `⨆ = ⋃` and `\` as the set difference.
  See `Set.instBooleanAlgebra`.
* `Set.unionEqSigmaOfDisjoint`: Equivalence between `⋃ i, t i` and `Σ i, t i`, where `t` is an
  indexed family of disjoint sets.

## Naming convention

In lemma names,
* `⋃ i, s i` is called `iUnion`
* `⋂ i, s i` is called `iInter`
* `⋃ i j, s i j` is called `iUnion₂`. This is an `iUnion` inside an `iUnion`.
* `⋂ i j, s i j` is called `iInter₂`. This is an `iInter` inside an `iInter`.
* `⋃ i ∈ s, t i` is called `biUnion` for "bounded `iUnion`". This is the special case of `iUnion₂`
  where `j : i ∈ s`.
* `⋂ i ∈ s, t i` is called `biInter` for "bounded `iInter`". This is the special case of `iInter₂`
  where `j : i ∈ s`.

## Notation

* `⋃`: `Set.iUnion`
* `⋂`: `Set.iInter`
* `⋃₀`: `Set.sUnion`
* `⋂₀`: `Set.sInter`
-/

@[expose] public section

open Function Set

universe u

variable {α β γ δ : Type*} {ι ι' ι₂ : Sort*} {κ κ₁ κ₂ : ι → Sort*} {κ' : ι' → Sort*}

namespace Set

/-! ### Complete lattice and complete Boolean algebra instances -/

/-
**Set.mem_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ exists i, x in s i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
### Complete lattice and complete Boolean algebra instances
-/
theorem mem_iUnion₂ {x : γ} {s : ∀ i, κ i → Set γ} : (x ∈ ⋃ (i) (j), s i j) ↔ ∃ i j, x ∈ s i j := by
  simp_rw [mem_iUnion]
/-
**Set.mem_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ forall i, x in s i
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_iInter₂ {x : γ} {s : ∀ i, κ i → Set γ} : (x ∈ ⋂ (i) (j), s i j) ↔ ∀ i j, x ∈ s i j := by
  simp_rw [mem_iInter]
/-
**Set.mem_iUnion_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_iUnion_of_mem {s : ι -> Set α} {a : α} (i : ι) (ha : a in s i) : a in 
⋃ i, s i
参数：i : ι；ha : a in s i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
-/
theorem mem_iUnion_of_mem {s : ι → Set α} {a : α} (i : ι) (ha : a ∈ s i) : a ∈ ⋃ i, s i :=
  mem_iUnion.2 ⟨i, ha⟩
/-
**Set.mem_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ exists i, x in s i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_iUnion₂_of_mem {s : ∀ i, κ i → Set α} {a : α} {i : ι} (j : κ i) (ha : a ∈ s i j) :
    a ∈ ⋃ (i) (j), s i j :=
  mem_iUnion₂.2 ⟨i, j, ha⟩
/-
**Set.mem_iInter_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_iInter_of_mem {s : ι -> Set α} {a : α} (h : forall i, a in s i) : a in
 ⋂ i, s i
参数：h : forall i, a in s i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
-/
theorem mem_iInter_of_mem {s : ι → Set α} {a : α} (h : ∀ i, a ∈ s i) : a ∈ ⋂ i, s i :=
  mem_iInter.2 h
/-
**Set.mem_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ forall i, x in s i
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_iInter₂_of_mem {s : ∀ i, κ i → Set α} {a : α} (h : ∀ i j, a ∈ s i j) :
    a ∈ ⋂ (i) (j), s i j :=
  mem_iInter₂.2 h

/-! ### Union and intersection over an indexed family of sets -/

@[congr]
/-
**Set.iUnion_congr_Prop** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} {f₂ : q -> Set α} (pq : p
 ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ = iUnion f₂
参数：pq : p ↔ q；f : forall x, f₁ (pq.mpr x) = f₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂

--- 原说明 ---
### Union and intersection over an indexed family of sets
-/
theorem iUnion_congr_Prop {p q : Prop} {f₁ : p → Set α} {f₂ : q → Set α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ = iUnion f₂ :=
  iSup_congr_Prop pq f

@[congr]
/-
**Set.iInter_congr_Prop** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} {f₂ : q -> Set α} (pq : p
 ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ = iInter f₂
参数：pq : p ↔ q；f : forall x, f₁ (pq.mpr x) = f₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
-/
theorem iInter_congr_Prop {p q : Prop} {f₁ : p → Set α} {f₂ : q → Set α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ = iInter f₂ :=
  iInf_congr_Prop pq f
/-
**Set.iUnion_plift_up** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_plift_up (f : PLift ι -> Set α) : ⋃ i, f (PLift.up i) = ⋃ i, f i
参数：f : PLift ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_plift_up`：iSup_plift_up (f : PLift ι -> α) : ⨆ i, f (PLift.up i) = 
⨆ i, f i
-/
theorem iUnion_plift_up (f : PLift ι → Set α) : ⋃ i, f (PLift.up i) = ⋃ i, f i :=
  iSup_plift_up _
/-
**Set.iUnion_plift_down** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_plift_down (f : ι -> Set α) : ⋃ i, f (PLift.down i) = ⋃ i, f i
参数：f : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_plift_down`：iSup_plift_down (f : ι -> α) : ⨆ i, f (PLift.down i) = 
⨆ i, f i
-/
theorem iUnion_plift_down (f : ι → Set α) : ⋃ i, f (PLift.down i) = ⋃ i, f i :=
  iSup_plift_down _
/-
**Set.iInter_plift_up** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_plift_up (f : PLift ι -> Set α) : ⋂ i, f (PLift.up i) = ⋂ i, f i
参数：f : PLift ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_plift_up`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] (f : PL
ift ι → α), ⨅ i, f { down := i } = ⨅ i, f i
-/
theorem iInter_plift_up (f : PLift ι → Set α) : ⋂ i, f (PLift.up i) = ⋂ i, f i :=
  iInf_plift_up _
/-
**Set.iInter_plift_down** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_plift_down (f : ι -> Set α) : ⋂ i, f (PLift.down i) = ⋂ i, f i
参数：f : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_plift_down`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] (f : 
ι → α), ⨅ i, f i.down = ⨅ i, f i
-/
theorem iInter_plift_down (f : ι → Set α) : ⋂ i, f (PLift.down i) = ⋂ i, f i :=
  iInf_plift_down _
/-
**Set.iUnion_eq_if** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_eq_if {p : Prop} [Decidable p] (s : Set α) : ⋃ _ : p, s = if p then
 s else ∅
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_eq_if`：iSup_eq_if {p : Prop} [Decidable p] (a : α) : ⨆ _ : p, a = i
f p then a else ⊥
-/
theorem iUnion_eq_if {p : Prop} [Decidable p] (s : Set α) : ⋃ _ : p, s = if p then s else ∅ :=
  iSup_eq_if _
/-
**Set.iUnion_eq_dif** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_eq_dif {p : Prop} [Decidable p] (s : p -> Set α) : ⋃ h : p, s h = i
f h : p then s h else ∅
参数：s : p -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_eq_dif`：iSup_eq_dif {p : Prop} [Decidable p] (a : p -> α) : ⨆ h : p
, a h = if h : p then a h else ⊥
-/
theorem iUnion_eq_dif {p : Prop} [Decidable p] (s : p → Set α) :
    ⋃ h : p, s h = if h : p then s h else ∅ :=
  iSup_eq_dif _
/-
**Set.iInter_eq_if** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_eq_if {p : Prop} [Decidable p] (s : Set α) : ⋂ _ : p, s = if p then
 s else univ
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_eq_if`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} [inst
_1 : Decidable p] (a : α), ⨅ (_ : p), a = if p then a else ⊤
-/
theorem iInter_eq_if {p : Prop} [Decidable p] (s : Set α) : ⋂ _ : p, s = if p then s else univ :=
  iInf_eq_if _
/-
**Set.iInf_eq_dif** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInf_eq_dif {p : Prop} [Decidable p] (s : p -> Set α) : ⋂ h : p, s h = if 
h : p then s h else univ
参数：s : p -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_eq_dif`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} [ins
t_1 : Decidable p] (a : p → α),   ⨅ (h : p), a h = if h : p then a h else ⊤
-/
theorem iInf_eq_dif {p : Prop} [Decidable p] (s : p → Set α) :
    ⋂ h : p, s h = if h : p then s h else univ :=
  _root_.iInf_eq_dif _
/-
**Set.exists_set_mem_of_union_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_set_mem_of_union_eq_top {ι : Type*} (t : Set ι) (s : ι -> Set β) (w
 : ⋃ i in t, s i = ⊤) (x : β) : exists i in t, x in s i
参数：t : Set ι；s : ι -> Set β；w : ⋃ i in t, s i = ⊤；x : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_set_mem_of_union_eq_top {ι : Type*} (t : Set ι) (s : ι → Set β)
    (w : ⋃ i ∈ t, s i = ⊤) (x : β) : ∃ i ∈ t, x ∈ s i := by
  have p : x ∈ ⊤ := Set.mem_univ x
  rw [← w, Set.mem_iUnion] at p
  simpa using p
/-
**Set.nonempty_of_union_eq_top_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_of_union_eq_top_of_nonempty {ι : Type*} (t : Set ι) (s : ι -> Set
 α) (H : Nonempty α) (w : ⋃ i in t, s i = ⊤) : t.Nonempty
参数：t : Set ι；s : ι -> Set α；H : Nonempty α；w : ⋃ i in t, s i = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_set_mem_of_union_eq_top`：exists_set_mem_of_union_eq_top {ι : 
Type*} (t : Set ι) (s : ι -> Set β) (w : ⋃ i in t, s i = ⊤) (x : β) : exists i i
n t, x in s i
-/
theorem nonempty_of_union_eq_top_of_nonempty {ι : Type*} (t : Set ι) (s : ι → Set α)
    (H : Nonempty α) (w : ⋃ i ∈ t, s i = ⊤) : t.Nonempty := by
  obtain ⟨x, m, -⟩ := exists_set_mem_of_union_eq_top t s w H.some
  exact ⟨x, m⟩
/-
**Set.nonempty_of_nonempty_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_of_nonempty_iUnion {s : ι -> Set α} (h_Union : (⋃ i, s i).Nonempt
y) : Nonempty ι
参数：h_Union : (⋃ i, s i).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
-/
theorem nonempty_of_nonempty_iUnion
    {s : ι → Set α} (h_Union : (⋃ i, s i).Nonempty) : Nonempty ι := by
  obtain ⟨x, hx⟩ := h_Union
  exact ⟨Classical.choose <| mem_iUnion.mp hx⟩
/-
**Set.nonempty_of_nonempty_iUnion_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_of_nonempty_iUnion_eq_univ {s : ι -> Set α} [Nonempty α] (h_Union
 : ⋃ i, s i = univ) : Nonempty ι
参数：h_Union : ⋃ i, s i = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nonempty_of_nonempty_iUnion`：nonempty_of_nonempty_iUnion {s : ι -> S
et α} (h_Union : (⋃ i, s i).Nonempty) : Nonempty ι
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
-/
theorem nonempty_of_nonempty_iUnion_eq_univ
    {s : ι → Set α} [Nonempty α] (h_Union : ⋃ i, s i = univ) : Nonempty ι :=
  nonempty_of_nonempty_iUnion (s := s) (by simpa only [h_Union] using univ_nonempty)
/-
**Set.ofPred_exists** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ofPred_exists (p : ι -> β -> Prop) : { x | exists i, p i x } = ⋃ i, { x | 
p i x }
参数：p : ι -> β -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
-/
theorem ofPred_exists (p : ι → β → Prop) : { x | ∃ i, p i x } = ⋃ i, { x | p i x } :=
  ext fun _ => .symm <| mem_iUnion

@[deprecated (since := "2026-07-09")] alias setOf_exists := ofPred_exists
/-
**Set.ofPred_forall** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, p i x } = ⋂ i, { x | 
p i x }
参数：p : ι -> β -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
-/
theorem ofPred_forall (p : ι → β → Prop) : { x | ∀ i, p i x } = ⋂ i, { x | p i x } :=
  ext fun _ => .symm <| mem_iInter

@[deprecated (since := "2026-07-09")] alias setOf_forall := ofPred_forall
/-
**Set.iUnion_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_subset {s : ι -> Set α} {t : Set α} (h : forall i, s i subseteq t) 
: ⋃ i, s i subseteq t
参数：h : forall i, s i subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
-/
theorem iUnion_subset {s : ι → Set α} {t : Set α} (h : ∀ i, s i ⊆ t) : ⋃ i, s i ⊆ t :=
  iSup_le h
/-
**Set.iUnion** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iUnion (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iUnion₂_subset {s : ∀ i, κ i → Set α} {t : Set α} (h : ∀ i j, s i j ⊆ t) :
    ⋃ (i) (j), s i j ⊆ t :=
  iUnion_subset fun x => iUnion_subset (h x)
/-
**Set.subset_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_iInter {t : Set β} {s : ι -> Set β} (h : forall i, t subseteq s i) 
: t subseteq ⋂ i, s i
参数：h : forall i, t subseteq s i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
-/
theorem subset_iInter {t : Set β} {s : ι → Set β} (h : ∀ i, t ⊆ s i) : t ⊆ ⋂ i, s i :=
  le_iInf h
/-
**Set.subset_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_iInter {t : Set β} {s : ι -> Set β} (h : forall i, t subseteq s i) 
: t subseteq ⋂ i, s i
参数：h : forall i, t subseteq s i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
-/
theorem subset_iInter₂ {s : Set α} {t : ∀ i, κ i → Set α} (h : ∀ i j, s ⊆ t i j) :
    s ⊆ ⋂ (i) (j), t i j :=
  subset_iInter fun x => subset_iInter <| h x

@[simp]
/-
**Set.iUnion_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_subset_iff {s : ι -> Set α} {t : Set α} : ⋃ i, s i subseteq t ↔ for
all i, s i subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
-/
theorem iUnion_subset_iff {s : ι → Set α} {t : Set α} : ⋃ i, s i ⊆ t ↔ ∀ i, s i ⊆ t :=
  ⟨fun h _ => Subset.trans (le_iSup s _) h, iUnion_subset⟩
/-
**Set.iUnion** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iUnion (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iUnion₂_subset_iff {s : ∀ i, κ i → Set α} {t : Set α} :
    ⋃ (i) (j), s i j ⊆ t ↔ ∀ i j, s i j ⊆ t := by simp_rw [iUnion_subset_iff]

@[simp]
/-
**Set.subset_iInter_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_iInter_iff {s : Set α} {t : ι -> Set α} : (s subseteq ⋂ i, t i) ↔ f
orall i, s subseteq t i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf_iff`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{f : ι → α} {a : α}, a ≤ iInf f ↔ ∀ (i : ι), a ≤ f i
-/
theorem subset_iInter_iff {s : Set α} {t : ι → Set α} : (s ⊆ ⋂ i, t i) ↔ ∀ i, s ⊆ t i :=
  le_iInf_iff
/-
**Set.subset_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_iInter {t : Set β} {s : ι -> Set β} (h : forall i, t subseteq s i) 
: t subseteq ⋂ i, s i
参数：h : forall i, t subseteq s i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
-/
theorem subset_iInter₂_iff {s : Set α} {t : ∀ i, κ i → Set α} :
    (s ⊆ ⋂ (i) (j), t i j) ↔ ∀ i j, s ⊆ t i j := by simp_rw [subset_iInter_iff]
/-
**Set.subset_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i subseteq ⋃ i, s i
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem subset_iUnion : ∀ (s : ι → Set β) (i : ι), s i ⊆ ⋃ i, s i :=
  le_iSup
/-
**Set.iInter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i, s i subseteq s i
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
theorem iInter_subset : ∀ (s : ι → Set β) (i : ι), ⋂ i, s i ⊆ s i :=
  iInf_le
/-
**Set.iInter_subset_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iInter_subset_iUnion [Nonempty ι] {s : ι -> Set α} : ⋂ i, s i subseteq ⋃ i
, s i
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `iInf_le_iSup`：iInf_le_iSup [Nonempty ι] : ⨅ i, f i <= ⨆ i, f i
-/
lemma iInter_subset_iUnion [Nonempty ι] {s : ι → Set α} : ⋂ i, s i ⊆ ⋃ i, s i := iInf_le_iSup
/-
**Set.subset_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i subseteq ⋃ i, s i
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem subset_iUnion₂ {s : ∀ i, κ i → Set α} (i : ι) (j : κ i) : s i j ⊆ ⋃ (i') (j'), s i' j' :=
  le_iSup₂ i j
/-
**Set.iInter** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iInter (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iInter₂_subset {s : ∀ i, κ i → Set α} (i : ι) (j : κ i) : ⋂ (i) (j), s i j ⊆ s i j :=
  iInf₂_le i j

/-- This rather trivial consequence of `subset_iUnion` is convenient with `apply`, and has `i`
explicit for this purpose. -/
/-
**Set.subset_iUnion_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_iUnion_of_subset {s : Set α} {t : ι -> Set α} (i : ι) (h : s subset
eq t i) : s subseteq ⋃ i, t i
参数：i : ι；h : s subseteq t i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f

--- 原说明 ---
This rather trivial consequence of `subset_iUnion` is convenient with `apply`, a
nd has `i`
explicit for this purpose.
-/
theorem subset_iUnion_of_subset {s : Set α} {t : ι → Set α} (i : ι) (h : s ⊆ t i) : s ⊆ ⋃ i, t i :=
  le_iSup_of_le i h

/-- This rather trivial consequence of `iInter_subset` is convenient with `apply`, and has `i`
explicit for this purpose. -/
/-
**Set.iInter_subset_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_subset_of_subset {s : ι -> Set α} {t : Set α} (i : ι) (h : s i subs
eteq t) : ⋂ i, s i subseteq t
参数：i : ι；h : s i subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a

--- 原说明 ---
This rather trivial consequence of `iInter_subset` is convenient with `apply`, a
nd has `i`
explicit for this purpose.
-/
theorem iInter_subset_of_subset {s : ι → Set α} {t : Set α} (i : ι) (h : s i ⊆ t) :
    ⋂ i, s i ⊆ t :=
  iInf_le_of_le i h

/-- This rather trivial consequence of `subset_iUnion₂` is convenient with `apply`, and has `i` and
`j` explicit for this purpose. -/
/-
**Set.subset_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i subseteq ⋃ i, s i
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f

--- 原说明 ---
This rather trivial consequence of `subset_iUnion₂` is convenient with `apply`, 
and has `i` and
`j` explicit for this purpose.
-/
theorem subset_iUnion₂_of_subset {s : Set α} {t : ∀ i, κ i → Set α} (i : ι) (j : κ i)
    (h : s ⊆ t i j) : s ⊆ ⋃ (i) (j), t i j :=
  le_iSup₂_of_le i j h

/-- This rather trivial consequence of `iInter₂_subset` is convenient with `apply`, and has `i` and
`j` explicit for this purpose. -/
/-
**Set.iInter** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iInter (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This rather trivial consequence of `iInter₂_subset` is convenient with `apply`, 
and has `i` and
`j` explicit for this purpose.
-/
theorem iInter₂_subset_of_subset {s : ∀ i, κ i → Set α} {t : Set α} (i : ι) (j : κ i)
    (h : s i j ⊆ t) : ⋂ (i) (j), s i j ⊆ t :=
  iInf₂_le_of_le i j h
/-
**Set.iUnion_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_mono {s t : ι -> Set α} (h : forall i, s i subseteq t i) : ⋃ i, s i
 subseteq ⋃ i, t i
参数：h : forall i, s i subseteq t i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
-/
theorem iUnion_mono {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : ⋃ i, s i ⊆ ⋃ i, t i :=
  iSup_mono h

@[gcongr]
/-
**Set.iUnion_mono''** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_mono'' {s t : ι -> Set α} (h : forall i, s i subseteq t i) : iUnion
 s subseteq iUnion t
参数：h : forall i, s i subseteq t i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
-/
theorem iUnion_mono'' {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : iUnion s ⊆ iUnion t :=
  iSup_mono h
/-
**Set.iUnion** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iUnion (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iUnion₂_mono {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j ⊆ t i j) :
    ⋃ (i) (j), s i j ⊆ ⋃ (i) (j), t i j :=
  iSup₂_mono h
/-
**Set.iInter_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_mono {s t : ι -> Set α} (h : forall i, s i subseteq t i) : ⋂ i, s i
 subseteq ⋂ i, t i
参数：h : forall i, s i subseteq t i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
-/
theorem iInter_mono {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : ⋂ i, s i ⊆ ⋂ i, t i :=
  iInf_mono h

@[gcongr]
/-
**Set.iInter_mono''** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_mono'' {s t : ι -> Set α} (h : forall i, s i subseteq t i) : iInter
 s subseteq iInter t
参数：h : forall i, s i subseteq t i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
-/
theorem iInter_mono'' {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : iInter s ⊆ iInter t :=
  iInf_mono h
/-
**Set.iInter** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iInter (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iInter₂_mono {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j ⊆ t i j) :
    ⋂ (i) (j), s i j ⊆ ⋂ (i) (j), t i j :=
  iInf₂_mono h
/-
**Set.iUnion_mono'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_mono' {s : ι -> Set α} {t : ι₂ -> Set α} (h : forall i, exists j, s
 i subseteq t j) : ⋃ i, s i subseteq ⋃ i, t i
参数：h : forall i, exists j, s i subseteq t j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_mono'`：iSup_mono' {g : ι' -> α} (h : forall i, exists i', f i <= g 
i') : iSup f <= iSup g
-/
theorem iUnion_mono' {s : ι → Set α} {t : ι₂ → Set α} (h : ∀ i, ∃ j, s i ⊆ t j) :
    ⋃ i, s i ⊆ ⋃ i, t i :=
  iSup_mono' h
/-
**Set.iUnion** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iUnion (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iUnion₂_mono' {s : ∀ i, κ i → Set α} {t : ∀ i', κ' i' → Set α}
    (h : ∀ i j, ∃ i' j', s i j ⊆ t i' j') : ⋃ (i) (j), s i j ⊆ ⋃ (i') (j'), t i' j' :=
  iSup₂_mono' h
/-
**Set.iInter_mono'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_mono' {s : ι -> Set α} {t : ι' -> Set α} (h : forall j, exists i, s
 i subseteq t j) : ⋂ i, s i subseteq ⋂ j, t j
参数：h : forall j, exists i, s i subseteq t j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_iInter`：subset_iInter {t : Set β} {s : ι -> Set β} (h : foral
l i, t subseteq s i) : t subseteq ⋂ i, s i
· 使用定理 `Set.iInter_subset_of_subset`：iInter_subset_of_subset {s : ι -> Set α} {t
 : Set α} (i : ι) (h : s i subseteq t) : ⋂ i, s i subseteq t
-/
theorem iInter_mono' {s : ι → Set α} {t : ι' → Set α} (h : ∀ j, ∃ i, s i ⊆ t j) :
    ⋂ i, s i ⊆ ⋂ j, t j :=
  Set.subset_iInter fun j =>
    let ⟨i, hi⟩ := h j
    iInter_subset_of_subset i hi
/-
**Set.iInter** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iInter (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iInter₂_mono' {s : ∀ i, κ i → Set α} {t : ∀ i', κ' i' → Set α}
    (h : ∀ i' j', ∃ i j, s i j ⊆ t i' j') : ⋂ (i) (j), s i j ⊆ ⋂ (i') (j'), t i' j' :=
  subset_iInter₂_iff.2 fun i' j' =>
    let ⟨_, _, hst⟩ := h i' j'
    (iInter₂_subset _ _).trans hst
/-
**Set.iUnion** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iUnion (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iUnion₂_subset_iUnion (κ : ι → Sort*) (s : ι → Set α) :
    ⋃ (i) (_ : κ i), s i ⊆ ⋃ i, s i :=
  iUnion_mono fun _ => iUnion_subset fun _ => Subset.rfl
/-
**Set.iInter_subset_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iInter_subset_iInter₂ (κ : ι → Sort*) (s : ι → Set α) :
    ⋂ i, s i ⊆ ⋂ (i) (_ : κ i), s i :=
  iInter_mono fun _ => subset_iInter fun _ => Subset.rfl
/-
**Set.iUnion_ofPred** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_ofPred (P : ι -> α -> Prop) : ⋃ i, { x : α | P i x } = { x : α | ex
ists i, P i x }
参数：P : ι -> α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
-/
theorem iUnion_ofPred (P : ι → α → Prop) : ⋃ i, { x : α | P i x } = { x : α | ∃ i, P i x } := by
  ext
  exact mem_iUnion

@[deprecated (since := "2026-07-09")] alias iUnion_setOf := iUnion_ofPred
/-
**Set.iInter_ofPred** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_ofPred (P : ι -> α -> Prop) : ⋂ i, { x : α | P i x } = { x : α | fo
rall i, P i x }
参数：P : ι -> α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
-/
theorem iInter_ofPred (P : ι → α → Prop) : ⋂ i, { x : α | P i x } = { x : α | ∀ i, P i x } := by
  ext
  exact mem_iInter

@[deprecated (since := "2026-07-09")] alias iInter_setOf := iInter_ofPred
/-
**Set.iUnion_congr_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_congr_of_surjective {f : ι -> Set α} {g : ι₂ -> Set α} (h : ι -> ι₂
) (h1 : Surjective h) (h2 : forall x, g (h x) = f x) : ⋃ x, f x = ⋃ y, g y
参数：h : ι -> ι₂；h1 : Surjective h；h2 : forall x, g (h x) = f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.iSup_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : So
rt u_5} [inst : SupSet α] {f : ι → α} {g : ι' → α} (h : ι → ι'),   Function.Surj
ective h → (∀ (x : ι…
-/
theorem iUnion_congr_of_surjective {f : ι → Set α} {g : ι₂ → Set α} (h : ι → ι₂) (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : ⋃ x, f x = ⋃ y, g y :=
  h1.iSup_congr h h2
/-
**Set.iInter_congr_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_congr_of_surjective {f : ι -> Set α} {g : ι₂ -> Set α} (h : ι -> ι₂
) (h1 : Surjective h) (h2 : forall x, g (h x) = f x) : ⋂ x, f x = ⋂ y, g y
参数：h : ι -> ι₂；h1 : Surjective h；h2 : forall x, g (h x) = f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : So
rt u_5} [inst : InfSet α] {f : ι → α} {g : ι' → α} (h : ι → ι'),   Function.Surj
ective h → (∀ (x : ι…
-/
theorem iInter_congr_of_surjective {f : ι → Set α} {g : ι₂ → Set α} (h : ι → ι₂) (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : ⋂ x, f x = ⋂ y, g y :=
  h1.iInf_congr h h2
/-
**Set.iUnion_congr** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iUnion_congr {s t : ι -> Set α} (h : forall i, s i = t i) : ⋃ i, s i = ⋃ i
, t i
参数：h : forall i, s i = t i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_congr`：iSup_congr (h : forall i, f i = g i) : ⨆ i, f i = ⨆ i, g i
-/
lemma iUnion_congr {s t : ι → Set α} (h : ∀ i, s i = t i) : ⋃ i, s i = ⋃ i, t i := iSup_congr h
/-
**Set.iInter_congr** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iInter_congr {s t : ι -> Set α} (h : forall i, s i = t i) : ⋂ i, s i = ⋂ i
, t i
参数：h : forall i, s i = t i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f g : ι →
 α}, (∀ (i : ι), f i = g i) → ⨅ i, f i = ⨅ i, g i
-/
lemma iInter_congr {s t : ι → Set α} (h : ∀ i, s i = t i) : ⋂ i, s i = ⋂ i, t i := iInf_congr h
/-
**Set.iUnion** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iUnion (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iUnion₂_congr {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j = t i j) :
    ⋃ (i) (j), s i j = ⋃ (i) (j), t i j :=
  iUnion_congr fun i => iUnion_congr <| h i
/-
**Set.iInter** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iInter (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iInter₂_congr {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j = t i j) :
    ⋂ (i) (j), s i j = ⋂ (i) (j), t i j :=
  iInter_congr fun i => iInter_congr <| h i
/-
**Set.BijOn.iUnion_comp** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set β} {t : Set γ} {f 
: β → γ} (g : γ → Set α),   Set.BijOn f s t → ⋃ x ∈ s, g (f x) = ⋃ y ∈ t, g y
参数：g : γ → Set α；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.iSup_comp`：Set.BijOn.iSup_comp {s : Set β} {t : Set γ} {f : β 
-> γ} (g : γ -> α) (hf : Set.BijOn f s t) : ⨆ x in s, g (f x) = ⨆ y in t, g y
-/
theorem BijOn.iUnion_comp {s : Set β} {t : Set γ} {f : β → γ} (g : γ → Set α)
    (hf : Set.BijOn f s t) : ⋃ x ∈ s, g (f x) = ⋃ y ∈ t, g y := hf.iSup_comp g
/-
**Set.BijOn.iInter_comp** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set β} {t : Set γ} {f 
: β → γ} (g : γ → Set α),   Set.BijOn f s t → ⋂ x ∈ s, g (f x) = ⋂ y ∈ t, g y
参数：g : γ → Set α；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.iInf_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [ins
t : CompleteLattice α] {s : Set β} {t : Set γ} {f : β → γ}   (g : γ → α), Set.Bi
jOn f s t…
-/
theorem BijOn.iInter_comp {s : Set β} {t : Set γ} {f : β → γ} (g : γ → Set α)
    (hf : Set.BijOn f s t) : ⋂ x ∈ s, g (f x) = ⋂ y ∈ t, g y := hf.iInf_comp g
/-
**Set.BijOn.iUnion_congr** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set β} {t : Set γ} (f 
: β → Set α) (g : γ → Set α) {h : β → γ},   Set.BijOn h s t → (∀ (x : β), g (h x
) = f x) → ⋃ x ∈ s, f x = ⋃ y ∈ t, g y
参数：f : β → Set α；g : γ → Set α；∀ (x : β), g (h x) = f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.iSup_congr`：Set.BijOn.iSup_congr {s : Set β} {t : Set γ} (f : 
β -> α) (g : γ -> α) {h : β -> γ} (h1 : Set.BijOn h s t) (h2 : forall x, g (h x)
 = f x) : …
-/
theorem BijOn.iUnion_congr {s : Set β} {t : Set γ} (f : β → Set α) (g : γ → Set α) {h : β → γ}
    (h1 : Set.BijOn h s t) (h2 : ∀ x, g (h x) = f x) : ⋃ x ∈ s, f x = ⋃ y ∈ t, g y :=
  h1.iSup_congr f g h2
/-
**Set.BijOn.iInter_congr** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set β} {t : Set γ} (f 
: β → Set α) (g : γ → Set α) {h : β → γ},   Set.BijOn h s t → (∀ (x : β), g (h x
) = f x) → ⋂ x ∈ s, f x = ⋂ y ∈ t, g y
参数：f : β → Set α；g : γ → Set α；∀ (x : β), g (h x) = f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.iInf_congr`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [in
st : CompleteLattice α] {s : Set β} {t : Set γ} (f : β → α)   (g : γ → α) {h : β
 → γ}, Set…
-/
theorem BijOn.iInter_congr {s : Set β} {t : Set γ} (f : β → Set α) (g : γ → Set α) {h : β → γ}
    (h1 : Set.BijOn h s t) (h2 : ∀ x, g (h x) = f x) : ⋂ x ∈ s, f x = ⋂ y ∈ t, g y :=
  h1.iInf_congr f g h2

section Nonempty
variable [Nonempty ι] {f : ι → Set α} {s : Set α}

/-
**Set.iUnion_const** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iUnion_const (s : Set β) : ⋃ _ : ι, s = s
参数：s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_const`：iSup_const [Nonempty ι] : ⨆ _ : ι, a = a
-/
lemma iUnion_const (s : Set β) : ⋃ _ : ι, s = s := iSup_const
/-
**Set.iInter_const** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iInter_const (s : Set β) : ⋂ _ : ι, s = s
参数：s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_const`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {
a : α} [Nonempty ι], ⨅ x, a = a
-/
lemma iInter_const (s : Set β) : ⋂ _ : ι, s = s := iInf_const
/-
**Set.iUnion_eq_const** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iUnion_eq_const (hf : forall i, f i = s) : ⋃ i, f i = s
参数：hf : forall i, f i = s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.iUnion_congr`：iUnion_congr {s t : ι -> Set α} (h : forall i, s i = t
 i) : ⋃ i, s i = ⋃ i, t i
· 使用引理 `Set.iUnion_const`：iUnion_const (s : Set β) : ⋃ _ : ι, s = s
-/
lemma iUnion_eq_const (hf : ∀ i, f i = s) : ⋃ i, f i = s :=
  (iUnion_congr hf).trans <| iUnion_const _
/-
**Set.iInter_eq_const** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iInter_eq_const (hf : forall i, f i = s) : ⋂ i, f i = s
参数：hf : forall i, f i = s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.iInter_congr`：iInter_congr {s t : ι -> Set α} (h : forall i, s i = t
 i) : ⋂ i, s i = ⋂ i, t i
· 使用引理 `Set.iInter_const`：iInter_const (s : Set β) : ⋂ _ : ι, s = s
-/
lemma iInter_eq_const (hf : ∀ i, f i = s) : ⋂ i, f i = s :=
  (iInter_congr hf).trans <| iInter_const _

end Nonempty

@[simp]
/-
**Set.compl_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s i)ᶜ
参数：s : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_iSup`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α
] {f : ι → α}, (iSup f)ᶜ = ⨅ i, (f i)ᶜ
-/
theorem compl_iUnion (s : ι → Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s i)ᶜ :=
  compl_iSup
/-
**Set.compl_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s i)ᶜ
参数：s : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_iSup`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α
] {f : ι → α}, (iSup f)ᶜ = ⨅ i, (f i)ᶜ
-/
theorem compl_iUnion₂ (s : ∀ i, κ i → Set α) : (⋃ (i) (j), s i j)ᶜ = ⋂ (i) (j), (s i j)ᶜ := by
  simp_rw [compl_iUnion]

@[simp]
/-
**Set.compl_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s i)ᶜ
参数：s : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_iInf`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α
] {f : ι → α}, (iInf f)ᶜ = ⨆ i, (f i)ᶜ
-/
theorem compl_iInter (s : ι → Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s i)ᶜ :=
  compl_iInf
/-
**Set.compl_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s i)ᶜ
参数：s : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_iInf`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α
] {f : ι → α}, (iInf f)ᶜ = ⨆ i, (f i)ᶜ
-/
theorem compl_iInter₂ (s : ∀ i, κ i → Set α) : (⋂ (i) (j), s i j)ᶜ = ⋃ (i) (j), (s i j)ᶜ := by
  simp_rw [compl_iInter]

-- classical -- complete_boolean_algebra
/-
**Set.iUnion_eq_compl_iInter_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_eq_compl_iInter_compl (s : ι -> Set β) : ⋃ i, s i = (⋂ i, (s i)ᶜ)ᶜ
参数：s : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_iInter`：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s 
i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_eq_compl_iInter_compl (s : ι → Set β) : ⋃ i, s i = (⋂ i, (s i)ᶜ)ᶜ := by
  simp only [compl_iInter, compl_compl]

-- classical -- complete_boolean_algebra
/-
**Set.iInter_eq_compl_iUnion_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_eq_compl_iUnion_compl (s : ι -> Set β) : ⋂ i, s i = (⋃ i, (s i)ᶜ)ᶜ
参数：s : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iInter_eq_compl_iUnion_compl (s : ι → Set β) : ⋂ i, s i = (⋃ i, (s i)ᶜ)ᶜ := by
  simp only [compl_iUnion, compl_compl]
/-
**Set.inter_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃ i, t i) = ⋃ i, s in
ter t i
参数：s : Set β；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_iSup_eq`：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] (a : α) 
(f : ι → α), a ⊓ ⨆ i, f i = ⨆ i, a ⊓ f i
-/
theorem inter_iUnion (s : Set β) (t : ι → Set β) : (s ∩ ⋃ i, t i) = ⋃ i, s ∩ t i :=
  inf_iSup_eq _ _
/-
**Set.iUnion_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i) inter s = ⋃ i, t i 
inter s
参数：s : Set β；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_inf_eq`：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] (f : ι →
 α) (a : α), (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a
-/
theorem iUnion_inter (s : Set β) (t : ι → Set β) : (⋃ i, t i) ∩ s = ⋃ i, t i ∩ s :=
  iSup_inf_eq _ _
/-
**Set.iUnion_union_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_union_distrib (s : ι -> Set β) (t : ι -> Set β) : ⋃ i, s i union t 
i = (⋃ i, s i) union ⋃ i, t i
参数：s : ι -> Set β；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_sup_eq`：iSup_sup_eq : ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ ⨆ x, g x
-/
theorem iUnion_union_distrib (s : ι → Set β) (t : ι → Set β) :
    ⋃ i, s i ∪ t i = (⋃ i, s i) ∪ ⋃ i, t i :=
  iSup_sup_eq
/-
**Set.iInter_inter_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_inter_distrib (s : ι -> Set β) (t : ι -> Set β) : ⋂ i, s i inter t 
i = (⋂ i, s i) inter ⋂ i, t i
参数：s : ι -> Set β；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_inf_eq`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{f g : ι → α}, ⨅ x, f x ⊓ g x = (⨅ x, f x) ⊓ ⨅ x, g x
-/
theorem iInter_inter_distrib (s : ι → Set β) (t : ι → Set β) :
    ⋂ i, s i ∩ t i = (⋂ i, s i) ∩ ⋂ i, t i :=
  iInf_inf_eq
/-
**Set.union_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_iUnion [Nonempty ι] (s : Set β) (t : ι -> Set β) : (s union ⋃ i, t i
) = ⋃ i, s union t i
参数：s : Set β；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_iSup`：sup_iSup [Nonempty ι] {f : ι -> α} {a : α} : (a ⊔ ⨆ x, f x) = 
⨆ x, a ⊔ f x
-/
theorem union_iUnion [Nonempty ι] (s : Set β) (t : ι → Set β) : (s ∪ ⋃ i, t i) = ⋃ i, s ∪ t i :=
  sup_iSup
/-
**Set.iUnion_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_union [Nonempty ι] (s : Set β) (t : ι -> Set β) : (⋃ i, t i) union 
s = ⋃ i, t i union s
参数：s : Set β；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_sup`：iSup_sup [Nonempty ι] {f : ι -> α} {a : α} : (⨆ x, f x) ⊔ a = 
⨆ x, f x ⊔ a
-/
theorem iUnion_union [Nonempty ι] (s : Set β) (t : ι → Set β) : (⋃ i, t i) ∪ s = ⋃ i, t i ∪ s :=
  iSup_sup
/-
**Set.inter_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_iInter [Nonempty ι] (s : Set β) (t : ι -> Set β) : (s inter ⋂ i, t i
) = ⋂ i, s inter t i
参数：s : Set β；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] [No
nempty ι] {f : ι → α} {a : α}, a ⊓ ⨅ x, f x = ⨅ x, a ⊓ f x
-/
theorem inter_iInter [Nonempty ι] (s : Set β) (t : ι → Set β) : (s ∩ ⋂ i, t i) = ⋂ i, s ∩ t i :=
  inf_iInf
/-
**Set.iInter_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_inter [Nonempty ι] (s : Set β) (t : ι -> Set β) : (⋂ i, t i) inter 
s = ⋂ i, t i inter s
参数：s : Set β；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_inf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] [No
nempty ι] {f : ι → α} {a : α},   (⨅ x, f x) ⊓ a = ⨅ x, f x ⊓ a
-/
theorem iInter_inter [Nonempty ι] (s : Set β) (t : ι → Set β) : (⋂ i, t i) ∩ s = ⋂ i, t i ∩ s :=
  iInf_inf
/-
**Set.insert_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_iUnion [Nonempty ι] (x : β) (t : ι -> Set β) : insert x (⋃ i, t i) 
= ⋃ i, insert x (t i)
参数：x : β；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iUnion_union`：iUnion_union [Nonempty ι] (s : Set β) (t : ι -> Set β)
 : (⋃ i, t i) union s = ⋃ i, t i union s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem insert_iUnion [Nonempty ι] (x : β) (t : ι → Set β) :
    insert x (⋃ i, t i) = ⋃ i, insert x (t i) := by
  simp_rw [← union_singleton, iUnion_union]

-- classical
/-
**Set.union_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_iInter (s : Set β) (t : ι -> Set β) : (s union ⋂ i, t i) = ⋂ i, s un
ion t i
参数：s : Set β；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_iInf_eq`：∀ {α : Type u} {ι : Sort w} [inst : Order.Coframe α] (a : α
) (f : ι → α), a ⊔ ⨅ i, f i = ⨅ i, a ⊔ f i
-/
theorem union_iInter (s : Set β) (t : ι → Set β) : (s ∪ ⋂ i, t i) = ⋂ i, s ∪ t i :=
  sup_iInf_eq _ _
/-
**Set.iInter_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_union (s : ι -> Set β) (t : Set β) : (⋂ i, s i) union t = ⋂ i, s i 
union t
参数：s : ι -> Set β；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_sup_eq`：∀ {α : Type u} {ι : Sort w} [inst : Order.Coframe α] (f : ι
 → α) (a : α), (⨅ i, f i) ⊔ a = ⨅ i, f i ⊔ a
-/
theorem iInter_union (s : ι → Set β) (t : Set β) : (⋂ i, s i) ∪ t = ⋂ i, s i ∪ t :=
  iInf_sup_eq _ _
/-
**Set.insert_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_iInter (x : β) (t : ι -> Set β) : insert x (⋂ i, t i) = ⋂ i, insert
 x (t i)
参数：x : β；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iInter_union`：iInter_union (s : ι -> Set β) (t : Set β) : (⋂ i, s i)
 union t = ⋂ i, s i union t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem insert_iInter (x : β) (t : ι → Set β) : insert x (⋂ i, t i) = ⋂ i, insert x (t i) := by
  simp_rw [← union_singleton, iInter_union]
/-
**Set.iUnion_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_sdiff (s : Set β) (t : ι -> Set β) : (⋃ i, t i) \ s = ⋃ i, t i \ s
参数：s : Set β；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_inter`：iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 inter s = ⋃ i, t i inter s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_sdiff (s : Set β) (t : ι → Set β) : (⋃ i, t i) \ s = ⋃ i, t i \ s := by
  simp only [sdiff_eq, iUnion_inter]

@[deprecated (since := "2026-06-03")] alias iUnion_diff := iUnion_sdiff
/-
**Set.sdiff_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_iUnion [Nonempty ι] (s : Set β) (t : ι -> Set β) : (s \ ⋃ i, t i) = 
⋂ i, s \ t i
参数：s : Set β；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `Set.inter_iInter`：inter_iInter [Nonempty ι] (s : Set β) (t : ι -> Set β)
 : (s inter ⋂ i, t i) = ⋂ i, s inter t i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sdiff_iUnion [Nonempty ι] (s : Set β) (t : ι → Set β) : (s \ ⋃ i, t i) = ⋂ i, s \ t i := by
  simp only [sdiff_eq, compl_iUnion, inter_iInter]

@[deprecated (since := "2026-06-03")] alias diff_iUnion := sdiff_iUnion
/-
**Set.sdiff_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_iInter (s : Set β) (t : ι -> Set β) : (s \ ⋂ i, t i) = ⋃ i, s \ t i
参数：s : Set β；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_iInter`：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s 
i)ᶜ
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sdiff_iInter (s : Set β) (t : ι → Set β) : (s \ ⋂ i, t i) = ⋃ i, s \ t i := by
  simp only [sdiff_eq, compl_iInter, inter_iUnion]

@[deprecated (since := "2026-06-03")] alias diff_iInter := sdiff_iInter

section SymmDiff

open scoped symmDiff

/-
**Set.iUnion_symmDiff_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iUnion_symmDiff_subset {s : Set α} [Nonempty ι] {f : ι -> Set α} : (⋃ n, f
 n) ∆ s subseteq ⋃ n, f n ∆ s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_symmDiff_le`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlg
ebra α] {f : ι → α} [Nonempty ι] {a : α},   symmDiff (⨆ i, f i) a ≤ ⨆ i, symmDif
f (f i…
-/
lemma iUnion_symmDiff_subset {s : Set α} [Nonempty ι] {f : ι → Set α} :
    (⋃ n, f n) ∆ s ⊆ ⋃ n, f n ∆ s :=
  iSup_symmDiff_le
/-
**Set.symmDiff_iUnion_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：symmDiff_iUnion_subset {s : Set α} [Nonempty ι] {f : ι -> Set α} : s ∆ (⋃ 
n, f n) subseteq ⋃ n, s ∆ f n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_iSup_le`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlg
ebra α] {f : ι → α} [Nonempty ι] {a : α},   symmDiff a (⨆ i, f i) ≤ ⨆ i, symmDif
f a (f…
-/
lemma symmDiff_iUnion_subset {s : Set α} [Nonempty ι] {f : ι → Set α} :
    s ∆ (⋃ n, f n) ⊆ ⋃ n, s ∆ f n :=
  symmDiff_iSup_le
/-
**Set.iUnion_symmDiff_iUnion_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iUnion_symmDiff_iUnion_subset {f g : ι -> Set α} : (⋃ n, f n) ∆ ⋃ n, g n s
ubseteq ⋃ n, f n ∆ g n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_symmDiff_iSup_le`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBoole
anAlgebra α] {f g : ι → α},   symmDiff (⨆ i, f i) (⨆ i, g i) ≤ ⨆ i, symmDiff (f 
i) (g i)
-/
lemma iUnion_symmDiff_iUnion_subset {f g : ι → Set α} :
    (⋃ n, f n) ∆ ⋃ n, g n ⊆ ⋃ n, f n ∆ g n :=
  iSup_symmDiff_iSup_le
/-
**Set.sUnion_symmDiff_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sUnion_symmDiff_subset {s : Set α} {S : Set (Set α)} (hS : S.Nonempty) : (
⋃₀ S) ∆ s subseteq ⋃₀ ((· ∆ s) '' S)
参数：Set α；hS : S.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_symmDiff_le`：∀ {α : Type u} [inst : CompleteBooleanAlgebra α] {s : 
Set α},   s.Nonempty → ∀ {a : α}, symmDiff (sSup s) a ≤ sSup ((fun x => symmDiff
 x a) …
-/
lemma sUnion_symmDiff_subset {s : Set α} {S : Set (Set α)} (hS : S.Nonempty) :
    (⋃₀ S) ∆ s ⊆ ⋃₀ ((· ∆ s) '' S) :=
  sSup_symmDiff_le hS
/-
**Set.symmDiff_sUnion_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：symmDiff_sUnion_subset {s : Set α} {S : Set (Set α)} (hS : S.Nonempty) : s
 ∆ (⋃₀ S) subseteq ⋃₀ ((s ∆ ·) '' S)
参数：Set α；hS : S.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_sSup_le`：∀ {α : Type u} [inst : CompleteBooleanAlgebra α] {s : 
Set α},   s.Nonempty → ∀ {a : α}, symmDiff a (sSup s) ≤ sSup ((fun x => symmDiff
 a x) …
-/
lemma symmDiff_sUnion_subset {s : Set α} {S : Set (Set α)} (hS : S.Nonempty) :
    s ∆ (⋃₀ S) ⊆ ⋃₀ ((s ∆ ·) '' S) :=
  symmDiff_sSup_le hS
/-
**Set.sUnion_symmDiff_sUnion_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sUnion_symmDiff_sUnion_subset {S T : Set (Set α)} (hS : S.Nonempty) (hT : 
T.Nonempty) : (⋃₀ S) ∆ ⋃₀ T subseteq ⋃₀ (image2 (· ∆ ·) S T)
参数：Set α；hS : S.Nonempty；hT : T.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_symmDiff_sSup_le`：∀ {α : Type u} [inst : CompleteBooleanAlgebra α] 
{s t : Set α},   s.Nonempty → t.Nonempty → symmDiff (sSup s) (sSup t) ≤ sSup (Se
t.image2 (f…
-/
lemma sUnion_symmDiff_sUnion_subset {S T : Set (Set α)} (hS : S.Nonempty)
    (hT : T.Nonempty) :
    (⋃₀ S) ∆ ⋃₀ T ⊆  ⋃₀ (image2 (· ∆ ·) S T) :=
  sSup_symmDiff_sSup_le hS hT

end SymmDiff

/-
**Set.iUnion_inter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_inter_subset {ι α} {s t : ι -> Set α} : ⋃ i, s i inter t i subseteq
 (⋃ i, s i) inter ⋃ i, t i
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup_inf_iSup`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattic
e α] (f g : ι → α), ⨆ i, f i ⊓ g i ≤ (⨆ i, f i) ⊓ ⨆ i, g i
-/
theorem iUnion_inter_subset {ι α} {s t : ι → Set α} : ⋃ i, s i ∩ t i ⊆ (⋃ i, s i) ∩ ⋃ i, t i :=
  le_iSup_inf_iSup s t
/-
**Set.iUnion_inter_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_inter_of_monotone {ι α} [Preorder ι] [IsDirectedOrder ι] {s t : ι -
> Set α} (hs : Monotone s) (ht : Monotone t) : ⋃ i, s i inter t i = (⋃ i, s i) i
nter ⋃ i, t i
参数：hs : Monotone s；ht : Monotone t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_inf_of_monotone`：∀ {α : Type u} [inst : Order.Frame α] {ι : Type u_
1} [inst_1 : Preorder ι] [IsDirectedOrder ι] {f g : ι → α},   Monotone f → Monot
one g → ⨆ …
-/
theorem iUnion_inter_of_monotone {ι α} [Preorder ι] [IsDirectedOrder ι] {s t : ι → Set α}
    (hs : Monotone s) (ht : Monotone t) : ⋃ i, s i ∩ t i = (⋃ i, s i) ∩ ⋃ i, t i :=
  iSup_inf_of_monotone hs ht
/-
**Set.iUnion_inter_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_inter_of_antitone {ι α} [Preorder ι] [IsCodirectedOrder ι] {s t : ι
 -> Set α} (hs : Antitone s) (ht : Antitone t) : ⋃ i, s i inter t i = (⋃ i, s i)
 inter ⋃ i, t i
参数：hs : Antitone s；ht : Antitone t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_inf_of_antitone`：∀ {α : Type u} [inst : Order.Frame α] {ι : Type u_
1} [inst_1 : Preorder ι] [IsCodirectedOrder ι] {f g : ι → α},   Antitone f → Ant
itone g → …
-/
theorem iUnion_inter_of_antitone {ι α} [Preorder ι] [IsCodirectedOrder ι] {s t : ι → Set α}
    (hs : Antitone s) (ht : Antitone t) : ⋃ i, s i ∩ t i = (⋃ i, s i) ∩ ⋃ i, t i :=
  iSup_inf_of_antitone hs ht
/-
**Set.iInter_union_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_union_of_monotone {ι α} [Preorder ι] [IsCodirectedOrder ι] {s t : ι
 -> Set α} (hs : Monotone s) (ht : Monotone t) : ⋂ i, s i union t i = (⋂ i, s i)
 union ⋂ i, t i
参数：hs : Monotone s；ht : Monotone t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_sup_of_monotone`：∀ {α : Type u} [inst : Order.Coframe α] {ι : Type 
u_1} [inst_1 : Preorder ι] [IsCodirectedOrder ι] {f g : ι → α},   Monotone f → M
onotone g …
-/
theorem iInter_union_of_monotone {ι α} [Preorder ι] [IsCodirectedOrder ι] {s t : ι → Set α}
    (hs : Monotone s) (ht : Monotone t) : ⋂ i, s i ∪ t i = (⋂ i, s i) ∪ ⋂ i, t i :=
  iInf_sup_of_monotone hs ht
/-
**Set.iInter_union_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_union_of_antitone {ι α} [Preorder ι] [IsDirectedOrder ι] {s t : ι -
> Set α} (hs : Antitone s) (ht : Antitone t) : ⋂ i, s i union t i = (⋂ i, s i) u
nion ⋂ i, t i
参数：hs : Antitone s；ht : Antitone t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_sup_of_antitone`：∀ {α : Type u} [inst : Order.Coframe α] {ι : Type 
u_1} [inst_1 : Preorder ι] [IsDirectedOrder ι] {f g : ι → α},   Antitone f → Ant
itone g → …
-/
theorem iInter_union_of_antitone {ι α} [Preorder ι] [IsDirectedOrder ι] {s t : ι → Set α}
    (hs : Antitone s) (ht : Antitone t) : ⋂ i, s i ∪ t i = (⋂ i, s i) ∪ ⋂ i, t i :=
  iInf_sup_of_antitone hs ht

/-- An equality version of this lemma is `iUnion_iInter_of_monotone` in `Data.Set.Finite`. -/
/-
**Set.iUnion_iInter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_iInter_subset {s : ι -> ι' -> Set α} : (⋃ j, ⋂ i, s i j) subseteq ⋂
 i, ⋃ j, s i j
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_iInf_le_iInf_iSup`：iSup_iInf_le_iInf_iSup (f : ι -> ι' -> α) : ⨆ i,
 ⨅ j, f i j <= ⨅ j, ⨆ i, f i j

--- 原说明 ---
An equality version of this lemma is `iUnion_iInter_of_monotone` in `Data.Set.Fi
nite`.
-/
theorem iUnion_iInter_subset {s : ι → ι' → Set α} : (⋃ j, ⋂ i, s i j) ⊆ ⋂ i, ⋃ j, s i j :=
  iSup_iInf_le_iInf_iSup (flip s)
/-
**Set.iUnion_option** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_option {ι} (s : Option ι -> Set α) : ⋃ o, s o = s none union ⋃ i, s
 (some i)
参数：s : Option ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_option`：iSup_option (f : Option β -> α) : ⨆ o, f o = f none ⊔ ⨆ b, 
f (Option.some b)
-/
theorem iUnion_option {ι} (s : Option ι → Set α) : ⋃ o, s o = s none ∪ ⋃ i, s (some i) :=
  iSup_option s
/-
**Set.iInter_option** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_option {ι} (s : Option ι -> Set α) : ⋂ o, s o = s none inter ⋂ i, s
 (some i)
参数：s : Option ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_option`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] 
(f : Option β → α), ⨅ o, f o = f none ⊓ ⨅ b, f (some b)
-/
theorem iInter_option {ι} (s : Option ι → Set α) : ⋂ o, s o = s none ∩ ⋂ i, s (some i) :=
  iInf_option s

section

variable (p : ι → Prop) [DecidablePred p]

/-
**Set.iUnion_dite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_dite (f : forall i, p i -> Set α) (g : forall i, ¬p i -> Set α) : ⋃
 i, (if h : p i then f i h else g i h) = (⋃ (i) (h : p i), f i h) union ⋃ (i) (h
 : ¬p i), g i h
参数：f : forall i, p i -> Set α；g : forall i, ¬p i -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_dite`：iSup_dite (f : forall i, p i -> α) (g : forall i, ¬p i -> α) 
: ⨆ i, (if h : p i then f i h else g i h) = (⨆ (i) (h : p i), f i h) ⊔ ⨆ (i) (h…
-/
theorem iUnion_dite (f : ∀ i, p i → Set α) (g : ∀ i, ¬p i → Set α) :
    ⋃ i, (if h : p i then f i h else g i h) = (⋃ (i) (h : p i), f i h) ∪ ⋃ (i) (h : ¬p i), g i h :=
  iSup_dite _ _ _
/-
**Set.iUnion_ite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_ite (f g : ι -> Set α) : ⋃ i, (if p i then f i else g i) = (⋃ (i) (
_ : p i), f i) union ⋃ (i) (_ : ¬p i), g i
参数：f g : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_dite`：iUnion_dite (f : forall i, p i -> Set α) (g : forall i,
 ¬p i -> Set α) : ⋃ i, (if h : p i then f i h else g i h) = (⋃ (i) (h : p i), f 
i h) …
-/
theorem iUnion_ite (f g : ι → Set α) :
    ⋃ i, (if p i then f i else g i) = (⋃ (i) (_ : p i), f i) ∪ ⋃ (i) (_ : ¬p i), g i :=
  iUnion_dite _ _ _
/-
**Set.iInter_dite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_dite (f : forall i, p i -> Set α) (g : forall i, ¬p i -> Set α) : ⋂
 i, (if h : p i then f i h else g i h) = (⋂ (i) (h : p i), f i h) inter ⋂ (i) (h
 : ¬p i), g i h
参数：f : forall i, p i -> Set α；g : forall i, ¬p i -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_dite`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (p
 : ι → Prop) [inst_1 : DecidablePred p]   (f : (i : ι) → p i → α) (g : (i : ι) …
-/
theorem iInter_dite (f : ∀ i, p i → Set α) (g : ∀ i, ¬p i → Set α) :
    ⋂ i, (if h : p i then f i h else g i h) = (⋂ (i) (h : p i), f i h) ∩ ⋂ (i) (h : ¬p i), g i h :=
  iInf_dite _ _ _
/-
**Set.iInter_ite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_ite (f g : ι -> Set α) : ⋂ i, (if p i then f i else g i) = (⋂ (i) (
_ : p i), f i) inter ⋂ (i) (_ : ¬p i), g i
参数：f g : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iInter_dite`：iInter_dite (f : forall i, p i -> Set α) (g : forall i,
 ¬p i -> Set α) : ⋂ i, (if h : p i then f i h else g i h) = (⋂ (i) (h : p i), f 
i h) …
-/
theorem iInter_ite (f g : ι → Set α) :
    ⋂ i, (if p i then f i else g i) = (⋂ (i) (_ : p i), f i) ∩ ⋂ (i) (_ : ¬p i), g i :=
  iInter_dite _ _ _

end

/-! ### Unions and intersections indexed by `Prop` -/


/-
**Set.iInter_false** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_false {s : False -> Set α} : iInter s = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_false`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : False → α},
 iInf s = ⊤

--- 原说明 ---
### Unions and intersections indexed by `Prop`
-/
theorem iInter_false {s : False → Set α} : iInter s = univ :=
  iInf_false
/-
**Set.iUnion_false** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_false {s : False -> Set α} : iUnion s = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_false`：iSup_false {s : False -> α} : iSup s = ⊥
-/
theorem iUnion_false {s : False → Set α} : iUnion s = ∅ :=
  iSup_false

@[simp]
/-
**Set.iInter_true** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_true {s : True -> Set α} : iInter s = s trivial
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_true`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : True → α}, i
Inf s = s trivial
-/
theorem iInter_true {s : True → Set α} : iInter s = s trivial :=
  iInf_true

@[simp]
/-
**Set.iUnion_true** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_true {s : True -> Set α} : iUnion s = s trivial
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_true`：iSup_true {s : True -> α} : iSup s = s trivial
-/
theorem iUnion_true {s : True → Set α} : iUnion s = s trivial :=
  iSup_true

@[simp]
/-
**Set.iInter_exists** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α} : ⋂ x, f x = ⋂ (i) (
h : p i), f ⟨i, h⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_exists`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{p : ι → Prop} {f : Exists p → α},   ⨅ (x : Exists p), f x = ⨅ i, ⨅ (h : p i), f
 …
-/
theorem iInter_exists {p : ι → Prop} {f : Exists p → Set α} :
    ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩ :=
  iInf_exists

@[simp]
/-
**Set.iUnion_exists** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α} : ⋃ x, f x = ⋃ (i) (
h : p i), f ⟨i, h⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_exists`：iSup_exists {p : ι -> Prop} {f : Exists p -> α} : ⨆ x, f x 
= ⨆ (i) (h), f ⟨i, h⟩
-/
theorem iUnion_exists {p : ι → Prop} {f : Exists p → Set α} :
    ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩ :=
  iSup_exists

@[simp]
/-
**Set.iUnion_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_bot`：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
-/
theorem iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅ :=
  iSup_bot

@[simp]
/-
**Set.iInter_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_univ : (⋂ _ : ι, univ : Set α) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_top`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α], ⨅ 
x, ⊤ = ⊤
-/
theorem iInter_univ : (⋂ _ : ι, univ : Set α) = univ :=
  iInf_top

section

variable {s : ι → Set α}

@[simp]
/-
**Set.iUnion_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_eq_empty : ⋃ i, s i = ∅ ↔ forall i, s i = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_eq_bot`：iSup_eq_bot : iSup s = ⊥ ↔ forall i, s i = ⊥
-/
theorem iUnion_eq_empty : ⋃ i, s i = ∅ ↔ ∀ i, s i = ∅ :=
  iSup_eq_bot

@[simp]
/-
**Set.iInter_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_eq_univ : ⋂ i, s i = univ ↔ forall i, s i = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_eq_top`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{s : ι → α}, iInf s = ⊤ ↔ ∀ (i : ι), s i = ⊤
-/
theorem iInter_eq_univ : ⋂ i, s i = univ ↔ ∀ i, s i = univ :=
  iInf_eq_top

@[simp]
/-
**Set.nonempty_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_iUnion : (⋃ i, s i).Nonempty ↔ exists i, (s i).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nonempty_iUnion : (⋃ i, s i).Nonempty ↔ ∃ i, (s i).Nonempty := by
  simp [nonempty_iff_ne_empty]
/-
**Set.nonempty_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_biUnion {t : Set α} {s : α -> Set β} : (⋃ i in t, s i).Nonempty ↔
 exists i in t, (s i).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nonempty_biUnion {t : Set α} {s : α → Set β} :
    (⋃ i ∈ t, s i).Nonempty ↔ ∃ i ∈ t, (s i).Nonempty := by simp
/-
**Set.iUnion_nonempty_index** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_nonempty_index (s : Set α) (t : s.Nonempty -> Set β) : ⋃ h, t h = ⋃
 x in s, t ⟨x, ‹_›⟩
参数：s : Set α；t : s.Nonempty -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_exists`：iSup_exists {p : ι -> Prop} {f : Exists p -> α} : ⨆ x, f x 
= ⨆ (i) (h), f ⟨i, h⟩
-/
theorem iUnion_nonempty_index (s : Set α) (t : s.Nonempty → Set β) :
    ⋃ h, t h = ⋃ x ∈ s, t ⟨x, ‹_›⟩ :=
  iSup_exists

end

@[simp]
/-
**Set.iInter_iInter_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_iInter_eq_left {b : β} {s : forall x : β, x = b -> Set α} : ⋂ (x) (
h : x = b), s x h = s b rfl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_iInf_eq_left`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatti
ce α] {b : β} {f : (x : β) → x = b → α},   ⨅ x, ⨅ (h : x = b), f x h = f b ⋯
-/
theorem iInter_iInter_eq_left {b : β} {s : ∀ x : β, x = b → Set α} :
    ⋂ (x) (h : x = b), s x h = s b rfl :=
  iInf_iInf_eq_left

@[simp]
/-
**Set.iInter_iInter_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_iInter_eq_right {b : β} {s : forall x : β, b = x -> Set α} : ⋂ (x) 
(h : b = x), s x h = s b rfl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_iInf_eq_right`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatt
ice α] {b : β} {f : (x : β) → b = x → α},   ⨅ x, ⨅ (h : b = x), f x h = f b ⋯
-/
theorem iInter_iInter_eq_right {b : β} {s : ∀ x : β, b = x → Set α} :
    ⋂ (x) (h : b = x), s x h = s b rfl :=
  iInf_iInf_eq_right

@[simp]
/-
**Set.iUnion_iUnion_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_iUnion_eq_left {b : β} {s : forall x : β, x = b -> Set α} : ⋃ (x) (
h : x = b), s x h = s b rfl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_iSup_eq_left`：iSup_iSup_eq_left {b : β} {f : forall x : β, x = b ->
 α} : ⨆ x, ⨆ h : x = b, f x h = f b rfl
-/
theorem iUnion_iUnion_eq_left {b : β} {s : ∀ x : β, x = b → Set α} :
    ⋃ (x) (h : x = b), s x h = s b rfl :=
  iSup_iSup_eq_left

@[simp]
/-
**Set.iUnion_iUnion_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_iUnion_eq_right {b : β} {s : forall x : β, b = x -> Set α} : ⋃ (x) 
(h : b = x), s x h = s b rfl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_iSup_eq_right`：iSup_iSup_eq_right {b : β} {f : forall x : β, b = x 
-> α} : ⨆ x, ⨆ h : b = x, f x h = f b rfl
-/
theorem iUnion_iUnion_eq_right {b : β} {s : ∀ x : β, b = x → Set α} :
    ⋃ (x) (h : b = x), s x h = s b rfl :=
  iSup_iSup_eq_right
/-
**Set.iInter_or** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_or {p q : Prop} (s : p ∨ q -> Set α) : ⋂ h, s h = (⋂ h : p, s (Or.i
nl h)) inter ⋂ h : q, s (Or.inr h)
参数：s : p ∨ q -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_or`：∀ {α : Type u_1} [inst : CompleteLattice α] {p q : Prop} {s : p
 ∨ q → α},   ⨅ (x : p ∨ q), s x = (⨅ (i : p), s ⋯) ⊓ ⨅ (j : q), s ⋯
-/
theorem iInter_or {p q : Prop} (s : p ∨ q → Set α) :
    ⋂ h, s h = (⋂ h : p, s (Or.inl h)) ∩ ⋂ h : q, s (Or.inr h) :=
  iInf_or
/-
**Set.iUnion_or** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_or {p q : Prop} (s : p ∨ q -> Set α) : ⋃ h, s h = (⋃ i, s (Or.inl i
)) union ⋃ j, s (Or.inr j)
参数：s : p ∨ q -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_or`：iSup_or {p q : Prop} {s : p ∨ q -> α} : ⨆ x, s x = (⨆ i, s (Or.
inl i)) ⊔ ⨆ j, s (Or.inr j)
-/
theorem iUnion_or {p q : Prop} (s : p ∨ q → Set α) :
    ⋃ h, s h = (⋃ i, s (Or.inl i)) ∪ ⋃ j, s (Or.inr j) :=
  iSup_or
/-
**Set.iUnion_and** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_and {p q : Prop} (s : p ∧ q -> Set α) : ⋃ h, s h = ⋃ (hp) (hq), s ⟨
hp, hq⟩
参数：s : p ∧ q -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_and`：iSup_and {p q : Prop} {s : p ∧ q -> α} : iSup s = ⨆ (h₁) (h₂),
 s ⟨h₁, h₂⟩
-/
theorem iUnion_and {p q : Prop} (s : p ∧ q → Set α) : ⋃ h, s h = ⋃ (hp) (hq), s ⟨hp, hq⟩ :=
  iSup_and
/-
**Set.iInter_and** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_and {p q : Prop} (s : p ∧ q -> Set α) : ⋂ h, s h = ⋂ (hp) (hq), s ⟨
hp, hq⟩
参数：s : p ∧ q -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_and`：∀ {α : Type u_1} [inst : CompleteLattice α] {p q : Prop} {s : 
p ∧ q → α}, iInf s = ⨅ (h₁ : p), ⨅ (h₂ : q), s ⋯
-/
theorem iInter_and {p q : Prop} (s : p ∧ q → Set α) : ⋂ h, s h = ⋂ (hp) (hq), s ⟨hp, hq⟩ :=
  iInf_and
/-
**Set.iUnion_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_comm (s : ι -> ι' -> Set α) : ⋃ (i) (i'), s i i' = ⋃ (i') (i), s i 
i'
参数：s : ι -> ι' -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_comm`：iSup_comm {f : ι -> ι' -> α} : ⨆ (i) (j), f i j = ⨆ (j) (i), 
f i j
-/
theorem iUnion_comm (s : ι → ι' → Set α) : ⋃ (i) (i'), s i i' = ⋃ (i') (i), s i i' :=
  iSup_comm
/-
**Set.iInter_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_comm (s : ι -> ι' -> Set α) : ⋂ (i) (i'), s i i' = ⋂ (i') (i), s i 
i'
参数：s : ι -> ι' -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_comm`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst : Compl
eteLattice α] {f : ι → ι' → α},   ⨅ i, ⨅ j, f i j = ⨅ j, ⨅ i, f i j
-/
theorem iInter_comm (s : ι → ι' → Set α) : ⋂ (i) (i'), s i i' = ⋂ (i') (i), s i i' :=
  iInf_comm
/-
**Set.iUnion_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_sigma {γ : α -> Type*} (s : Sigma γ -> Set β) : ⋃ ia, s ia = ⋃ i, ⋃
 a, s ⟨i, a⟩
参数：s : Sigma γ -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_sigma`：iSup_sigma {p : β -> Type*} {f : Sigma p -> α} : ⨆ x, f x = 
⨆ (i) (j), f ⟨i, j⟩
-/
theorem iUnion_sigma {γ : α → Type*} (s : Sigma γ → Set β) : ⋃ ia, s ia = ⋃ i, ⋃ a, s ⟨i, a⟩ :=
  iSup_sigma
/-
**Set.iUnion_sigma'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_sigma' {γ : α -> Type*} (s : forall i, γ i -> Set β) : ⋃ i, ⋃ a, s 
i a = ⋃ ia : Sigma γ, s ia.1 ia.2
参数：s : forall i, γ i -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `iSup_sigma'`：iSup_sigma' {κ : β -> Type*} (f : forall i, κ i -> α) : (⨆ 
i, ⨆ j, f i j) = ⨆ x : Σ i, κ i, f x.1 x.2
-/
theorem iUnion_sigma' {γ : α → Type*} (s : ∀ i, γ i → Set β) :
    ⋃ i, ⋃ a, s i a = ⋃ ia : Sigma γ, s ia.1 ia.2 :=
  iSup_sigma' _
/-
**Set.iInter_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_sigma {γ : α -> Type*} (s : Sigma γ -> Set β) : ⋂ ia, s ia = ⋂ i, ⋂
 a, s ⟨i, a⟩
参数：s : Sigma γ -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_sigma`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
p : β → Type u_8} {f : Sigma p → α},   ⨅ x, f x = ⨅ i, ⨅ j, f ⟨i, j⟩
-/
theorem iInter_sigma {γ : α → Type*} (s : Sigma γ → Set β) : ⋂ ia, s ia = ⋂ i, ⋂ a, s ⟨i, a⟩ :=
  iInf_sigma
/-
**Set.iInter_sigma'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_sigma' {γ : α -> Type*} (s : forall i, γ i -> Set β) : ⋂ i, ⋂ a, s 
i a = ⋂ ia : Sigma γ, s ia.1 ia.2
参数：s : forall i, γ i -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_sigma'`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] 
{κ : β → Type u_8} (f : (i : β) → κ i → α),   ⨅ i, ⨅ j, f i j = ⨅ x, f x.fst x.s
n…
-/
theorem iInter_sigma' {γ : α → Type*} (s : ∀ i, γ i → Set β) :
    ⋂ i, ⋂ a, s i a = ⋂ ia : Sigma γ, s ia.1 ia.2 :=
  iInf_sigma' _
/-
**Set.iUnion** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iUnion (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iUnion₂_comm (s : ∀ i, κ i → ∀ i', κ' i' → Set α) :
    ⋃ (i) (j) (i') (j'), s i j i' j' = ⋃ (i') (j') (i) (j), s i j i' j' :=
  iSup₂_comm _
/-
**Set.iInter** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iInter (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iInter₂_comm (s : ∀ i, κ i → ∀ i', κ' i' → Set α) :
    ⋂ (i) (j) (i') (j'), s i j i' j' = ⋂ (i') (j') (i) (j), s i j i' j' :=
  iInf₂_comm _

@[simp]
/-
**Set.biUnion_and** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_and (p : ι -> Prop) (q : ι -> ι' -> Prop) (s : forall x y, p x ∧ q
 x y -> Set α) : ⋃ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h = ⋃ (x : ι) (hx :
 p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩
参数：p : ι -> Prop；q : ι -> ι' -> Prop；s : forall x y, p x ∧ q x y -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_and`：iUnion_and {p q : Prop} (s : p ∧ q -> Set α) : ⋃ h, s h 
= ⋃ (hp) (hq), s ⟨hp, hq⟩
· 使用定理 `Set.iUnion_comm`：iUnion_comm (s : ι -> ι' -> Set α) : ⋃ (i) (i'), s i i'
 = ⋃ (i') (i), s i i'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biUnion_and (p : ι → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p x ∧ q x y → Set α) :
    ⋃ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h =
      ⋃ (x : ι) (hx : p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩ := by
  simp only [iUnion_and, @iUnion_comm _ ι']

@[simp]
/-
**Set.biUnion_and'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s : forall x y, p y ∧
 q x y -> Set α) : ⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h = ⋃ (y : ι') (h
y : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩
参数：p : ι' -> Prop；q : ι -> ι' -> Prop；s : forall x y, p y ∧ q x y -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_and`：iUnion_and {p q : Prop} (s : p ∧ q -> Set α) : ⋃ h, s h 
= ⋃ (hp) (hq), s ⟨hp, hq⟩
· 使用定理 `Set.iUnion_comm`：iUnion_comm (s : ι -> ι' -> Set α) : ⋃ (i) (i'), s i i'
 = ⋃ (i') (i), s i i'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biUnion_and' (p : ι' → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p y ∧ q x y → Set α) :
    ⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h =
      ⋃ (y : ι') (hy : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩ := by
  simp only [iUnion_and, @iUnion_comm _ ι]

@[simp]
/-
**Set.biInter_and** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_and (p : ι -> Prop) (q : ι -> ι' -> Prop) (s : forall x y, p x ∧ q
 x y -> Set α) : ⋂ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h = ⋂ (x : ι) (hx :
 p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩
参数：p : ι -> Prop；q : ι -> ι' -> Prop；s : forall x y, p x ∧ q x y -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_and`：iInter_and {p q : Prop} (s : p ∧ q -> Set α) : ⋂ h, s h 
= ⋂ (hp) (hq), s ⟨hp, hq⟩
· 使用定理 `Set.iInter_comm`：iInter_comm (s : ι -> ι' -> Set α) : ⋂ (i) (i'), s i i'
 = ⋂ (i') (i), s i i'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biInter_and (p : ι → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p x ∧ q x y → Set α) :
    ⋂ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h =
      ⋂ (x : ι) (hx : p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩ := by
  simp only [iInter_and, @iInter_comm _ ι']

@[simp]
/-
**Set.biInter_and'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s : forall x y, p y ∧
 q x y -> Set α) : ⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h = ⋂ (y : ι') (h
y : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩
参数：p : ι' -> Prop；q : ι -> ι' -> Prop；s : forall x y, p y ∧ q x y -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_and`：iInter_and {p q : Prop} (s : p ∧ q -> Set α) : ⋂ h, s h 
= ⋂ (hp) (hq), s ⟨hp, hq⟩
· 使用定理 `Set.iInter_comm`：iInter_comm (s : ι -> ι' -> Set α) : ⋂ (i) (i'), s i i'
 = ⋂ (i') (i), s i i'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biInter_and' (p : ι' → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p y ∧ q x y → Set α) :
    ⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h =
      ⋂ (y : ι') (hy : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩ := by
  simp only [iInter_and, @iInter_comm _ ι]

@[simp]
/-
**Set.iUnion_iUnion_eq_or_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_iUnion_eq_or_left {b : β} {p : β -> Prop} {s : forall x : β, x = b 
∨ p x -> Set α} : ⋃ (x) (h), s x h = s b (Or.inl rfl) union ⋃ (x) (h : p x), s x
 (Or.inr h)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_or`：iUnion_or {p q : Prop} (s : p ∨ q -> Set α) : ⋃ h, s h = 
(⋃ i, s (Or.inl i)) union ⋃ j, s (Or.inr j)
· 使用定理 `Set.iUnion_union_distrib`：iUnion_union_distrib (s : ι -> Set β) (t : ι -
> Set β) : ⋃ i, s i union t i = (⋃ i, s i) union ⋃ i, t i
· 使用定理 `Set.iUnion_iUnion_eq_left`：iUnion_iUnion_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋃ (x) (h : x = b), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_iUnion_eq_or_left {b : β} {p : β → Prop} {s : ∀ x : β, x = b ∨ p x → Set α} :
    ⋃ (x) (h), s x h = s b (Or.inl rfl) ∪ ⋃ (x) (h : p x), s x (Or.inr h) := by
  simp only [iUnion_or, iUnion_union_distrib, iUnion_iUnion_eq_left]

@[simp]
/-
**Set.iInter_iInter_eq_or_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_iInter_eq_or_left {b : β} {p : β -> Prop} {s : forall x : β, x = b 
∨ p x -> Set α} : ⋂ (x) (h), s x h = s b (Or.inl rfl) inter ⋂ (x) (h : p x), s x
 (Or.inr h)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_or`：iInter_or {p q : Prop} (s : p ∨ q -> Set α) : ⋂ h, s h = 
(⋂ h : p, s (Or.inl h)) inter ⋂ h : q, s (Or.inr h)
· 使用定理 `Set.iInter_inter_distrib`：iInter_inter_distrib (s : ι -> Set β) (t : ι -
> Set β) : ⋂ i, s i inter t i = (⋂ i, s i) inter ⋂ i, t i
· 使用定理 `Set.iInter_iInter_eq_left`：iInter_iInter_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋂ (x) (h : x = b), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iInter_iInter_eq_or_left {b : β} {p : β → Prop} {s : ∀ x : β, x = b ∨ p x → Set α} :
    ⋂ (x) (h), s x h = s b (Or.inl rfl) ∩ ⋂ (x) (h : p x), s x (Or.inr h) := by
  simp only [iInter_or, iInter_inter_distrib, iInter_iInter_eq_left]
/-
**Set.iUnion_sum** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iUnion_sum {s : α oplus β -> Set γ} : ⋃ x, s x = (⋃ x, s (.inl x)) union ⋃
 x, s (.inr x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_sum`：iSup_sum {f : β oplus γ -> α} : ⨆ x, f x = (⨆ i, f (Sum.inl i)
) ⊔ ⨆ j, f (Sum.inr j)
-/
lemma iUnion_sum {s : α ⊕ β → Set γ} : ⋃ x, s x = (⋃ x, s (.inl x)) ∪ ⋃ x, s (.inr x) := iSup_sum
/-
**Set.iInter_sum** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iInter_sum {s : α oplus β -> Set γ} : ⋂ x, s x = (⋂ x, s (.inl x)) inter ⋂
 x, s (.inr x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_sum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Complet
eLattice α] {f : β ⊕ γ → α},   ⨅ x, f x = (⨅ i, f (Sum.inl i)) ⊓ ⨅ j, f (Sum.i…
-/
lemma iInter_sum {s : α ⊕ β → Set γ} : ⋂ x, s x = (⋂ x, s (.inl x)) ∩ ⋂ x, s (.inr x) := iInf_sum
/-
**Set.iUnion_psigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_psigma {γ : α -> Type*} (s : PSigma γ -> Set β) : ⋃ ia, s ia = ⋃ i,
 ⋃ a, s ⟨i, a⟩
参数：s : PSigma γ -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `iSup_psigma`：iSup_psigma {ι : Sort*} {κ : ι -> Sort*} (f : (Σ' i, κ i) -
> α) : ⨆ ij, f ij = ⨆ i, ⨆ j, f ⟨i, j⟩
-/
theorem iUnion_psigma {γ : α → Type*} (s : PSigma γ → Set β) : ⋃ ia, s ia = ⋃ i, ⋃ a, s ⟨i, a⟩ :=
  iSup_psigma _

/-- A reversed version of `iUnion_psigma` with a curried map. -/
/-
**Set.iUnion_psigma'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_psigma' {γ : α -> Type*} (s : forall i, γ i -> Set β) : ⋃ i, ⋃ a, s
 i a = ⋃ ia : PSigma γ, s ia.1 ia.2
参数：s : forall i, γ i -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `iSup_psigma'`：iSup_psigma' {ι : Sort*} {κ : ι -> Sort*} (f : forall i, κ
 i -> α) : (⨆ i, ⨆ j, f i j) = ⨆ ij : Σ' i, κ i, f ij.1 ij.2

--- 原说明 ---
A reversed version of `iUnion_psigma` with a curried map.
-/
theorem iUnion_psigma' {γ : α → Type*} (s : ∀ i, γ i → Set β) :
    ⋃ i, ⋃ a, s i a = ⋃ ia : PSigma γ, s ia.1 ia.2 :=
  iSup_psigma' _
/-
**Set.iInter_psigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_psigma {γ : α -> Type*} (s : PSigma γ -> Set β) : ⋂ ia, s ia = ⋂ i,
 ⋂ a, s ⟨i, a⟩
参数：s : PSigma γ -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_psigma`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Sort u_8} 
{κ : ι → Sort u_9} (f : (i : ι) ×' κ i → α),   ⨅ ij, f ij = ⨅ i, ⨅ j, f ⟨i, j⟩
-/
theorem iInter_psigma {γ : α → Type*} (s : PSigma γ → Set β) : ⋂ ia, s ia = ⋂ i, ⋂ a, s ⟨i, a⟩ :=
  iInf_psigma _

/-- A reversed version of `iInter_psigma` with a curried map. -/
/-
**Set.iInter_psigma'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_psigma' {γ : α -> Type*} (s : forall i, γ i -> Set β) : ⋂ i, ⋂ a, s
 i a = ⋂ ia : PSigma γ, s ia.1 ia.2
参数：s : forall i, γ i -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_psigma'`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Sort u_8}
 {κ : ι → Sort u_9} (f : (i : ι) → κ i → α),   ⨅ i, ⨅ j, f i j = ⨅ ij, f ij.fst 
ij…

--- 原说明 ---
A reversed version of `iInter_psigma` with a curried map.
-/
theorem iInter_psigma' {γ : α → Type*} (s : ∀ i, γ i → Set β) :
    ⋂ i, ⋂ a, s i a = ⋂ ia : PSigma γ, s ia.1 ia.2 :=
  iInf_psigma' _

/-! ### Bounded unions and intersections -/


/-- A specialization of `mem_iUnion₂`. -/
/-
**Set.mem_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β} (xs : x in s) (yt
x : y in t x) : y in ⋃ x in s, t x
参数：xs : x in s；ytx : y in t x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_iUnion₂_of_mem`：mem_iUnion₂_of_mem {s : forall i, κ i -> Set α} 
{a : α} {i : ι} (j : κ i) (ha : a in s i j) : a in ⋃ (i) (j), s i j

--- 原说明 ---
A specialization of `mem_iUnion₂`.
-/
theorem mem_biUnion {s : Set α} {t : α → Set β} {x : α} {y : β} (xs : x ∈ s) (ytx : y ∈ t x) :
    y ∈ ⋃ x ∈ s, t x :=
  mem_iUnion₂_of_mem xs ytx

/-- A specialization of `mem_iInter₂`. -/
/-
**Set.mem_biInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_biInter {s : Set α} {t : α -> Set β} {y : β} (h : forall x in s, y in 
t x) : y in ⋂ x in s, t x
参数：h : forall x in s, y in t x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_iInter₂_of_mem`：mem_iInter₂_of_mem {s : forall i, κ i -> Set α} 
{a : α} (h : forall i j, a in s i j) : a in ⋂ (i) (j), s i j

--- 原说明 ---
A specialization of `mem_iInter₂`.
-/
theorem mem_biInter {s : Set α} {t : α → Set β} {y : β} (h : ∀ x ∈ s, y ∈ t x) :
    y ∈ ⋂ x ∈ s, t x :=
  mem_iInter₂_of_mem h

/-- A specialization of `subset_iUnion₂`. -/
/-
**Set.subset_biUnion_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_biUnion_of_mem {s : Set α} {u : α -> Set β} {x : α} (xs : x in s) :
 u x subseteq ⋃ x in s, u x
参数：xs : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_iUnion₂`：subset_iUnion₂ {s : forall i, κ i -> Set α} (i : ι) 
(j : κ i) : s i j subseteq ⋃ (i') (j'), s i' j'

--- 原说明 ---
A specialization of `subset_iUnion₂`.
-/
theorem subset_biUnion_of_mem {s : Set α} {u : α → Set β} {x : α} (xs : x ∈ s) :
    u x ⊆ ⋃ x ∈ s, u x :=
  subset_iUnion₂ (s := fun i _ => u i) x xs

/-- A specialization of `iInter₂_subset`. -/
/-
**Set.biInter_subset_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_subset_of_mem {s : Set α} {t : α -> Set β} {x : α} (xs : x in s) :
 ⋂ x in s, t x subseteq t x
参数：xs : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iInter₂_subset`：iInter₂_subset {s : forall i, κ i -> Set α} (i : ι) 
(j : κ i) : ⋂ (i) (j), s i j subseteq s i j

--- 原说明 ---
A specialization of `iInter₂_subset`.
-/
theorem biInter_subset_of_mem {s : Set α} {t : α → Set β} {x : α} (xs : x ∈ s) :
    ⋂ x ∈ s, t x ⊆ t x :=
  iInter₂_subset x xs
/-
**Set.biInter_subset_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：biInter_subset_biUnion {s : Set α} (hs : s.Nonempty) {t : α -> Set β} : ⋂ 
x in s, t x subseteq ⋃ x in s, t x
参数：hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `biInf_le_biSup`：biInf_le_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty)
 {f : ι -> α} : ⨅ i in s, f i <= ⨆ i in s, f i
-/
lemma biInter_subset_biUnion {s : Set α} (hs : s.Nonempty) {t : α → Set β} :
    ⋂ x ∈ s, t x ⊆ ⋃ x ∈ s, t x := biInf_le_biSup hs
/-
**Set.biUnion_subset_biUnion_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_subset_biUnion_left {s s' : Set α} {t : α -> Set β} (h : s subsete
q s') : ⋃ x in s, t x subseteq ⋃ x in s', t x
参数：h : s subseteq s'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Set.subset_biUnion_of_mem`：subset_biUnion_of_mem {s : Set α} {u : α -> S
et β} {x : α} (xs : x in s) : u x subseteq ⋃ x in s, u x
-/
theorem biUnion_subset_biUnion_left {s s' : Set α} {t : α → Set β} (h : s ⊆ s') :
    ⋃ x ∈ s, t x ⊆ ⋃ x ∈ s', t x :=
  iUnion₂_subset fun _ hx => subset_biUnion_of_mem <| h hx
/-
**Set.biInter_subset_biInter_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_subset_biInter_left {s s' : Set α} {t : α -> Set β} (h : s' subset
eq s) : ⋂ x in s, t x subseteq ⋂ x in s', t x
参数：h : s' subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_iInter₂`：subset_iInter₂ {s : Set α} {t : forall i, κ i -> Set
 α} (h : forall i j, s subseteq t i j) : s subseteq ⋂ (i) (j), t i j
· 使用定理 `Set.biInter_subset_of_mem`：biInter_subset_of_mem {s : Set α} {t : α -> S
et β} {x : α} (xs : x in s) : ⋂ x in s, t x subseteq t x
-/
theorem biInter_subset_biInter_left {s s' : Set α} {t : α → Set β} (h : s' ⊆ s) :
    ⋂ x ∈ s, t x ⊆ ⋂ x ∈ s', t x :=
  subset_iInter₂ fun _ hx => biInter_subset_of_mem <| h hx
/-
**Set.biUnion_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_mono {s s' : Set α} {t t' : α -> Set β} (hs : s' subseteq s) (h : 
forall x in s, t x subseteq t' x) : ⋃ x in s', t x subseteq ⋃ x in s, t' x
参数：hs : s' subseteq s；h : forall x in s, t x subseteq t' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.biUnion_subset_biUnion_left`：biUnion_subset_biUnion_left {s s' : Set
 α} {t : α -> Set β} (h : s subseteq s') : ⋃ x in s, t x subseteq ⋃ x in s', t x
· 使用定理 `Set.iUnion₂_mono`：iUnion₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋃ (i) (j), s i j subseteq ⋃ (i) (j), t i j
-/
theorem biUnion_mono {s s' : Set α} {t t' : α → Set β} (hs : s' ⊆ s) (h : ∀ x ∈ s, t x ⊆ t' x) :
    ⋃ x ∈ s', t x ⊆ ⋃ x ∈ s, t' x :=
  (biUnion_subset_biUnion_left hs).trans <| iUnion₂_mono h
/-
**Set.biInter_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_mono {s s' : Set α} {t t' : α -> Set β} (hs : s subseteq s') (h : 
forall x in s, t x subseteq t' x) : ⋂ x in s', t x subseteq ⋂ x in s, t' x
参数：hs : s subseteq s'；h : forall x in s, t x subseteq t' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.biInter_subset_biInter_left`：biInter_subset_biInter_left {s s' : Set
 α} {t : α -> Set β} (h : s' subseteq s) : ⋂ x in s, t x subseteq ⋂ x in s', t x
· 使用定理 `Set.iInter₂_mono`：iInter₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋂ (i) (j), s i j subseteq ⋂ (i) (j), t i j
-/
theorem biInter_mono {s s' : Set α} {t t' : α → Set β} (hs : s ⊆ s') (h : ∀ x ∈ s, t x ⊆ t' x) :
    ⋂ x ∈ s', t x ⊆ ⋂ x ∈ s, t' x :=
  (biInter_subset_biInter_left hs).trans <| iInter₂_mono h
/-
**Set.biUnion_eq_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_eq_iUnion (s : Set α) (t : forall x in s, Set β) : ⋃ x in s, t x ‹
_› = ⋃ x : s, t x x.2
参数：s : Set α；t : forall x in s, Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
-/
theorem biUnion_eq_iUnion (s : Set α) (t : ∀ x ∈ s, Set β) :
    ⋃ x ∈ s, t x ‹_› = ⋃ x : s, t x x.2 :=
  iSup_subtype'
/-
**Set.biInter_eq_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_eq_iInter (s : Set α) (t : forall x in s, Set β) : ⋂ x in s, t x ‹
_› = ⋂ x : s, t x x.2
参数：s : Set α；t : forall x in s, Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_subtype'`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {p : ι → Prop} {f : (i : ι) → p i → α},   ⨅ i, ⨅ (h : p i), f i h = ⨅ x, f ↑x 
⋯
-/
theorem biInter_eq_iInter (s : Set α) (t : ∀ x ∈ s, Set β) :
    ⋂ x ∈ s, t x ‹_› = ⋂ x : s, t x x.2 :=
  iInf_subtype'
/-
**Set.biUnion_const** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.Nonempty → ∀ (t : Set β), ⋃
 a ∈ s, t = t
参数：t : Set β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biSup_const`：biSup_const {a : α} {s : Set β} (hs : s.Nonempty) : ⨆ i in 
s, a = a
-/
@[simp] lemma biUnion_const {s : Set α} (hs : s.Nonempty) (t : Set β) : ⋃ a ∈ s, t = t :=
  biSup_const hs
/-
**Set.biInter_const** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.Nonempty → ∀ (t : Set β), ⋂
 a ∈ s, t = t
参数：t : Set β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biInf_const`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] 
{a : α} {s : Set β}, s.Nonempty → ⨅ i ∈ s, a = a
-/
@[simp] lemma biInter_const {s : Set α} (hs : s.Nonempty) (t : Set β) : ⋂ a ∈ s, t = t :=
  biInf_const hs
/-
**Set.iUnion_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_subtype (p : α -> Prop) (s : { x // p x } -> Set β) : ⋃ x : { x // 
p x }, s x = ⋃ (x) (hx : p x), s ⟨x, hx⟩
参数：p : α -> Prop；s : { x // p x } -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
-/
theorem iUnion_subtype (p : α → Prop) (s : { x // p x } → Set β) :
    ⋃ x : { x // p x }, s x = ⋃ (x) (hx : p x), s ⟨x, hx⟩ :=
  iSup_subtype
/-
**Set.iInter_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_subtype (p : α -> Prop) (s : { x // p x } -> Set β) : ⋂ x : { x // 
p x }, s x = ⋂ (x) (hx : p x), s ⟨x, hx⟩
参数：p : α -> Prop；s : { x // p x } -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_subtype`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α]
 {p : ι → Prop} {f : Subtype p → α},   iInf f = ⨅ i, ⨅ (h : p i), f ⟨i, h⟩
-/
theorem iInter_subtype (p : α → Prop) (s : { x // p x } → Set β) :
    ⋂ x : { x // p x }, s x = ⋂ (x) (hx : p x), s ⟨x, hx⟩ :=
  iInf_subtype
/-
**Set.biInter_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_empty (u : α -> Set β) : ⋂ x in (∅ : Set α), u x = univ
参数：u : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_emptyset`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α
] {f : β → α}, ⨅ x ∈ ∅, f x = ⊤
-/
theorem biInter_empty (u : α → Set β) : ⋂ x ∈ (∅ : Set α), u x = univ :=
  iInf_emptyset
/-
**Set.biInter_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_univ (u : α -> Set β) : ⋂ x in @univ α, u x = ⋂ x, u x
参数：u : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_univ`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {f
 : β → α}, ⨅ x ∈ Set.univ, f x = ⨅ x, f x
-/
theorem biInter_univ (u : α → Set β) : ⋂ x ∈ @univ α, u x = ⋂ x, u x :=
  iInf_univ

@[simp]
/-
**Set.biUnion_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_self (s : Set α) : ⋃ x in s, s = s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
-/
theorem biUnion_self (s : Set α) : ⋃ x ∈ s, s = s :=
  Subset.antisymm (iUnion₂_subset fun _ _ => Subset.refl s) fun _ hx => mem_biUnion hx hx

@[simp]
/-
**Set.iUnion_nonempty_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_nonempty_self (s : Set α) : ⋃ _ : s.Nonempty, s = s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_nonempty_index`：iUnion_nonempty_index (s : Set α) (t : s.None
mpty -> Set β) : ⋃ h, t h = ⋃ x in s, t ⟨x, ‹_›⟩
· 使用定理 `Set.biUnion_self`：biUnion_self (s : Set α) : ⋃ x in s, s = s
-/
theorem iUnion_nonempty_self (s : Set α) : ⋃ _ : s.Nonempty, s = s := by
  rw [iUnion_nonempty_index, biUnion_self]
/-
**Set.biInter_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_singleton (a : α) (s : α -> Set β) : ⋂ x in ({a} : Set α), s x = s
 a
参数：a : α；s : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_singleton`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice 
α] {f : β → α} {b : β}, ⨅ x ∈ {b}, f x = f b
-/
theorem biInter_singleton (a : α) (s : α → Set β) : ⋂ x ∈ ({a} : Set α), s x = s a :=
  iInf_singleton
/-
**Set.biInter_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_union (s t : Set α) (u : α -> Set β) : ⋂ x in s union t, u x = (⋂ 
x in s, u x) inter ⋂ x in t, u x
参数：s t : Set α；u : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_union`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
f : β → α} {s t : Set β},   ⨅ x ∈ s ∪ t, f x = (⨅ x ∈ s, f x) ⊓ ⨅ x ∈ t, f x
-/
theorem biInter_union (s t : Set α) (u : α → Set β) :
    ⋂ x ∈ s ∪ t, u x = (⋂ x ∈ s, u x) ∩ ⋂ x ∈ t, u x :=
  iInf_union
/-
**Set.biInter_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_insert (a : α) (s : Set α) (t : α -> Set β) : ⋂ x in insert a s, t
 x = t a inter ⋂ x in s, t x
参数：a : α；s : Set α；t : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_iInter_eq_or_left`：iInter_iInter_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋂ (x) (h), s x h = s b (Or.inl
 rfl) inter ⋂ (x) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biInter_insert (a : α) (s : Set α) (t : α → Set β) :
    ⋂ x ∈ insert a s, t x = t a ∩ ⋂ x ∈ s, t x := by simp
/-
**Set.biInter_pair** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_pair (a b : α) (s : α -> Set β) : ⋂ x in ({a, b} : Set α), s x = s
 a inter s b
参数：a b : α；s : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biInter_insert`：biInter_insert (a : α) (s : Set α) (t : α -> Set β) 
: ⋂ x in insert a s, t x = t a inter ⋂ x in s, t x
· 使用定理 `Set.biInter_singleton`：biInter_singleton (a : α) (s : α -> Set β) : ⋂ x 
in ({a} : Set α), s x = s a
-/
theorem biInter_pair (a b : α) (s : α → Set β) : ⋂ x ∈ ({a, b} : Set α), s x = s a ∩ s b := by
  rw [biInter_insert, biInter_singleton]
/-
**Set.biInter_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_inter {ι α : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι -> Set α)
 (t : Set α) : ⋂ i in s, f i inter t = (⋂ i in s, f i) inter t
参数：hs : s.Nonempty；f : ι -> Set α；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biInter_eq_iInter`：biInter_eq_iInter (s : Set α) (t : forall x in s,
 Set β) : ⋂ x in s, t x ‹_› = ⋂ x : s, t x x.2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biInter_inter {ι α : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → Set α) (t : Set α) :
    ⋂ i ∈ s, f i ∩ t = (⋂ i ∈ s, f i) ∩ t := by
  have : Nonempty s := hs.to_subtype
  simp [biInter_eq_iInter, ← iInter_inter]
/-
**Set.inter_biInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_biInter {ι α : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι -> Set α)
 (t : Set α) : ⋂ i in s, t inter f i = t inter ⋂ i in s, f i
参数：hs : s.Nonempty；f : ι -> Set α；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biInter_inter`：biInter_inter {ι α : Type*} {s : Set ι} (hs : s.Nonem
pty) (f : ι -> Set α) (t : Set α) : ⋂ i in s, f i inter t = (⋂ i in s, f i) inte
r t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inter_biInter {ι α : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → Set α) (t : Set α) :
    ⋂ i ∈ s, t ∩ f i = t ∩ ⋂ i ∈ s, f i := by
  rw [inter_comm, ← biInter_inter hs]
  simp [inter_comm]
/-
**Set.biUnion_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_empty (s : α -> Set β) : ⋃ x in (∅ : Set α), s x = ∅
参数：s : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_emptyset`：iSup_emptyset {f : β -> α} : ⨆ x in (∅ : Set β), f x = ⊥
-/
theorem biUnion_empty (s : α → Set β) : ⋃ x ∈ (∅ : Set α), s x = ∅ :=
  iSup_emptyset
/-
**Set.biUnion_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_univ (s : α -> Set β) : ⋃ x in @univ α, s x = ⋃ x, s x
参数：s : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_univ`：iSup_univ {f : β -> α} : ⨆ x in (univ : Set β), f x = ⨆ x, f 
x
-/
theorem biUnion_univ (s : α → Set β) : ⋃ x ∈ @univ α, s x = ⋃ x, s x :=
  iSup_univ
/-
**Set.biUnion_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_singleton (a : α) (s : α -> Set β) : ⋃ x in ({a} : Set α), s x = s
 a
参数：a : α；s : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_singleton`：iSup_singleton {f : β -> α} {b : β} : ⨆ x in (singleton 
b : Set β), f x = f b
-/
theorem biUnion_singleton (a : α) (s : α → Set β) : ⋃ x ∈ ({a} : Set α), s x = s a :=
  iSup_singleton

@[simp]
/-
**Set.biUnion_of_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_of_singleton (s : Set α) : ⋃ x in s, {x} = s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem biUnion_of_singleton (s : Set α) : ⋃ x ∈ s, {x} = s :=
  ext <| by simp
/-
**Set.biUnion_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_union (s t : Set α) (u : α -> Set β) : ⋃ x in s union t, u x = (⋃ 
x in s, u x) union ⋃ x in t, u x
参数：s t : Set α；u : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_union`：iSup_union {f : β -> α} {s t : Set β} : ⨆ x in s union t, f 
x = (⨆ x in s, f x) ⊔ ⨆ x in t, f x
-/
theorem biUnion_union (s t : Set α) (u : α → Set β) :
    ⋃ x ∈ s ∪ t, u x = (⋃ x ∈ s, u x) ∪ ⋃ x ∈ t, u x :=
  iSup_union

@[simp]
/-
**Set.iUnion_coe_set** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> Set β) : ⋃ i, f i = ⋃ i
 in s, f ⟨i, ‹i in s›⟩
参数：s : Set α；f : s -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_subtype`：iUnion_subtype (p : α -> Prop) (s : { x // p x } -> 
Set β) : ⋃ x : { x // p x }, s x = ⋃ (x) (hx : p x), s ⟨x, hx⟩
-/
theorem iUnion_coe_set {α β : Type*} (s : Set α) (f : s → Set β) :
    ⋃ i, f i = ⋃ i ∈ s, f ⟨i, ‹i ∈ s›⟩ :=
  iUnion_subtype _ _

@[simp]
/-
**Set.iInter_coe_set** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_coe_set {α β : Type*} (s : Set α) (f : s -> Set β) : ⋂ i, f i = ⋂ i
 in s, f ⟨i, ‹i in s›⟩
参数：s : Set α；f : s -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iInter_subtype`：iInter_subtype (p : α -> Prop) (s : { x // p x } -> 
Set β) : ⋂ x : { x // p x }, s x = ⋂ (x) (hx : p x), s ⟨x, hx⟩
-/
theorem iInter_coe_set {α β : Type*} (s : Set α) (f : s → Set β) :
    ⋂ i, f i = ⋂ i ∈ s, f ⟨i, ‹i ∈ s›⟩ :=
  iInter_subtype _ _
/-
**Set.biUnion_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_insert (a : α) (s : Set α) (t : α -> Set β) : ⋃ x in insert a s, t
 x = t a union ⋃ x in s, t x
参数：a : α；s : Set α；t : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_iUnion_eq_or_left`：iUnion_iUnion_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋃ (x) (h), s x h = s b (Or.inl
 rfl) union ⋃ (x) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biUnion_insert (a : α) (s : Set α) (t : α → Set β) :
    ⋃ x ∈ insert a s, t x = t a ∪ ⋃ x ∈ s, t x := by simp
/-
**Set.biUnion_pair** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_pair (a b : α) (s : α -> Set β) : ⋃ x in ({a, b} : Set α), s x = s
 a union s b
参数：a b : α；s : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_iUnion_eq_or_left`：iUnion_iUnion_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋃ (x) (h), s x h = s b (Or.inl
 rfl) union ⋃ (x) …
· 使用定理 `Set.iUnion_iUnion_eq_left`：iUnion_iUnion_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋃ (x) (h : x = b), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biUnion_pair (a b : α) (s : α → Set β) : ⋃ x ∈ ({a, b} : Set α), s x = s a ∪ s b := by
  simp
/-
**Set.inter_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃ i, t i) = ⋃ i, s in
ter t i
参数：s : Set β；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_iSup_eq`：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] (a : α) 
(f : ι → α), a ⊓ ⨆ i, f i = ⨆ i, a ⊓ f i
-/
theorem inter_iUnion₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∩ ⋃ (i) (j), t i j) = ⋃ (i) (j), s ∩ t i j := by simp only [inter_iUnion]
/-
**Set.iUnion** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iUnion (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iUnion₂_inter (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) ∩ t = ⋃ (i) (j), s i j ∩ t := by simp_rw [iUnion_inter]
/-
**Set.union_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_iInter (s : Set β) (t : ι -> Set β) : (s union ⋂ i, t i) = ⋂ i, s un
ion t i
参数：s : Set β；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_iInf_eq`：∀ {α : Type u} {ι : Sort w} [inst : Order.Coframe α] (a : α
) (f : ι → α), a ⊔ ⨅ i, f i = ⨅ i, a ⊔ f i
-/
theorem union_iInter₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∪ ⋂ (i) (j), t i j) = ⋂ (i) (j), s ∪ t i j := by simp_rw [union_iInter]
/-
**Set.iInter** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iInter (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iInter₂_union (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) ∪ t = ⋂ (i) (j), s i j ∪ t := by simp_rw [iInter_union]
/-
**Set.mem_sUnion_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_sUnion_of_mem {x : α} {t : Set α} {S : Set (Set α)} (hx : x in t) (ht 
: t in S) : x in ⋃₀ S
参数：Set α；hx : x in t；ht : t in S。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_sUnion_of_mem {x : α} {t : Set α} {S : Set (Set α)} (hx : x ∈ t) (ht : t ∈ S) :
    x ∈ ⋃₀ S :=
  ⟨t, ht, hx⟩

-- is this theorem really necessary?
/-
**Set.notMem_of_notMem_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：notMem_of_notMem_sUnion {x : α} {t : Set α} {S : Set (Set α)} (hx : x ∉ ⋃₀
 S) (ht : t in S) : x ∉ t
参数：Set α；hx : x ∉ ⋃₀ S；ht : t in S。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem notMem_of_notMem_sUnion {x : α} {t : Set α} {S : Set (Set α)} (hx : x ∉ ⋃₀ S)
    (ht : t ∈ S) : x ∉ t := fun h => hx ⟨t, ht, h⟩
/-
**Set.sInter_subset_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_subset_of_mem {S : Set (Set α)} {t : Set α} (tS : t in S) : ⋂₀ S su
bseteq t
参数：Set α；tS : t in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
-/
theorem sInter_subset_of_mem {S : Set (Set α)} {t : Set α} (tS : t ∈ S) : ⋂₀ S ⊆ t :=
  sInf_le tS
/-
**Set.subset_sUnion_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_sUnion_of_mem {S : Set (Set α)} {t : Set α} (tS : t in S) : t subse
teq ⋃₀ S
参数：Set α；tS : t in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
theorem subset_sUnion_of_mem {S : Set (Set α)} {t : Set α} (tS : t ∈ S) : t ⊆ ⋃₀ S :=
  le_sSup tS
/-
**Set.subset_sUnion_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_sUnion_of_subset {s : Set α} (t : Set (Set α)) (u : Set α) (h₁ : s 
subseteq u) (h₂ : u in t) : s subseteq ⋃₀ t
参数：t : Set (Set α)；u : Set α；h₁ : s subseteq u；h₂ : u in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
-/
theorem subset_sUnion_of_subset {s : Set α} (t : Set (Set α)) (u : Set α) (h₁ : s ⊆ u)
    (h₂ : u ∈ t) : s ⊆ ⋃₀ t :=
  Subset.trans h₁ (subset_sUnion_of_mem h₂)
/-
**Set.sUnion_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_subset {S : Set (Set α)} {t : Set α} (h : forall t' in S, t' subset
eq t) : ⋃₀ S subseteq t
参数：Set α；h : forall t' in S, t' subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
-/
theorem sUnion_subset {S : Set (Set α)} {t : Set α} (h : ∀ t' ∈ S, t' ⊆ t) : ⋃₀ S ⊆ t :=
  sSup_le h

@[simp]
/-
**Set.sUnion_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_subset_iff {s : Set (Set α)} {t : Set α} : ⋃₀ s subseteq t ↔ forall
 t' in s, t' subseteq t
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_le_iff`：sSup_le_iff : sSup s <= a ↔ forall b in s, b <= a
-/
theorem sUnion_subset_iff {s : Set (Set α)} {t : Set α} : ⋃₀ s ⊆ t ↔ ∀ t' ∈ s, t' ⊆ t :=
  sSup_le_iff

/-- `sUnion` is monotone under taking a subset of each set. -/
/-
**Set.sUnion_mono_subsets** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sUnion_mono_subsets {s : Set (Set α)} {f : Set α -> Set α} (hf : forall t 
: Set α, t subseteq f t) : ⋃₀ s subseteq ⋃₀ (f '' s)
参数：Set α；hf : forall t : Set α, t subseteq f t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
`sUnion` is monotone under taking a subset of each set.
-/
lemma sUnion_mono_subsets {s : Set (Set α)} {f : Set α → Set α} (hf : ∀ t : Set α, t ⊆ f t) :
    ⋃₀ s ⊆ ⋃₀ (f '' s) :=
  fun _ ⟨t, htx, hxt⟩ ↦ ⟨f t, mem_image_of_mem f htx, hf t hxt⟩

/-- `sUnion` is monotone under taking a superset of each set. -/
/-
**Set.sUnion_mono_supsets** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sUnion_mono_supsets {s : Set (Set α)} {f : Set α -> Set α} (hf : forall t 
: Set α, f t subseteq t) : ⋃₀ (f '' s) subseteq ⋃₀ s
参数：Set α；hf : forall t : Set α, f t subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sUnion` is monotone under taking a superset of each set.
-/
lemma sUnion_mono_supsets {s : Set (Set α)} {f : Set α → Set α} (hf : ∀ t : Set α, f t ⊆ t) :
    ⋃₀ (f '' s) ⊆ ⋃₀ s :=
  -- If t ∈ f '' s is arbitrary; t = f u for some u : Set α.
  fun _ ⟨_, ⟨u, hus, hut⟩, hxt⟩ ↦ ⟨u, hus, (hut ▸ hf u) hxt⟩
/-
**Set.subset_sInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_sInter {S : Set (Set α)} {t : Set α} (h : forall t' in S, t subsete
q t') : t subseteq ⋂₀ S
参数：Set α；h : forall t' in S, t subseteq t'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
-/
theorem subset_sInter {S : Set (Set α)} {t : Set α} (h : ∀ t' ∈ S, t ⊆ t') : t ⊆ ⋂₀ S :=
  le_sInf h

@[simp]
/-
**Set.subset_sInter_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_sInter_iff {S : Set (Set α)} {t : Set α} : t subseteq ⋂₀ S ↔ forall
 t' in S, t subseteq t'
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sInf_iff`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set
 α} {a : α}, a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b
-/
theorem subset_sInter_iff {S : Set (Set α)} {t : Set α} : t ⊆ ⋂₀ S ↔ ∀ t' ∈ S, t ⊆ t' :=
  le_sInf_iff

@[gcongr]
/-
**Set.sUnion_subset_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_subset_sUnion {S T : Set (Set α)} (h : S subseteq T) : ⋃₀ S subsete
q ⋃₀ T
参数：Set α；h : S subseteq T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sUnion_subset`：sUnion_subset {S : Set (Set α)} {t : Set α} (h : fora
ll t' in S, t' subseteq t) : ⋃₀ S subseteq t
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
-/
theorem sUnion_subset_sUnion {S T : Set (Set α)} (h : S ⊆ T) : ⋃₀ S ⊆ ⋃₀ T :=
  sUnion_subset fun _ hs => subset_sUnion_of_mem (h hs)

@[gcongr]
/-
**Set.sInter_subset_sInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_subset_sInter {S T : Set (Set α)} (h : S subseteq T) : ⋂₀ T subsete
q ⋂₀ S
参数：Set α；h : S subseteq T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_sInter`：subset_sInter {S : Set (Set α)} {t : Set α} (h : fora
ll t' in S, t subseteq t') : t subseteq ⋂₀ S
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
-/
theorem sInter_subset_sInter {S T : Set (Set α)} (h : S ⊆ T) : ⋂₀ T ⊆ ⋂₀ S :=
  subset_sInter fun _ hs => sInter_subset_of_mem (h hs)

@[simp]
/-
**Set.sUnion_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_empty : ⋃₀ ∅ = (∅ : Set α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_empty`：sSup_empty : sSup ∅ = (⊥ : α)
-/
theorem sUnion_empty : ⋃₀ ∅ = (∅ : Set α) :=
  sSup_empty

@[simp]
/-
**Set.sInter_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_empty : ⋂₀ ∅ = (univ : Set α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_empty`：∀ {α : Type u_1} [inst : CompleteLattice α], sInf ∅ = ⊤
-/
theorem sInter_empty : ⋂₀ ∅ = (univ : Set α) :=
  sInf_empty

@[simp]
/-
**Set.sUnion_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_singleton (s : Set α) : ⋃₀ {s} = s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_singleton`：sSup_singleton {a : α} : sSup {a} = a
-/
theorem sUnion_singleton (s : Set α) : ⋃₀ {s} = s :=
  sSup_singleton

@[simp]
/-
**Set.sInter_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_singleton (s : Set α) : ⋂₀ {s} = s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_singleton`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {a : 
α}, sInf {a} = a
-/
theorem sInter_singleton (s : Set α) : ⋂₀ {s} = s :=
  sInf_singleton

@[simp]
/-
**Set.sUnion_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_eq_empty {S : Set (Set α)} : ⋃₀ S = ∅ ↔ forall s in S, s = ∅
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_eq_bot`：sSup_eq_bot : sSup s = ⊥ ↔ forall a in s, a = ⊥
-/
theorem sUnion_eq_empty {S : Set (Set α)} : ⋃₀ S = ∅ ↔ ∀ s ∈ S, s = ∅ :=
  sSup_eq_bot

@[simp]
/-
**Set.sInter_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_eq_univ {S : Set (Set α)} : ⋂₀ S = univ ↔ forall s in S, s = univ
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_eq_top`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : Set α}, sI
nf s = ⊤ ↔ ∀ a ∈ s, a = ⊤
-/
theorem sInter_eq_univ {S : Set (Set α)} : ⋂₀ S = univ ↔ ∀ s ∈ S, s = univ :=
  sInf_eq_top
/-
**Set.subset_powerset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_powerset_iff {s : Set (Set α)} {t : Set α} : s subseteq 𝒫 t ↔ ⋃₀ s 
subseteq t
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.sUnion_subset_iff`：sUnion_subset_iff {s : Set (Set α)} {t : Set α} :
 ⋃₀ s subseteq t ↔ forall t' in s, t' subseteq t
-/
theorem subset_powerset_iff {s : Set (Set α)} {t : Set α} : s ⊆ 𝒫 t ↔ ⋃₀ s ⊆ t :=
  sUnion_subset_iff.symm

/-- `⋃₀` and `𝒫` form a Galois connection. -/
/-
**Set.sUnion_powerset_gc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_powerset_gc : GaloisConnection (⋃₀ · : Set (Set α) -> Set α) (𝒫 · :
 Set α -> Set (Set α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `gc_sSup_Iic`：gc_sSup_Iic [CompleteSemilatticeSup α] : GaloisConnection (
sSup : Set α -> α) (Iic : α -> Set α)

--- 原说明 ---
`⋃₀` and `𝒫` form a Galois connection.
-/
theorem sUnion_powerset_gc :
    GaloisConnection (⋃₀ · : Set (Set α) → Set α) (𝒫 · : Set α → Set (Set α)) :=
  gc_sSup_Iic

/-- `⋃₀` and `𝒫` form a Galois insertion. -/
/-
**Set.sUnionPowersetGI** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：sUnionPowersetGI : GaloisInsertion (⋃₀ · : Set (Set α) -> Set α) (𝒫 · : Se
t α -> Set (Set α))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`⋃₀` and `𝒫` form a Galois insertion.
-/
def sUnionPowersetGI :
    GaloisInsertion (⋃₀ · : Set (Set α) → Set α) (𝒫 · : Set α → Set (Set α)) :=
  giSSupIic

/-- If all sets in a collection are either `∅` or `Set.univ`, then so is their union. -/
/-
**Set.sUnion_mem_empty_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_mem_empty_univ {S : Set (Set α)} (h : S subseteq {∅, univ}) : ⋃₀ S 
in ({∅, univ} : Set (Set α))
参数：Set α；h : S subseteq {∅, univ}。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If all sets in a collection are either `∅` or `Set.univ`, then so is their union
.
-/
theorem sUnion_mem_empty_univ {S : Set (Set α)} (h : S ⊆ {∅, univ}) :
    ⋃₀ S ∈ ({∅, univ} : Set (Set α)) := by
  grind

@[simp]
/-
**Set.nonempty_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_sUnion {S : Set (Set α)} : (⋃₀ S).Nonempty ↔ exists s in S, Set.N
onempty s
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nonempty_sUnion {S : Set (Set α)} : (⋃₀ S).Nonempty ↔ ∃ s ∈ S, Set.Nonempty s := by
  simp [nonempty_iff_ne_empty]
/-
**Set.Nonempty.of_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} {s : Set (Set α)}, (⋃₀ s).Nonempty → s.Nonempty
参数：Set α；⋃₀ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.nonempty_sUnion`：nonempty_sUnion {S : Set (Set α)} : (⋃₀ S).Nonempty
 ↔ exists s in S, Set.Nonempty s
-/
theorem Nonempty.of_sUnion {s : Set (Set α)} (h : (⋃₀ s).Nonempty) : s.Nonempty :=
  let ⟨s, hs, _⟩ := nonempty_sUnion.1 h
  ⟨s, hs⟩
/-
**Set.Nonempty.of_sUnion_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} [Nonempty α] {s : Set (Set α)}, ⋃₀ s = Set.univ → s.Nonem
pty
参数：Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.of_sUnion`：∀ {α : Type u_1} {s : Set (Set α)}, (⋃₀ s).Nonem
pty → s.Nonempty
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Nonempty.of_sUnion_eq_univ [Nonempty α] {s : Set (Set α)} (h : ⋃₀ s = univ) : s.Nonempty :=
  Nonempty.of_sUnion <| h.symm ▸ univ_nonempty
/-
**Set.sUnion_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_union (S T : Set (Set α)) : ⋃₀ (S union T) = ⋃₀ S union ⋃₀ T
参数：S T : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_union`：sSup_union {s t : Set α} : sSup (s union t) = sSup s ⊔ sSup 
t
-/
theorem sUnion_union (S T : Set (Set α)) : ⋃₀ (S ∪ T) = ⋃₀ S ∪ ⋃₀ T :=
  sSup_union
/-
**Set.sInter_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_union (S T : Set (Set α)) : ⋂₀ (S union T) = ⋂₀ S inter ⋂₀ T
参数：S T : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_union`：∀ {α : Type u_1} [inst : CompleteLattice α] {s t : Set α}, s
Inf (s ∪ t) = sInf s ⊓ sInf t
-/
theorem sInter_union (S T : Set (Set α)) : ⋂₀ (S ∪ T) = ⋂₀ S ∩ ⋂₀ T :=
  sInf_union

@[simp]
/-
**Set.sUnion_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_insert (s : Set α) (T : Set (Set α)) : ⋃₀ insert s T = s union ⋃₀ T
参数：s : Set α；T : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_insert`：sSup_insert {a : α} {s : Set α} : sSup (insert a s) = a ⊔ s
Sup s
-/
theorem sUnion_insert (s : Set α) (T : Set (Set α)) : ⋃₀ insert s T = s ∪ ⋃₀ T :=
  sSup_insert

@[simp]
/-
**Set.sInter_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_insert (s : Set α) (T : Set (Set α)) : ⋂₀ insert s T = s inter ⋂₀ T
参数：s : Set α；T : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_insert`：∀ {α : Type u_1} [inst : CompleteLattice α] {a : α} {s : Se
t α}, sInf (insert a s) = a ⊓ sInf s
-/
theorem sInter_insert (s : Set α) (T : Set (Set α)) : ⋂₀ insert s T = s ∩ ⋂₀ T :=
  sInf_insert

@[simp]
/-
**Set.sUnion_sdiff_singleton_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_sdiff_singleton_empty (s : Set (Set α)) : ⋃₀ (s \ {∅}) = ⋃₀ s
参数：s : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_sdiff_singleton_bot`：sSup_sdiff_singleton_bot (s : Set α) : sSup (s
 \ {⊥}) = sSup s
-/
theorem sUnion_sdiff_singleton_empty (s : Set (Set α)) : ⋃₀ (s \ {∅}) = ⋃₀ s :=
  sSup_sdiff_singleton_bot s

@[deprecated (since := "2026-06-03")]
alias sUnion_diff_singleton_empty := sUnion_sdiff_singleton_empty

@[simp]
/-
**Set.sInter_sdiff_singleton_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_sdiff_singleton_univ (s : Set (Set α)) : ⋂₀ (s \ {univ}) = ⋂₀ s
参数：s : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_sdiff_singleton_top`：∀ {α : Type u_1} [inst : CompleteLattice α] (s
 : Set α), sInf (s \ {⊤}) = sInf s
-/
theorem sInter_sdiff_singleton_univ (s : Set (Set α)) : ⋂₀ (s \ {univ}) = ⋂₀ s :=
  sInf_sdiff_singleton_top s

@[deprecated (since := "2026-06-03")]
alias sInter_diff_singleton_univ := sInter_sdiff_singleton_univ
/-
**Set.sUnion_pair** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_pair (s t : Set α) : ⋃₀ {s, t} = s union t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_pair`：sSup_pair {a b : α} : sSup {a, b} = a ⊔ b
-/
theorem sUnion_pair (s t : Set α) : ⋃₀ {s, t} = s ∪ t :=
  sSup_pair
/-
**Set.sInter_pair** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_pair (s t : Set α) : ⋂₀ {s, t} = s inter t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_pair`：∀ {α : Type u_1} [inst : CompleteLattice α] {a b : α}, sInf {
a, b} = a ⊓ b
-/
theorem sInter_pair (s t : Set α) : ⋂₀ {s, t} = s ∩ t :=
  sInf_pair

@[simp]
/-
**Set.sUnion_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s) = ⋃ a in s, f a
参数：f : α -> Set β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
-/
theorem sUnion_image (f : α → Set β) (s : Set α) : ⋃₀ (f '' s) = ⋃ a ∈ s, f a :=
  sSup_image

@[simp]
/-
**Set.sInter_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s) = ⋂ a in s, f a
参数：f : α -> Set β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
s : Set β} {f : β → α}, sInf (f '' s) = ⨅ a ∈ s, f a
-/
theorem sInter_image (f : α → Set β) (s : Set α) : ⋂₀ (f '' s) = ⋂ a ∈ s, f a :=
  sInf_image

@[simp]
/-
**Set.sUnion_image2** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sUnion_image2 (f : α -> β -> Set γ) (s : Set α) (t : Set β) : ⋃₀ (image2 f
 s t) = ⋃ (a in s) (b in t), f a b
参数：f : α -> β -> Set γ；s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_image2`：sSup_image2 {f : β -> γ -> α} {s : Set β} {t : Set γ} : sSu
p (image2 f s t) = ⨆ (a in s) (b in t), f a b
-/
lemma sUnion_image2 (f : α → β → Set γ) (s : Set α) (t : Set β) :
    ⋃₀ (image2 f s t) = ⋃ (a ∈ s) (b ∈ t), f a b := sSup_image2

@[simp]
/-
**Set.sInter_image2** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sInter_image2 (f : α -> β -> Set γ) (s : Set α) (t : Set β) : ⋂₀ (image2 f
 s t) = ⋂ (a in s) (b in t), f a b
参数：f : α -> β -> Set γ；s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_image2`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Comp
leteLattice α] {f : β → γ → α} {s : Set β} {t : Set γ},   sInf (Set.image2 f s t
)…
-/
lemma sInter_image2 (f : α → β → Set γ) (s : Set α) (t : Set β) :
    ⋂₀ (image2 f s t) = ⋂ (a ∈ s) (b ∈ t), f a b := sInf_image2

@[simp]
/-
**Set.sUnion_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_range (f : ι -> Set β) : ⋃₀ range f = ⋃ x, f x
参数：f : ι -> Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sUnion_range (f : ι → Set β) : ⋃₀ range f = ⋃ x, f x :=
  rfl

@[simp]
/-
**Set.sInter_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_range (f : ι -> Set β) : ⋂₀ range f = ⋂ x, f x
参数：f : ι -> Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sInter_range (f : ι → Set β) : ⋂₀ range f = ⋂ x, f x :=
  rfl
/-
**Set.iUnion_eq_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_eq_univ_iff {f : ι -> Set α} : ⋃ i, f i = univ ↔ forall x, exists i
, x in f i
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
-/
theorem iUnion_eq_univ_iff {f : ι → Set α} : ⋃ i, f i = univ ↔ ∀ x, ∃ i, x ∈ f i := by
  simp only [eq_univ_iff_forall, mem_iUnion]
/-
**Set.iUnion** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iUnion (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iUnion₂_eq_univ_iff {s : ∀ i, κ i → Set α} :
    ⋃ (i) (j), s i j = univ ↔ ∀ a, ∃ i j, a ∈ s i j := by
  simp only [iUnion_eq_univ_iff, mem_iUnion]
/-
**Set.sUnion_eq_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_eq_univ_iff {c : Set (Set α)} : ⋃₀ c = univ ↔ forall a, exists b in
 c, a in b
参数：Set α。
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
-/
theorem sUnion_eq_univ_iff {c : Set (Set α)} : ⋃₀ c = univ ↔ ∀ a, ∃ b ∈ c, a ∈ b := by
  simp only [eq_univ_iff_forall, mem_sUnion]
/-
**Set.iInter_eq_empty_of_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_eq_empty_of_eq_empty {i : ι} {f : ι -> Set α} (h : f i = ∅) : ⋂ j, 
f j = ∅
参数：h : f i = ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_eq_empty`：subset_eq_empty {s t : Set α} (h : t subseteq s) (e
 : s = ∅) : t = ∅
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
-/
theorem iInter_eq_empty_of_eq_empty {i : ι} {f : ι → Set α} (h : f i = ∅) :
    ⋂ j, f j = ∅ :=
  subset_eq_empty (iInter_subset _ i) h

-- classical
/-
**Set.iInter_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_eq_empty_iff {f : ι -> Set α} : ⋂ i, f i = ∅ ↔ forall x, exists i, 
x ∉ f i
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
-/
theorem iInter_eq_empty_iff {f : ι → Set α} : ⋂ i, f i = ∅ ↔ ∀ x, ∃ i, x ∉ f i := by
  simp [Set.eq_empty_iff_forall_notMem]

-- classical
/-
**Set.iInter** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iInter (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iInter₂_eq_empty_iff {s : ∀ i, κ i → Set α} :
    ⋂ (i) (j), s i j = ∅ ↔ ∀ a, ∃ i j, a ∉ s i j := by
  simp only [eq_empty_iff_forall_notMem, mem_iInter, not_forall]

-- classical
/-
**Set.sInter_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_eq_empty_iff {c : Set (Set α)} : ⋂₀ c = ∅ ↔ forall a, exists b in c
, a ∉ b
参数：Set α。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sInter_eq_empty_iff {c : Set (Set α)} : ⋂₀ c = ∅ ↔ ∀ a, ∃ b ∈ c, a ∉ b := by
  simp [Set.eq_empty_iff_forall_notMem]

-- classical
@[simp]
/-
**Set.nonempty_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_iInter {f : ι -> Set α} : (⋂ i, f i).Nonempty ↔ exists x, forall 
i, x in f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nonempty_iInter {f : ι → Set α} : (⋂ i, f i).Nonempty ↔ ∃ x, ∀ i, x ∈ f i := by
  simp [nonempty_iff_ne_empty, iInter_eq_empty_iff]

-- classical
/-
**Set.nonempty_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_iInter {f : ι -> Set α} : (⋂ i, f i).Nonempty ↔ exists x, forall 
i, x in f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nonempty_iInter₂ {s : ∀ i, κ i → Set α} :
    (⋂ (i) (j), s i j).Nonempty ↔ ∃ a, ∀ i j, a ∈ s i j := by
  simp

-- classical
@[simp]
/-
**Set.nonempty_sInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_sInter {c : Set (Set α)} : (⋂₀ c).Nonempty ↔ exists a, forall b i
n c, a in b
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nonempty_sInter {c : Set (Set α)} : (⋂₀ c).Nonempty ↔ ∃ a, ∀ b ∈ c, a ∈ b := by
  simp [nonempty_iff_ne_empty, sInter_eq_empty_iff]

-- classical
/-
**Set.compl_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_sUnion (S : Set (Set α)) : (⋃₀ S)ᶜ = ⋂₀ (compl '' S)
参数：S : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem compl_sUnion (S : Set (Set α)) : (⋃₀ S)ᶜ = ⋂₀ (compl '' S) :=
  ext fun x => by simp

-- classical
/-
**Set.sUnion_eq_compl_sInter_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_eq_compl_sInter_compl (S : Set (Set α)) : ⋃₀ S = (⋂₀ (compl '' S))ᶜ
参数：S : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.compl_sUnion`：compl_sUnion (S : Set (Set α)) : (⋃₀ S)ᶜ = ⋂₀ (compl '
' S)
-/
theorem sUnion_eq_compl_sInter_compl (S : Set (Set α)) : ⋃₀ S = (⋂₀ (compl '' S))ᶜ := by
  rw [← compl_compl (⋃₀ S), compl_sUnion]

-- classical
/-
**Set.compl_sInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_sInter (S : Set (Set α)) : (⋂₀ S)ᶜ = ⋃₀ (compl '' S)
参数：S : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_compl_sInter_compl`：sUnion_eq_compl_sInter_compl (S : Set 
(Set α)) : ⋃₀ S = (⋂₀ (compl '' S))ᶜ
· 使用定理 `Set.compl_compl_image`：compl_compl_image [BooleanAlgebra α] (s : Set α) 
: Compl.compl '' Compl.compl '' s = s
-/
theorem compl_sInter (S : Set (Set α)) : (⋂₀ S)ᶜ = ⋃₀ (compl '' S) := by
  rw [sUnion_eq_compl_sInter_compl, compl_compl_image]

-- classical
/-
**Set.sInter_eq_compl_sUnion_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_eq_compl_sUnion_compl (S : Set (Set α)) : ⋂₀ S = (⋃₀ (compl '' S))ᶜ
参数：S : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.compl_sInter`：compl_sInter (S : Set (Set α)) : (⋂₀ S)ᶜ = ⋃₀ (compl '
' S)
-/
theorem sInter_eq_compl_sUnion_compl (S : Set (Set α)) : ⋂₀ S = (⋃₀ (compl '' S))ᶜ := by
  rw [← compl_compl (⋂₀ S), compl_sInter]
/-
**Set.inter_empty_of_inter_sUnion_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_empty_of_inter_sUnion_empty {s t : Set α} {S : Set (Set α)} (hs : t 
in S) (h : s inter ⋃₀ S = ∅) : s inter t = ∅
参数：Set α；hs : t in S；h : s inter ⋃₀ S = ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_of_subset_empty`：eq_empty_of_subset_empty {s : Set α} : s s
ubseteq ∅ -> s = ∅
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_subset_inter_right`：inter_subset_inter_right {s t : Set α} (u 
: Set α) (H : s subseteq t) : u inter s subseteq u inter t
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
-/
theorem inter_empty_of_inter_sUnion_empty {s t : Set α} {S : Set (Set α)} (hs : t ∈ S)
    (h : s ∩ ⋃₀ S = ∅) : s ∩ t = ∅ :=
  eq_empty_of_subset_empty <| by
    rw [← h]; exact inter_subset_inter_right _ (subset_sUnion_of_mem hs)
/-
**Set.range_sigma_eq_iUnion_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_sigma_eq_iUnion_range {γ : α -> Type*} (f : Sigma γ -> β) : range f 
= ⋃ a, range fun b => f ⟨a, b⟩
参数：f : Sigma γ -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem range_sigma_eq_iUnion_range {γ : α → Type*} (f : Sigma γ → β) :
    range f = ⋃ a, range fun b => f ⟨a, b⟩ :=
  Set.ext <| by simp
/-
**Set.iUnion_eq_range_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_eq_range_sigma (s : α -> Set β) : ⋃ i, s i = range fun a : Σ i, s i
 => a.2
参数：s : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem iUnion_eq_range_sigma (s : α → Set β) : ⋃ i, s i = range fun a : Σ i, s i => a.2 := by
  simp [Set.ext_iff]
/-
**Set.iUnion_eq_range_psigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_eq_range_psigma (s : ι -> Set β) : ⋃ i, s i = range fun a : Σ' i, s
 i => a.2
参数：s : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem iUnion_eq_range_psigma (s : ι → Set β) : ⋃ i, s i = range fun a : Σ' i, s i => a.2 := by
  simp [Set.ext_iff]
/-
**Set.iUnion_image_preimage_sigma_mk_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_image_preimage_sigma_mk_eq_self {ι : Type*} {σ : ι -> Type*} (s : S
et (Sigma σ)) : ⋃ i, Sigma.mk i '' Sigma.mk i ⁻¹' s = s
参数：s : Set (Sigma σ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem iUnion_image_preimage_sigma_mk_eq_self {ι : Type*} {σ : ι → Type*} (s : Set (Sigma σ)) :
    ⋃ i, Sigma.mk i '' Sigma.mk i ⁻¹' s = s := by
  ext x
  simp only [mem_iUnion, mem_image, mem_preimage]
  grind
/-
**Set.Sigma.univ** 是 Mathlib 中的一个定理，位于命名空间 `Set.Sigma`。
形式化陈述：∀ {α : Type u_1} (X : α → Type u_12), Set.univ = ⋃ a, Set.range (Sigma.mk 
a)
参数：X : α → Type u_12；Sigma.mk a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `trivial`：True
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
-/
theorem Sigma.univ (X : α → Type*) : (Set.univ : Set (Σ a, X a)) = ⋃ a, range (Sigma.mk a) :=
  Set.ext fun x =>
    iff_of_true trivial ⟨range (Sigma.mk x.1), Set.mem_range_self _, x.2, Sigma.eta x⟩

alias sUnion_mono := sUnion_subset_sUnion

alias sInter_mono := sInter_subset_sInter
/-
**Set.iUnion_subset_iUnion_const** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_subset_iUnion_const {s : Set α} (h : ι -> ι₂) : ⋃ _ : ι, s subseteq
 ⋃ _ : ι₂, s
参数：h : ι -> ι₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_const_mono`：iSup_const_mono (h : ι -> ι') : ⨆ _ : ι, a <= ⨆ _ : ι',
 a
-/
theorem iUnion_subset_iUnion_const {s : Set α} (h : ι → ι₂) : ⋃ _ : ι, s ⊆ ⋃ _ : ι₂, s :=
  iSup_const_mono (α := Set α) h

@[simp]
/-
**Set.iUnion_singleton_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_singleton_eq_range (f : α -> β) : ⋃ x : α, {f x} = range f
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iUnion_singleton_eq_range (f : α → β) : ⋃ x : α, {f x} = range f := by
  ext x
  simp [@eq_comm _ x]
/-
**Set.iUnion_insert_eq_range_union_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_insert_eq_range_union_iUnion {ι : Type*} (x : ι -> β) (t : ι -> Set
 β) : ⋃ i, insert (x i) (t i) = range x union ⋃ i, t i
参数：x : ι -> β；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_union_distrib`：iUnion_union_distrib (s : ι -> Set β) (t : ι -
> Set β) : ⋃ i, s i union t i = (⋃ i, s i) union ⋃ i, t i
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_singleton_eq_range`：iUnion_singleton_eq_range (f : α -> β) : 
⋃ x : α, {f x} = range f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_insert_eq_range_union_iUnion {ι : Type*} (x : ι → β) (t : ι → Set β) :
    ⋃ i, insert (x i) (t i) = range x ∪ ⋃ i, t i := by
  simp_rw [← union_singleton, iUnion_union_distrib, union_comm, iUnion_singleton_eq_range]
/-
**Set.iUnion_of_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_of_singleton (α : Type*) : (⋃ x, {x} : Set α) = univ
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem iUnion_of_singleton (α : Type*) : (⋃ x, {x} : Set α) = univ := by simp [Set.ext_iff]
/-
**Set.iUnion_of_singleton_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_of_singleton_coe (s : Set α) : ⋃ i : s, ({(i : α)} : Set α) = s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_singleton_eq_range`：iUnion_singleton_eq_range (f : α -> β) : 
⋃ x : α, {f x} = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_of_singleton_coe (s : Set α) : ⋃ i : s, ({(i : α)} : Set α) = s := by simp
/-
**Set.sUnion_eq_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i : Set α) (_ : i in s), i
参数：Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
-/
theorem sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i : Set α) (_ : i ∈ s), i := by
  rw [← sUnion_image, image_id']
/-
**Set.sInter_eq_biInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i : Set α) (_ : i in s), i
参数：Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
-/
theorem sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i : Set α) (_ : i ∈ s), i := by
  rw [← sInter_image, image_id']
/-
**Set.sUnion_eq_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : s, i
参数：Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : s, i := by
  simp only [← sUnion_range, Subtype.range_coe]
/-
**Set.sInter_eq_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_eq_iInter {s : Set (Set α)} : ⋂₀ s = ⋂ i : s, i
参数：Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sInter_eq_iInter {s : Set (Set α)} : ⋂₀ s = ⋂ i : s, i := by
  simp only [← sInter_range, Subtype.range_coe]

@[simp]
/-
**Set.iUnion_of_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i, s i = ∅
参数：s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_of_empty`：iSup_of_empty [IsEmpty ι] (f : ι -> α) : iSup f = ⊥
-/
theorem iUnion_of_empty [IsEmpty ι] (s : ι → Set α) : ⋃ i, s i = ∅ :=
  iSup_of_empty _

@[simp]
/-
**Set.iInter_of_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i, s i = univ
参数：s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_of_empty`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] [IsEmpty ι] (f : ι → α), iInf f = ⊤
-/
theorem iInter_of_empty [IsEmpty ι] (s : ι → Set α) : ⋂ i, s i = univ :=
  iInf_of_empty _
/-
**Set.union_eq_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b : Bool, cond b s₁ s₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_iSup`：sup_eq_iSup (x y : α) : x ⊔ y = ⨆ b : Bool, cond b x y
-/
theorem union_eq_iUnion {s₁ s₂ : Set α} : s₁ ∪ s₂ = ⋃ b : Bool, cond b s₁ s₂ :=
  sup_eq_iSup s₁ s₂
/-
**Set.inter_eq_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_eq_iInter {s₁ s₂ : Set α} : s₁ inter s₂ = ⋂ b : Bool, cond b s₁ s₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] (x y : α), x ⊓ 
y = ⨅ b, bif b then x else y
-/
theorem inter_eq_iInter {s₁ s₂ : Set α} : s₁ ∩ s₂ = ⋂ b : Bool, cond b s₁ s₂ :=
  inf_eq_iInf s₁ s₂
/-
**Set.sInter_union_sInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_union_sInter {S T : Set (Set α)} : ⋂₀ S union ⋂₀ T = ⋂ p in S ×ˢ T,
 (p : Set α × Set α).1 union p.2
参数：Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_sup_sInf`：∀ {α : Type u} [inst : Order.Coframe α] {s t : Set α}, sI
nf s ⊔ sInf t = ⨅ p ∈ s ×ˢ t, p.1 ⊔ p.2
-/
theorem sInter_union_sInter {S T : Set (Set α)} :
    ⋂₀ S ∪ ⋂₀ T = ⋂ p ∈ S ×ˢ T, (p : Set α × Set α).1 ∪ p.2 :=
  sInf_sup_sInf
/-
**Set.sUnion_inter_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_inter_sUnion {s t : Set (Set α)} : ⋃₀ s inter ⋃₀ t = ⋃ p in s ×ˢ t,
 (p : Set α × Set α).1 inter p.2
参数：Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_inf_sSup`：∀ {α : Type u} [inst : Order.Frame α] {s t : Set α}, sSup
 s ⊓ sSup t = ⨆ p ∈ s ×ˢ t, p.1 ⊓ p.2
-/
theorem sUnion_inter_sUnion {s t : Set (Set α)} :
    ⋃₀ s ∩ ⋃₀ t = ⋃ p ∈ s ×ˢ t, (p : Set α × Set α).1 ∩ p.2 :=
  sSup_inf_sSup
/-
**Set.biUnion_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_iUnion (s : ι -> Set α) (t : α -> Set β) : ⋃ x in ⋃ i, s i, t x = 
⋃ (i) (x in s i), t x
参数：s : ι -> Set α；t : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iUnion_comm`：iUnion_comm (s : ι -> ι' -> Set α) : ⋃ (i) (i'), s i i'
 = ⋃ (i') (i), s i i'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biUnion_iUnion (s : ι → Set α) (t : α → Set β) :
    ⋃ x ∈ ⋃ i, s i, t x = ⋃ (i) (x ∈ s i), t x := by simp [@iUnion_comm _ ι]
/-
**Set.biInter_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_iUnion (s : ι -> Set α) (t : α -> Set β) : ⋂ x in ⋃ i, s i, t x = 
⋂ (i) (x in s i), t x
参数：s : ι -> Set α；t : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_comm`：iInter_comm (s : ι -> ι' -> Set α) : ⋂ (i) (i'), s i i'
 = ⋂ (i') (i), s i i'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biInter_iUnion (s : ι → Set α) (t : α → Set β) :
    ⋂ x ∈ ⋃ i, s i, t x = ⋂ (i) (x ∈ s i), t x := by simp [@iInter_comm _ ι]
/-
**Set.sUnion_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_iUnion (s : ι -> Set (Set α)) : ⋃₀ ⋃ i, s i = ⋃ i, ⋃₀ s i
参数：s : ι -> Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.biUnion_iUnion`：biUnion_iUnion (s : ι -> Set α) (t : α -> Set β) : ⋃
 x in ⋃ i, s i, t x = ⋃ (i) (x in s i), t x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sUnion_iUnion (s : ι → Set (Set α)) : ⋃₀ ⋃ i, s i = ⋃ i, ⋃₀ s i := by
  simp only [sUnion_eq_biUnion, biUnion_iUnion]
/-
**Set.sInter_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_iUnion (s : ι -> Set (Set α)) : ⋂₀ ⋃ i, s i = ⋂ i, ⋂₀ s i
参数：s : ι -> Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.biInter_iUnion`：biInter_iUnion (s : ι -> Set α) (t : α -> Set β) : ⋂
 x in ⋃ i, s i, t x = ⋂ (i) (x in s i), t x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sInter_iUnion (s : ι → Set (Set α)) : ⋂₀ ⋃ i, s i = ⋂ i, ⋂₀ s i := by
  simp only [sInter_eq_biInter, biInter_iUnion]
/-
**Set.iUnion_range_eq_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_range_eq_sUnion {α β : Type*} (C : Set (Set α)) {f : forall s : C, 
β -> (s : Type _)} (hf : forall s : C, Surjective (f s)) : ⋃ y : β, range (fun s
 : C => (f s y).val) = ⋃₀ C
参数：C : Set (Set α)；s : Type _；hf : forall s : C, Surjective (f s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem iUnion_range_eq_sUnion {α β : Type*} (C : Set (Set α)) {f : ∀ s : C, β → (s : Type _)}
    (hf : ∀ s : C, Surjective (f s)) : ⋃ y : β, range (fun s : C => (f s y).val) = ⋃₀ C := by
  ext x; constructor
  · rintro ⟨s, ⟨y, rfl⟩, ⟨s, hs⟩, rfl⟩
    refine ⟨_, hs, ?_⟩
    exact (f ⟨s, hs⟩ y).2
  · rintro ⟨s, hs, hx⟩
    obtain ⟨y, hy⟩ := hf ⟨s, hs⟩ ⟨x, hx⟩
    refine ⟨_, ⟨y, rfl⟩, ⟨s, hs⟩, ?_⟩
    exact congr_arg Subtype.val hy
/-
**Set.iUnion_range_eq_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_range_eq_iUnion (C : ι -> Set α) {f : forall x : ι, β -> C x} (hf :
 forall x : ι, Surjective (f x)) : ⋃ y : β, range (fun x : ι => (f x y).val) = ⋃
 x, C x
参数：C : ι -> Set α；hf : forall x : ι, Surjective (f x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem iUnion_range_eq_iUnion (C : ι → Set α) {f : ∀ x : ι, β → C x}
    (hf : ∀ x : ι, Surjective (f x)) : ⋃ y : β, range (fun x : ι => (f x y).val) = ⋃ x, C x := by
  ext x; rw [mem_iUnion, mem_iUnion]; constructor
  · rintro ⟨y, i, rfl⟩
    exact ⟨i, (f i y).2⟩
  · rintro ⟨i, hx⟩
    obtain ⟨y, hy⟩ := hf i ⟨x, hx⟩
    exact ⟨y, i, congr_arg Subtype.val hy⟩
/-
**Set.iUnion_sumElim** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iUnion_sumElim {ι σ : Type*} (s : ι -> Set α) (t : σ -> Set α) : ⋃ x, Sum.
elim s t x = (⋃ x, s x) union ⋃ x, t x
参数：s : ι -> Set α；t : σ -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iUnion_sumElim {ι σ : Type*} (s : ι → Set α) (t : σ → Set α) :
    ⋃ x, Sum.elim s t x = (⋃ x, s x) ∪ ⋃ x, t x := by
  ext
  simp
/-
**Set.union_distrib_iInter_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_distrib_iInter_left (s : ι -> Set α) (t : Set α) : (t union ⋂ i, s i
) = ⋂ i, t union s i
参数：s : ι -> Set α；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_iInf_eq`：∀ {α : Type u} {ι : Sort w} [inst : Order.Coframe α] (a : α
) (f : ι → α), a ⊔ ⨅ i, f i = ⨅ i, a ⊔ f i
-/
theorem union_distrib_iInter_left (s : ι → Set α) (t : Set α) : (t ∪ ⋂ i, s i) = ⋂ i, t ∪ s i :=
  sup_iInf_eq _ _
/-
**Set.union_distrib_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem union_distrib_iInter₂_left (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∪ ⋂ (i) (j), t i j) = ⋂ (i) (j), s ∪ t i j := by simp_rw [union_distrib_iInter_left]
/-
**Set.union_distrib_iInter_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_distrib_iInter_right (s : ι -> Set α) (t : Set α) : (⋂ i, s i) union
 t = ⋂ i, s i union t
参数：s : ι -> Set α；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_sup_eq`：∀ {α : Type u} {ι : Sort w} [inst : Order.Coframe α] (f : ι
 → α) (a : α), (⨅ i, f i) ⊔ a = ⨅ i, f i ⊔ a
-/
theorem union_distrib_iInter_right (s : ι → Set α) (t : Set α) : (⋂ i, s i) ∪ t = ⋂ i, s i ∪ t :=
  iInf_sup_eq _ _
/-
**Set.union_distrib_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem union_distrib_iInter₂_right (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) ∪ t = ⋂ (i) (j), s i j ∪ t := by simp_rw [union_distrib_iInter_right]
/-
**Set.biUnion_lt_eq_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：biUnion_lt_eq_iUnion [LT α] [NoMaxOrder α] {s : α -> Set β} : ⋃ (n) (m < n
), s m = ⋃ n, s n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `biSup_lt_eq_iSup`：biSup_lt_eq_iSup {ι : Type*} [LT ι] [NoMaxOrder ι] {f 
: ι -> α} : ⨆ (i) (j < i), f j = ⨆ i, f i
-/
lemma biUnion_lt_eq_iUnion [LT α] [NoMaxOrder α] {s : α → Set β} :
    ⋃ (n) (m < n), s m = ⋃ n, s n := biSup_lt_eq_iSup
/-
**Set.biUnion_le_eq_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：biUnion_le_eq_iUnion [Preorder α] {s : α -> Set β} : ⋃ (n) (m <= n), s m =
 ⋃ n, s n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `biSup_le_eq_iSup`：biSup_le_eq_iSup {ι : Type*} [Preorder ι] {f : ι -> α}
 : ⨆ (i) (j <= i), f j = ⨆ i, f i
-/
lemma biUnion_le_eq_iUnion [Preorder α] {s : α → Set β} :
    ⋃ (n) (m ≤ n), s m = ⋃ n, s n := biSup_le_eq_iSup
/-
**Set.biInter_lt_eq_iInter** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：biInter_lt_eq_iInter [LT α] [NoMaxOrder α] {s : α -> Set β} : ⋂ (n) (m < n
), s m = ⋂ (n), s n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biInf_lt_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type 
u_8} [inst_1 : LT ι] [NoMaxOrder ι] {f : ι → α},   ⨅ i, ⨅ j, ⨅ (_ : j < i), f j 
= ⨅ i,…
-/
lemma biInter_lt_eq_iInter [LT α] [NoMaxOrder α] {s : α → Set β} :
    ⋂ (n) (m < n), s m = ⋂ (n), s n := biInf_lt_eq_iInf
/-
**Set.biInter_le_eq_iInter** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：biInter_le_eq_iInter [Preorder α] {s : α -> Set β} : ⋂ (n) (m <= n), s m =
 ⋂ (n), s n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biInf_le_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type 
u_8} [inst_1 : Preorder ι] {f : ι → α},   ⨅ i, ⨅ j, ⨅ (_ : j ≤ i), f j = ⨅ i, f 
i
-/
lemma biInter_le_eq_iInter [Preorder α] {s : α → Set β} :
    ⋂ (n) (m ≤ n), s m = ⋂ (n), s n := biInf_le_eq_iInf
/-
**Set.biUnion_gt_eq_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：biUnion_gt_eq_iUnion [LT α] [NoMinOrder α] {s : α -> Set β} : ⋃ (n) (m > n
), s m = ⋃ n, s n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `biSup_gt_eq_iSup`：biSup_gt_eq_iSup {ι : Type*} [LT ι] [NoMinOrder ι] {f 
: ι -> α} : ⨆ (i) (j > i), f j = ⨆ i, f i
-/
lemma biUnion_gt_eq_iUnion [LT α] [NoMinOrder α] {s : α → Set β} :
    ⋃ (n) (m > n), s m = ⋃ n, s n := biSup_gt_eq_iSup
/-
**Set.biUnion_ge_eq_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：biUnion_ge_eq_iUnion [Preorder α] {s : α -> Set β} : ⋃ (n) (m >= n), s m =
 ⋃ n, s n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `biSup_ge_eq_iSup`：biSup_ge_eq_iSup {ι : Type*} [Preorder ι] {f : ι -> α}
 : ⨆ (i) (j >= i), f j = ⨆ i, f i
-/
lemma biUnion_ge_eq_iUnion [Preorder α] {s : α → Set β} :
    ⋃ (n) (m ≥ n), s m = ⋃ n, s n := biSup_ge_eq_iSup
/-
**Set.biInter_gt_eq_iInf** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：biInter_gt_eq_iInf [LT α] [NoMinOrder α] {s : α -> Set β} : ⋂ (n) (m > n),
 s m = ⋂ n, s n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biInf_gt_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type 
u_8} [inst_1 : LT ι] [NoMinOrder ι] {f : ι → α},   ⨅ i, ⨅ j, ⨅ (_ : j > i), f j 
= ⨅ i,…
-/
lemma biInter_gt_eq_iInf [LT α] [NoMinOrder α] {s : α → Set β} :
    ⋂ (n) (m > n), s m = ⋂ n, s n := biInf_gt_eq_iInf
/-
**Set.biInter_ge_eq_iInf** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：biInter_ge_eq_iInf [Preorder α] {s : α -> Set β} : ⋂ (n) (m >= n), s m = ⋂
 n, s n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biInf_ge_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type 
u_8} [inst_1 : Preorder ι] {f : ι → α},   ⨅ i, ⨅ j, ⨅ (_ : j ≥ i), f j = ⨅ i, f 
i
-/
lemma biInter_ge_eq_iInf [Preorder α] {s : α → Set β} :
    ⋂ (n) (m ≥ n), s m = ⋂ n, s n := biInf_ge_eq_iInf

section le

variable {ι : Type*} [PartialOrder ι] (s : ι → Set α) (i : ι)

/-
**Set.biUnion_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_le : (⋃ j <= i, s j) = (⋃ j < i, s j) union s i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biSup_le_eq_sup`：biSup_le_eq_sup : (⨆ j <= i, f j) = (⨆ j < i, f j) ⊔ f 
i
-/
theorem biUnion_le : (⋃ j ≤ i, s j) = (⋃ j < i, s j) ∪ s i :=
  biSup_le_eq_sup s i
/-
**Set.biInter_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_le : (⋂ j <= i, s j) = (⋂ j < i, s j) inter s i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biInf_le_eq_inf`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type u
_8} [inst_1 : PartialOrder ι] (f : ι → α) (i : ι),   ⨅ j, ⨅ (_ : j ≤ i), f j = (
⨅ j, …
-/
theorem biInter_le : (⋂ j ≤ i, s j) = (⋂ j < i, s j) ∩ s i :=
  biInf_le_eq_inf s i
/-
**Set.biUnion_ge** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_ge : (⋃ j >= i, s j) = s i union ⋃ j > i, s j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biSup_ge_eq_sup`：biSup_ge_eq_sup : (⨆ j >= i, f j) = f i ⊔ (⨆ j > i, f j
)
-/
theorem biUnion_ge : (⋃ j ≥ i, s j) = s i ∪ ⋃ j > i, s j :=
  biSup_ge_eq_sup s i
/-
**Set.biInter_ge** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_ge : (⋂ j >= i, s j) = s i inter ⋂ j > i, s j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biInf_ge_eq_inf`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type u
_8} [inst_1 : PartialOrder ι] (f : ι → α) (i : ι),   ⨅ j, ⨅ (_ : j ≥ i), f j = f
 i ⊓ …
-/
theorem biInter_ge : (⋂ j ≥ i, s j) = s i ∩ ⋂ j > i, s j :=
  biInf_ge_eq_inf s i

end le

section Pi

variable {π : α → Type*}

/-
**Set.pi_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_def (i : Set α) (s : forall a, Set (π a)) : pi i s = ⋂ a in i, eval a ⁻
¹' s a
参数：i : Set α；s : forall a, Set (π a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pi_def (i : Set α) (s : ∀ a, Set (π a)) : pi i s = ⋂ a ∈ i, eval a ⁻¹' s a := by
  ext
  simp
/-
**Set.univ_pi_eq_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_pi_eq_iInter (t : forall i, Set (π i)) : pi univ t = ⋂ i, eval i ⁻¹' 
t i
参数：t : forall i, Set (π i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pi_def`：pi_def (i : Set α) (s : forall a, Set (π a)) : pi i s = ⋂ a 
in i, eval a ⁻¹' s a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_true`：iInter_true {s : True -> Set α} : iInter s = s trivial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem univ_pi_eq_iInter (t : ∀ i, Set (π i)) : pi univ t = ⋂ i, eval i ⁻¹' t i := by
  simp only [pi_def, iInter_true, mem_univ]
/-
**Set.pi_sdiff_pi_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_sdiff_pi_subset (i : Set α) (s t : forall a, Set (π a)) : pi i s \ pi i
 t subseteq ⋃ a in i, eval a ⁻¹' (s a \ t a)
参数：i : Set α；s t : forall a, Set (π a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.sdiff_subset_comm`：sdiff_subset_comm {s t u : Set α} : s \ t subsete
q u ↔ s \ u subseteq t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem pi_sdiff_pi_subset (i : Set α) (s t : ∀ a, Set (π a)) :
    pi i s \ pi i t ⊆ ⋃ a ∈ i, eval a ⁻¹' (s a \ t a) := by
  refine sdiff_subset_comm.2 fun x hx a ha => ?_
  simp only [mem_sdiff, mem_pi, mem_iUnion, not_exists, mem_preimage, not_and, not_not] at hx
  exact hx.2 _ ha (hx.1 _ ha)

@[deprecated (since := "2026-06-03")] alias pi_diff_pi_subset := pi_sdiff_pi_subset
/-
**Set.iUnion_univ_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_univ_pi {ι : α -> Type*} (t : (a : α) -> ι a -> Set (π a)) : ⋃ x : 
(a : α) -> ι a, pi univ (fun a => t a (x a)) = pi univ fun a => ⋃ j : ι a, t a j
参数：t : (a : α) -> ι a -> Set (π a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iUnion_univ_pi {ι : α → Type*} (t : (a : α) → ι a → Set (π a)) :
    ⋃ x : (a : α) → ι a, pi univ (fun a => t a (x a)) = pi univ fun a => ⋃ j : ι a, t a j := by
  ext
  simp [Classical.skolem]
/-
**Set.biUnion_univ_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_univ_pi {ι : α -> Type*} (s : (a : α) -> Set (ι a)) (t : (a : α) -
> ι a -> Set (π a)) : ⋃ x in univ.pi s, pi univ (fun a => t a (x a)) = pi univ f
un a => ⋃ j in s a, t a j
参数：s : (a : α) -> Set (ι a)；t : (a : α) -> ι a -> Set (π a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem biUnion_univ_pi {ι : α → Type*} (s : (a : α) → Set (ι a)) (t : (a : α) → ι a → Set (π a)) :
    ⋃ x ∈ univ.pi s, pi univ (fun a => t a (x a)) = pi univ fun a => ⋃ j ∈ s a, t a j := by
  ext
  simp [Classical.skolem, forall_and]
/-
**Set.pi_iUnion_eq_iInter_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_iUnion_eq_iInter_pi {α' : Type*} (s : α' -> Set α) (t : (a : α) -> Set 
(π a)) : (⋃ i, s i).pi t = ⋂ i, (s i).pi t
参数：s : α' -> Set α；t : (a : α) -> Set (π a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem pi_iUnion_eq_iInter_pi {α' : Type*} (s : α' → Set α) (t : (a : α) → Set (π a)) :
    (⋃ i, s i).pi t = ⋂ i, (s i).pi t := by
  ext f
  simp
  grind

end Pi

section Directed

/-
**Set.directedOn_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：directedOn_iUnion {r} {f : ι -> Set α} (hd : Directed (· subseteq ·) f) (h
 : forall x, DirectedOn r (f x)) : DirectedOn r (⋃ x, f x)
参数：hd : Directed (· subseteq ·) f；h : forall x, DirectedOn r (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem directedOn_iUnion {r} {f : ι → Set α} (hd : Directed (· ⊆ ·) f)
    (h : ∀ x, DirectedOn r (f x)) : DirectedOn r (⋃ x, f x) := by
  simp only [DirectedOn, mem_iUnion, exists_imp]
  exact fun a₁ b₁ fb₁ a₂ b₂ fb₂ =>
    let ⟨z, zb₁, zb₂⟩ := hd b₁ b₂
    let ⟨x, xf, xa₁, xa₂⟩ := h z a₁ (zb₁ fb₁) a₂ (zb₂ fb₂)
    ⟨x, ⟨z, xf⟩, xa₁, xa₂⟩
/-
**Set.directedOn_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：directedOn_sUnion {r} {S : Set (Set α)} (hd : DirectedOn (· subseteq ·) S)
 (h : forall x in S, DirectedOn r x) : DirectedOn r (⋃₀ S)
参数：Set α；hd : DirectedOn (· subseteq ·) S；h : forall x in S, DirectedOn r x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
· 使用定理 `Set.directedOn_iUnion`：directedOn_iUnion {r} {f : ι -> Set α} (hd : Dire
cted (· subseteq ·) f) (h : forall x, DirectedOn r (f x)) : DirectedOn r (⋃ x, f
 x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `directedOn_iff_directed`：directedOn_iff_directed {s} : @DirectedOn α r s
 ↔ Directed r (Subtype.val : s -> α)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem directedOn_sUnion {r} {S : Set (Set α)} (hd : DirectedOn (· ⊆ ·) S)
    (h : ∀ x ∈ S, DirectedOn r x) : DirectedOn r (⋃₀ S) := by
  rw [sUnion_eq_iUnion]
  exact directedOn_iUnion (directedOn_iff_directed.mp hd) (fun i ↦ h i.1 i.2)
end Directed

end Set

namespace Function

namespace Surjective

/-
**Function.Surjective.iUnion_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective
`。
形式化陈述：iUnion_comp {f : ι -> ι₂} (hf : Surjective f) (g : ι₂ -> Set α) : ⋃ x, g (
f x) = ⋃ y, g y
参数：hf : Surjective f；g : ι₂ -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.iSup_comp`：Function.Surjective.iSup_comp {f : ι -> ι
'} (hf : Surjective f) (g : ι' -> α) : ⨆ x, g (f x) = ⨆ y, g y
-/
theorem iUnion_comp {f : ι → ι₂} (hf : Surjective f) (g : ι₂ → Set α) : ⋃ x, g (f x) = ⋃ y, g y :=
  hf.iSup_comp g
/-
**Function.Surjective.iInter_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective
`。
形式化陈述：iInter_comp {f : ι -> ι₂} (hf : Surjective f) (g : ι₂ -> Set α) : ⋂ x, g (
f x) = ⋂ y, g y
参数：hf : Surjective f；g : ι₂ -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.iInf_comp`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sor
t u_5} [inst : InfSet α] {f : ι → ι'},   Function.Surjective f → ∀ (g : ι' → α),
 ⨅ x, g (f x) = ⨅ y…
-/
theorem iInter_comp {f : ι → ι₂} (hf : Surjective f) (g : ι₂ → Set α) : ⋂ x, g (f x) = ⋂ y, g y :=
  hf.iInf_comp g

end Surjective

end Function

/-!
### Disjoint sets
-/


section Disjoint

variable {s t : Set α}

namespace Set

@[simp]
/-
**Set.disjoint_iUnion_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_iUnion_left {ι : Sort*} {s : ι -> Set α} : Disjoint (⋃ i, s i) t 
↔ forall i, Disjoint (s i) t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_disjoint_iff`：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] {a
 : α} {f : ι → α},   Disjoint (⨆ i, f i) a ↔ ∀ (i : ι), Disjoint (f i) a
-/
theorem disjoint_iUnion_left {ι : Sort*} {s : ι → Set α} :
    Disjoint (⋃ i, s i) t ↔ ∀ i, Disjoint (s i) t :=
  iSup_disjoint_iff

@[simp]
/-
**Set.disjoint_iUnion_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_iUnion_right {ι : Sort*} {s : ι -> Set α} : Disjoint t (⋃ i, s i)
 ↔ forall i, Disjoint t (s i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_iSup_iff`：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] {a
 : α} {f : ι → α},   Disjoint a (⨆ i, f i) ↔ ∀ (i : ι), Disjoint a (f i)
-/
theorem disjoint_iUnion_right {ι : Sort*} {s : ι → Set α} :
    Disjoint t (⋃ i, s i) ↔ ∀ i, Disjoint t (s i) :=
  disjoint_iSup_iff
/-
**Set.disjoint_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjoint_iUnion₂_left {s : ∀ i, κ i → Set α} {t : Set α} :
    Disjoint (⋃ (i) (j), s i j) t ↔ ∀ i j, Disjoint (s i j) t :=
  iSup₂_disjoint_iff
/-
**Set.disjoint_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjoint_iUnion₂_right {s : Set α} {t : ∀ i, κ i → Set α} :
    Disjoint s (⋃ (i) (j), t i j) ↔ ∀ i j, Disjoint s (t i j) :=
  disjoint_iSup₂_iff

@[simp]
/-
**Set.disjoint_sUnion_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_sUnion_left {S : Set (Set α)} {t : Set α} : Disjoint (⋃₀ S) t ↔ f
orall s in S, Disjoint s t
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_disjoint_iff`：∀ {α : Type u} [inst : Order.Frame α] {a : α} {s : Se
t α}, Disjoint (sSup s) a ↔ ∀ b ∈ s, Disjoint b a
-/
theorem disjoint_sUnion_left {S : Set (Set α)} {t : Set α} :
    Disjoint (⋃₀ S) t ↔ ∀ s ∈ S, Disjoint s t :=
  sSup_disjoint_iff

@[simp]
/-
**Set.disjoint_sUnion_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_sUnion_right {s : Set α} {S : Set (Set α)} : Disjoint s (⋃₀ S) ↔ 
forall t in S, Disjoint s t
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_sSup_iff`：∀ {α : Type u} [inst : Order.Frame α] {a : α} {s : Se
t α}, Disjoint a (sSup s) ↔ ∀ b ∈ s, Disjoint a b
-/
theorem disjoint_sUnion_right {s : Set α} {S : Set (Set α)} :
    Disjoint s (⋃₀ S) ↔ ∀ t ∈ S, Disjoint s t :=
  disjoint_sSup_iff
/-
**Set.biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ** 是 Mathlib 中的一个引理
，位于命名空间 `Set`。
形式化陈述：biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ {ι : Type*} {Es : 
ι -> Set α} (Es_union : ⋃ i, Es i = univ) (Es_disj : Pairwise fun i j => Disjoin
t (Es i) (Es j)) (I : Set ι) : (⋃ i in I, Es i)ᶜ = ⋃ i in Iᶜ, Es i
参数：Es_union : ⋃ i, Es i = univ；Es_disj : Pairwise fun i j => Disjoint (Es i) (Es
 j)；I : Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Disjoint.ne_of_mem`：∀ {α : Type u} {s t : Set α}, Disjoint s t → ∀ ⦃a : 
α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ t → a ≠ b
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ {ι : Type*} {Es : ι → Set α}
    (Es_union : ⋃ i, Es i = univ) (Es_disj : Pairwise fun i j ↦ Disjoint (Es i) (Es j))
    (I : Set ι) :
    (⋃ i ∈ I, Es i)ᶜ = ⋃ i ∈ Iᶜ, Es i := by
  ext x
  obtain ⟨i, hix⟩ : ∃ i, x ∈ Es i := by simp [← mem_iUnion, Es_union]
  have obs : ∀ (J : Set ι), x ∈ ⋃ j ∈ J, Es j ↔ i ∈ J := by
    refine fun J ↦ ⟨?_, fun i_in_J ↦ by simpa only [mem_iUnion, exists_prop] using ⟨i, i_in_J, hix⟩⟩
    intro x_in_U
    simp only [mem_iUnion, exists_prop] at x_in_U
    obtain ⟨j, j_in_J, hjx⟩ := x_in_U
    rwa [show i = j by by_contra i_ne_j; exact Disjoint.ne_of_mem (Es_disj i_ne_j) hix hjx rfl]
  have obs' : ∀ (J : Set ι), x ∈ (⋃ j ∈ J, Es j)ᶜ ↔ i ∉ J :=
    fun J ↦ by simpa only [mem_compl_iff, not_iff_not] using obs J
  rw [obs, obs', mem_compl_iff]

end Set

end Disjoint

/-! ### Intervals -/

namespace Set

/-
**Set.nonempty_iInter_Iic_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：nonempty_iInter_Iic_iff [Preorder α] {f : ι -> α} : (⋂ i, Iic (f i)).Nonem
pty ↔ BddBelow (range f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nonempty_iInter_Iic_iff [Preorder α] {f : ι → α} :
    (⋂ i, Iic (f i)).Nonempty ↔ BddBelow (range f) := by
  have : (⋂ (i : ι), Iic (f i)) = lowerBounds (range f) := by
    ext c; simp [lowerBounds]
  simp [this, BddBelow]
/-
**Set.nonempty_iInter_Ici_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：nonempty_iInter_Ici_iff [Preorder α] {f : ι -> α} : (⋂ i, Ici (f i)).Nonem
pty ↔ BddAbove (range f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.nonempty_iInter_Iic_iff`：nonempty_iInter_Iic_iff [Preorder α] {f : ι
 -> α} : (⋂ i, Iic (f i)).Nonempty ↔ BddBelow (range f)
-/
lemma nonempty_iInter_Ici_iff [Preorder α] {f : ι → α} :
    (⋂ i, Ici (f i)).Nonempty ↔ BddAbove (range f) :=
  nonempty_iInter_Iic_iff (α := αᵒᵈ)

variable [CompleteLattice α]
/-
**Set.Ici_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ici_iSup (f : ι -> α) : Ici (⨆ i, f i) = ⋂ i, Ici (f i)
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ici_iSup (f : ι → α) : Ici (⨆ i, f i) = ⋂ i, Ici (f i) :=
  ext fun _ => by simp only [mem_Ici, iSup_le_iff, mem_iInter]
/-
**Set.Iic_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_iInf (f : ι -> α) : Iic (⨅ i, f i) = ⋂ i, Iic (f i)
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Iic_iInf (f : ι → α) : Iic (⨅ i, f i) = ⋂ i, Iic (f i) :=
  ext fun _ => by simp only [mem_Iic, le_iInf_iff, mem_iInter]
/-
**Set.Ici_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ici_iSup (f : ι -> α) : Ici (⨆ i, f i) = ⋂ i, Ici (f i)
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ici_iSup₂ (f : ∀ i, κ i → α) : Ici (⨆ (i) (j), f i j) = ⋂ (i) (j), Ici (f i j) := by
  simp_rw [Ici_iSup]
/-
**Set.Iic_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_iInf (f : ι -> α) : Iic (⨅ i, f i) = ⋂ i, Iic (f i)
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Iic_iInf₂ (f : ∀ i, κ i → α) : Iic (⨅ (i) (j), f i j) = ⋂ (i) (j), Iic (f i j) := by
  simp_rw [Iic_iInf]
/-
**Set.Ici_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ici_sSup (s : Set α) : Ici (sSup s) = ⋂ a in s, Ici a
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `Set.Ici_iSup₂`：Ici_iSup₂ (f : forall i, κ i -> α) : Ici (⨆ (i) (j), f i 
j) = ⋂ (i) (j), Ici (f i j)
-/
theorem Ici_sSup (s : Set α) : Ici (sSup s) = ⋂ a ∈ s, Ici a := by rw [sSup_eq_iSup, Ici_iSup₂]
/-
**Set.Iic_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_sInf (s : Set α) : Iic (sInf s) = ⋂ a in s, Iic a
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : Set α}, s
Inf s = ⨅ a ∈ s, a
· 使用定理 `Set.Iic_iInf₂`：Iic_iInf₂ (f : forall i, κ i -> α) : Iic (⨅ (i) (j), f i 
j) = ⋂ (i) (j), Iic (f i j)
-/
theorem Iic_sInf (s : Set α) : Iic (sInf s) = ⋂ a ∈ s, Iic a := by rw [sInf_eq_iInf, Iic_iInf₂]

end Set

namespace Set

variable (t : α → Set β)

/-
**Set.biUnion_sdiff_biUnion_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_sdiff_biUnion_subset (s₁ s₂ : Set α) : ((⋃ x in s₁, t x) \ ⋃ x in 
s₂, t x) subseteq ⋃ x in s₁ \ s₂, t x
参数：s₁ s₂ : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_subset_biUnion_left`：biUnion_subset_biUnion_left {s s' : Set
 α} {t : α -> Set β} (h : s subseteq s') : ⋃ x in s, t x subseteq ⋃ x in s', t x
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
-/
theorem biUnion_sdiff_biUnion_subset (s₁ s₂ : Set α) :
    ((⋃ x ∈ s₁, t x) \ ⋃ x ∈ s₂, t x) ⊆ ⋃ x ∈ s₁ \ s₂, t x := by
  simp only [sdiff_subset_iff, ← biUnion_union]
  apply biUnion_subset_biUnion_left
  rw [union_sdiff_self]
  apply subset_union_right

@[deprecated (since := "2026-06-03")]
alias biUnion_diff_biUnion_subset := biUnion_sdiff_biUnion_subset

/-- If `t` is an indexed family of sets, then there is a natural map from `Σ i, t i` to `⋃ i, t i`
sending `⟨i, x⟩` to `x`. -/
/-
**Set.sigmaToiUnion** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：sigmaToiUnion (x : Σ i, t i) : ⋃ i, t i
参数：x : Σ i, t i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `t` is an indexed family of sets, then there is a natural map from `Σ i, t i`
 to `⋃ i, t i`
sending `⟨i, x⟩` to `x`.
-/
def sigmaToiUnion (x : Σ i, t i) : ⋃ i, t i :=
  ⟨x.2, mem_iUnion.2 ⟨x.1, x.2.2⟩⟩
/-
**Set.sigmaToiUnion_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sigmaToiUnion_surjective : Surjective (sigmaToiUnion t) | ⟨b, hb⟩ => have 
: exists a, b in t a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigmaToiUnion_surjective : Surjective (sigmaToiUnion t)
  | ⟨b, hb⟩ =>
    have : ∃ a, b ∈ t a := by simpa using hb
    let ⟨a, hb⟩ := this
    ⟨⟨a, b, hb⟩, rfl⟩
/-
**Set.sigmaToiUnion_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sigmaToiUnion_injective (h : Pairwise (Disjoint on t)) : Injective (sigmaT
oiUnion t) | ⟨a₁, b₁, h₁⟩, ⟨a₂, b₂, h₂⟩, eq => have b_eq : b₁ = b₂
参数：h : Pairwise (Disjoint on t)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Sigma.eq`：∀ {α : Type u_7} {β : α → Type u_8} {p₁ p₂ : (a : α) × β a} (h
₁ : p₁.fst = p₂.fst),   Eq.recOn h₁ p₁.snd = p₂.snd → p₁ = p₂
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem sigmaToiUnion_injective (h : Pairwise (Disjoint on t)) :
    Injective (sigmaToiUnion t)
  | ⟨a₁, b₁, h₁⟩, ⟨a₂, b₂, h₂⟩, eq =>
    have b_eq : b₁ = b₂ := congr_arg Subtype.val eq
    have a_eq : a₁ = a₂ :=
      by_contradiction fun ne =>
        have : b₁ ∈ t a₁ ∩ t a₂ := ⟨h₁, b_eq.symm ▸ h₂⟩
        (h ne).le_bot this
    Sigma.eq a_eq <| Subtype.ext <| by subst b_eq; subst a_eq; rfl
/-
**Set.sigmaToiUnion_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sigmaToiUnion_bijective (h : Pairwise (Disjoint on t)) : Bijective (sigmaT
oiUnion t)
参数：h : Pairwise (Disjoint on t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sigmaToiUnion_injective`：sigmaToiUnion_injective (h : Pairwise (Disj
oint on t)) : Injective (sigmaToiUnion t) | ⟨a₁, b₁, h₁⟩, ⟨a₂, b₂, h₂⟩, eq => ha
ve b_eq : b₁ = b₂
· 使用定理 `Set.sigmaToiUnion_surjective`：sigmaToiUnion_surjective : Surjective (sig
maToiUnion t) | ⟨b, hb⟩ => have : exists a, b in t a
-/
theorem sigmaToiUnion_bijective (h : Pairwise (Disjoint on t)) :
    Bijective (sigmaToiUnion t) :=
  ⟨sigmaToiUnion_injective t h, sigmaToiUnion_surjective t⟩

/-- Equivalence from the disjoint union of a family of sets forming a partition of `β`, to `β`
itself. -/
/-
**Set.sigmaEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：sigmaEquiv (s : α -> Set β) (hs : forall b, exists! i, b in s i) : (Σ i, s
 i) ≃ β where toFun | ⟨_, b⟩ => b invFun b
参数：s : α -> Set β；hs : forall b, exists! i, b in s i。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence from the disjoint union of a family of sets forming a partition of `
β`, to `β`
itself.
-/
noncomputable def sigmaEquiv (s : α → Set β) (hs : ∀ b, ∃! i, b ∈ s i) :
    (Σ i, s i) ≃ β where
  toFun | ⟨_, b⟩ => b
  invFun b := ⟨(hs b).choose, b, (hs b).choose_spec.1⟩
  left_inv | ⟨i, b, hb⟩ => Sigma.subtype_ext ((hs b).choose_spec.2 i hb).symm rfl

/-- Equivalence between a disjoint union and a dependent sum. -/
/-
**Set.unionEqSigmaOfDisjoint** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：unionEqSigmaOfDisjoint {t : α -> Set β} (h : Pairwise (Disjoint on t)) : (
⋃ i, t i) ≃ Σ i, t i
参数：h : Pairwise (Disjoint on t)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.sigmaToiUnion_bijective`：sigmaToiUnion_bijective (h : Pairwise (Disj
oint on t)) : Bijective (sigmaToiUnion t)

--- 原说明 ---
Equivalence between a disjoint union and a dependent sum.
-/
noncomputable def unionEqSigmaOfDisjoint {t : α → Set β}
    (h : Pairwise (Disjoint on t)) :
    (⋃ i, t i) ≃ Σ i, t i :=
  (Equiv.ofBijective _ <| sigmaToiUnion_bijective t h).symm

@[simp]
/-
**Set.coe_unionEqSigmaOfDisjoint_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：coe_unionEqSigmaOfDisjoint_symm_apply {α β : Type*} {t : α -> Set β} (h : 
Pairwise (Disjoint on t)) (x : (i : α) × t i) : ((Set.unionEqSigmaOfDisjoint h).
symm x : β) = x.2
参数：h : Pairwise (Disjoint on t)；x : (i : α) × t i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma coe_unionEqSigmaOfDisjoint_symm_apply {α β : Type*} {t : α → Set β}
    (h : Pairwise (Disjoint on t)) (x : (i : α) × t i) :
    ((Set.unionEqSigmaOfDisjoint h).symm x : β) = x.2 := by
  rfl

@[simp]
/-
**Set.coe_snd_unionEqSigmaOfDisjoint** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：coe_snd_unionEqSigmaOfDisjoint {α β : Type*} {t : α -> Set β} (h : Pairwis
e (Disjoint on t)) (x : ⋃ (i : α), t i) : ((Set.unionEqSigmaOfDisjoint h x).snd 
: β) = x
参数：h : Pairwise (Disjoint on t)；x : ⋃ (i : α), t i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma coe_snd_unionEqSigmaOfDisjoint {α β : Type*} {t : α → Set β}
    (h : Pairwise (Disjoint on t)) (x : ⋃ (i : α), t i) :
    ((Set.unionEqSigmaOfDisjoint h x).snd : β) = x := by
  conv => right; rw [← unionEqSigmaOfDisjoint h |>.symm_apply_apply x]
  rfl
/-
**Set.iUnion_ge_eq_iUnion_nat_add** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_ge_eq_iUnion_nat_add (u : Nat -> Set α) (n : Nat) : ⋃ i >= n, u i =
 ⋃ i, u (i + n)
参数：u : Nat -> Set α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_ge_eq_iSup_nat_add`：iSup_ge_eq_iSup_nat_add (u : Nat -> α) (n : Nat
) : ⨆ i >= n, u i = ⨆ i, u (i + n)
-/
theorem iUnion_ge_eq_iUnion_nat_add (u : ℕ → Set α) (n : ℕ) : ⋃ i ≥ n, u i = ⋃ i, u (i + n) :=
  iSup_ge_eq_iSup_nat_add u n
/-
**Set.iInter_ge_eq_iInter_nat_add** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_ge_eq_iInter_nat_add (u : Nat -> Set α) (n : Nat) : ⋂ i >= n, u i =
 ⋂ i, u (i + n)
参数：u : Nat -> Set α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_ge_eq_iInf_nat_add`：∀ {α : Type u_1} [inst : CompleteLattice α] (u 
: ℕ → α) (n : ℕ), ⨅ i, ⨅ (_ : i ≥ n), u i = ⨅ i, u (i + n)
-/
theorem iInter_ge_eq_iInter_nat_add (u : ℕ → Set α) (n : ℕ) : ⋂ i ≥ n, u i = ⋂ i, u (i + n) :=
  iInf_ge_eq_iInf_nat_add u n
/-
**Set._root_.Monotone.iUnion_nat_add** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Monotone.iUnion_nat_add {f : ℕ → Set α} (hf : Monotone f) (k : ℕ) :
    ⋃ n, f (n + k) = ⋃ n, f n :=
  hf.iSup_nat_add k
/-
**Set._root_.Antitone.iInter_nat_add** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Antitone.iInter_nat_add {f : ℕ → Set α} (hf : Antitone f) (k : ℕ) :
    ⋂ n, f (n + k) = ⋂ n, f n :=
  hf.iInf_nat_add k

@[simp]
/-
**Set.iUnion_iInter_ge_nat_add** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_iInter_ge_nat_add (f : Nat -> Set α) (k : Nat) : ⋃ n, ⋂ i >= n, f (
i + k) = ⋃ n, ⋂ i >= n, f i
参数：f : Nat -> Set α；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_iInf_ge_nat_add`：iSup_iInf_ge_nat_add (f : Nat -> α) (k : Nat) : ⨆ 
n, ⨅ i >= n, f (i + k) = ⨆ n, ⨅ i >= n, f i
-/
theorem iUnion_iInter_ge_nat_add (f : ℕ → Set α) (k : ℕ) :
    ⋃ n, ⋂ i ≥ n, f (i + k) = ⋃ n, ⋂ i ≥ n, f i :=
  iSup_iInf_ge_nat_add f k
/-
**Set.union_iUnion_nat_succ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_iUnion_nat_succ (u : Nat -> Set α) : (u 0 union ⋃ i, u (i + 1)) = ⋃ 
i, u i
参数：u : Nat -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_iSup_nat_succ`：sup_iSup_nat_succ (u : Nat -> α) : (u 0 ⊔ ⨆ i, u (i +
 1)) = ⨆ i, u i
-/
theorem union_iUnion_nat_succ (u : ℕ → Set α) : (u 0 ∪ ⋃ i, u (i + 1)) = ⋃ i, u i :=
  sup_iSup_nat_succ u
/-
**Set.inter_iInter_nat_succ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_iInter_nat_succ (u : Nat -> Set α) : (u 0 inter ⋂ i, u (i + 1)) = ⋂ 
i, u i
参数：u : Nat -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_iInf_nat_succ`：∀ {α : Type u_1} [inst : CompleteLattice α] (u : ℕ → 
α), u 0 ⊓ ⨅ i, u (i + 1) = ⨅ i, u i
-/
theorem inter_iInter_nat_succ (u : ℕ → Set α) : (u 0 ∩ ⋂ i, u (i + 1)) = ⋂ i, u i :=
  inf_iInf_nat_succ u
/-
**Set.iUnion_le_nat** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_le_nat : ⋃ n : Nat, {i | i <= n} = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Set.mem_iUnion_of_mem`：mem_iUnion_of_mem {s : ι -> Set α} {a : α} (i : ι
) (ha : a in s i) : a in ⋃ i, s i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem iUnion_le_nat : ⋃ n : ℕ, {i | i ≤ n} = Set.univ :=
  subset_antisymm (Set.subset_univ _)
    (fun i _ ↦ Set.mem_iUnion_of_mem i (Set.mem_ofPred.mpr (le_refl _)))

end Set

open Set

variable [CompleteLattice β]

/-
**iSup_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_iUnion (s : ι -> Set α) (f : α -> β) : ⨆ a in ⋃ i, s i, f a = ⨆ (i) (
a in s i), f a
参数：s : ι -> Set α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_comm`：iSup_comm {f : ι -> ι' -> α} : ⨆ (i) (j), f i j = ⨆ (j) (i), 
f i j
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_exists`：iSup_exists {p : ι -> Prop} {f : Exists p -> α} : ⨆ x, f x 
= ⨆ (i) (h), f ⟨i, h⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_iUnion (s : ι → Set α) (f : α → β) : ⨆ a ∈ ⋃ i, s i, f a = ⨆ (i) (a ∈ s i), f a := by
  rw [iSup_comm]
  simp_rw [mem_iUnion, iSup_exists]
/-
**iInf_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iInf_iUnion (s : ι -> Set α) (f : α -> β) : ⨅ a in ⋃ i, s i, f a = ⨅ (i) (
a in s i), f a
参数：s : ι -> Set α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_iUnion`：iSup_iUnion (s : ι -> Set α) (f : α -> β) : ⨆ a in ⋃ i, s i
, f a = ⨆ (i) (a in s i), f a
-/
theorem iInf_iUnion (s : ι → Set α) (f : α → β) : ⨅ a ∈ ⋃ i, s i, f a = ⨅ (i) (a ∈ s i), f a :=
  iSup_iUnion (β := βᵒᵈ) s f
/-
**sSup_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_iUnion (t : ι -> Set β) : sSup (⋃ i, t i) = ⨆ i, sSup (t i)
参数：t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_iUnion`：iSup_iUnion (s : ι -> Set α) (f : α -> β) : ⨆ a in ⋃ i, s i
, f a = ⨆ (i) (a in s i), f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sSup_iUnion (t : ι → Set β) : sSup (⋃ i, t i) = ⨆ i, sSup (t i) := by
  simp_rw [sSup_eq_iSup, iSup_iUnion]
/-
**sSup_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_sUnion (s : Set (Set β)) : sSup (⋃₀ s) = ⨆ t in s, sSup t
参数：s : Set (Set β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `iSup_iUnion`：iSup_iUnion (s : ι -> Set α) (f : α -> β) : ⨆ a in ⋃ i, s i
, f a = ⨆ (i) (a in s i), f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sSup_sUnion (s : Set (Set β)) : sSup (⋃₀ s) = ⨆ t ∈ s, sSup t := by
  simp only [sUnion_eq_biUnion, sSup_eq_iSup, iSup_iUnion]
/-
**sInf_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sInf_sUnion (s : Set (Set β)) : sInf (⋃₀ s) = ⨅ t in s, sInf t
参数：s : Set (Set β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_sUnion`：sSup_sUnion (s : Set (Set β)) : sSup (⋃₀ s) = ⨆ t in s, sSu
p t
-/
theorem sInf_sUnion (s : Set (Set β)) : sInf (⋃₀ s) = ⨅ t ∈ s, sInf t :=
  sSup_sUnion (β := βᵒᵈ) s
/-
**iSup_sUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSup_sUnion (S : Set (Set α)) (f : α -> β) : (⨆ x in ⋃₀ S, f x) = ⨆ (s in 
S) (x in s), f x
参数：S : Set (Set α)；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
· 使用定理 `iSup_iUnion`：iSup_iUnion (s : ι -> Set α) (f : α -> β) : ⨆ a in ⋃ i, s i
, f a = ⨆ (i) (a in s i), f a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_subtype''`：iSup_subtype'' {ι} (s : Set ι) (f : ι -> α) : ⨆ i : s, f
 i = ⨆ (t : ι) (_ : t in s), f t
-/
lemma iSup_sUnion (S : Set (Set α)) (f : α → β) :
    (⨆ x ∈ ⋃₀ S, f x) = ⨆ (s ∈ S) (x ∈ s), f x := by
  rw [sUnion_eq_iUnion, iSup_iUnion, ← iSup_subtype'']
/-
**iInf_sUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iInf_sUnion (S : Set (Set α)) (f : α -> β) : (⨅ x in ⋃₀ S, f x) = ⨅ (s in 
S) (x in s), f x
参数：S : Set (Set α)；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
· 使用定理 `iInf_iUnion`：iInf_iUnion (s : ι -> Set α) (f : α -> β) : ⨅ a in ⋃ i, s i
, f a = ⨅ (i) (a in s i), f a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iInf_subtype''`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type u_
8} (s : Set ι) (f : ι → α), ⨅ i, f ↑i = ⨅ t ∈ s, f t
-/
lemma iInf_sUnion (S : Set (Set α)) (f : α → β) :
    (⨅ x ∈ ⋃₀ S, f x) = ⨅ (s ∈ S) (x ∈ s), f x := by
  rw [sUnion_eq_iUnion, iInf_iUnion, ← iInf_subtype'']
/-
**forall_sUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：forall_sUnion {S : Set (Set α)} {p : α -> Prop} : (forall x in ⋃₀ S, p x) 
↔ forall s in S, forall x in s, p x
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `iInf_sUnion`：iInf_sUnion (S : Set (Set α)) (f : α -> β) : (⨅ x in ⋃₀ S, 
f x) = ⨅ (s in S) (x in s), f x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma forall_sUnion {S : Set (Set α)} {p : α → Prop} :
    (∀ x ∈ ⋃₀ S, p x) ↔ ∀ s ∈ S, ∀ x ∈ s, p x := by
  simp_rw [← iInf_Prop_eq, iInf_sUnion]
/-
**exists_sUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_sUnion {S : Set (Set α)} {p : α -> Prop} : (exists x in ⋃₀ S, p x) 
↔ exists s in S, exists x in s, p x
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `iSup_sUnion`：iSup_sUnion (S : Set (Set α)) (f : α -> β) : (⨆ x in ⋃₀ S, 
f x) = ⨆ (s in S) (x in s), f x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma exists_sUnion {S : Set (Set α)} {p : α → Prop} :
    (∃ x ∈ ⋃₀ S, p x) ↔ ∃ s ∈ S, ∃ x ∈ s, p x := by
  simp_rw [← exists_prop, ← iSup_Prop_eq, iSup_sUnion]
