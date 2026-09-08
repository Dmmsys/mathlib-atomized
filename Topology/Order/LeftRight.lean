/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Order.Antichain
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Left and right continuity

In this file we prove a few lemmas about left and right continuous functions:

* `continuousWithinAt_Ioi_iff_Ici`: two definitions of right continuity
  (with `(a, ∞)` and with `[a, ∞)`) are equivalent;
* `continuousWithinAt_Iio_iff_Iic`: two definitions of left continuity
  (with `(-∞, a)` and with `(-∞, a]`) are equivalent;
* `continuousAt_iff_continuous_left_right`, `continuousAt_iff_continuous_left'_right'` :
  a function is continuous at `a` if and only if it is left and right continuous at `a`.

## Tags

left continuous, right continuous
-/

public section


open Set Filter Topology

section Preorder

variable {α : Type*} [TopologicalSpace α] [Preorder α]

@[to_dual frequently_gt_nhds]
/-
**frequently_lt_nhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：frequently_lt_nhds (a : α) [NeBot (𝓝[<] a)] : existsᶠ x in 𝓝 a, x < a
参数：a : α；𝓝[<] a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.frequently_iff_neBot`：frequently_iff_neBot {l : Filter α} {p : α 
-> Prop} : (existsᶠ x in l, p x) ↔ NeBot (l ⊓ 𝓟 {x | p x})
-/
lemma frequently_lt_nhds (a : α) [NeBot (𝓝[<] a)] : ∃ᶠ x in 𝓝 a, x < a :=
  frequently_iff_neBot.2 ‹_›

@[to_dual exists_gt]
/-
**Filter.Eventually.exists_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.exists_lt {a : α} [NeBot (𝓝[<] a)] {p : α -> Prop} (h : 
forallᶠ x in 𝓝 a, p x) : exists b < a, p b
参数：𝓝[<] a；h : forallᶠ x in 𝓝 a, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用引理 `frequently_lt_nhds`：frequently_lt_nhds (a : α) [NeBot (𝓝[<] a)] : exists
ᶠ x in 𝓝 a, x < a
-/
theorem Filter.Eventually.exists_lt {a : α} [NeBot (𝓝[<] a)] {p : α → Prop}
    (h : ∀ᶠ x in 𝓝 a, p x) : ∃ b < a, p b :=
  ((frequently_lt_nhds a).and_eventually h).exists

@[to_dual]
/-
**nhdsWithin_Ici_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_Ici_neBot {a b : α} (H₂ : a <= b) : NeBot (𝓝[Ici a] b)
参数：H₂ : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_neBot_of_mem`：nhdsWithin_neBot_of_mem {s : Set α} {x : α} (hx
 : x in s) : NeBot (𝓝[s] x)
-/
theorem nhdsWithin_Ici_neBot {a b : α} (H₂ : a ≤ b) : NeBot (𝓝[Ici a] b) :=
  nhdsWithin_neBot_of_mem H₂

@[to_dual]
/-
**nhdsLE_neBot** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：nhdsLE_neBot (a : α) : NeBot (𝓝[<=] a)
参数：a : α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_Iic_neBot`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst
_1 : Preorder α] {a b : α}, b ≤ a → (nhdsWithin b (Set.Iic a)).NeBot
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
instance nhdsLE_neBot (a : α) : NeBot (𝓝[≤] a) := nhdsWithin_Iic_neBot (le_refl a)

@[to_dual]
/-
**nhdsLT_le_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsLT_le_nhdsNE (a : α) : 𝓝[<] a <= 𝓝[!=] a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
-/
theorem nhdsLT_le_nhdsNE (a : α) : 𝓝[<] a ≤ 𝓝[≠] a :=
  nhdsWithin_mono a fun _ => ne_of_lt

-- TODO: add instances for `NeBot (𝓝[<] x)` on (indexed) product types
/-
**IsAntichain.interior_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAntichain.interior_eq_empty [forall x : α, (𝓝[<] x).NeBot] {s : Set α} (
hs : IsAntichain (· <= ·) s) : interior s = ∅
参数：𝓝[<] x；hs : IsAntichain (· <= ·) s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_of_forall_notMem`：eq_empty_of_forall_notMem (h : forall x, 
x ∉ s) : s = ∅
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Filter.Eventually.exists_lt`：Filter.Eventually.exists_lt {a : α} [NeBot 
(𝓝[<] a)] {p : α -> Prop} (h : forallᶠ x in 𝓝 a, p x) : exists b < a, p b
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma IsAntichain.interior_eq_empty [∀ x : α, (𝓝[<] x).NeBot] {s : Set α}
    (hs : IsAntichain (· ≤ ·) s) : interior s = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx ↦ ?_
  have : ∀ᶠ y in 𝓝 x, y ∈ s := mem_interior_iff_mem_nhds.1 hx
  rcases this.exists_lt with ⟨y, hyx, hys⟩
  exact hs hys (interior_subset hx) hyx.ne hyx.le
/-
**IsAntichain.interior_eq_empty'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAntichain.interior_eq_empty' [forall x : α, (𝓝[>] x).NeBot] {s : Set α} 
(hs : IsAntichain (· <= ·) s) : interior s = ∅
参数：𝓝[>] x；hs : IsAntichain (· <= ·) s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsAntichain.interior_eq_empty`：IsAntichain.interior_eq_empty [forall x :
 α, (𝓝[<] x).NeBot] {s : Set α} (hs : IsAntichain (· <= ·) s) : interior s = ∅
· 使用定理 `IsAntichain.to_dual`：to_dual [LE α] (hs : IsAntichain (· <= ·) s) : @IsA
ntichain αᵒᵈ (· <= ·) s
-/
lemma IsAntichain.interior_eq_empty' [∀ x : α, (𝓝[>] x).NeBot] {s : Set α}
    (hs : IsAntichain (· ≤ ·) s) : interior s = ∅ :=
  have : ∀ x : αᵒᵈ, NeBot (𝓝[<] x) := ‹_›
  hs.to_dual.interior_eq_empty

end Preorder

section PartialOrder

variable {α β : Type*} [TopologicalSpace α] [PartialOrder α] [TopologicalSpace β]

@[to_dual]
/-
**continuousWithinAt_Ioi_iff_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_Ioi_iff_Ici {a : α} {f : α -> β} : ContinuousWithinAt f
 (Ioi a) a ↔ ContinuousWithinAt f (Ici a) a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousWithinAt_Ioi_iff_Ici {a : α} {f : α → β} :
    ContinuousWithinAt f (Ioi a) a ↔ ContinuousWithinAt f (Ici a) a := by
  simp only [← Ici_sdiff_left, continuousWithinAt_sdiff_self]

@[to_dual]
/-
**continuousWithinAt_inter_Ioi_iff_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_inter_Ioi_iff_Ici {a : α} {f : α -> β} {s : Set α} : Co
ntinuousWithinAt f (s inter Ioi a) a ↔ ContinuousWithinAt f (s inter Ici a) a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousWithinAt_inter_Ioi_iff_Ici {a : α} {f : α → β} {s : Set α} :
    ContinuousWithinAt f (s ∩ Ioi a) a ↔ ContinuousWithinAt f (s ∩ Ici a) a := by
  simp [← Ici_sdiff_left, ← inter_sdiff_assoc, continuousWithinAt_sdiff_self]

end PartialOrder

section TopologicalSpace

variable {α β : Type*} [TopologicalSpace α] [LinearOrder α] [TopologicalSpace β] {s : Set α}

@[to_dual nhdsGE_sup_nhdsLE]
/-
**nhdsLE_sup_nhdsGE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsLE_sup_nhdsGE (a : α) : 𝓝[<=] a ⊔ 𝓝[>=] a = 𝓝 a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `Set.Iic_union_Ici`：Iic_union_Ici : Iic a union Ici a = univ
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
-/
theorem nhdsLE_sup_nhdsGE (a : α) : 𝓝[≤] a ⊔ 𝓝[≥] a = 𝓝 a := by
  rw [← nhdsWithin_union, Iic_union_Ici, nhdsWithin_univ]

@[to_dual nhdsWithinGE_sup_nhdsWithinLE]
/-
**nhdsWithinLE_sup_nhdsWithinGE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithinLE_sup_nhdsWithinGE (a : α) : 𝓝[s inter Iic a] a ⊔ 𝓝[s inter Ici
 a] a = 𝓝[s] a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `Set.Iic_union_Ici`：Iic_union_Ici : Iic a union Ici a = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
theorem nhdsWithinLE_sup_nhdsWithinGE (a : α) : 𝓝[s ∩ Iic a] a ⊔ 𝓝[s ∩ Ici a] a = 𝓝[s] a := by
  rw [← nhdsWithin_union, ← inter_union_distrib_left, Iic_union_Ici, inter_univ]

@[to_dual nhdsGT_sup_nhdsLE]
/-
**nhdsLT_sup_nhdsGE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsLT_sup_nhdsGE (a : α) : 𝓝[<] a ⊔ 𝓝[>=] a = 𝓝 a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `Set.Iio_union_Ici`：Iio_union_Ici : Iio a union Ici a = univ
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
-/
theorem nhdsLT_sup_nhdsGE (a : α) : 𝓝[<] a ⊔ 𝓝[≥] a = 𝓝 a := by
  rw [← nhdsWithin_union, Iio_union_Ici, nhdsWithin_univ]

@[to_dual nhdsWithinGT_sup_nhdsWithinLE]
/-
**nhdsWithinLT_sup_nhdsWithinGE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithinLT_sup_nhdsWithinGE (a : α) : 𝓝[s inter Iio a] a ⊔ 𝓝[s inter Ici
 a] a = 𝓝[s] a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `Set.Iio_union_Ici`：Iio_union_Ici : Iio a union Ici a = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
theorem nhdsWithinLT_sup_nhdsWithinGE (a : α) : 𝓝[s ∩ Iio a] a ⊔ 𝓝[s ∩ Ici a] a = 𝓝[s] a := by
  rw [← nhdsWithin_union, ← inter_union_distrib_left, Iio_union_Ici, inter_univ]

@[to_dual nhdsGE_sup_nhdsLT]
/-
**nhdsLE_sup_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsLE_sup_nhdsGT (a : α) : 𝓝[<=] a ⊔ 𝓝[>] a = 𝓝 a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `Set.Iic_union_Ioi`：Iic_union_Ioi : Iic a union Ioi a = univ
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
-/
theorem nhdsLE_sup_nhdsGT (a : α) : 𝓝[≤] a ⊔ 𝓝[>] a = 𝓝 a := by
  rw [← nhdsWithin_union, Iic_union_Ioi, nhdsWithin_univ]

@[to_dual nhdsWithinGE_sup_nhdsWithinLT]
/-
**nhdsWithinLE_sup_nhdsWithinGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithinLE_sup_nhdsWithinGT (a : α) : 𝓝[s inter Iic a] a ⊔ 𝓝[s inter Ioi
 a] a = 𝓝[s] a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `Set.Iic_union_Ioi`：Iic_union_Ioi : Iic a union Ioi a = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
theorem nhdsWithinLE_sup_nhdsWithinGT (a : α) : 𝓝[s ∩ Iic a] a ⊔ 𝓝[s ∩ Ioi a] a = 𝓝[s] a := by
  rw [← nhdsWithin_union, ← inter_union_distrib_left, Iic_union_Ioi, inter_univ]

@[to_dual nhdsGT_sup_nhdsLT]
/-
**nhdsLT_sup_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsLT_sup_nhdsGT (a : α) : 𝓝[<] a ⊔ 𝓝[>] a = 𝓝[!=] a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `Set.Iio_union_Ioi`：Iio_union_Ioi : Iio a union Ioi a = {a}ᶜ
-/
theorem nhdsLT_sup_nhdsGT (a : α) : 𝓝[<] a ⊔ 𝓝[>] a = 𝓝[≠] a := by
  rw [← nhdsWithin_union, Iio_union_Ioi]

@[to_dual nhdsWithinGT_sup_nhdsWithinLT]
/-
**nhdsWithinLT_sup_nhdsWithinGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithinLT_sup_nhdsWithinGT (a : α) : 𝓝[s inter Iio a] a ⊔ 𝓝[s inter Ioi
 a] a = 𝓝[s \ {a}] a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `Set.Iio_union_Ioi`：Iio_union_Ioi : Iio a union Ioi a = {a}ᶜ
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用引理 `Set.inter_sdiff_left_comm`：inter_sdiff_left_comm (s t u : Set α) : s int
er (t \ u) = t inter (s \ u)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
-/
theorem nhdsWithinLT_sup_nhdsWithinGT (a : α) :
    𝓝[s ∩ Iio a] a ⊔ 𝓝[s ∩ Ioi a] a = 𝓝[s \ {a}] a := by
  rw [← nhdsWithin_union, ← inter_union_distrib_left, Iio_union_Ioi, compl_eq_univ_sdiff,
    inter_sdiff_left_comm, univ_inter]

@[to_dual nhdsLT_sup_nhdsWithin_singleton]
/-
**nhdsGT_sup_nhdsWithin_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsGT_sup_nhdsWithin_singleton (a : α) : 𝓝[>] a ⊔ 𝓝[{a}] a = 𝓝[>=] a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.Ioi_insert`：∀ {α : Type u_1} [inst : PartialOrder α] {a : α}, insert
 a (Set.Ioi a) = Set.Ici a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nhdsGT_sup_nhdsWithin_singleton (a : α) :
    𝓝[>] a ⊔ 𝓝[{a}] a = 𝓝[≥] a := by
  simp only [union_singleton, Ioi_insert, ← nhdsWithin_union]
/-
**nhdsWithin_uIoo_left_le_nhdsNE** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsWithin_uIoo_left_le_nhdsNE {a b : α} : 𝓝[uIoo a b] a <= 𝓝[!=] a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma nhdsWithin_uIoo_left_le_nhdsNE {a b : α} : 𝓝[uIoo a b] a ≤ 𝓝[≠] a :=
  nhdsWithin_mono _ (by simp)
/-
**nhdsWithin_uIoo_right_le_nhdsNE** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsWithin_uIoo_right_le_nhdsNE {a b : α} : 𝓝[uIoo a b] b <= 𝓝[!=] b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma nhdsWithin_uIoo_right_le_nhdsNE {a b : α} : 𝓝[uIoo a b] b ≤ 𝓝[≠] b :=
  nhdsWithin_mono _ (by simp)

@[to_dual none]
/-
**continuousAt_iff_continuous_left_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_iff_continuous_left_right {a : α} {f : α -> β} : ContinuousAt
 f a ↔ ContinuousWithinAt f (Iic a) a ∧ ContinuousWithinAt f (Ici a) a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsLE_sup_nhdsGE`：nhdsLE_sup_nhdsGE (a : α) : 𝓝[<=] a ⊔ 𝓝[>=] a = 𝓝 a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousAt_iff_continuous_left_right {a : α} {f : α → β} :
    ContinuousAt f a ↔ ContinuousWithinAt f (Iic a) a ∧ ContinuousWithinAt f (Ici a) a := by
  simp only [ContinuousWithinAt, ContinuousAt, ← tendsto_sup, nhdsLE_sup_nhdsGE]

@[to_dual none]
/-
**continuousAt_iff_continuous_left'_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Line
arOrder α] [inst_2 : TopologicalSpace β]   {a : α} {f : α → β}, ContinuousAt f a
 ↔ ContinuousWithinAt f (Set.Iio a) a ∧ ContinuousWithinAt f (Set.Ioi a) a
参数：Set.Iio a；Set.Ioi a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousWithinAt_Ioi_iff_Ici`：continuousWithinAt_Ioi_iff_Ici {a : α} {
f : α -> β} : ContinuousWithinAt f (Ioi a) a ↔ ContinuousWithinAt f (Ici a) a
· 使用定理 `continuousWithinAt_Iio_iff_Iic`：∀ {α : Type u_1} {β : Type u_2} [inst : 
TopologicalSpace α] [inst_1 : PartialOrder α] [inst_2 : TopologicalSpace β]   {a
 : α} {f : α → β}, C…
· 使用定理 `continuousAt_iff_continuous_left_right`：continuousAt_iff_continuous_left
_right {a : α} {f : α -> β} : ContinuousAt f a ↔ ContinuousWithinAt f (Iic a) a 
∧ ContinuousWithinAt f (Ici …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousAt_iff_continuous_left'_right' {a : α} {f : α → β} :
    ContinuousAt f a ↔ ContinuousWithinAt f (Iio a) a ∧ ContinuousWithinAt f (Ioi a) a := by
  rw [continuousWithinAt_Ioi_iff_Ici, continuousWithinAt_Iio_iff_Iic,
    continuousAt_iff_continuous_left_right]

@[to_dual none]
/-
**continuousWithinAt_iff_continuous_left_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_iff_continuous_left_right {a : α} {f : α -> β} : Contin
uousWithinAt f s a ↔ ContinuousWithinAt f (s inter Iic a) a ∧ ContinuousWithinAt
 f (s inter Ici a) a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithinLE_sup_nhdsWithinGE`：nhdsWithinLE_sup_nhdsWithinGE (a : α) : 𝓝
[s inter Iic a] a ⊔ 𝓝[s inter Ici a] a = 𝓝[s] a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousWithinAt_iff_continuous_left_right {a : α} {f : α → β} :
    ContinuousWithinAt f s a ↔
      ContinuousWithinAt f (s ∩ Iic a) a ∧ ContinuousWithinAt f (s ∩ Ici a) a := by
  simp only [ContinuousWithinAt, ← tendsto_sup, nhdsWithinLE_sup_nhdsWithinGE]

@[to_dual none]
/-
**continuousWithinAt_iff_continuous_left'_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Line
arOrder α] [inst_2 : TopologicalSpace β]   {s : Set α} {a : α} {f : α → β},   Co
ntinuousWithinAt f s a ↔ ContinuousWithinAt f (s ∩ Set.Iio a) a ∧ ContinuousWith
inAt f (s ∩ Set.Ioi a) a
参数：s ∩ Set.Iio a；s ∩ Set.Ioi a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousWithinAt_inter_Ioi_iff_Ici`：continuousWithinAt_inter_Ioi_iff_I
ci {a : α} {f : α -> β} {s : Set α} : ContinuousWithinAt f (s inter Ioi a) a ↔ C
ontinuousWithinAt f (s int…
· 使用定理 `continuousWithinAt_inter_Iio_iff_Iic`：∀ {α : Type u_1} {β : Type u_2} [i
nst : TopologicalSpace α] [inst_1 : PartialOrder α] [inst_2 : TopologicalSpace β
]   {a : α} {f : α → β} {s…
· 使用定理 `continuousWithinAt_iff_continuous_left_right`：continuousWithinAt_iff_con
tinuous_left_right {a : α} {f : α -> β} : ContinuousWithinAt f s a ↔ ContinuousW
ithinAt f (s inter Iic a) a ∧ Cont…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousWithinAt_iff_continuous_left'_right' {a : α} {f : α → β} :
    ContinuousWithinAt f s a ↔
      ContinuousWithinAt f (s ∩ Iio a) a ∧ ContinuousWithinAt f (s ∩ Ioi a) a := by
  rw [continuousWithinAt_inter_Ioi_iff_Ici, continuousWithinAt_inter_Iio_iff_Iic,
    continuousWithinAt_iff_continuous_left_right]

end TopologicalSpace

