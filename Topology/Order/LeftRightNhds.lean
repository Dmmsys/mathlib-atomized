/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.AtTopBot.CompleteLattice
public import Mathlib.Order.Filter.AtTopBot.Group
public import Mathlib.Topology.Order.Basic

/-!
# Neighborhoods to the left and to the right on an `OrderTopology`

We've seen some properties of left and right neighborhood of a point in an `OrderClosedTopology`.
In an `OrderTopology`, such neighborhoods can be characterized as the sets containing suitable
intervals to the right or to the left of `a`. We give now these characterizations. -/

public section

open Set Filter TopologicalSpace Topology Function

open OrderDual (toDual ofDual)

variable {α β γ : Type*}

section LinearOrder

variable [TopologicalSpace α] [LinearOrder α]

section OrderTopology

variable [OrderTopology α]

open List in
/-- The following statements are equivalent:

0. `s` is a neighborhood of `a` within `(a, +∞)`;
1. `s` is a neighborhood of `a` within `(a, b]`;
2. `s` is a neighborhood of `a` within `(a, b)`;
3. `s` includes `(a, u)` for some `u ∈ (a, b]`;
4. `s` includes `(a, u)` for some `u > a`.
-/
/-
**TFAE_mem_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TFAE_mem_nhdsGT {a b : α} (hab : a < b) (s : Set α) : TFAE [s in 𝓝[>] a, s
 in 𝓝[Ioc a b] a, s in 𝓝[Ioo a b] a, exists u in Ioc a b, Ioo a u subseteq s, ex
ists u in Ioi a, Ioo a u subseteq s]
参数：hab : a < b；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_Ioc_eq_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [in
st_1 : LinearOrder α] [ClosedIciTopology α] {a b : α},   b < a → nhdsWithin b (S
et.Ioc b a) = …
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `nhdsWithin_Ioo_eq_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [in
st_1 : LinearOrder α] [ClosedIciTopology α] {a b : α},   b < a → nhdsWithin b (S
et.Ioo b a) = …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioo_mem_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ioo b a ∈ nhdsWithin 
b (S…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin_iff_exists_mem_nhds_inter`：mem_nhdsWithin_iff_exists_mem_
nhds_inter {t : Set α} {a : α} {s : Set α} : t in 𝓝[s] a ↔ exists u in 𝓝 a, u in
ter s subseteq t
· 使用定理 `exists_Ico_subset_of_mem_nhds'`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : LinearOrder α] [OrderTopology α] {a : α} {s : Set α},   s ∈ nhds a 
→ ∀ {l : α}, a < l →…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
The following statements are equivalent:

0. `s` is a neighborhood of `a` within `(a, +∞)`;
1. `s` is a neighborhood of `a` within `(a, b]`;
2. `s` is a neighborhood of `a` within `(a, b)`;
3. `s` includes `(a, u)` for some `u ∈ (a, b]`;
4. `s` includes `(a, u)` for some `u > a`.
-/
theorem TFAE_mem_nhdsGT {a b : α} (hab : a < b) (s : Set α) :
    TFAE [s ∈ 𝓝[>] a,
      s ∈ 𝓝[Ioc a b] a,
      s ∈ 𝓝[Ioo a b] a,
      ∃ u ∈ Ioc a b, Ioo a u ⊆ s,
      ∃ u ∈ Ioi a, Ioo a u ⊆ s] := by
  tfae_have 1 ↔ 2 := by
    rw [nhdsWithin_Ioc_eq_nhdsGT hab]
  tfae_have 1 ↔ 3 := by
    rw [nhdsWithin_Ioo_eq_nhdsGT hab]
  tfae_have 4 → 5 := fun ⟨u, umem, hu⟩ => ⟨u, umem.1, hu⟩
  tfae_have 5 → 1
  | ⟨u, hau, hu⟩ => mem_of_superset (Ioo_mem_nhdsGT hau) hu
  tfae_have 1 → 4
  | h => by
    rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 h with ⟨v, va, hv⟩
    rcases exists_Ico_subset_of_mem_nhds' va hab with ⟨u, au, hu⟩
    exact ⟨u, au, fun x hx => hv ⟨hu ⟨le_of_lt hx.1, hx.2⟩, hx.1⟩⟩
  tfae_finish
/-
**mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset {a u' : α} {s : Set α} (hu' : a <
 u') : s in 𝓝[>] a ↔ exists u in Ioc a u', Ioo a u subseteq s
参数：hu' : a < u'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `TFAE_mem_nhdsGT`：TFAE_mem_nhdsGT {a b : α} (hab : a < b) (s : Set α) : T
FAE [s in 𝓝[>] a, s in 𝓝[Ioc a b] a, s in 𝓝[Ioo a b] a, exists u in Ioc a b, Ioo
 a u …
-/
theorem mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset {a u' : α} {s : Set α} (hu' : a < u') :
    s ∈ 𝓝[>] a ↔ ∃ u ∈ Ioc a u', Ioo a u ⊆ s :=
  (TFAE_mem_nhdsGT hu' s).out 0 3

/-- A set is a neighborhood of `a` within `(a, +∞)` if and only if it contains an interval `(a, u)`
with `a < u < u'`, provided `a` is not a top element. -/
/-
**mem_nhdsGT_iff_exists_Ioo_subset'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsGT_iff_exists_Ioo_subset' {a u' : α} {s : Set α} (hu' : a < u') : 
s in 𝓝[>] a ↔ exists u in Ioi a, Ioo a u subseteq s
参数：hu' : a < u'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `TFAE_mem_nhdsGT`：TFAE_mem_nhdsGT {a b : α} (hab : a < b) (s : Set α) : T
FAE [s in 𝓝[>] a, s in 𝓝[Ioc a b] a, s in 𝓝[Ioo a b] a, exists u in Ioc a b, Ioo
 a u …

--- 原说明 ---
A set is a neighborhood of `a` within `(a, +∞)` if and only if it contains an in
terval `(a, u)`
with `a < u < u'`, provided `a` is not a top element.
-/
theorem mem_nhdsGT_iff_exists_Ioo_subset' {a u' : α} {s : Set α} (hu' : a < u') :
    s ∈ 𝓝[>] a ↔ ∃ u ∈ Ioi a, Ioo a u ⊆ s :=
  (TFAE_mem_nhdsGT hu' s).out 0 4
/-
**nhdsGT_basis_of_exists_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsGT_basis_of_exists_gt {a : α} (h : exists b, a < b) : (𝓝[>] a).HasBasi
s (a < ·) (Ioo a)
参数：h : exists b, a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_nhdsGT_iff_exists_Ioo_subset'`：mem_nhdsGT_iff_exists_Ioo_subset' {a 
u' : α} {s : Set α} (hu' : a < u') : s in 𝓝[>] a ↔ exists u in Ioi a, Ioo a u su
bseteq s
-/
theorem nhdsGT_basis_of_exists_gt {a : α} (h : ∃ b, a < b) : (𝓝[>] a).HasBasis (a < ·) (Ioo a) :=
  let ⟨_, h⟩ := h
  ⟨fun _ => mem_nhdsGT_iff_exists_Ioo_subset' h⟩
/-
**nhdsGT_basis** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsGT_basis [NoMaxOrder α] (a : α) : (𝓝[>] a).HasBasis (a < ·) (Ioo a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsGT_basis_of_exists_gt`：nhdsGT_basis_of_exists_gt {a : α} (h : exists
 b, a < b) : (𝓝[>] a).HasBasis (a < ·) (Ioo a)
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
-/
lemma nhdsGT_basis [NoMaxOrder α] (a : α) : (𝓝[>] a).HasBasis (a < ·) (Ioo a) :=
  nhdsGT_basis_of_exists_gt <| exists_gt a
/-
**nhdsGT_basis_Ioc_of_exists_gt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsGT_basis_Ioc_of_exists_gt [DenselyOrdered α] {a : α} (h : exists b, a 
< b) : (𝓝[>] a).HasBasis (fun x => a < x) (Ioc a)
参数：h : exists b, a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' 
→ Set α},   l.HasB…
· 使用定理 `nhdsGT_basis_of_exists_gt`：nhdsGT_basis_of_exists_gt {a : α} (h : exists
 b, a < b) : (𝓝[>] a).HasBasis (a < ·) (Ioo a)
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `Set.Ioc_subset_Ioo_right`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b 
: α}, a₂ < a₁ → Set.Ioc b a₂ ⊆ Set.Ioo b a₁
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
-/
lemma nhdsGT_basis_Ioc_of_exists_gt [DenselyOrdered α] {a : α} (h : ∃ b, a < b) :
    (𝓝[>] a).HasBasis (fun x ↦ a < x) (Ioc a) :=
  nhdsGT_basis_of_exists_gt h |>.to_hasBasis'
    (fun _ hac ↦
      have ⟨b, hab, hbc⟩ := exists_between hac
      ⟨b, hab, Ioc_subset_Ioo_right hbc⟩)
    fun _ hac ↦ mem_of_superset ((nhdsGT_basis_of_exists_gt h).mem_of_mem hac) Ioo_subset_Ioc_self
/-
**nhdsGT_basis_Ioc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsGT_basis_Ioc [DenselyOrdered α] [NoMaxOrder α] (a : α) : (𝓝[>] a).HasB
asis (fun x => a < x) (Ioc a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `nhdsGT_basis_Ioc_of_exists_gt`：nhdsGT_basis_Ioc_of_exists_gt [DenselyOrd
ered α] {a : α} (h : exists b, a < b) : (𝓝[>] a).HasBasis (fun x => a < x) (Ioc 
a)
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
-/
lemma nhdsGT_basis_Ioc [DenselyOrdered α] [NoMaxOrder α] (a : α) :
    (𝓝[>] a).HasBasis (fun x ↦ a < x) (Ioc a) :=
  nhdsGT_basis_Ioc_of_exists_gt <| exists_gt a
/-
**nhdsGT_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsGT_eq_bot_iff {a : α} : 𝓝[>] a = ⊥ ↔ IsTop a ∨ exists b, a ⋖ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsMax.Ioi_eq`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsMax a → Se
t.Ioi a = ∅
· 使用定理 `IsTop.isMax`：∀ {α : Type u_1} [inst : LE α] {a : α}, IsTop a → IsMax a
· 使用定理 `nhdsWithin_empty`：nhdsWithin_empty (a : α) : 𝓝[∅] a = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Filter.HasBasis.eq_bot_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (l = ⊥ ↔ ∃ i, p i ∧ s i = 
∅)
· 使用定理 `nhdsGT_basis_of_exists_gt`：nhdsGT_basis_of_exists_gt {a : α} (h : exists
 b, a < b) : (𝓝[>] a).HasBasis (a < ·) (Ioo a)
· 使用定理 `not_isMax_iff`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, ¬IsMax a ↔ 
∃ b, a < b
· 使用定理 `isTop_iff_isMax`：isTop_iff_isMax [IsDirectedOrder α] : IsTop a ↔ IsMax a
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem nhdsGT_eq_bot_iff {a : α} : 𝓝[>] a = ⊥ ↔ IsTop a ∨ ∃ b, a ⋖ b := by
  by_cases ha : IsTop a
  · simp [ha, ha.isMax.Ioi_eq]
  · simp only [ha, false_or]
    rw [isTop_iff_isMax, not_isMax_iff] at ha
    simp only [(nhdsGT_basis_of_exists_gt ha).eq_bot_iff, covBy_iff_Ioo_eq]

/-- A set is a neighborhood of `a` within `(a, +∞)` if and only if it contains an interval `(a, u)`
with `a < u`. -/
/-
**mem_nhdsGT_iff_exists_Ioo_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsGT_iff_exists_Ioo_subset [NoMaxOrder α] {a : α} {s : Set α} : s in
 𝓝[>] a ↔ exists u in Ioi a, Ioo a u subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `mem_nhdsGT_iff_exists_Ioo_subset'`：mem_nhdsGT_iff_exists_Ioo_subset' {a 
u' : α} {s : Set α} (hu' : a < u') : s in 𝓝[>] a ↔ exists u in Ioi a, Ioo a u su
bseteq s

--- 原说明 ---
A set is a neighborhood of `a` within `(a, +∞)` if and only if it contains an in
terval `(a, u)`
with `a < u`.
-/
theorem mem_nhdsGT_iff_exists_Ioo_subset [NoMaxOrder α] {a : α} {s : Set α} :
    s ∈ 𝓝[>] a ↔ ∃ u ∈ Ioi a, Ioo a u ⊆ s :=
  let ⟨_u', hu'⟩ := exists_gt a
  mem_nhdsGT_iff_exists_Ioo_subset' hu'

/-- The set of points which are isolated on the right is countable when the space is
second-countable. -/
/-
**countable_setOfPred_isolated_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：countable_setOfPred_isolated_right [SecondCountableTopology α] : { x : α |
 𝓝[>] x = ⊥ }.Countable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Countable.union`：∀ {α : Type u} {s t : Set α}, s.Countable → t.Count
able → (s ∪ t).Countable
· 使用定理 `Set.Subsingleton.countable`：∀ {α : Type u} {s : Set α}, s.Subsingleton →
 s.Countable
· 使用定理 `Set.subsingleton_isTop`：subsingleton_isTop (α : Type*) [PartialOrder α] 
: { x : α | IsTop x }.Subsingleton
· 使用定理 `countable_setOfPred_covBy_right`：countable_setOfPred_covBy_right [Second
CountableTopology α] : Set.Countable { x : α | exists y, x ⋖ y }

--- 原说明 ---
The set of points which are isolated on the right is countable when the space is
second-countable.
-/
theorem countable_setOfPred_isolated_right [SecondCountableTopology α] :
    { x : α | 𝓝[>] x = ⊥ }.Countable := by
  simp only [nhdsGT_eq_bot_iff, ofPred_or]
  exact (subsingleton_isTop α).countable.union countable_setOfPred_covBy_right

@[deprecated (since := "2026-07-09")]
alias countable_setOf_isolated_right := countable_setOfPred_isolated_right

/-- The set of points which are isolated on the left is countable when the space is
second-countable. -/
/-
**countable_setOfPred_isolated_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：countable_setOfPred_isolated_left [SecondCountableTopology α] : { x : α | 
𝓝[<] x = ⊥ }.Countable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `countable_setOfPred_isolated_right`：countable_setOfPred_isolated_right [
SecondCountableTopology α] : { x : α | 𝓝[>] x = ⊥ }.Countable
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instSecondCountableTopologyOrderDual`：∀ {α : Type u} [inst : Topological
Space α] [h : SecondCountableTopology α], SecondCountableTopology αᵒᵈ

--- 原说明 ---
The set of points which are isolated on the left is countable when the space is
second-countable.
-/
theorem countable_setOfPred_isolated_left [SecondCountableTopology α] :
    { x : α | 𝓝[<] x = ⊥ }.Countable :=
  countable_setOfPred_isolated_right (α := αᵒᵈ)

@[deprecated (since := "2026-07-09")]
alias countable_setOf_isolated_left := countable_setOfPred_isolated_left

/-- The set of points in a set which are isolated on the right in this set is countable when the
space is second-countable. -/
/-
**countable_setOfPred_isolated_right_within** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：countable_setOfPred_isolated_right_within [SecondCountableTopology α] {s :
 Set α} : { x in s | 𝓝[s inter Ioi x] x = ⊥ }.Countable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_Ico_subset_of_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α
] [inst_1 : LinearOrder α] [OrderTopology α] {a : α} {s : Set α},   s ∈ nhds a →
 (∃ l, a < l) → ∃ l…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.PairwiseDisjoint.countable_of_Ioo`：Set.PairwiseDisjoint.countable_of
_Ioo [SecondCountableTopology α] {y : α -> α} {s : Set α} (h : PairwiseDisjoint 
s fun x => Ioo x (y x)) (h'…
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `Set.disjoint_iff_forall_ne`：disjoint_iff_forall_ne : Disjoint s t ↔ fora
ll ⦃a⦄, a in s -> forall ⦃b⦄, b in t -> a != b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The set of points in a set which are isolated on the right in this set is counta
ble when the
space is second-countable.
-/
theorem countable_setOfPred_isolated_right_within [SecondCountableTopology α] {s : Set α} :
    { x ∈ s | 𝓝[s ∩ Ioi x] x = ⊥ }.Countable := by
  /- This does not follow from `countable_setOfPred_isolated_right`, which gives the result when `s`
  is the whole space, as one cannot use it inside the subspace since it doesn't have the order
  topology. Instead, we follow the main steps of its proof. -/
  let t := { x ∈ s | 𝓝[s ∩ Ioi x] x = ⊥ ∧ ¬ IsTop x}
  suffices H : t.Countable by
    have : { x ∈ s | 𝓝[s ∩ Ioi x] x = ⊥ } ⊆ t ∪ {x | IsTop x} := by
      intro x hx
      by_cases h'x : IsTop x
      · simp [h'x]
      · simpa [-sep_and, t, h'x]
    apply Countable.mono this
    simp [H, (subsingleton_isTop α).countable]
  have (x) (hx : x ∈ t) : ∃ y > x, s ∩ Ioo x y = ∅ := by
    simp only [← empty_mem_iff_bot, mem_nhdsWithin_iff_exists_mem_nhds_inter,
      subset_empty_iff, IsTop, not_forall, not_le, mem_ofPred_eq, t] at hx
    rcases hx.2.1 with ⟨u, hu, h'u⟩
    obtain ⟨y, hxy, hy⟩ : ∃ y, x < y ∧ Ico x y ⊆ u := exists_Ico_subset_of_mem_nhds hu hx.2.2
    refine ⟨y, hxy, ?_⟩
    contrapose! h'u
    apply h'u.mono
    intro z hz
    exact ⟨hy ⟨hz.2.1.le, hz.2.2⟩, hz.1, hz.2.1⟩
  choose! y hy h'y using this
  apply Set.PairwiseDisjoint.countable_of_Ioo (y := y) _ hy
  simp only [PairwiseDisjoint, Set.Pairwise, Function.onFun]
  intro a ha b hb hab
  wlog! H : a < b generalizing a b with h
  · have : b < a := lt_of_le_of_ne H hab.symm
    exact (h hb ha hab.symm this).symm
  have : y a ≤ b := by
    by_contra!
    have : b ∈ s ∩ Ioo a (y a) := by simp [hb.1, H, this]
    simp [h'y a ha] at this
  rw [disjoint_iff_forall_ne]
  exact fun u hu v hv ↦ ((hu.2.trans_le this).trans hv.1).ne

@[deprecated (since := "2026-07-09")]
alias countable_setOf_isolated_right_within := countable_setOfPred_isolated_right_within

/-- The set of points in a set which are isolated on the left in this set is countable when the
space is second-countable. -/
/-
**countable_setOfPred_isolated_left_within** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：countable_setOfPred_isolated_left_within [SecondCountableTopology α] {s : 
Set α} : { x in s | 𝓝[s inter Iio x] x = ⊥ }.Countable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `countable_setOfPred_isolated_right_within`：countable_setOfPred_isolated_
right_within [SecondCountableTopology α] {s : Set α} : { x in s | 𝓝[s inter Ioi 
x] x = ⊥ }.Countable
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instSecondCountableTopologyOrderDual`：∀ {α : Type u} [inst : Topological
Space α] [h : SecondCountableTopology α], SecondCountableTopology αᵒᵈ

--- 原说明 ---
The set of points in a set which are isolated on the left in this set is countab
le when the
space is second-countable.
-/
theorem countable_setOfPred_isolated_left_within [SecondCountableTopology α] {s : Set α} :
    { x ∈ s | 𝓝[s ∩ Iio x] x = ⊥ }.Countable :=
  countable_setOfPred_isolated_right_within (α := αᵒᵈ)

@[deprecated (since := "2026-07-09")]
alias countable_setOf_isolated_left_within := countable_setOfPred_isolated_left_within

/-- A set is a neighborhood of `a` within `(a, +∞)` if and only if it contains an interval `(a, u]`
with `a < u`. -/
/-
**mem_nhdsGT_iff_exists_Ioc_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsGT_iff_exists_Ioc_subset [NoMaxOrder α] [DenselyOrdered α] {a : α}
 {s : Set α} : s in 𝓝[>] a ↔ exists u in Ioi a, Ioc a u subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nhdsGT_iff_exists_Ioo_subset`：mem_nhdsGT_iff_exists_Ioo_subset [NoMa
xOrder α] {a : α} {s : Set α} : s in 𝓝[>] a ↔ exists u in Ioi a, Ioo a u subsete
q s
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a

--- 原说明 ---
A set is a neighborhood of `a` within `(a, +∞)` if and only if it contains an in
terval `(a, u]`
with `a < u`.
-/
theorem mem_nhdsGT_iff_exists_Ioc_subset [NoMaxOrder α] [DenselyOrdered α] {a : α} {s : Set α} :
    s ∈ 𝓝[>] a ↔ ∃ u ∈ Ioi a, Ioc a u ⊆ s := by
  rw [mem_nhdsGT_iff_exists_Ioo_subset]
  constructor
  · rintro ⟨u, au, as⟩
    rcases exists_between au with ⟨v, hv⟩
    exact ⟨v, hv.1, fun x hx => as ⟨hx.1, lt_of_le_of_lt hx.2 hv.2⟩⟩
  · rintro ⟨u, au, as⟩
    exact ⟨u, au, Subset.trans Ioo_subset_Ioc_self as⟩

open List in
/-- The following statements are equivalent:

0. `s` is a neighborhood of `b` within `(-∞, b)`
1. `s` is a neighborhood of `b` within `[a, b)`
2. `s` is a neighborhood of `b` within `(a, b)`
3. `s` includes `(l, b)` for some `l ∈ [a, b)`
4. `s` includes `(l, b)` for some `l < b` -/
/-
**TFAE_mem_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TFAE_mem_nhdsLT {a b : α} (h : a < b) (s : Set α) : TFAE [s in 𝓝[<] b, -- 
0 : `s` is a neighborhood of `b` within `(-∞, b)` s in 𝓝[Ico a b] b, -- 1 : `s` 
is a neighborhood of `b` within `[a, b)` s in 𝓝[Ioo a b] b, -- 2 : `s` is a neig
hborhood of `b` within `(a, b)` exists l in Ico a b, Ioo l b subseteq s, -- 3 : 
`s` includes `(l, b)` for some `l ∈ [a, b)` exists l in Iio b, Ioo l b subseteq 
s]
参数：h : a < b；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Ioc_toDual`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},   Set.Io
c (OrderDual.toDual b) (OrderDual.toDual a) = ⇑OrderDual.ofDual ⁻¹' Set.Ico a b
· 使用定理 `Set.Ioo_toDual`：Ioo_toDual : Ioo (toDual a) (toDual b) = ofDual ⁻¹' Ioo 
b a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
· 使用定理 `TFAE_mem_nhdsGT`：TFAE_mem_nhdsGT {a b : α} (hab : a < b) (s : Set α) : T
FAE [s in 𝓝[>] a, s in 𝓝[Ioc a b] a, s in 𝓝[Ioo a b] a, exists u in Ioc a b, Ioo
 a u …
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `LT.lt.dual`：∀ {α : Type u_1} [inst : LT α] {a b : α}, b < a → OrderDual.
toDual a < OrderDual.toDual b

--- 原说明 ---
The following statements are equivalent:

0. `s` is a neighborhood of `b` within `(-∞, b)`
1. `s` is a neighborhood of `b` within `[a, b)`
2. `s` is a neighborhood of `b` within `(a, b)`
3. `s` includes `(l, b)` for some `l ∈ [a, b)`
4. `s` includes `(l, b)` for some `l < b`
-/
theorem TFAE_mem_nhdsLT {a b : α} (h : a < b) (s : Set α) :
    TFAE [s ∈ 𝓝[<] b, -- 0 : `s` is a neighborhood of `b` within `(-∞, b)`
        s ∈ 𝓝[Ico a b] b, -- 1 : `s` is a neighborhood of `b` within `[a, b)`
        s ∈ 𝓝[Ioo a b] b, -- 2 : `s` is a neighborhood of `b` within `(a, b)`
        ∃ l ∈ Ico a b, Ioo l b ⊆ s, -- 3 : `s` includes `(l, b)` for some `l ∈ [a, b)`
        ∃ l ∈ Iio b, Ioo l b ⊆ s] := by -- 4 : `s` includes `(l, b)` for some `l < b`
  simpa using! TFAE_mem_nhdsGT h.dual (ofDual ⁻¹' s)
/-
**mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset {a l' : α} {s : Set α} (hl' : l' 
< a) : s in 𝓝[<] a ↔ exists l in Ico l' a, Ioo l a subseteq s
参数：hl' : l' < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `TFAE_mem_nhdsLT`：TFAE_mem_nhdsLT {a b : α} (h : a < b) (s : Set α) : TFA
E [s in 𝓝[<] b, -- 0 : `s` is a neighborhood of `b` within `(-∞, b)` s in 𝓝[Ico 
a b] …
-/
theorem mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset {a l' : α} {s : Set α} (hl' : l' < a) :
    s ∈ 𝓝[<] a ↔ ∃ l ∈ Ico l' a, Ioo l a ⊆ s :=
  (TFAE_mem_nhdsLT hl' s).out 0 3

/-- A set is a neighborhood of `a` within `(-∞, a)` if and only if it contains an interval `(l, a)`
with `l < a`, provided `a` is not a bottom element. -/
/-
**mem_nhdsLT_iff_exists_Ioo_subset'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsLT_iff_exists_Ioo_subset' {a l' : α} {s : Set α} (hl' : l' < a) : 
s in 𝓝[<] a ↔ exists l in Iio a, Ioo l a subseteq s
参数：hl' : l' < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `TFAE_mem_nhdsLT`：TFAE_mem_nhdsLT {a b : α} (h : a < b) (s : Set α) : TFA
E [s in 𝓝[<] b, -- 0 : `s` is a neighborhood of `b` within `(-∞, b)` s in 𝓝[Ico 
a b] …

--- 原说明 ---
A set is a neighborhood of `a` within `(-∞, a)` if and only if it contains an in
terval `(l, a)`
with `l < a`, provided `a` is not a bottom element.
-/
theorem mem_nhdsLT_iff_exists_Ioo_subset' {a l' : α} {s : Set α} (hl' : l' < a) :
    s ∈ 𝓝[<] a ↔ ∃ l ∈ Iio a, Ioo l a ⊆ s :=
  (TFAE_mem_nhdsLT hl' s).out 0 4

/-- A set is a neighborhood of `a` within `(-∞, a)` if and only if it contains an interval `(l, a)`
with `l < a`. -/
/-
**mem_nhdsLT_iff_exists_Ioo_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsLT_iff_exists_Ioo_subset [NoMinOrder α] {a : α} {s : Set α} : s in
 𝓝[<] a ↔ exists l in Iio a, Ioo l a subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `mem_nhdsLT_iff_exists_Ioo_subset'`：mem_nhdsLT_iff_exists_Ioo_subset' {a 
l' : α} {s : Set α} (hl' : l' < a) : s in 𝓝[<] a ↔ exists l in Iio a, Ioo l a su
bseteq s

--- 原说明 ---
A set is a neighborhood of `a` within `(-∞, a)` if and only if it contains an in
terval `(l, a)`
with `l < a`.
-/
theorem mem_nhdsLT_iff_exists_Ioo_subset [NoMinOrder α] {a : α} {s : Set α} :
    s ∈ 𝓝[<] a ↔ ∃ l ∈ Iio a, Ioo l a ⊆ s :=
  let ⟨_, h⟩ := exists_lt a
  mem_nhdsLT_iff_exists_Ioo_subset' h

/-- A set is a neighborhood of `a` within `(-∞, a)` if and only if it contains an interval `[l, a)`
with `l < a`. -/
/-
**mem_nhdsLT_iff_exists_Ico_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsLT_iff_exists_Ico_subset [NoMinOrder α] [DenselyOrdered α] {a : α}
 {s : Set α} : s in 𝓝[<] a ↔ exists l in Iio a, Ico l a subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_nhdsGT_iff_exists_Ioc_subset`：mem_nhdsGT_iff_exists_Ioc_subset [NoMa
xOrder α] [DenselyOrdered α] {a : α} {s : Set α} : s in 𝓝[>] a ↔ exists u in Ioi
 a, Ioc a u subseteq s
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `OrderDual.noMaxOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α], NoM
axOrder αᵒᵈ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Ioc_toDual`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},   Set.Io
c (OrderDual.toDual b) (OrderDual.toDual a) = ⇑OrderDual.ofDual ⁻¹' Set.Ico a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ

--- 原说明 ---
A set is a neighborhood of `a` within `(-∞, a)` if and only if it contains an in
terval `[l, a)`
with `l < a`.
-/
theorem mem_nhdsLT_iff_exists_Ico_subset [NoMinOrder α] [DenselyOrdered α] {a : α} {s : Set α} :
    s ∈ 𝓝[<] a ↔ ∃ l ∈ Iio a, Ico l a ⊆ s := by
  have : ofDual ⁻¹' s ∈ 𝓝[>] toDual a ↔ _ := mem_nhdsGT_iff_exists_Ioc_subset
  simpa using! this
/-
**nhdsLT_basis_of_exists_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsLT_basis_of_exists_lt {a : α} (h : exists b, b < a) : (𝓝[<] a).HasBasi
s (· < a) (Ioo · a)
参数：h : exists b, b < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_nhdsLT_iff_exists_Ioo_subset'`：mem_nhdsLT_iff_exists_Ioo_subset' {a 
l' : α} {s : Set α} (hl' : l' < a) : s in 𝓝[<] a ↔ exists l in Iio a, Ioo l a su
bseteq s
-/
theorem nhdsLT_basis_of_exists_lt {a : α} (h : ∃ b, b < a) : (𝓝[<] a).HasBasis (· < a) (Ioo · a) :=
  let ⟨_, h⟩ := h
  ⟨fun _ => mem_nhdsLT_iff_exists_Ioo_subset' h⟩
/-
**nhdsLT_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsLT_basis [NoMinOrder α] (a : α) : (𝓝[<] a).HasBasis (· < a) (Ioo · a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsLT_basis_of_exists_lt`：nhdsLT_basis_of_exists_lt {a : α} (h : exists
 b, b < a) : (𝓝[<] a).HasBasis (· < a) (Ioo · a)
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
-/
theorem nhdsLT_basis [NoMinOrder α] (a : α) : (𝓝[<] a).HasBasis (· < a) (Ioo · a) :=
  nhdsLT_basis_of_exists_lt <| exists_lt a
/-
**nhdsLT_basis_Ico_of_exists_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsLT_basis_Ico_of_exists_lt [DenselyOrdered α] {a : α} (h : exists b, b 
< a) : (𝓝[<] a).HasBasis (· < a) (Ico · a)
参数：h : exists b, b < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' 
→ Set α},   l.HasB…
· 使用定理 `nhdsLT_basis_of_exists_lt`：nhdsLT_basis_of_exists_lt {a : α} (h : exists
 b, b < a) : (𝓝[<] a).HasBasis (· < a) (Ioo · a)
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `Set.Ico_subset_Ioo_left`：Ico_subset_Ioo_left (h : a₁ < a₂) : Ico a₂ b su
bseteq Ioo a₁ b
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
-/
lemma nhdsLT_basis_Ico_of_exists_lt [DenselyOrdered α] {a : α} (h : ∃ b, b < a) :
    (𝓝[<] a).HasBasis (· < a) (Ico · a) :=
  nhdsLT_basis_of_exists_lt h |>.to_hasBasis'
    (fun _ hac ↦
      have ⟨b, hab, hbc⟩ := exists_between hac
      ⟨b, hbc, Ico_subset_Ioo_left hab⟩)
      fun _ hac ↦ mem_of_superset ((nhdsLT_basis_of_exists_lt h).mem_of_mem hac) Ioo_subset_Ico_self
/-
**nhdsLT_basis_Ico** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsLT_basis_Ico [DenselyOrdered α] [NoMinOrder α] (a : α) : (𝓝[<] a).HasB
asis (· < a) (Ico · a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `nhdsLT_basis_Ico_of_exists_lt`：nhdsLT_basis_Ico_of_exists_lt [DenselyOrd
ered α] {a : α} (h : exists b, b < a) : (𝓝[<] a).HasBasis (· < a) (Ico · a)
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
-/
lemma nhdsLT_basis_Ico [DenselyOrdered α] [NoMinOrder α] (a : α) :
    (𝓝[<] a).HasBasis (· < a) (Ico · a) :=
  nhdsLT_basis_Ico_of_exists_lt <| exists_lt a
/-
**nhdsLT_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsLT_eq_bot_iff {a : α} : 𝓝[<] a = ⊥ ↔ IsBot a ∨ exists b, b ⋖ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ofDual_covBy_ofDual_iff`：ofDual_covBy_ofDual_iff {a b : αᵒᵈ} : ofDual a 
⋖ ofDual b ↔ b ⋖ a
· 使用定理 `nhdsGT_eq_bot_iff`：nhdsGT_eq_bot_iff {a : α} : 𝓝[>] a = ⊥ ↔ IsTop a ∨ ex
ists b, a ⋖ b
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem nhdsLT_eq_bot_iff {a : α} : 𝓝[<] a = ⊥ ↔ IsBot a ∨ ∃ b, b ⋖ a := by
  convert! (config := { preTransparency := .default })
    nhdsGT_eq_bot_iff (a := OrderDual.toDual a) using 4
  exact ofDual_covBy_ofDual_iff

open List in
/-- The following statements are equivalent:

0. `s` is a neighborhood of `a` within `[a, +∞)`;
1. `s` is a neighborhood of `a` within `[a, b]`;
2. `s` is a neighborhood of `a` within `[a, b)`;
3. `s` includes `[a, u)` for some `u ∈ (a, b]`;
4. `s` includes `[a, u)` for some `u > a`.
-/
/-
**TFAE_mem_nhdsGE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TFAE_mem_nhdsGE {a b : α} (hab : a < b) (s : Set α) : TFAE [s in 𝓝[>=] a, 
s in 𝓝[Icc a b] a, s in 𝓝[Ico a b] a, exists u in Ioc a b, Ico a u subseteq s, e
xists u in Ioi a, Ico a u subseteq s]
参数：hab : a < b；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_Icc_eq_nhdsGE`：∀ {α : Type u} [inst : TopologicalSpace α] [in
st_1 : LinearOrder α] [ClosedIciTopology α] {a b : α},   b < a → nhdsWithin b (S
et.Icc b a) = …
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `nhdsWithin_Ico_eq_nhdsGE`：∀ {α : Type u} [inst : TopologicalSpace α] [in
st_1 : LinearOrder α] [ClosedIciTopology α] {a b : α},   b < a → nhdsWithin b (S
et.Ico b a) = …
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `nhdsGE_basis_of_exists_gt`：nhdsGE_basis_of_exists_gt [TopologicalSpace α
] [LinearOrder α] [OrderTopology α] {a : α} (ha : exists u, a < u) : (𝓝[>=] a).H
asBasis (fun u …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ico_subset_Ico_right`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b 
: α}, a₂ ≤ a₁ → Set.Ico b a₂ ⊆ Set.Ico b a₁
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
The following statements are equivalent:

0. `s` is a neighborhood of `a` within `[a, +∞)`;
1. `s` is a neighborhood of `a` within `[a, b]`;
2. `s` is a neighborhood of `a` within `[a, b)`;
3. `s` includes `[a, u)` for some `u ∈ (a, b]`;
4. `s` includes `[a, u)` for some `u > a`.
-/
theorem TFAE_mem_nhdsGE {a b : α} (hab : a < b) (s : Set α) :
    TFAE [s ∈ 𝓝[≥] a,
      s ∈ 𝓝[Icc a b] a,
      s ∈ 𝓝[Ico a b] a,
      ∃ u ∈ Ioc a b, Ico a u ⊆ s,
      ∃ u ∈ Ioi a, Ico a u ⊆ s] := by
  tfae_have 1 ↔ 2 := by
    rw [nhdsWithin_Icc_eq_nhdsGE hab]
  tfae_have 1 ↔ 3 := by
    rw [nhdsWithin_Ico_eq_nhdsGE hab]
  tfae_have 1 ↔ 5 := (nhdsGE_basis_of_exists_gt ⟨b, hab⟩).mem_iff
  tfae_have 4 → 5 := fun ⟨u, umem, hu⟩ => ⟨u, umem.1, hu⟩
  tfae_have 5 → 4
  | ⟨u, hua, hus⟩ => ⟨min u b, ⟨lt_min hua hab, min_le_right _ _⟩,
      (Ico_subset_Ico_right <| min_le_left _ _).trans hus⟩
  tfae_finish
/-
**mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset {a u' : α} {s : Set α} (hu' : a <
 u') : s in 𝓝[>=] a ↔ exists u in Ioc a u', Ico a u subseteq s
参数：hu' : a < u'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `TFAE_mem_nhdsGE`：TFAE_mem_nhdsGE {a b : α} (hab : a < b) (s : Set α) : T
FAE [s in 𝓝[>=] a, s in 𝓝[Icc a b] a, s in 𝓝[Ico a b] a, exists u in Ioc a b, Ic
o a u…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
-/
theorem mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset {a u' : α} {s : Set α} (hu' : a < u') :
    s ∈ 𝓝[≥] a ↔ ∃ u ∈ Ioc a u', Ico a u ⊆ s :=
  (TFAE_mem_nhdsGE hu' s).out 0 3 (by simp) (by simp)

/-- A set is a neighborhood of `a` within `[a, +∞)` if and only if it contains an interval `[a, u)`
with `a < u < u'`, provided `a` is not a top element. -/
/-
**mem_nhdsGE_iff_exists_Ico_subset'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsGE_iff_exists_Ico_subset' {a u' : α} {s : Set α} (hu' : a < u') : 
s in 𝓝[>=] a ↔ exists u in Ioi a, Ico a u subseteq s
参数：hu' : a < u'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `TFAE_mem_nhdsGE`：TFAE_mem_nhdsGE {a b : α} (hab : a < b) (s : Set α) : T
FAE [s in 𝓝[>=] a, s in 𝓝[Icc a b] a, s in 𝓝[Ico a b] a, exists u in Ioc a b, Ic
o a u…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A set is a neighborhood of `a` within `[a, +∞)` if and only if it contains an in
terval `[a, u)`
with `a < u < u'`, provided `a` is not a top element.
-/
theorem mem_nhdsGE_iff_exists_Ico_subset' {a u' : α} {s : Set α} (hu' : a < u') :
    s ∈ 𝓝[≥] a ↔ ∃ u ∈ Ioi a, Ico a u ⊆ s :=
  (TFAE_mem_nhdsGE hu' s).out 0 4 (by simp) (by simp)

/-- A set is a neighborhood of `a` within `[a, +∞)` if and only if it contains an interval `[a, u)`
with `a < u`. -/
/-
**mem_nhdsGE_iff_exists_Ico_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsGE_iff_exists_Ico_subset [NoMaxOrder α] {a : α} {s : Set α} : s in
 𝓝[>=] a ↔ exists u in Ioi a, Ico a u subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `mem_nhdsGE_iff_exists_Ico_subset'`：mem_nhdsGE_iff_exists_Ico_subset' {a 
u' : α} {s : Set α} (hu' : a < u') : s in 𝓝[>=] a ↔ exists u in Ioi a, Ico a u s
ubseteq s

--- 原说明 ---
A set is a neighborhood of `a` within `[a, +∞)` if and only if it contains an in
terval `[a, u)`
with `a < u`.
-/
theorem mem_nhdsGE_iff_exists_Ico_subset [NoMaxOrder α] {a : α} {s : Set α} :
    s ∈ 𝓝[≥] a ↔ ∃ u ∈ Ioi a, Ico a u ⊆ s :=
  let ⟨_, hu'⟩ := exists_gt a
  mem_nhdsGE_iff_exists_Ico_subset' hu'
/-
**nhdsGE_basis_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsGE_basis_Ico [NoMaxOrder α] (a : α) : (𝓝[>=] a).HasBasis (fun u => a <
 u) (Ico a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_nhdsGE_iff_exists_Ico_subset`：mem_nhdsGE_iff_exists_Ico_subset [NoMa
xOrder α] {a : α} {s : Set α} : s in 𝓝[>=] a ↔ exists u in Ioi a, Ico a u subset
eq s
-/
theorem nhdsGE_basis_Ico [NoMaxOrder α] (a : α) : (𝓝[≥] a).HasBasis (fun u => a < u) (Ico a) :=
  ⟨fun _ => mem_nhdsGE_iff_exists_Ico_subset⟩

/-- The filter of right neighborhoods has a basis of closed intervals. -/
/-
**nhdsGE_basis_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsGE_basis_Icc [NoMaxOrder α] [DenselyOrdered α] {a : α} : (𝓝[>=] a).Has
Basis (a < ·) (Icc a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `nhdsGE_basis`：nhdsGE_basis [TopologicalSpace α] [LinearOrder α] [OrderTo
pology α] [NoMaxOrder α] (a : α) : (𝓝[>=] a).HasBasis (fun u => a < u) fun u => 
Ic…
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `Set.Icc_subset_Ico_right`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b 
: α}, a₂ < a₁ → Set.Icc b a₂ ⊆ Set.Ico b a₁
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a

--- 原说明 ---
The filter of right neighborhoods has a basis of closed intervals.
-/
theorem nhdsGE_basis_Icc [NoMaxOrder α] [DenselyOrdered α] {a : α} :
    (𝓝[≥] a).HasBasis (a < ·) (Icc a) :=
  (nhdsGE_basis _).to_hasBasis
    (fun _u hu ↦ (exists_between hu).imp fun _v hv ↦ hv.imp_right Icc_subset_Ico_right) fun u hu ↦
    ⟨u, hu, Ico_subset_Icc_self⟩

/-- A set is a neighborhood of `a` within `[a, +∞)` if and only if it contains an interval `[a, u]`
with `a < u`. -/
/-
**mem_nhdsGE_iff_exists_Icc_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsGE_iff_exists_Icc_subset [NoMaxOrder α] [DenselyOrdered α] {a : α}
 {s : Set α} : s in 𝓝[>=] a ↔ exists u, a < u ∧ Icc a u subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `nhdsGE_basis_Icc`：nhdsGE_basis_Icc [NoMaxOrder α] [DenselyOrdered α] {a 
: α} : (𝓝[>=] a).HasBasis (a < ·) (Icc a)

--- 原说明 ---
A set is a neighborhood of `a` within `[a, +∞)` if and only if it contains an in
terval `[a, u]`
with `a < u`.
-/
theorem mem_nhdsGE_iff_exists_Icc_subset [NoMaxOrder α] [DenselyOrdered α] {a : α} {s : Set α} :
    s ∈ 𝓝[≥] a ↔ ∃ u, a < u ∧ Icc a u ⊆ s :=
  nhdsGE_basis_Icc.mem_iff

open List in
/-- The following statements are equivalent:

0. `s` is a neighborhood of `b` within `(-∞, b]`
1. `s` is a neighborhood of `b` within `[a, b]`
2. `s` is a neighborhood of `b` within `(a, b]`
3. `s` includes `(l, b]` for some `l ∈ [a, b)`
4. `s` includes `(l, b]` for some `l < b` -/
/-
**TFAE_mem_nhdsLE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TFAE_mem_nhdsLE {a b : α} (h : a < b) (s : Set α) : TFAE [s in 𝓝[<=] b, --
 0 : `s` is a neighborhood of `b` within `(-∞, b]` s in 𝓝[Icc a b] b, -- 1 : `s`
 is a neighborhood of `b` within `[a, b]` s in 𝓝[Ioc a b] b, -- 2 : `s` is a nei
ghborhood of `b` within `(a, b]` exists l in Ico a b, Ioc l b subseteq s, -- 3 :
 `s` includes `(l, b]` for some `l ∈ [a, b)` exists l in Iio b, Ioc l b subseteq
 s]
参数：h : a < b；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Icc_toDual`：Icc_toDual : Icc (toDual a) (toDual b) = ofDual ⁻¹' Icc 
b a
· 使用定理 `Set.Ico_toDual`：Ico_toDual : Ico (toDual a) (toDual b) = ofDual ⁻¹' Ioc 
b a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Ioc_toDual`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},   Set.Io
c (OrderDual.toDual b) (OrderDual.toDual a) = ⇑OrderDual.ofDual ⁻¹' Set.Ico a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
· 使用定理 `TFAE_mem_nhdsGE`：TFAE_mem_nhdsGE {a b : α} (hab : a < b) (s : Set α) : T
FAE [s in 𝓝[>=] a, s in 𝓝[Icc a b] a, s in 𝓝[Ico a b] a, exists u in Ioc a b, Ic
o a u…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `LT.lt.dual`：∀ {α : Type u_1} [inst : LT α] {a b : α}, b < a → OrderDual.
toDual a < OrderDual.toDual b

--- 原说明 ---
The following statements are equivalent:

0. `s` is a neighborhood of `b` within `(-∞, b]`
1. `s` is a neighborhood of `b` within `[a, b]`
2. `s` is a neighborhood of `b` within `(a, b]`
3. `s` includes `(l, b]` for some `l ∈ [a, b)`
4. `s` includes `(l, b]` for some `l < b`
-/
theorem TFAE_mem_nhdsLE {a b : α} (h : a < b) (s : Set α) :
    TFAE [s ∈ 𝓝[≤] b, -- 0 : `s` is a neighborhood of `b` within `(-∞, b]`
      s ∈ 𝓝[Icc a b] b, -- 1 : `s` is a neighborhood of `b` within `[a, b]`
      s ∈ 𝓝[Ioc a b] b, -- 2 : `s` is a neighborhood of `b` within `(a, b]`
      ∃ l ∈ Ico a b, Ioc l b ⊆ s, -- 3 : `s` includes `(l, b]` for some `l ∈ [a, b)`
      ∃ l ∈ Iio b, Ioc l b ⊆ s] := by -- 4 : `s` includes `(l, b]` for some `l < b`
  simpa using! TFAE_mem_nhdsGE h.dual (ofDual ⁻¹' s)
/-
**mem_nhdsLE_iff_exists_mem_Ico_Ioc_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsLE_iff_exists_mem_Ico_Ioc_subset {a l' : α} {s : Set α} (hl' : l' 
< a) : s in 𝓝[<=] a ↔ exists l in Ico l' a, Ioc l a subseteq s
参数：hl' : l' < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `TFAE_mem_nhdsLE`：TFAE_mem_nhdsLE {a b : α} (h : a < b) (s : Set α) : TFA
E [s in 𝓝[<=] b, -- 0 : `s` is a neighborhood of `b` within `(-∞, b]` s in 𝓝[Icc
 a b]…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
-/
theorem mem_nhdsLE_iff_exists_mem_Ico_Ioc_subset {a l' : α} {s : Set α} (hl' : l' < a) :
    s ∈ 𝓝[≤] a ↔ ∃ l ∈ Ico l' a, Ioc l a ⊆ s :=
  (TFAE_mem_nhdsLE hl' s).out 0 3 (by simp) (by simp)

/-- A set is a neighborhood of `a` within `(-∞, a]` if and only if it contains an interval `(l, a]`
with `l < a`, provided `a` is not a bottom element. -/
/-
**mem_nhdsLE_iff_exists_Ioc_subset'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsLE_iff_exists_Ioc_subset' {a l' : α} {s : Set α} (hl' : l' < a) : 
s in 𝓝[<=] a ↔ exists l in Iio a, Ioc l a subseteq s
参数：hl' : l' < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `TFAE_mem_nhdsLE`：TFAE_mem_nhdsLE {a b : α} (h : a < b) (s : Set α) : TFA
E [s in 𝓝[<=] b, -- 0 : `s` is a neighborhood of `b` within `(-∞, b]` s in 𝓝[Icc
 a b]…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A set is a neighborhood of `a` within `(-∞, a]` if and only if it contains an in
terval `(l, a]`
with `l < a`, provided `a` is not a bottom element.
-/
theorem mem_nhdsLE_iff_exists_Ioc_subset' {a l' : α} {s : Set α} (hl' : l' < a) :
    s ∈ 𝓝[≤] a ↔ ∃ l ∈ Iio a, Ioc l a ⊆ s :=
  (TFAE_mem_nhdsLE hl' s).out 0 4 (by simp) (by simp)

/-- A set is a neighborhood of `a` within `(-∞, a]` if and only if it contains an interval `(l, a]`
with `l < a`. -/
/-
**mem_nhdsLE_iff_exists_Ioc_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsLE_iff_exists_Ioc_subset [NoMinOrder α] {a : α} {s : Set α} : s in
 𝓝[<=] a ↔ exists l in Iio a, Ioc l a subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `mem_nhdsLE_iff_exists_Ioc_subset'`：mem_nhdsLE_iff_exists_Ioc_subset' {a 
l' : α} {s : Set α} (hl' : l' < a) : s in 𝓝[<=] a ↔ exists l in Iio a, Ioc l a s
ubseteq s

--- 原说明 ---
A set is a neighborhood of `a` within `(-∞, a]` if and only if it contains an in
terval `(l, a]`
with `l < a`.
-/
theorem mem_nhdsLE_iff_exists_Ioc_subset [NoMinOrder α] {a : α} {s : Set α} :
    s ∈ 𝓝[≤] a ↔ ∃ l ∈ Iio a, Ioc l a ⊆ s :=
  let ⟨_, hl'⟩ := exists_lt a
  mem_nhdsLE_iff_exists_Ioc_subset' hl'

/-- A set is a neighborhood of `a` within `(-∞, a]` if and only if it contains an interval `[l, a]`
with `l < a`. -/
/-
**mem_nhdsLE_iff_exists_Icc_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsLE_iff_exists_Icc_subset [NoMinOrder α] [DenselyOrdered α] {a : α}
 {s : Set α} : s in 𝓝[<=] a ↔ exists l, l < a ∧ Icc l a subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mem_nhdsGE_iff_exists_Icc_subset`：mem_nhdsGE_iff_exists_Icc_subset [NoMa
xOrder α] [DenselyOrdered α] {a : α} {s : Set α} : s in 𝓝[>=] a ↔ exists u, a < 
u ∧ Icc a u subseteq s
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `OrderDual.noMaxOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α], NoM
axOrder αᵒᵈ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.Icc_toDual`：Icc_toDual : Icc (toDual a) (toDual b) = ofDual ⁻¹' Icc 
b a
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A set is a neighborhood of `a` within `(-∞, a]` if and only if it contains an in
terval `[l, a]`
with `l < a`.
-/
theorem mem_nhdsLE_iff_exists_Icc_subset [NoMinOrder α] [DenselyOrdered α] {a : α}
    {s : Set α} : s ∈ 𝓝[≤] a ↔ ∃ l, l < a ∧ Icc l a ⊆ s :=
  calc s ∈ 𝓝[≤] a ↔ ofDual ⁻¹' s ∈ 𝓝[≥] (toDual a) := Iff.rfl
  _ ↔ ∃ u : α, toDual a < toDual u ∧ Icc (toDual a) (toDual u) ⊆ ofDual ⁻¹' s :=
    mem_nhdsGE_iff_exists_Icc_subset
  _ ↔ ∃ l, l < a ∧ Icc l a ⊆ s := by simp

/-- The filter of left neighborhoods has a basis of closed intervals. -/
/-
**nhdsLE_basis_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsLE_basis_Icc [NoMinOrder α] [DenselyOrdered α] {a : α} : (𝓝[<=] a).Has
Basis (· < a) (Icc · a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_nhdsLE_iff_exists_Icc_subset`：mem_nhdsLE_iff_exists_Icc_subset [NoMi
nOrder α] [DenselyOrdered α] {a : α} {s : Set α} : s in 𝓝[<=] a ↔ exists l, l < 
a ∧ Icc l a subseteq s

--- 原说明 ---
The filter of left neighborhoods has a basis of closed intervals.
-/
theorem nhdsLE_basis_Icc [NoMinOrder α] [DenselyOrdered α] {a : α} :
    (𝓝[≤] a).HasBasis (· < a) (Icc · a) :=
  ⟨fun _ ↦ mem_nhdsLE_iff_exists_Icc_subset⟩

end OrderTopology

end LinearOrder

section LinearOrderedCommGroup

variable [TopologicalSpace α] [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]
  [OrderTopology α]
variable {l : Filter β} {f g : β → α}

@[to_additive]
/-
**nhds_eq_iInf_mabs_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_eq_iInf_mabs_div (a : α) : 𝓝 a = ⨅ r > 1, 𝓟 { b | |a / b|ₘ < r }
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_order`：nhds_eq_order [OrderTopology α] (a : α) : 𝓝 a = (⨅ b in I
io a, 𝓟 (Ioi b)) ⊓ ⨅ b in Ioi a, 𝓟 (Iio b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `iInf_inf_eq`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{f g : ι → α}, ⨅ x, f x ⊓ g x = (⨅ x, f x) ⊓ ⨅ x, g x
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Equiv.iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst 
: InfSet α] {f : ι → α} {g : ι' → α} (e : ι ≃ ι'),   (∀ (x : ι), g (e x) = f x) 
→ ⨅ x,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.divLeft_apply`：∀ {G : Type u_5} [inst : Group G] (a b : G), (Equiv
.divLeft a) b = a / b
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.divRight_apply`：∀ {G : Type u_5} [inst : Group G] (a b : G), (Equi
v.divRight a) b = b / a
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
-/
theorem nhds_eq_iInf_mabs_div (a : α) : 𝓝 a = ⨅ r > 1, 𝓟 { b | |a / b|ₘ < r } := by
  simp only [nhds_eq_order, mabs_lt, ofPred_and, ← inf_principal, iInf_inf_eq]
  refine (congr_arg₂ _ ?_ ?_).trans (inf_comm ..)
  · refine (Equiv.divLeft a).iInf_congr fun x => ?_; simp [Ioi]
  · refine (Equiv.divRight a).iInf_congr fun x => ?_; simp [Iio]

@[to_additive]
/-
**orderTopology_of_nhds_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderTopology_of_nhds_mabs {α : Type*} [TopologicalSpace α] [CommGroup α] 
[LinearOrder α] [IsOrderedMonoid α] (h_nhds : forall a : α, 𝓝 a = ⨅ r > 1, 𝓟 { b
 | |a / b|ₘ < r }) : OrderTopology α
参数：h_nhds : forall a : α, 𝓝 a = ⨅ r > 1, 𝓟 { b | |a / b|ₘ < r }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.ext_nhds`：∀ {X : Type u_2} {t t' : TopologicalSpace X},
 (∀ (x : X), nhds x = nhds x) → t = t'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhds_eq_iInf_mabs_div`：nhds_eq_iInf_mabs_div (a : α) : 𝓝 a = ⨅ r > 1, 𝓟 
{ b | |a / b|ₘ < r }
-/
theorem orderTopology_of_nhds_mabs {α : Type*} [TopologicalSpace α] [CommGroup α] [LinearOrder α]
    [IsOrderedMonoid α]
    (h_nhds : ∀ a : α, 𝓝 a = ⨅ r > 1, 𝓟 { b | |a / b|ₘ < r }) : OrderTopology α := by
  refine ⟨TopologicalSpace.ext_nhds fun a => ?_⟩
  rw [h_nhds]
  let := Preorder.topology α; let : OrderTopology α := ⟨rfl⟩
  exact (nhds_eq_iInf_mabs_div a).symm

@[to_additive]
/-
**LinearOrderedCommGroup.tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearOrderedCommGroup.tendsto_nhds {x : Filter β} {a : α} : Tendsto f x (
𝓝 a) ↔ forall ε > (1 : α), forallᶠ b in x, |f b / a|ₘ < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_iInf_mabs_div`：nhds_eq_iInf_mabs_div (a : α) : 𝓝 a = ⨅ r > 1, 𝓟 
{ b | |a / b|ₘ < r }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mabs_div_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a
 b : α), |a / b|ₘ = |b / a|ₘ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem LinearOrderedCommGroup.tendsto_nhds {x : Filter β} {a : α} :
    Tendsto f x (𝓝 a) ↔ ∀ ε > (1 : α), ∀ᶠ b in x, |f b / a|ₘ < ε := by
  simp [nhds_eq_iInf_mabs_div, mabs_div_comm a]

@[to_additive]
/-
**eventually_mabs_div_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_mabs_div_lt (a : α) {ε : α} (hε : 1 < ε) : forallᶠ x in 𝓝 a, |x
 / a|ₘ < ε
参数：a : α；hε : 1 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_iInf_of_mem`：mem_iInf_of_mem {f : ι -> Filter α} (i : ι) {s} 
(hs : s in f i) : s in ⨅ i, f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mabs_div_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a
 b : α), |a / b|ₘ = |b / a|ₘ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhds_eq_iInf_mabs_div`：nhds_eq_iInf_mabs_div (a : α) : 𝓝 a = ⨅ r > 1, 𝓟 
{ b | |a / b|ₘ < r }
-/
theorem eventually_mabs_div_lt (a : α) {ε : α} (hε : 1 < ε) : ∀ᶠ x in 𝓝 a, |x / a|ₘ < ε :=
  (nhds_eq_iInf_mabs_div a).symm ▸
    mem_iInf_of_mem ε (mem_iInf_of_mem hε <| by simp only [mabs_div_comm, mem_principal_self])

/-- In a linearly ordered commutative group with the order topology,
if `f` tends to `C` and `g` tends to `atTop` then `f * g` tends to `atTop`. -/
@[to_additive add_atTop /-- In a linearly ordered additive commutative group with the order
topology, if `f` tends to `C` and `g` tends to `atTop` then `f + g` tends to `atTop`. -/]
/-
**Filter.Tendsto.mul_atTop'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.mul_atTop' {C : α} (hf : Tendsto f l (𝓝 C)) (hg : Tendsto g
 l atTop) : Tendsto (fun x => f x * g x) l atTop
参数：hf : Tendsto f l (𝓝 C)；hg : Tendsto g l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Subsingleton.atTop_eq`：∀ (α : Type u_6) [Subsingleton α] [inst : 
Preorder α], Filter.atTop = ⊤
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `LinearOrderedCommGroup.to_noMinOrder`：∀ {α : Type u} [inst : CommGroup α
] [inst_1 : LinearOrder α] [IsOrderedMonoid α] [Nontrivial α], NoMinOrder α
· 使用定理 `Filter.tendsto_atTop_mul_left_of_le'`：tendsto_atTop_mul_left_of_le' (C :
 G) (hf : forallᶠ x in l, C <= f x) (hg : Tendsto g l atTop) : Tendsto (fun x =>
 f x * g x) l atTop
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `lt_mem_nhds`：lt_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : foral
lᶠ x in 𝓝 b, a < x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem Filter.Tendsto.mul_atTop' {C : α} (hf : Tendsto f l (𝓝 C)) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop := by
  nontriviality α
  obtain ⟨C', hC'⟩ : ∃ C', C' < C := exists_lt C
  refine tendsto_atTop_mul_left_of_le' _ C' ?_ hg
  exact (hf.eventually (lt_mem_nhds hC')).mono fun x => le_of_lt

/-- In a linearly ordered commutative group with the order topology,
if `f` tends to `C` and `g` tends to `atBot` then `f * g` tends to `atBot`. -/
@[to_additive add_atBot /-- In a linearly ordered additive commutative group with the order
topology, if `f` tends to `C` and `g` tends to `atBot` then `f + g` tends to `atBot`. -/]
/-
**Filter.Tendsto.mul_atBot'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.mul_atBot' {C : α} (hf : Tendsto f l (𝓝 C)) (hg : Tendsto g
 l atBot) : Tendsto (fun x => f x * g x) l atBot
参数：hf : Tendsto f l (𝓝 C)；hg : Tendsto g l atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mul_atTop'`：Filter.Tendsto.mul_atTop' {C : α} (hf : Tends
to f l (𝓝 C)) (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atTop
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem Filter.Tendsto.mul_atBot' {C : α} (hf : Tendsto f l (𝓝 C)) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot :=
  Filter.Tendsto.mul_atTop' (α := αᵒᵈ) hf hg

/-- In a linearly ordered commutative group with the order topology,
if `f` tends to `atTop` and `g` tends to `C` then `f * g` tends to `atTop`. -/
@[to_additive atTop_add /-- In a linearly ordered additive commutative group with the order
topology, if `f` tends to `atTop` and `g` tends to `C` then `f + g` tends to `atTop`. -/]
/-
**Filter.Tendsto.atTop_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.atTop_mul' {C : α} (hf : Tendsto f l atTop) (hg : Tendsto g
 l (𝓝 C)) : Tendsto (fun x => f x * g x) l atTop
参数：hf : Tendsto f l atTop；hg : Tendsto g l (𝓝 C)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Filter.Tendsto.mul_atTop'`：Filter.Tendsto.mul_atTop' {C : α} (hf : Tends
to f l (𝓝 C)) (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atTop
-/
theorem Filter.Tendsto.atTop_mul' {C : α} (hf : Tendsto f l atTop) (hg : Tendsto g l (𝓝 C)) :
    Tendsto (fun x => f x * g x) l atTop := by
  conv in _ * _ => rw [mul_comm]
  exact hg.mul_atTop' hf

/-- In a linearly ordered commutative group with the order topology,
if `f` tends to `atBot` and `g` tends to `C` then `f * g` tends to `atBot`. -/
@[to_additive atBot_add /-- In a linearly ordered additive commutative group with the order
topology, if `f` tends to `atBot` and `g` tends to `C` then `f + g` tends to `atBot`. -/]
/-
**Filter.Tendsto.atBot_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.atBot_mul' {C : α} (hf : Tendsto f l atBot) (hg : Tendsto g
 l (𝓝 C)) : Tendsto (fun x => f x * g x) l atBot
参数：hf : Tendsto f l atBot；hg : Tendsto g l (𝓝 C)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Filter.Tendsto.mul_atBot'`：Filter.Tendsto.mul_atBot' {C : α} (hf : Tends
to f l (𝓝 C)) (hg : Tendsto g l atBot) : Tendsto (fun x => f x * g x) l atBot
-/
theorem Filter.Tendsto.atBot_mul' {C : α} (hf : Tendsto f l atBot) (hg : Tendsto g l (𝓝 C)) :
    Tendsto (fun x => f x * g x) l atBot := by
  conv in _ * _ => rw [mul_comm]
  exact hg.mul_atBot' hf

@[to_additive]
/-
**nhds_basis_mabs_div_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_basis_mabs_div_lt [NoMaxOrder α] (a : α) : (𝓝 a).HasBasis (fun ε : α 
=> (1 : α) < ε) fun ε => { b | |b / a|ₘ < ε }
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nhds_eq_iInf_mabs_div`：nhds_eq_iInf_mabs_div (a : α) : 𝓝 a = ⨅ r > 1, 𝓟 
{ b | |a / b|ₘ < r }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `mabs_div_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a
 b : α), |a / b|ₘ = |b / a|ₘ
· 使用定理 `Filter.hasBasis_biInf_principal'`：hasBasis_biInf_principal' {ι : Type*} 
{p : ι -> Prop} {s : ι -> Set α} (h : forall i, p i -> forall j, p j -> exists k
, p k ∧ s k subseteq s…
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
-/
theorem nhds_basis_mabs_div_lt [NoMaxOrder α] (a : α) :
    (𝓝 a).HasBasis (fun ε : α => (1 : α) < ε) fun ε => { b | |b / a|ₘ < ε } := by
  simp only [nhds_eq_iInf_mabs_div, mabs_div_comm (a := a)]
  refine hasBasis_biInf_principal' (fun x hx y hy => ?_) (exists_gt _)
  exact ⟨min x y, lt_min hx hy, fun _ hz => hz.trans_le (min_le_left _ _),
    fun _ hz => hz.trans_le (min_le_right _ _)⟩

@[to_additive]
/-
**nhds_basis_Ioo_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_basis_Ioo_one_lt [NoMaxOrder α] (a : α) : (𝓝 a).HasBasis (fun ε : α =
> (1 : α) < ε) fun ε => Ioo (a / ε) (a * ε)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `nhds_basis_mabs_div_lt`：nhds_basis_mabs_div_lt [NoMaxOrder α] (a : α) : 
(𝓝 a).HasBasis (fun ε : α => (1 : α) < ε) fun ε => { b | |b / a|ₘ < ε }
-/
theorem nhds_basis_Ioo_one_lt [NoMaxOrder α] (a : α) :
    (𝓝 a).HasBasis (fun ε : α => (1 : α) < ε) fun ε => Ioo (a / ε) (a * ε) := by
  convert! nhds_basis_mabs_div_lt a
  simp only [Ioo, mabs_lt, ← div_lt_iff_lt_mul, inv_lt_div_iff_lt_mul, div_lt_comm]

@[to_additive]
/-
**nhds_basis_Icc_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_basis_Icc_one_lt [NoMaxOrder α] [DenselyOrdered α] (a : α) : (𝓝 a).Ha
sBasis ((1 : α) < ·) fun ε => Icc (a / ε) (a * ε)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `nhds_basis_Ioo_one_lt`：nhds_basis_Ioo_one_lt [NoMaxOrder α] (a : α) : (𝓝
 a).HasBasis (fun ε : α => (1 : α) < ε) fun ε => Ioo (a / ε) (a * ε)
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `Set.Icc_subset_Ioo`：Icc_subset_Ioo (ha : a₂ < a₁) (hb : b₁ < b₂) : Icc a
₁ b₁ subseteq Ioo a₂ b₂
· 使用定理 `div_lt_div_left'`：div_lt_div_left' (h : a < b) (c : α) : c / b < c / a
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `mul_lt_mul_right`：mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc :
 b < c) (a : α) : a * b < a * c
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
-/
theorem nhds_basis_Icc_one_lt [NoMaxOrder α] [DenselyOrdered α] (a : α) :
    (𝓝 a).HasBasis ((1 : α) < ·) fun ε ↦ Icc (a / ε) (a * ε) :=
  (nhds_basis_Ioo_one_lt a).to_hasBasis
    (fun _ε ε₁ ↦ let ⟨δ, δ₁, δε⟩ := exists_between ε₁
      ⟨δ, δ₁, Icc_subset_Ioo (by gcongr) (by gcongr)⟩)
    (fun ε ε₁ ↦ ⟨ε, ε₁, Ioo_subset_Icc_self⟩)

variable (α) in
@[to_additive]
/-
**nhds_basis_one_mabs_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_basis_one_mabs_lt [NoMaxOrder α] : (𝓝 (1 : α)).HasBasis (fun ε : α =>
 (1 : α) < ε) fun ε => { b | |b|ₘ < ε }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `nhds_basis_mabs_div_lt`：nhds_basis_mabs_div_lt [NoMaxOrder α] (a : α) : 
(𝓝 a).HasBasis (fun ε : α => (1 : α) < ε) fun ε => { b | |b / a|ₘ < ε }
-/
theorem nhds_basis_one_mabs_lt [NoMaxOrder α] :
    (𝓝 (1 : α)).HasBasis (fun ε : α => (1 : α) < ε) fun ε => { b | |b|ₘ < ε } := by
  simpa using nhds_basis_mabs_div_lt (1 : α)

/-- If `a > 1`, then open intervals `(a / ε, aε)`, `1 < ε ≤ a`,
form a basis of neighborhoods of `a`.

This upper bound for `ε` guarantees that all elements of these intervals are greater than one. -/
@[to_additive /-- If `a` is positive, then the intervals `(a - ε, a + ε)`, `0 < ε ≤ a`,
form a basis of neighborhoods of `a`.

This upper bound for `ε` guarantees that all elements of these intervals are positive. -/]
/-
**nhds_basis_Ioo_one_lt_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_basis_Ioo_one_lt_of_one_lt [NoMaxOrder α] {a : α} (ha : 1 < a) : (𝓝 a
).HasBasis (fun ε : α => (1 : α) < ε ∧ ε <= a) fun ε => Ioo (a / ε) (a * ε)
参数：ha : 1 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.restrict`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : ι → Prop}, (∀ (i : ι)
, p i → ∃ j, p…
· 使用定理 `nhds_basis_Ioo_one_lt`：nhds_basis_Ioo_one_lt [NoMaxOrder α] (a : α) : (𝓝
 a).HasBasis (fun ε : α => (1 : α) < ε) fun ε => Ioo (a / ε) (a * ε)
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `Set.Ioo_subset_Ioo`：Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioo
 a₁ b₁ subseteq Ioo a₂ b₂
· 使用定理 `div_le_div_left'`：div_le_div_left' (h : a <= b) (c : α) : c / b <= c / a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem nhds_basis_Ioo_one_lt_of_one_lt [NoMaxOrder α] {a : α} (ha : 1 < a) :
    (𝓝 a).HasBasis (fun ε : α => (1 : α) < ε ∧ ε ≤ a) fun ε => Ioo (a / ε) (a * ε) :=
  (nhds_basis_Ioo_one_lt a).restrict fun ε hε ↦
    ⟨min a ε, lt_min ha hε, min_le_left _ _, by gcongr <;> apply min_le_right⟩

end LinearOrderedCommGroup

namespace Set.OrdConnected

section ClosedIciTopology

variable [TopologicalSpace α] [LinearOrder α] [ClosedIciTopology α] {S : Set α} {x y : α}

/-- If `S` is order-connected and contains two points `x < y`,
then `S` is a right neighbourhood of `x`. -/
/-
**Set.OrdConnected.mem_nhdsGE** 是 Mathlib 中的一个引理，位于命名空间 `Set.OrdConnected`。
形式化陈述：mem_nhdsGE (hS : OrdConnected S) (hx : x in S) (hy : y in S) (hxy : x < y)
 : S in 𝓝[>=] x
参数：hS : OrdConnected S；hx : x in S；hy : y in S；hxy : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Icc_mem_nhdsGE`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Icc b a ∈ nhdsWithin 
b (S…
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s

--- 原说明 ---
If `S` is order-connected and contains two points `x < y`,
then `S` is a right neighbourhood of `x`.
-/
lemma mem_nhdsGE (hS : OrdConnected S) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) : S ∈ 𝓝[≥] x :=
  mem_of_superset (Icc_mem_nhdsGE hxy) <| hS.out hx hy

/-- If `S` is order-connected and contains two points `x < y`,
then `S` is a punctured right neighbourhood of `x`. -/
/-
**Set.OrdConnected.mem_nhdsGT** 是 Mathlib 中的一个引理，位于命名空间 `Set.OrdConnected`。
形式化陈述：mem_nhdsGT (hS : OrdConnected S) (hx : x in S) (hy : y in S) (hxy : x < y)
 : S in 𝓝[>] x
参数：hS : OrdConnected S；hx : x in S；hy : y in S；hxy : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
· 使用引理 `Set.OrdConnected.mem_nhdsGE`：mem_nhdsGE (hS : OrdConnected S) (hx : x in
 S) (hy : y in S) (hxy : x < y) : S in 𝓝[>=] x

--- 原说明 ---
If `S` is order-connected and contains two points `x < y`,
then `S` is a punctured right neighbourhood of `x`.
-/
lemma mem_nhdsGT (hS : OrdConnected S) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) : S ∈ 𝓝[>] x :=
  nhdsWithin_mono _ Ioi_subset_Ici_self <| hS.mem_nhdsGE hx hy hxy

end ClosedIciTopology

variable [TopologicalSpace α] [LinearOrder α] [ClosedIicTopology α] {S : Set α} {x y : α}

/-- If `S` is order-connected and contains two points `x < y`, then `S` is a left neighbourhood
of `y`. -/
/-
**Set.OrdConnected.mem_nhdsLE** 是 Mathlib 中的一个引理，位于命名空间 `Set.OrdConnected`。
形式化陈述：mem_nhdsLE (hS : OrdConnected S) (hx : x in S) (hy : y in S) (hxy : x < y)
 : S in 𝓝[<=] y
参数：hS : OrdConnected S；hx : x in S；hy : y in S；hxy : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.OrdConnected.mem_nhdsGE`：mem_nhdsGE (hS : OrdConnected S) (hx : x in
 S) (hy : y in S) (hxy : x < y) : S in 𝓝[>=] x
· 使用定理 `instClosedIciTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIicTopology α], ClosedIciTopology αᵒᵈ
· 使用定理 `Set.OrdConnected.dual`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α},
 s.OrdConnected → (⇑OrderDual.ofDual ⁻¹' s).OrdConnected

--- 原说明 ---
If `S` is order-connected and contains two points `x < y`, then `S` is a left ne
ighbourhood
of `y`.
-/
lemma mem_nhdsLE (hS : OrdConnected S) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) : S ∈ 𝓝[≤] y :=
  hS.dual.mem_nhdsGE hy hx hxy

/-- If `S` is order-connected and contains two points `x < y`, then `S` is a punctured left
neighbourhood of `y`. -/
/-
**Set.OrdConnected.mem_nhdsLT** 是 Mathlib 中的一个引理，位于命名空间 `Set.OrdConnected`。
形式化陈述：mem_nhdsLT (hS : OrdConnected S) (hx : x in S) (hy : y in S) (hxy : x < y)
 : S in 𝓝[<] y
参数：hS : OrdConnected S；hx : x in S；hy : y in S；hxy : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.OrdConnected.mem_nhdsGT`：mem_nhdsGT (hS : OrdConnected S) (hx : x in
 S) (hy : y in S) (hxy : x < y) : S in 𝓝[>] x
· 使用定理 `instClosedIciTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIicTopology α], ClosedIciTopology αᵒᵈ
· 使用定理 `Set.OrdConnected.dual`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α},
 s.OrdConnected → (⇑OrderDual.ofDual ⁻¹' s).OrdConnected

--- 原说明 ---
If `S` is order-connected and contains two points `x < y`, then `S` is a punctur
ed left
neighbourhood of `y`.
-/
lemma mem_nhdsLT (hS : OrdConnected S) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) : S ∈ 𝓝[<] y :=
  hS.dual.mem_nhdsGT hy hx hxy

end OrdConnected

end Set

