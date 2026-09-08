/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Data.Finset.Pairwise

/-!
# Sums of collections of Finsupp, and their support

This file provides results about the `Finsupp.support` of sums of collections of `Finsupp`,
including sums of `List`, `Multiset`, and `Finset`.

The support of the sum is a subset of the union of the supports:
* `List.support_sum_subset`
* `Multiset.support_sum_subset`
* `Finset.support_sum_subset`

The support of the sum of pairwise disjoint finsupps is equal to the union of the supports
* `List.support_sum_eq`
* `Multiset.support_sum_eq`
* `Finset.support_sum_eq`

Member in the support of the indexed union over a collection iff
it is a member of the support of a member of the collection:
* `List.mem_foldr_sup_support_iff`
* `Multiset.mem_sup_map_support_iff`
* `Finset.mem_sup_support_iff`

-/

public section


variable {ι M : Type*} [DecidableEq ι]

/-
**List.support_sum_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.support_sum_subset [AddZeroClass M] (l : List (ι ->₀ M)) : l.sum.supp
ort subseteq l.foldr (Finsupp.support · ⊔ ·) ∅
参数：l : List (ι ->₀ M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Finsupp.support_add`：support_add [DecidableEq ι] : (g₁ + g₂).support sub
seteq g₁.support union g₂.support
· 使用定理 `Finset.union_subset_union`：union_subset_union (hsu : s subseteq u) (htv 
: t subseteq v) : s union t subseteq u union v
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
-/
theorem List.support_sum_subset [AddZeroClass M] (l : List (ι →₀ M)) :
    l.sum.support ⊆ l.foldr (Finsupp.support · ⊔ ·) ∅ := by
  induction l with
  | nil => simp
  | cons hd tl IH =>
    simp only [List.sum_cons]
    exact Finsupp.support_add.trans (Finset.union_subset_union Finset.Subset.rfl IH)
/-
**Multiset.support_sum_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.support_sum_subset [AddCommMonoid M] (s : Multiset (ι ->₀ M)) : s
.sum.support subseteq (s.map Finsupp.support).sup
参数：s : Multiset (ι ->₀ M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldr_map`：∀ {α₁ : Type u_1} {α₂ : Type u_2} {β : Type u_3} {f : α₁
 → α₂} {g : α₂ → β → β} {l : List α₁} {init : β},   List.foldr g init (List.map 
f l)…
· 使用定理 `List.support_sum_subset`：List.support_sum_subset [AddZeroClass M] (l : L
ist (ι ->₀ M)) : l.sum.support subseteq l.foldr (Finsupp.support · ⊔ ·) ∅
-/
theorem Multiset.support_sum_subset [AddCommMonoid M] (s : Multiset (ι →₀ M)) :
    s.sum.support ⊆ (s.map Finsupp.support).sup := by
  induction s using Quot.inductionOn
  simpa only [Multiset.quot_mk_to_coe'', Multiset.sum_coe, Multiset.map_coe, Multiset.sup_coe,
    List.foldr_map] using! List.support_sum_subset _
/-
**Finset.support_sum_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.support_sum_subset [AddCommMonoid M] (s : Finset (ι ->₀ M)) : (s.su
m id).support subseteq Finset.sup s Finsupp.support
参数：s : Finset (ι ->₀ M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_val`：∀ {M : Type u_3} [inst : AddCommMonoid M] (s : Finset M)
, s.val.sum = s.sum id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.support_sum_subset`：Multiset.support_sum_subset [AddCommMonoid 
M] (s : Multiset (ι ->₀ M)) : s.sum.support subseteq (s.map Finsupp.support).sup
-/
theorem Finset.support_sum_subset [AddCommMonoid M] (s : Finset (ι →₀ M)) :
    (s.sum id).support ⊆ Finset.sup s Finsupp.support := by
  convert! Multiset.support_sum_subset s.1; simp
/-
**List.mem_foldr_sup_support_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.mem_foldr_sup_support_iff [Zero M] {l : List (ι ->₀ M)} {x : ι} : x i
n l.foldr (Finsupp.support · ⊔ ·) ∅ ↔ exists f in l, x in f.support
参数：ι ->₀ M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem List.mem_foldr_sup_support_iff [Zero M] {l : List (ι →₀ M)} {x : ι} :
    x ∈ l.foldr (Finsupp.support · ⊔ ·) ∅ ↔ ∃ f ∈ l, x ∈ f.support := by
  simp only [Finset.sup_eq_union, Finsupp.mem_support_iff]
  induction l with
  | nil => simp
  | cons hd tl IH =>
    simp only [foldr, Finset.mem_union, Finsupp.mem_support_iff, ne_eq, IH,
      mem_cons, exists_eq_or_imp]
/-
**Multiset.mem_sup_map_support_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.mem_sup_map_support_iff [Zero M] {s : Multiset (ι ->₀ M)} {x : ι}
 : x in (s.map Finsupp.support).sup ↔ exists f in s, x in f.support
参数：ι ->₀ M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldr_map`：∀ {α₁ : Type u_1} {α₂ : Type u_2} {β : Type u_3} {f : α₁
 → α₂} {g : α₂ → β → β} {l : List α₁} {init : β},   List.foldr g init (List.map 
f l)…
· 使用定理 `List.mem_foldr_sup_support_iff`：List.mem_foldr_sup_support_iff [Zero M] 
{l : List (ι ->₀ M)} {x : ι} : x in l.foldr (Finsupp.support · ⊔ ·) ∅ ↔ exists f
 in l, x in f.suppor…
-/
theorem Multiset.mem_sup_map_support_iff [Zero M] {s : Multiset (ι →₀ M)} {x : ι} :
    x ∈ (s.map Finsupp.support).sup ↔ ∃ f ∈ s, x ∈ f.support :=
  Quot.inductionOn s fun _ ↦ by
    simpa only [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.sup_coe, List.foldr_map]
    using! List.mem_foldr_sup_support_iff
/-
**Finset.mem_sup_support_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.mem_sup_support_iff [Zero M] {s : Finset (ι ->₀ M)} {x : ι} : x in 
s.sup Finsupp.support ↔ exists f in s, x in f.support
参数：ι ->₀ M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_sup_map_support_iff`：Multiset.mem_sup_map_support_iff [Zero
 M] {s : Multiset (ι ->₀ M)} {x : ι} : x in (s.map Finsupp.support).sup ↔ exists
 f in s, x in f.suppor…
-/
theorem Finset.mem_sup_support_iff [Zero M] {s : Finset (ι →₀ M)} {x : ι} :
    x ∈ s.sup Finsupp.support ↔ ∃ f ∈ s, x ∈ f.support :=
  Multiset.mem_sup_map_support_iff

open scoped Function -- required for scoped `on` notation
/-
**List.support_sum_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.support_sum_eq [AddZeroClass M] (l : List (ι ->₀ M)) (hl : l.Pairwise
 (_root_.Disjoint on Finsupp.support)) : l.sum.support = l.foldr (Finsupp.suppor
t · ⊔ ·) ∅
参数：l : List (ι ->₀ M)；hl : l.Pairwise (_root_.Disjoint on Finsupp.support)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.support_add_eq`：support_add_eq [DecidableEq ι] (h : Disjoint g₁.
support g₂.support) : (g₁ + g₂).support = g₁.support union g₂.support
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.foldr_map`：∀ {α₁ : Type u_1} {α₂ : Type u_2} {β : Type u_3} {f : α₁
 → α₂} {g : α₂ → β → β} {l : List α₁} {init : β},   List.foldr g init (List.map 
f l)…
· 使用定理 `Finset.bot_eq_empty`：bot_eq_empty : (⊥ : Finset α) = ∅
· 使用定理 `List.foldr_sup_eq_sup_toFinset`：∀ {α : Type u_2} [inst : SemilatticeSup 
α] [inst_1 : OrderBot α] [inst_2 : DecidableEq α] (l : List α),   List.foldr (fu
n x1 x2 => x1 ⊔ x2) …
· 使用定理 `Finset.disjoint_sup_right`：∀ {α : Type u_2} {ι : Type u_5} [inst : Distr
ibLattice α] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   Disjoin
t a (s.sup f) ↔…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.disjoint_of_subset_right`：disjoint_of_subset_right (h : t subsete
q u) (d : Disjoint s u) : Disjoint s t
· 使用定理 `List.support_sum_subset`：List.support_sum_subset [AddZeroClass M] (l : L
ist (ι ->₀ M)) : l.sum.support subseteq l.foldr (Finsupp.support · ⊔ ·) ∅
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.sup_eq_union`：sup_eq_union {s t : Finset α} : s ⊔ t = s union t
-/
theorem List.support_sum_eq [AddZeroClass M] (l : List (ι →₀ M))
    (hl : l.Pairwise (_root_.Disjoint on Finsupp.support)) :
    l.sum.support = l.foldr (Finsupp.support · ⊔ ·) ∅ := by
  induction l with
  | nil => simp
  | cons hd tl IH =>
    simp only [List.pairwise_cons] at hl
    simp only [List.sum_cons, List.foldr_cons]
    rw [Finsupp.support_add_eq, IH hl.right, Finset.sup_eq_union]
    suffices _root_.Disjoint hd.support (tl.foldr (fun x y ↦ (Finsupp.support x ⊔ y)) ∅) by
      exact Finset.disjoint_of_subset_right (List.support_sum_subset _) this
    rw [← List.foldr_map, ← Finset.bot_eq_empty, List.foldr_sup_eq_sup_toFinset,
      Finset.disjoint_sup_right]
    intro f hf
    simp only [List.mem_toFinset, List.mem_map] at hf
    obtain ⟨f, hf, rfl⟩ := hf
    exact hl.left _ hf
/-
**Multiset.support_sum_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.support_sum_eq [AddCommMonoid M] (s : Multiset (ι ->₀ M)) (hs : s
.Pairwise (_root_.Disjoint on Finsupp.support)) : s.sum.support = (s.map Finsupp
.support).sup
参数：s : Multiset (ι ->₀ M)；hs : s.Pairwise (_root_.Disjoint on Finsupp.support)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.Perm.pairwise`：∀ {α : Type u_1} {R : α → α → Prop} {l l' : List α},
   l.Perm l' → List.Pairwise R l → (∀ {x y : α}, R x y → R y x) → List.Pairwise 
R l'
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldr_map`：∀ {α₁ : Type u_1} {α₂ : Type u_2} {β : Type u_3} {f : α₁
 → α₂} {g : α₂ → β → β} {l : List α₁} {init : β},   List.foldr g init (List.map 
f l)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.support_sum_eq`：List.support_sum_eq [AddZeroClass M] (l : List (ι -
>₀ M)) (hl : l.Pairwise (_root_.Disjoint on Finsupp.support)) : l.sum.support = 
l.foldr (…
-/
theorem Multiset.support_sum_eq [AddCommMonoid M] (s : Multiset (ι →₀ M))
    (hs : s.Pairwise (_root_.Disjoint on Finsupp.support)) :
    s.sum.support = (s.map Finsupp.support).sup := by
  induction s using Quot.inductionOn with | _ a
  obtain ⟨l, hl, hd⟩ := hs
  suffices a.Pairwise (_root_.Disjoint on Finsupp.support) by
    convert! List.support_sum_eq a this
    simp only [quot_mk_to_coe'', map_coe, sup_coe,
      Finset.sup_eq_union, Finset.bot_eq_empty, List.foldr_map]
  simp only [Multiset.quot_mk_to_coe'', Multiset.coe_eq_coe] at hl
  exact hl.symm.pairwise hd fun h ↦ _root_.Disjoint.symm h
/-
**Finset.support_sum_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.support_sum_eq [AddCommMonoid M] (s : Finset (ι ->₀ M)) (hs : (s : 
Set (ι ->₀ M)).PairwiseDisjoint Finsupp.support) : (s.sum id).support = Finset.s
up s Finsupp.support
参数：s : Finset (ι ->₀ M)；hs : (s : Set (ι ->₀ M)).PairwiseDisjoint Finsupp.suppor
t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.toList_toFinset`：toList_toFinset [DecidableEq α] (s : Finset α) :
 s.toList.toFinset = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.nodup_toList`：nodup_toList (s : Finset α) : s.toList.Nodup
· 使用定理 `List.toFinset_val`：toFinset_val (l : List α) : l.toFinset.1 = (l.dedup :
 Multiset α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.dedup_eq_self`：dedup_eq_self {l : List α} : dedup l = l ↔ Nodup l
· 使用定理 `Multiset.pairwise_coe_iff_pairwise`：pairwise_coe_iff_pairwise {r : α -> 
α -> Prop} [Std.Symm r] {l : List α} : Multiset.Pairwise r l ↔ l.Pairwise r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint`：pairwiseDisjoi
nt_iff_coe_toFinset_pairwise_disjoint {α ι} [PartialOrder α] [OrderBot α] [Decid
ableEq ι] {l : List ι} {f : ι -> α} (hn : l.No…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_val`：∀ {M : Type u_3} [inst : AddCommMonoid M] (s : Finset M)
, s.val.sum = s.sum id
· 使用定理 `Multiset.support_sum_eq`：Multiset.support_sum_eq [AddCommMonoid M] (s : 
Multiset (ι ->₀ M)) (hs : s.Pairwise (_root_.Disjoint on Finsupp.support)) : s.s
um.support = …
-/
theorem Finset.support_sum_eq [AddCommMonoid M] (s : Finset (ι →₀ M))
    (hs : (s : Set (ι →₀ M)).PairwiseDisjoint Finsupp.support) :
    (s.sum id).support = Finset.sup s Finsupp.support := by
  classical
  suffices s.1.Pairwise (_root_.Disjoint on Finsupp.support) by
    convert! Multiset.support_sum_eq s.1 this
    exact (Finset.sum_val _).symm
  obtain ⟨l, hl, hn⟩ : ∃ l : List (ι →₀ M), l.toFinset = s ∧ l.Nodup := by
    refine ⟨s.toList, ?_, Finset.nodup_toList _⟩
    simp
  subst hl
  rwa [List.toFinset_val, List.dedup_eq_self.mpr hn, Multiset.pairwise_coe_iff_pairwise,
    ← List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint hn]
