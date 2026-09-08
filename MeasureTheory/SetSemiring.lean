/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Order.SupClosed

/-! # Semirings and rings of sets

A semi-ring of sets `C` (in the sense of measure theory) is a family of sets containing `∅`,
stable by intersection and such that for all `s, t ∈ C`, `t \ s` is equal to a disjoint union of
finitely many sets in `C`. Note that a semi-ring of sets may not contain unions.

An important example of a semi-ring of sets is intervals in `ℝ`. The intersection of two intervals
is an interval (possibly empty). The union of two intervals may not be an interval.
The set difference of two intervals may not be an interval, but it will be a disjoint union of
two intervals.

A ring of sets is a set of sets containing `∅`, stable by union, set difference and intersection.

## Main definitions

* `MeasureTheory.IsSetSemiring C`: property of being a semi-ring of sets.
* `MeasureTheory.IsSetSemiring.disjointOfDiff hs ht`: for `s, t` in a semi-ring `C`
  (with `hC : IsSetSemiring C`) with `hs : s ∈ C`, `ht : t ∈ C`, this is a `Finset` of
  pairwise disjoint sets such that `s \ t = ⋃₀ hC.disjointOfDiff hs ht`.
* `MeasureTheory.IsSetSemiring.disjointOfDiffUnion hs hI`: for `hs : s ∈ C` and a finset
  `I` of sets in `C` (with `hI : ↑I ⊆ C`), this is a `Finset` of pairwise disjoint sets such that
  `s \ ⋃₀ I = ⋃₀ hC.disjointOfDiffUnion hs hI`.
* `MeasureTheory.IsSetSemiring.disjointOfUnion hJ`: for `hJ ⊆ C`, this is a
  `Finset` of pairwise disjoint sets such that `⋃₀ J = ⋃₀ hC.disjointOfUnion hJ`.

* `MeasureTheory.IsSetRing`: property of being a ring of sets.

## Main statements

* `MeasureTheory.IsSetSemiring.exists_disjoint_finset_sdiff_eq`: the existence of the `Finset` given
  by the definition `IsSetSemiring.disjointOfDiffUnion` (see above).
* `MeasureTheory.IsSetSemiring.disjointOfUnion_props`: In a `hC : IsSetSemiring C`,
  for a `J : Finset (Set α)` with `J ⊆ C`, there is
  for every `x in J` some `K x ⊆ C` finite, such that
  * `⋃ x ∈ J, K x` are pairwise disjoint and do not contain ∅,
  * `⋃ s ∈ K x, s ⊆ x`,
  * `⋃ x ∈ J, x = ⋃ x ∈ J, ⋃ s ∈ K x, s`.

-/

public section

open Finset Set

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)} {s t : Set α}

/-- A semi-ring of sets `C` is a family of sets containing `∅`, stable by intersection and such that
for all `s, t ∈ C`, `s \ t` is equal to a disjoint union of finitely many sets in `C`. -/
/-
**MeasureTheory.IsSetSemiring** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`。
形式化陈述：{α : Type u_1} → Set (Set α) → Prop
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A semi-ring of sets `C` is a family of sets containing `∅`, stable by intersecti
on and such that
for all `s, t ∈ C`, `s \ t` is equal to a disjoint union of finitely many sets i
n `C`.
-/
structure IsSetSemiring (C : Set (Set α)) : Prop where
  empty_mem : ∅ ∈ C
  inter_mem : ∀ s ∈ C, ∀ t ∈ C, s ∩ t ∈ C
  sdiff_eq_sUnion' : ∀ s ∈ C, ∀ t ∈ C,
    ∃ I : Finset (Set α), ↑I ⊆ C ∧ PairwiseDisjoint (I : Set (Set α)) id ∧ s \ t = ⋃₀ I

/-- A ring of sets `C` is a family of sets containing `∅`, stable by union and set difference.
It is then also stable by intersection (see `IsSetRing.inter_mem`). -/
/-
**MeasureTheory.IsSetRing** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`。
形式化陈述：{α : Type u_1} → Set (Set α) → Prop
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring of sets `C` is a family of sets containing `∅`, stable by union and set d
ifference.
It is then also stable by intersection (see `IsSetRing.inter_mem`).
-/
structure IsSetRing (C : Set (Set α)) : Prop where
  empty_mem : ∅ ∈ C
  union_mem ⦃s t : Set α⦄ : s ∈ C → t ∈ C → s ∪ t ∈ C
  sdiff_mem ⦃s t : Set α⦄ : s ∈ C → t ∈ C → s \ t ∈ C

namespace IsSetRing

/-
**MeasureTheory.IsSetRing.inter_mem** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.IsS
etRing`。
形式化陈述：inter_mem (hC : IsSetRing C) (hs : s in C) (ht : t in C) : s inter t in C
参数：hC : IsSetRing C；hs : s in C；ht : t in C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_sdiff_right_self`：sdiff_sdiff_right_self (s t : Set α) : s \ (
s \ t) = s inter t
· 使用定理 `MeasureTheory.IsSetRing.sdiff_mem`：∀ {α : Type u_1} {C : Set (Set α)}, M
easureTheory.IsSetRing C → ∀ ⦃s t : Set α⦄, s ∈ C → t ∈ C → s \ t ∈ C
-/
lemma inter_mem (hC : IsSetRing C) (hs : s ∈ C) (ht : t ∈ C) : s ∩ t ∈ C := by
  rw [← sdiff_sdiff_right_self]; exact hC.sdiff_mem hs (hC.sdiff_mem hs ht)
/-
**MeasureTheory.IsSetRing.isSetSemiring** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.IsSetRing`。
形式化陈述：isSetSemiring (hC : IsSetRing C) : IsSetSemiring C where empty_mem
参数：hC : IsSetRing C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsSetRing.empty_mem`：∀ {α : Type u_1} {C : Set (Set α)}, M
easureTheory.IsSetRing C → ∅ ∈ C
· 使用引理 `MeasureTheory.IsSetRing.inter_mem`：inter_mem (hC : IsSetRing C) (hs : s 
in C) (ht : t in C) : s inter t in C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `MeasureTheory.IsSetRing.sdiff_mem`：∀ {α : Type u_1} {C : Set (Set α)}, M
easureTheory.IsSetRing C → ∀ ⦃s t : Set α⦄, s ∈ C → t ∈ C → s \ t ∈ C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.sUnion_singleton`：sUnion_singleton (s : Set α) : ⋃₀ {s} = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isSetSemiring (hC : IsSetRing C) : IsSetSemiring C where
  empty_mem := hC.empty_mem
  inter_mem := fun _ hs _ ht => hC.inter_mem hs ht
  sdiff_eq_sUnion' := by
    refine fun s hs t ht => ⟨{s \ t}, ?_, ?_, ?_⟩
    · simp only [coe_singleton, Set.singleton_subset_iff]
      exact hC.sdiff_mem hs ht
    · simp only [coe_singleton, pairwiseDisjoint_singleton]
    · simp only [coe_singleton, sUnion_singleton]
/-
**MeasureTheory.IsSetRing.biUnion_mem** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.I
sSetRing`。
形式化陈述：biUnion_mem {ι : Type*} (hC : IsSetRing C) {s : ι -> Set α} (S : Finset ι)
 (hs : forall n in S, s n in C) : ⋃ i in S, s i in C
参数：hC : IsSetRing C；S : Finset ι；hs : forall n in S, s n in C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.IsSetRing.empty_mem`：∀ {α : Type u_1} {C : Set (Set α)}, M
easureTheory.IsSetRing C → ∅ ∈ C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Set.biUnion_insert`：biUnion_insert (a : α) (s : Set α) (t : α -> Set β) 
: ⋃ x in insert a s, t x = t a union ⋃ x in s, t x
· 使用定理 `MeasureTheory.IsSetRing.union_mem`：∀ {α : Type u_1} {C : Set (Set α)}, M
easureTheory.IsSetRing C → ∀ ⦃s t : Set α⦄, s ∈ C → t ∈ C → s ∪ t ∈ C
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
-/
lemma biUnion_mem {ι : Type*} (hC : IsSetRing C) {s : ι → Set α}
    (S : Finset ι) (hs : ∀ n ∈ S, s n ∈ C) :
    ⋃ i ∈ S, s i ∈ C := by
  classical
  induction S using Finset.induction with
  | empty => simp [hC.empty_mem]
  | insert i S _ h =>
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    refine hC.union_mem (hs i (mem_insert_self i S)) ?_
    exact h (fun n hnS ↦ hs n (mem_insert_of_mem hnS))
/-
**MeasureTheory.IsSetRing.biInter_mem** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.I
sSetRing`。
形式化陈述：biInter_mem {ι : Type*} (hC : IsSetRing C) {s : ι -> Set α} (S : Finset ι)
 (hS : S.Nonempty) (hs : forall n in S, s n in C) : ⋂ i in S, s i in C
参数：hC : IsSetRing C；S : Finset ι；hS : S.Nonempty；hs : forall n in S, s n in C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_iInter_eq_left`：iInter_iInter_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋂ (x) (h : x = b), s x h = s b rfl
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_cons`：coe_cons {a s h} : (@cons α a s h : Set α) = insert a (
s : Set α)
· 使用定理 `Set.biInter_insert`：biInter_insert (a : α) (s : Set α) (t : α -> Set β) 
: ⋂ x in insert a s, t x = t a inter ⋂ x in s, t x
· 使用引理 `MeasureTheory.IsSetRing.inter_mem`：inter_mem (hC : IsSetRing C) (hs : s 
in C) (ht : t in C) : s inter t in C
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma biInter_mem {ι : Type*} (hC : IsSetRing C) {s : ι → Set α}
    (S : Finset ι) (hS : S.Nonempty) (hs : ∀ n ∈ S, s n ∈ C) :
    ⋂ i ∈ S, s i ∈ C := by
  classical
  induction hS using Finset.Nonempty.cons_induction with
  | singleton => simpa using hs
  | cons i S hiS _ h =>
    simp_rw [← Finset.mem_coe, Finset.coe_cons, Set.biInter_insert]
    simp only [cons_eq_insert, Finset.mem_insert, forall_eq_or_imp] at hs
    refine hC.inter_mem hs.1 ?_
    exact h (fun n hnS ↦ hs.2 n hnS)
/-
**MeasureTheory.IsSetRing.finsetSup_mem** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.IsSetRing`。
形式化陈述：finsetSup_mem (hC : IsSetRing C) {ι : Type*} {s : ι -> Set α} {t : Finset 
ι} (hs : forall i in t, s i in C) : t.sup s in C
参数：hC : IsSetRing C；hs : forall i in t, s i in C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_set_eq_biUnion`：sup_set_eq_biUnion (s : Finset α) (f : α -> S
et β) : s.sup f = ⋃ x in s, f x
· 使用引理 `MeasureTheory.IsSetRing.biUnion_mem`：biUnion_mem {ι : Type*} (hC : IsSet
Ring C) {s : ι -> Set α} (S : Finset ι) (hs : forall n in S, s n in C) : ⋃ i in 
S, s i in C
-/
lemma finsetSup_mem (hC : IsSetRing C) {ι : Type*} {s : ι → Set α} {t : Finset ι}
    (hs : ∀ i ∈ t, s i ∈ C) :
    t.sup s ∈ C := by
  simpa using biUnion_mem hC _ hs
/-
**MeasureTheory.IsSetRing.partialSups_mem** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry.IsSetRing`。
形式化陈述：partialSups_mem {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι] (hC : I
sSetRing C) {s : ι -> Set α} (hs : forall n, s n in C) (n : ι) : partialSups s n
 in C
参数：hC : IsSetRing C；hs : forall n, s n in C；n : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用引理 `Finset.nonempty_Iic`：nonempty_Iic : (Iic a).Nonempty
· 使用引理 `MeasureTheory.IsSetRing.finsetSup_mem`：finsetSup_mem (hC : IsSetRing C) 
{ι : Type*} {s : ι -> Set α} {t : Finset ι} (hs : forall i in t, s i in C) : t.s
up s in C
-/
lemma partialSups_mem {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    (hC : IsSetRing C) {s : ι → Set α} (hs : ∀ n, s n ∈ C) (n : ι) :
    partialSups s n ∈ C := by
  simpa only [partialSups_apply, sup'_eq_sup] using hC.finsetSup_mem (fun i hi ↦ hs i)
/-
**MeasureTheory.IsSetRing.disjointed_mem** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y.IsSetRing`。
形式化陈述：disjointed_mem {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι] (hC : Is
SetRing C) {s : ι -> Set α} (hs : forall j, s j in C) (i : ι) : disjointed s i i
n C
参数：hC : IsSetRing C；hs : forall j, s j in C；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `disjointedRec`：disjointedRec {f : ι -> α} {p : α -> Prop} (hdiff : foral
l ⦃t i⦄, p t -> p (t \ f i)) : forall ⦃i⦄, p (f i) -> p (disjointed f i)
· 使用定理 `MeasureTheory.IsSetRing.sdiff_mem`：∀ {α : Type u_1} {C : Set (Set α)}, M
easureTheory.IsSetRing C → ∀ ⦃s t : Set α⦄, s ∈ C → t ∈ C → s \ t ∈ C
-/
lemma disjointed_mem {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    (hC : IsSetRing C) {s : ι → Set α} (hs : ∀ j, s j ∈ C) (i : ι) :
    disjointed s i ∈ C :=
  disjointedRec (fun _ j ht ↦ hC.sdiff_mem ht <| hs j) (hs i)
/-
**MeasureTheory.IsSetRing.iUnion_le_mem** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.IsSetRing`。
形式化陈述：iUnion_le_mem (hC : IsSetRing C) {s : Nat -> Set α} (hs : forall n, s n in
 C) (n : Nat) : (⋃ i <= n, s i) in C
参数：hC : IsSetRing C；hs : forall n, s n in C；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Set.iUnion_iUnion_eq_left`：iUnion_iUnion_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋃ (x) (h : x = b), s x h = s b rfl
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.biUnion_le_succ`：biUnion_le_succ (u : Nat -> Set α) (n : Nat) : ⋃ k 
<= n + 1, u k = (⋃ k <= n, u k) union u (n + 1)
· 使用定理 `MeasureTheory.IsSetRing.union_mem`：∀ {α : Type u_1} {C : Set (Set α)}, M
easureTheory.IsSetRing C → ∀ ⦃s t : Set α⦄, s ∈ C → t ∈ C → s ∪ t ∈ C
-/
theorem iUnion_le_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋃ i ≤ n, s i) ∈ C := by
  induction n with
  | zero => simp [hs 0]
  | succ n hn => rw [biUnion_le_succ]; exact hC.union_mem hn (hs _)
/-
**MeasureTheory.IsSetRing.iInter_le_mem** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.IsSetRing`。
形式化陈述：iInter_le_mem (hC : IsSetRing C) {s : Nat -> Set α} (hs : forall n, s n in
 C) (n : Nat) : (⋂ i <= n, s i) in C
参数：hC : IsSetRing C；hs : forall n, s n in C；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Set.iInter_iInter_eq_left`：iInter_iInter_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋂ (x) (h : x = b), s x h = s b rfl
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.biInter_le_succ`：biInter_le_succ (u : Nat -> Set α) (n : Nat) : ⋂ k 
<= n + 1, u k = (⋂ k <= n, u k) inter u (n + 1)
· 使用引理 `MeasureTheory.IsSetRing.inter_mem`：inter_mem (hC : IsSetRing C) (hs : s 
in C) (ht : t in C) : s inter t in C
-/
theorem iInter_le_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋂ i ≤ n, s i) ∈ C := by
  induction n with
  | zero => simp [hs 0]
  | succ n hn => rw [biInter_le_succ]; exact hC.inter_mem hn (hs _)
/-
**MeasureTheory.IsSetRing.accumulate_mem** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.IsSetRing`。
形式化陈述：accumulate_mem (hC : IsSetRing C) {s : Nat -> Set α} (hs : forall i, s i i
n C) (n : Nat) : accumulate s n in C
参数：hC : IsSetRing C；hs : forall i, s i in C；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.accumulate_zero_nat`：accumulate_zero_nat (s : Nat -> Set β) : accumu
late s 0 = s 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.accumulate_succ`：accumulate_succ (u : Nat -> Set α) (n : Nat) : accu
mulate u (n + 1) = accumulate u n union u (n + 1)
· 使用定理 `MeasureTheory.IsSetRing.union_mem`：∀ {α : Type u_1} {C : Set (Set α)}, M
easureTheory.IsSetRing C → ∀ ⦃s t : Set α⦄, s ∈ C → t ∈ C → s ∪ t ∈ C
-/
theorem accumulate_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ i, s i ∈ C) (n : ℕ) :
    accumulate s n ∈ C := by
  induction n with
  | zero => simp [hs 0]
  | succ n hn => rw [accumulate_succ]; exact hC.union_mem hn (hs _)

end IsSetRing

namespace IsSetSemiring

/-
**MeasureTheory.IsSetSemiring.isPiSystem** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y.IsSetSemiring`。
形式化陈述：isPiSystem (hC : IsSetSemiring C) : IsPiSystem C
参数：hC : IsSetSemiring C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsSetSemiring.inter_mem`：∀ {α : Type u_1} {C : Set (Set α)
}, MeasureTheory.IsSetSemiring C → ∀ s ∈ C, ∀ t ∈ C, s ∩ t ∈ C
-/
lemma isPiSystem (hC : IsSetSemiring C) : IsPiSystem C := fun s hs t ht _ ↦ hC.inter_mem s hs t ht
/-
**MeasureTheory.IsSetSemiring.exists_finpartition_sdiff** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.IsSetSemiring`。
形式化陈述：exists_finpartition_sdiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in 
C) : exists P : Finpartition (s \ t), ↑P.parts subseteq C
参数：hC : IsSetSemiring C；hs : s in C；ht : t in C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsSetSemiring.sdiff_eq_sUnion'`：∀ {α : Type u_1} {C : Set 
(Set α)},   MeasureTheory.IsSetSemiring C → ∀ s ∈ C, ∀ t ∈ C, ∃ I, ↑I ⊆ C ∧ (↑I)
.PairwiseDisjoint id ∧ s \ t = ⋃₀ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.supIndep_iff_pairwiseDisjoint`：supIndep_iff_pairwiseDisjoint : s.
SupIndep f ↔ (s : Set ι).PairwiseDisjoint f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_id_eq_sSup`：sup_id_eq_sSup [CompleteLattice α] (s : Finset α)
 : s.sup id = sSup s
· 使用定理 `Set.sSup_eq_sUnion`：sSup_eq_sUnion (S : Set (Set α)) : sSup S = ⋃₀ S
· 使用定理 `Finpartition.ofErase_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 
: OrderBot α] [inst_2 : DecidableEq α] {a : α} (parts : Finset α)   (sup_indep :
 parts.SupIndep …
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Finset.coe_subset._gcongr_2`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s
₂ → ↑s₁ ⊆ ↑s₂
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem exists_finpartition_sdiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    ∃ P : Finpartition (s \ t), ↑P.parts ⊆ C := by
  obtain ⟨I, hIC, hI, hst⟩ := hC.sdiff_eq_sUnion' s hs t ht
  refine ⟨.ofErase I (supIndep_iff_pairwiseDisjoint.mpr hI) ?_, ?_⟩
  · rw [sup_id_eq_sSup, sSup_eq_sUnion, hst]
  · grw [Finpartition.ofErase_parts, Finset.erase_subset, hIC]

@[deprecated (since := "2026-06-03")] alias exists_finpartition_diff := exists_finpartition_sdiff
/-
**MeasureTheory.IsSetSemiring.mem_supClosure_iff** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.IsSetSemiring`。
形式化陈述：mem_supClosure_iff (hC : IsSetSemiring C) : s in supClosure C ↔ exists P :
 Finpartition s, ↑P.parts subseteq C where mp
参数：hC : IsSetSemiring C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DistribLattice.instIsModularLattice`：∀ {α : Type u_1} [inst : DistribLat
tice α], IsModularLattice α
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `sdiff_sup_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
(a b : α), b \ a ⊔ a = b ⊔ a
· 使用定理 `Finpartition.extend_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 :
 OrderBot α] [inst_2 : IsModularLattice α] [inst_3 : DecidableEq α]   {a b c : α
} (P : Finparti…
· 使用定理 `Finpartition.bind_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : O
rderBot α] [inst_2 : IsModularLattice α] [inst_3 : DecidableEq α] {a : α}   (P :
 Finpartition…
· 使用引理 `Finset.coe_biUnion`：coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Se
t α), t x
· 使用定理 `Set.iUnion₂_subset_iff`：iUnion₂_subset_iff {s : forall i, κ i -> Set α} 
{t : Set α} : ⋃ (i) (j), s i j subseteq t ↔ forall i j, s i j subseteq t
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.IsSetSemiring.exists_finpartition_sdiff`：exists_finpartiti
on_sdiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) : exists P : Finpart
ition (s \ t), ↑P.parts subseteq C
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Finpartition.sup_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Or
derBot α] {a : α} (self : Finpartition a), self.parts.sup id = a
· 使用定理 `Finset.sup_id_set_eq_sUnion`：sup_id_set_eq_sUnion (s : Finset (Set α)) :
 s.sup id = ⋃₀ ↑s
· 使用引理 `SupClosed.sSup_mem`：SupClosed.sSup_mem (hs : SupClosed s) (ht : t.Finite
) (hbot : ⊥ in s) (hts : t subseteq s) : sSup t in s
· 使用引理 `supClosed_supClosure`：supClosed_supClosure : SupClosed (supClosure s)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
（共 33 条，此处仅展示前 30 条）
-/
theorem mem_supClosure_iff (hC : IsSetSemiring C) :
    s ∈ supClosure C ↔ ∃ P : Finpartition s, ↑P.parts ⊆ C where
  mp := by
    rintro ⟨S, hS, hSC, rfl⟩
    rw [sup'_eq_sup]
    clear hS
    induction S using Finset.induction with
    | empty =>
      rw [sup_empty]
      exact ⟨.empty _, hSC⟩
    | insert s S _ ih =>
      rw [coe_insert, insert_subset_iff] at hSC
      obtain ⟨hsC, hSC⟩ := hSC
      obtain ⟨P, hP⟩ := ih hSC
      rw [sup_insert, sup_comm, id]
      rcases eq_or_ne s ⊥ with rfl | hs
      · rw [sup_bot_eq]; exact ⟨P, hP⟩
      choose Q hQ using show ∀ t ∈ (P.avoid s).parts, ∃ Q : Finpartition t, ↑Q.parts ⊆ C by
        simp_rw [Finpartition.mem_avoid]
        rintro _ ⟨t, ht, -, rfl⟩
        exact hC.exists_finpartition_sdiff (hP ht) hsC
      exists P.avoid s |>.bind Q |>.extend hs disjoint_sdiff_left (sdiff_sup_self _ _)
      rw [Finpartition.extend_parts, coe_insert, insert_subset_iff, Finpartition.bind_parts,
        coe_biUnion, iUnion₂_subset_iff, Subtype.forall]
      exact ⟨hsC, fun t ht _ => hQ t ht⟩
  mpr := by
    intro ⟨P, hP⟩
    rw [← P.sup_parts, sup_id_set_eq_sUnion]
    exact supClosed_supClosure.sSup_mem
      (Finset.finite_toSet _)
      (subset_supClosure hC.empty_mem)
      (hP.trans subset_supClosure)
/-
**MeasureTheory.IsSetSemiring.sdiff_mem_supClosure** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.IsSetSemiring`。
形式化陈述：sdiff_mem_supClosure (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) : 
s \ t in supClosure C
参数：hC : IsSetSemiring C；hs : s in C；ht : t in C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.IsSetSemiring.mem_supClosure_iff`：mem_supClosure_iff (hC :
 IsSetSemiring C) : s in supClosure C ↔ exists P : Finpartition s, ↑P.parts subs
eteq C where mp
· 使用定理 `MeasureTheory.IsSetSemiring.exists_finpartition_sdiff`：exists_finpartiti
on_sdiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) : exists P : Finpart
ition (s \ t), ↑P.parts subseteq C
-/
theorem sdiff_mem_supClosure (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    s \ t ∈ supClosure C :=
  hC.mem_supClosure_iff.mpr <| hC.exists_finpartition_sdiff hs ht

@[deprecated (since := "2026-06-03")] alias diff_mem_supClosure := sdiff_mem_supClosure
/-
**MeasureTheory.IsSetSemiring.isSetRing_supClosure** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.IsSetSemiring`。
形式化陈述：isSetRing_supClosure (hC : IsSetSemiring C) : IsSetRing (supClosure C) whe
re empty_mem
参数：hC : IsSetSemiring C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `subset_supClosure`：subset_supClosure {s : Set α} : s subseteq supClosure
 s
· 使用定理 `MeasureTheory.IsSetSemiring.empty_mem`：∀ {α : Type u_1} {C : Set (Set α)
}, MeasureTheory.IsSetSemiring C → ∅ ∈ C
· 使用引理 `supClosed_supClosure`：supClosed_supClosure : SupClosed (supClosure s)
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `Set.sdiff_empty`：sdiff_empty {s : Set α} : s \ ∅ = s
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `Set.sup_eq_union`：sup_eq_union : ((· ⊔ ·) : Set α -> Set α -> Set α) = (
· union ·)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_sdiff`：sdiff_sdiff {u : Set α} : (s \ t) \ u = s \ (t union u)
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.sup_sdiff_right`：sup_sdiff_right {α β : Type*} [GeneralizedBoolea
nAlgebra α] (s : Finset β) (f : β -> α) (a : α) : (s.sup fun b => f b \ a) = s.s
up f \ a
· 使用引理 `SupClosed.finsetSup_mem`：SupClosed.finsetSup_mem [OrderBot α] (hs : SupC
losed s) (ht : t.Nonempty) : (forall i in t, f i in s) -> t.sup f in s
· 使用定理 `MeasureTheory.IsSetSemiring.sdiff_mem_supClosure`：sdiff_mem_supClosure (
hC : IsSetSemiring C) (hs : s in C) (ht : t in C) : s \ t in supClosure C
-/
theorem isSetRing_supClosure (hC : IsSetSemiring C) : IsSetRing (supClosure C) where
  empty_mem := subset_supClosure hC.empty_mem
  union_mem _ _ h₁ h₂ := supClosed_supClosure h₁ h₂
  sdiff_mem := by
    rintro s _ hs ⟨T, hT, hTC, rfl⟩
    rw [sup'_eq_sup]
    clear hT
    induction T using Finset.induction generalizing s with
    | empty => simpa
    | insert t T _ ih =>
      simp_rw [sup_insert, id, sup_eq_union, ← sdiff_sdiff]
      rw [coe_insert, insert_subset_iff] at hTC
      obtain ⟨htC, hTC⟩ := hTC
      refine ih ?_ hTC
      obtain ⟨S, hS, hSC, rfl⟩ := hs
      rw [sup'_eq_sup, ← Finset.sup_sdiff_right]
      refine supClosed_supClosure.finsetSup_mem hS fun s hs => ?_
      exact hC.sdiff_mem_supClosure (hSC hs) htC

section disjointOfDiff

/-- In a semi-ring of sets `C`, for all sets `s, t ∈ C`, `s \ t` is equal to a disjoint union of
finitely many sets in `C`. The finite set of sets in the union is not unique, but this definition
gives an arbitrary `Finset (Set α)` that satisfies the equality.

We remove the empty set to ensure that `t ∉ hC.disjointOfDiff hs ht` even if `t = ∅`. -/
/-
**MeasureTheory.IsSetSemiring.disjointOfDiff** 是 Mathlib 中的一个定义，位于命名空间 `MeasureT
heory.IsSetSemiring`。
形式化陈述：disjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) : Finset
 (Set α)
参数：hC : IsSetSemiring C；hs : s in C；ht : t in C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsSetSemiring.exists_finpartition_sdiff`：exists_finpartiti
on_sdiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) : exists P : Finpart
ition (s \ t), ↑P.parts subseteq C

--- 原说明 ---
In a semi-ring of sets `C`, for all sets `s, t ∈ C`, `s \ t` is equal to a disjo
int union of
finitely many sets in `C`. The finite set of sets in the union is not unique, bu
t this definition
gives an arbitrary `Finset (Set α)` that satisfies the equality.

We remove the empty set to ensure that `t ∉ hC.disjointOfDiff hs ht` even if `t 
= ∅`.
-/
noncomputable def disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    Finset (Set α) :=
  (hC.exists_finpartition_sdiff hs ht).choose.parts
/-
**MeasureTheory.IsSetSemiring.empty_notMem_disjointOfDiff** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：empty_notMem_disjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht : t i
n C) : ∅ ∉ hC.disjointOfDiff hs ht
参数：hC : IsSetSemiring C；hs : s in C；ht : t in C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finpartition.bot_notMem`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : O
rderBot α] {a : α} (self : Finpartition a), ⊥ ∉ self.parts
· 使用定理 `MeasureTheory.IsSetSemiring.exists_finpartition_sdiff`：exists_finpartiti
on_sdiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) : exists P : Finpart
ition (s \ t), ↑P.parts subseteq C
-/
lemma empty_notMem_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    ∅ ∉ hC.disjointOfDiff hs ht :=
  Finpartition.bot_notMem _
/-
**MeasureTheory.IsSetSemiring.subset_disjointOfDiff** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.IsSetSemiring`。
形式化陈述：subset_disjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) :
 ↑(hC.disjointOfDiff hs ht) subseteq C
参数：hC : IsSetSemiring C；hs : s in C；ht : t in C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `MeasureTheory.IsSetSemiring.exists_finpartition_sdiff`：exists_finpartiti
on_sdiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) : exists P : Finpart
ition (s \ t), ↑P.parts subseteq C
-/
lemma subset_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    ↑(hC.disjointOfDiff hs ht) ⊆ C :=
  (hC.exists_finpartition_sdiff hs ht).choose_spec
/-
**MeasureTheory.IsSetSemiring.pairwiseDisjoint_disjointOfDiff** 是 Mathlib 中的一个引理
，位于命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：pairwiseDisjoint_disjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht :
 t in C) : PairwiseDisjoint (hC.disjointOfDiff hs ht : Set (Set α)) id
参数：hC : IsSetSemiring C；hs : s in C；ht : t in C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.SupIndep.pairwiseDisjoint`：∀ {α : Type u_1} {ι : Type u_3} [inst 
: Lattice α] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α},   s.SupIndep f → 
(↑s).PairwiseDisjoint …
· 使用定理 `MeasureTheory.IsSetSemiring.exists_finpartition_sdiff`：exists_finpartiti
on_sdiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) : exists P : Finpart
ition (s \ t), ↑P.parts subseteq C
· 使用定理 `Finpartition.supIndep`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (self : Finpartition a), self.parts.SupIndep id
-/
lemma pairwiseDisjoint_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    PairwiseDisjoint (hC.disjointOfDiff hs ht : Set (Set α)) id :=
  Finpartition.supIndep _ |>.pairwiseDisjoint
/-
**MeasureTheory.IsSetSemiring.sUnion_disjointOfDiff** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.IsSetSemiring`。
形式化陈述：sUnion_disjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) :
 ⋃₀ hC.disjointOfDiff hs ht = s \ t
参数：hC : IsSetSemiring C；hs : s in C；ht : t in C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_id_eq_sSup`：sup_id_eq_sSup [CompleteLattice α] (s : Finset α)
 : s.sup id = sSup s
· 使用定理 `Finpartition.sup_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Or
derBot α] {a : α} (self : Finpartition a), self.parts.sup id = a
· 使用定理 `MeasureTheory.IsSetSemiring.exists_finpartition_sdiff`：exists_finpartiti
on_sdiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) : exists P : Finpart
ition (s \ t), ↑P.parts subseteq C
-/
lemma sUnion_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    ⋃₀ hC.disjointOfDiff hs ht = s \ t :=
  (sup_id_eq_sSup _).symm.trans (Finpartition.sup_parts _)
/-
**MeasureTheory.IsSetSemiring.notMem_disjointOfDiff** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.IsSetSemiring`。
形式化陈述：notMem_disjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) :
 t ∉ hC.disjointOfDiff hs ht
参数：hC : IsSetSemiring C；hs : s in C；ht : t in C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.eq_bot_of_le`：Disjoint.eq_bot_of_le (hab : Disjoint a b) (h : a
 <= b) : a = ⊥
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
· 使用定理 `Finpartition.le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : OrderBot 
α] {a : α} (P : Finpartition a) {b : α}, b ∈ P.parts → b ≤ a
· 使用定理 `MeasureTheory.IsSetSemiring.exists_finpartition_sdiff`：exists_finpartiti
on_sdiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) : exists P : Finpart
ition (s \ t), ↑P.parts subseteq C
· 使用引理 `MeasureTheory.IsSetSemiring.empty_notMem_disjointOfDiff`：empty_notMem_di
sjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) : ∅ ∉ hC.disjoin
tOfDiff hs ht
-/
lemma notMem_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    t ∉ hC.disjointOfDiff hs ht := by
  intro hs_mem
  cases disjoint_sdiff_self_right.eq_bot_of_le (Finpartition.le _ hs_mem)
  exact hC.empty_notMem_disjointOfDiff hs ht hs_mem
/-
**MeasureTheory.IsSetSemiring.sUnion_insert_disjointOfDiff** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：sUnion_insert_disjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht : t 
in C) (hst : t subseteq s) : ⋃₀ insert t (hC.disjointOfDiff hs ht) = s
参数：hC : IsSetSemiring C；hs : s in C；ht : t in C；hst : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_sdiff_cancel`：union_sdiff_cancel {s t : Set α} (h : s subseteq
 t) : s union t \ s = t
· 使用引理 `MeasureTheory.IsSetSemiring.sUnion_disjointOfDiff`：sUnion_disjointOfDiff
 (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) : ⋃₀ hC.disjointOfDiff hs ht
 = s \ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sUnion_insert`：sUnion_insert (s : Set α) (T : Set (Set α)) : ⋃₀ inse
rt s T = s union ⋃₀ T
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sUnion_insert_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C)
    (ht : t ∈ C) (hst : t ⊆ s) :
    ⋃₀ insert t (hC.disjointOfDiff hs ht) = s := by
  conv_rhs => rw [← union_sdiff_cancel hst, ← hC.sUnion_disjointOfDiff hs ht]
  simp only [sUnion_insert]
/-
**MeasureTheory.IsSetSemiring.disjoint_sUnion_disjointOfDiff** 是 Mathlib 中的一个引理，
位于命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：disjoint_sUnion_disjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht : 
t in C) : Disjoint t (⋃₀ hC.disjointOfDiff hs ht)
参数：hC : IsSetSemiring C；hs : s in C；ht : t in C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.IsSetSemiring.sUnion_disjointOfDiff`：sUnion_disjointOfDiff
 (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) : ⋃₀ hC.disjointOfDiff hs ht
 = s \ t
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)
-/
lemma disjoint_sUnion_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    Disjoint t (⋃₀ hC.disjointOfDiff hs ht) := by
  rw [hC.sUnion_disjointOfDiff]
  exact disjoint_sdiff_right
/-
**MeasureTheory.IsSetSemiring.pairwiseDisjoint_insert_disjointOfDiff** 是 Mathlib
 中的一个引理，位于命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：pairwiseDisjoint_insert_disjointOfDiff (hC : IsSetSemiring C) (hs : s in C
) (ht : t in C) : PairwiseDisjoint (insert t (hC.disjointOfDiff hs ht) : Set (Se
t α)) id
参数：hC : IsSetSemiring C；hs : s in C；ht : t in C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.IsSetSemiring.pairwiseDisjoint_disjointOfDiff`：pairwiseDis
joint_disjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) : Pairwi
seDisjoint (hC.disjointOfDiff hs ht : Set (Set α)…
· 使用定理 `Set.PairwiseDisjoint.insert_of_notMem`：∀ {α : Type u_1} {ι : Type u_4} [
inst : PartialOrder α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},   s.Pairwi
seDisjoint f → ∀ {i : ι}, i…
· 使用引理 `MeasureTheory.IsSetSemiring.notMem_disjointOfDiff`：notMem_disjointOfDiff
 (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) : t ∉ hC.disjointOfDiff hs h
t
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用引理 `MeasureTheory.IsSetSemiring.disjoint_sUnion_disjointOfDiff`：disjoint_sUn
ion_disjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) : Disjoint
 t (⋃₀ hC.disjointOfDiff hs ht)
-/
lemma pairwiseDisjoint_insert_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C)
    (ht : t ∈ C) :
    PairwiseDisjoint (insert t (hC.disjointOfDiff hs ht) : Set (Set α)) id := by
  have h := hC.pairwiseDisjoint_disjointOfDiff hs ht
  refine PairwiseDisjoint.insert_of_notMem h (hC.notMem_disjointOfDiff hs ht) fun u hu ↦ ?_
  simp_rw [id]
  refine Disjoint.mono_right ?_ (hC.disjoint_sUnion_disjointOfDiff hs ht)
  exact subset_sUnion_of_mem hu

end disjointOfDiff

section disjointOfDiffUnion

variable {I : Finset (Set α)}

/-
**MeasureTheory.IsSetSemiring.exists_finpartition_sdiff_sUnion** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.IsSetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem exists_finpartition_sdiff_sUnion (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    ∃ P : Finpartition (s \ ⋃₀ I), ↑P.parts ⊆ C := by
  rw [← hC.mem_supClosure_iff, ← sSup_eq_sUnion, ← sup_id_eq_sSup]
  have hC' := hC.isSetRing_supClosure
  exact hC'.sdiff_mem (subset_supClosure hs) <| hC'.finsetSup_mem <| hI.trans subset_supClosure

/-- In a semiring of sets `C`, for all set `s ∈ C` and finite set of sets `I ⊆ C`,
`disjointOfDiffUnion` is a finite set of sets in `C` such that
`s \ ⋃₀ I = ⋃₀ (hC.disjointOfDiffUnion hs I hI)`.
`disjointOfDiff` is a special case of `disjointOfDiffUnion` where `I` is a
singleton. -/
/-
**MeasureTheory.IsSetSemiring.disjointOfDiffUnion** 是 Mathlib 中的一个定义，位于命名空间 `Mea
sureTheory.IsSetSemiring`。
形式化陈述：disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I subseteq
 C) : Finset (Set α)
参数：hC : IsSetSemiring C；hs : s in C；hI : ↑I subseteq C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.MeasureTheory.IsSetSemiring
.exists_finpartition_sdiff_sUnion`：∀ {α : Type u_1} {C : Set (Set α)} {s : Set α
} {I : Finset (Set α)},   MeasureTheory.IsSetSemiring C → s ∈ C → ↑I ⊆ C → ∃ P, 
↑P.parts ⊆ C

--- 原说明 ---
In a semiring of sets `C`, for all set `s ∈ C` and finite set of sets `I ⊆ C`,
`disjointOfDiffUnion` is a finite set of sets in `C` such that
`s \ ⋃₀ I = ⋃₀ (hC.disjointOfDiffUnion hs I hI)`.
`disjointOfDiff` is a special case of `disjointOfDiffUnion` where `I` is a
singleton.
-/
noncomputable def disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    Finset (Set α) :=
  (hC.exists_finpartition_sdiff_sUnion hs hI).choose.parts
/-
**MeasureTheory.IsSetSemiring.empty_notMem_disjointOfDiffUnion** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：empty_notMem_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) (hI 
: ↑I subseteq C) : ∅ ∉ hC.disjointOfDiffUnion hs hI
参数：hC : IsSetSemiring C；hs : s in C；hI : ↑I subseteq C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finpartition.bot_notMem`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : O
rderBot α] {a : α} (self : Finpartition a), ⊥ ∉ self.parts
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.MeasureTheory.IsSetSemiring
.exists_finpartition_sdiff_sUnion`：∀ {α : Type u_1} {C : Set (Set α)} {s : Set α
} {I : Finset (Set α)},   MeasureTheory.IsSetSemiring C → s ∈ C → ↑I ⊆ C → ∃ P, 
↑P.parts ⊆ C
-/
lemma empty_notMem_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) :
    ∅ ∉ hC.disjointOfDiffUnion hs hI :=
  Finpartition.bot_notMem _
/-
**MeasureTheory.IsSetSemiring.disjointOfDiffUnion_subset** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：disjointOfDiffUnion_subset (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I s
ubseteq C) : ↑(hC.disjointOfDiffUnion hs hI) subseteq C
参数：hC : IsSetSemiring C；hs : s in C；hI : ↑I subseteq C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.MeasureTheory.IsSetSemiring
.exists_finpartition_sdiff_sUnion`：∀ {α : Type u_1} {C : Set (Set α)} {s : Set α
} {I : Finset (Set α)},   MeasureTheory.IsSetSemiring C → s ∈ C → ↑I ⊆ C → ∃ P, 
↑P.parts ⊆ C
-/
lemma disjointOfDiffUnion_subset (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    ↑(hC.disjointOfDiffUnion hs hI) ⊆ C :=
  (hC.exists_finpartition_sdiff_sUnion hs hI).choose_spec
/-
**MeasureTheory.IsSetSemiring.pairwiseDisjoint_disjointOfDiffUnion** 是 Mathlib 中
的一个引理，位于命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：pairwiseDisjoint_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) 
(hI : ↑I subseteq C) : PairwiseDisjoint (hC.disjointOfDiffUnion hs hI : Set (Set
 α)) id
参数：hC : IsSetSemiring C；hs : s in C；hI : ↑I subseteq C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.SupIndep.pairwiseDisjoint`：∀ {α : Type u_1} {ι : Type u_3} [inst 
: Lattice α] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α},   s.SupIndep f → 
(↑s).PairwiseDisjoint …
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.MeasureTheory.IsSetSemiring
.exists_finpartition_sdiff_sUnion`：∀ {α : Type u_1} {C : Set (Set α)} {s : Set α
} {I : Finset (Set α)},   MeasureTheory.IsSetSemiring C → s ∈ C → ↑I ⊆ C → ∃ P, 
↑P.parts ⊆ C
· 使用定理 `Finpartition.supIndep`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (self : Finpartition a), self.parts.SupIndep id
-/
lemma pairwiseDisjoint_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) : PairwiseDisjoint (hC.disjointOfDiffUnion hs hI : Set (Set α)) id :=
  (Finpartition.supIndep _).pairwiseDisjoint
/-
**MeasureTheory.IsSetSemiring.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion** 是 Mat
hlib 中的一个引理，位于命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：sdiff_sUnion_eq_sUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s 
in C) (hI : ↑I subseteq C) : s \ ⋃₀ I = ⋃₀ hC.disjointOfDiffUnion hs hI
参数：hC : IsSetSemiring C；hs : s in C；hI : ↑I subseteq C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.MeasureTheory.IsSetSemiring
.exists_finpartition_sdiff_sUnion`：∀ {α : Type u_1} {C : Set (Set α)} {s : Set α
} {I : Finset (Set α)},   MeasureTheory.IsSetSemiring C → s ∈ C → ↑I ⊆ C → ∃ P, 
↑P.parts ⊆ C
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finpartition.sup_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Or
derBot α] {a : α} (self : Finpartition a), self.parts.sup id = a
· 使用定理 `Finset.sup_id_eq_sSup`：sup_id_eq_sSup [CompleteLattice α] (s : Finset α)
 : s.sup id = sSup s
-/
lemma sdiff_sUnion_eq_sUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) : s \ ⋃₀ I = ⋃₀ hC.disjointOfDiffUnion hs hI :=
  (Finpartition.sup_parts _).symm.trans (sup_id_eq_sSup _)

@[deprecated (since := "2026-06-03")]
alias diff_sUnion_eq_sUnion_disjointOfDiffUnion := sdiff_sUnion_eq_sUnion_disjointOfDiffUnion

/-- In a semiring of sets `C`, for all set `s ∈ C` and finite set of sets `I ⊆ C`, there is a
finite set of sets in `C` whose union is `s \ ⋃₀ I`.
See `IsSetSemiring.disjointOfDiffUnion` for a definition that gives such a set. -/
/-
**MeasureTheory.IsSetSemiring.exists_disjoint_finset_sdiff_eq** 是 Mathlib 中的一个引理
，位于命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：exists_disjoint_finset_sdiff_eq (hC : IsSetSemiring C) (hs : s in C) (hI :
 ↑I subseteq C) : exists J : Finset (Set α), ↑J subseteq C ∧ PairwiseDisjoint (J
 : Set (Set α)) id ∧ s \ ⋃₀ I = ⋃₀ J
参数：hC : IsSetSemiring C；hs : s in C；hI : ↑I subseteq C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.IsSetSemiring.disjointOfDiffUnion_subset`：disjointOfDiffUn
ion_subset (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I subseteq C) : ↑(hC.disj
ointOfDiffUnion hs hI) subseteq C
· 使用引理 `MeasureTheory.IsSetSemiring.pairwiseDisjoint_disjointOfDiffUnion`：pairwi
seDisjoint_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I sub
seteq C) : PairwiseDisjoint (hC.disjointOfDiffUnion hs…
· 使用引理 `MeasureTheory.IsSetSemiring.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion`：
sdiff_sUnion_eq_sUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) 
(hI : ↑I subseteq C) : s \ ⋃₀ I = ⋃₀ hC.disjointOfDiffUnion …

--- 原说明 ---
In a semiring of sets `C`, for all set `s ∈ C` and finite set of sets `I ⊆ C`, t
here is a
finite set of sets in `C` whose union is `s \ ⋃₀ I`.
See `IsSetSemiring.disjointOfDiffUnion` for a definition that gives such a set.
-/
lemma exists_disjoint_finset_sdiff_eq (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    ∃ J : Finset (Set α), ↑J ⊆ C ∧ PairwiseDisjoint (J : Set (Set α)) id ∧
      s \ ⋃₀ I = ⋃₀ J :=
  ⟨hC.disjointOfDiffUnion hs hI,
   hC.disjointOfDiffUnion_subset hs hI,
   hC.pairwiseDisjoint_disjointOfDiffUnion hs hI,
   hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion hs hI⟩

@[deprecated (since := "2026-06-03")]
alias exists_disjoint_finset_diff_eq := exists_disjoint_finset_sdiff_eq
/-
**MeasureTheory.IsSetSemiring.sUnion_disjointOfDiffUnion_subset** 是 Mathlib 中的一个
引理，位于命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：sUnion_disjointOfDiffUnion_subset (hC : IsSetSemiring C) (hs : s in C) (hI
 : ↑I subseteq C) : ⋃₀ (hC.disjointOfDiffUnion hs hI : Set (Set α)) subseteq s
参数：hC : IsSetSemiring C；hs : s in C；hI : ↑I subseteq C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.IsSetSemiring.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion`：
sdiff_sUnion_eq_sUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) 
(hI : ↑I subseteq C) : s \ ⋃₀ I = ⋃₀ hC.disjointOfDiffUnion …
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
lemma sUnion_disjointOfDiffUnion_subset (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) : ⋃₀ (hC.disjointOfDiffUnion hs hI : Set (Set α)) ⊆ s := by
  rw [← hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion]
  exact sdiff_subset
/-
**MeasureTheory.IsSetSemiring.subset_of_diffUnion_disjointOfDiffUnion** 是 Mathli
b 中的一个引理，位于命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：subset_of_diffUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in 
C) (hI : ↑I subseteq C) (t : Set α) (ht : t in (hC.disjointOfDiffUnion hs hI : S
et (Set α))) : t subseteq s \ ⋃₀ I
参数：hC : IsSetSemiring C；hs : s in C；hI : ↑I subseteq C；t : Set α；ht : t in (hC.d
isjointOfDiffUnion hs hI : Set (Set α))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_subset_iff`：sUnion_subset_iff {s : Set (Set α)} {t : Set α} :
 ⋃₀ s subseteq t ↔ forall t' in s, t' subseteq t
· 使用引理 `MeasureTheory.IsSetSemiring.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion`：
sdiff_sUnion_eq_sUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) 
(hI : ↑I subseteq C) : s \ ⋃₀ I = ⋃₀ hC.disjointOfDiffUnion …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma subset_of_diffUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C)
    (t : Set α) (ht : t ∈ (hC.disjointOfDiffUnion hs hI : Set (Set α))) :
    t ⊆ s \ ⋃₀ I := by
  revert t ht
  rw [← sUnion_subset_iff, hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion hs hI]
/-
**MeasureTheory.IsSetSemiring.subset_of_mem_disjointOfDiffUnion** 是 Mathlib 中的一个
引理，位于命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：subset_of_mem_disjointOfDiffUnion (hC : IsSetSemiring C) {I : Finset (Set 
α)} (hs : s in C) (hI : ↑I subseteq C) (t : Set α) (ht : t in (hC.disjointOfDiff
Union hs hI : Set (Set α))) : t subseteq s
参数：hC : IsSetSemiring C；Set α；hs : s in C；hI : ↑I subseteq C；t : Set α；ht : t in
 (hC.disjointOfDiffUnion hs hI : Set (Set α))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `MeasureTheory.IsSetSemiring.subset_of_diffUnion_disjointOfDiffUnion`：sub
set_of_diffUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) (hI : 
↑I subseteq C) (t : Set α) (ht : t in (hC.disjointOfDiffU…
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
-/
lemma subset_of_mem_disjointOfDiffUnion (hC : IsSetSemiring C) {I : Finset (Set α)}
    (hs : s ∈ C) (hI : ↑I ⊆ C) (t : Set α)
    (ht : t ∈ (hC.disjointOfDiffUnion hs hI : Set (Set α))) :
    t ⊆ s := by
  apply le_trans <| hC.subset_of_diffUnion_disjointOfDiffUnion hs hI t ht
  exact sdiff_le (a := s) (b := ⋃₀ I)
/-
**MeasureTheory.IsSetSemiring.disjoint_sUnion_disjointOfDiffUnion** 是 Mathlib 中的
一个引理，位于命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：disjoint_sUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) (
hI : ↑I subseteq C) : Disjoint (⋃₀ (I : Set (Set α))) (⋃₀ hC.disjointOfDiffUnion
 hs hI)
参数：hC : IsSetSemiring C；hs : s in C；hI : ↑I subseteq C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.IsSetSemiring.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion`：
sdiff_sUnion_eq_sUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) 
(hI : ↑I subseteq C) : s \ ⋃₀ I = ⋃₀ hC.disjointOfDiffUnion …
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)
-/
lemma disjoint_sUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) :
    Disjoint (⋃₀ (I : Set (Set α))) (⋃₀ hC.disjointOfDiffUnion hs hI) := by
  rw [← hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion]; exact Set.disjoint_sdiff_right
/-
**MeasureTheory.IsSetSemiring.disjoint_disjointOfDiffUnion** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：disjoint_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I
 subseteq C) : Disjoint I (hC.disjointOfDiffUnion hs hI)
参数：hC : IsSetSemiring C；hs : s in C；hI : ↑I subseteq C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists a, a 
in s ∧ a in t
· 使用引理 `MeasureTheory.IsSetSemiring.disjoint_sUnion_disjointOfDiffUnion`：disjoin
t_sUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I subse
teq C) : Disjoint (⋃₀ (I : Set (Set α))) (⋃₀ hC.disjo…
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用引理 `MeasureTheory.IsSetSemiring.empty_notMem_disjointOfDiffUnion`：empty_notM
em_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I subseteq C)
 : ∅ ∉ hC.disjointOfDiffUnion hs hI
-/
lemma disjoint_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    Disjoint I (hC.disjointOfDiffUnion hs hI) := by
  by_contra h
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨u, huI, hu_disjointOfDiffUnion⟩ := h
  have h_disj : u ≤ ⊥ :=
    hC.disjoint_sUnion_disjointOfDiffUnion hs hI (subset_sUnion_of_mem huI)
    (subset_sUnion_of_mem hu_disjointOfDiffUnion)
  simp only [Set.bot_eq_empty, subset_empty_iff] at h_disj
  refine hC.empty_notMem_disjointOfDiffUnion hs hI ?_
  rwa [h_disj] at hu_disjointOfDiffUnion
/-
**MeasureTheory.IsSetSemiring.pairwiseDisjoint_union_disjointOfDiffUnion** 是 Mat
hlib 中的一个引理，位于命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：pairwiseDisjoint_union_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s 
in C) (hI : ↑I subseteq C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id) : Pai
rwiseDisjoint (I union hC.disjointOfDiffUnion hs hI : Set (Set α)) id
参数：hC : IsSetSemiring C；hs : s in C；hI : ↑I subseteq C；h_dis : PairwiseDisjoint 
(I : Set (Set α)) id。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pairwiseDisjoint_union`：pairwiseDisjoint_union : (s union t).Pairwis
eDisjoint f ↔ s.PairwiseDisjoint f ∧ t.PairwiseDisjoint f ∧ forall ⦃i⦄, i in s -
> forall ⦃j⦄, j …
· 使用引理 `MeasureTheory.IsSetSemiring.pairwiseDisjoint_disjointOfDiffUnion`：pairwi
seDisjoint_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I sub
seteq C) : PairwiseDisjoint (hC.disjointOfDiffUnion hs…
· 使用引理 `Set.disjoint_of_subset`：disjoint_of_subset (hs : s₁ subseteq s₂) (ht : t
₁ subseteq t₂) (h : Disjoint s₂ t₂) : Disjoint s₁ t₁
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用引理 `MeasureTheory.IsSetSemiring.disjoint_sUnion_disjointOfDiffUnion`：disjoin
t_sUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I subse
teq C) : Disjoint (⋃₀ (I : Set (Set α))) (⋃₀ hC.disjo…
-/
lemma pairwiseDisjoint_union_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id) :
    PairwiseDisjoint (I ∪ hC.disjointOfDiffUnion hs hI : Set (Set α)) id := by
  rw [pairwiseDisjoint_union]
  refine ⟨h_dis, hC.pairwiseDisjoint_disjointOfDiffUnion hs hI, fun u hu v hv _ ↦ ?_⟩
  simp_rw [id]
  exact disjoint_of_subset (subset_sUnion_of_mem hu) (subset_sUnion_of_mem hv)
    (hC.disjoint_sUnion_disjointOfDiffUnion hs hI)
/-
**MeasureTheory.IsSetSemiring.sUnion_union_sUnion_disjointOfDiffUnion_of_subset*
* 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：sUnion_union_sUnion_disjointOfDiffUnion_of_subset (hC : IsSetSemiring C) (
hs : s in C) (hI : ↑I subseteq C) (hI_ss : forall t in I, t subseteq s) : ⋃₀ I u
nion ⋃₀ hC.disjointOfDiffUnion hs hI = s
参数：hC : IsSetSemiring C；hs : s in C；hI : ↑I subseteq C；hI_ss : forall t in I, t 
subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_sdiff_cancel`：union_sdiff_cancel {s t : Set α} (h : s subseteq
 t) : s union t \ s = t
· 使用定理 `Set.sUnion_subset`：sUnion_subset {S : Set (Set α)} {t : Set α} (h : fora
ll t' in S, t' subseteq t) : ⋃₀ S subseteq t
· 使用引理 `MeasureTheory.IsSetSemiring.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion`：
sdiff_sUnion_eq_sUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) 
(hI : ↑I subseteq C) : s \ ⋃₀ I = ⋃₀ hC.disjointOfDiffUnion …
-/
lemma sUnion_union_sUnion_disjointOfDiffUnion_of_subset (hC : IsSetSemiring C)
    (hs : s ∈ C) (hI : ↑I ⊆ C) (hI_ss : ∀ t ∈ I, t ⊆ s) :
    ⋃₀ I ∪ ⋃₀ hC.disjointOfDiffUnion hs hI = s := by
  conv_rhs => rw [← union_sdiff_cancel (Set.sUnion_subset hI_ss : ⋃₀ ↑I ⊆ s),
    hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion hs hI]
/-
**MeasureTheory.IsSetSemiring.sUnion_union_disjointOfDiffUnion_of_subset** 是 Mat
hlib 中的一个引理，位于命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：sUnion_union_disjointOfDiffUnion_of_subset (hC : IsSetSemiring C) (hs : s 
in C) (hI : ↑I subseteq C) (hI_ss : forall t in I, t subseteq s) : ⋃₀ ↑(I union 
hC.disjointOfDiffUnion hs hI) = s
参数：hC : IsSetSemiring C；hs : s in C；hI : ↑I subseteq C；hI_ss : forall t in I, t 
subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.IsSetSemiring.sUnion_union_sUnion_disjointOfDiffUnion_of_s
ubset`：sUnion_union_sUnion_disjointOfDiffUnion_of_subset (hC : IsSetSemiring C) 
(hs : s in C) (hI : ↑I subseteq C) (hI_ss : forall t in I, t subset…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Set.sUnion_union`：sUnion_union (S T : Set (Set α)) : ⋃₀ (S union T) = ⋃₀
 S union ⋃₀ T
-/
lemma sUnion_union_disjointOfDiffUnion_of_subset (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) (hI_ss : ∀ t ∈ I, t ⊆ s) :
    ⋃₀ ↑(I ∪ hC.disjointOfDiffUnion hs hI) = s := by
  conv_rhs => rw [← sUnion_union_sUnion_disjointOfDiffUnion_of_subset hC hs hI hI_ss]
  simp_rw [coe_union]
  rw [sUnion_union]

end disjointOfDiffUnion

section disjointOfUnion


variable {j : Set α} {J : Finset (Set α)}

open MeasureTheory Order

/-
**MeasureTheory.IsSetSemiring.exists_partition_disjointed** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.IsSetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem exists_partition_disjointed (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (j : J) :
    ∃ P : Finpartition (disjointed (fun i ↦ (J.equivFin.symm i : Set α)) (J.equivFin j)),
      ↑P.parts ⊆ C :=
  hC.mem_supClosure_iff.mp <|
    hC.isSetRing_supClosure.disjointed_mem (fun _ ↦ subset_supClosure (hJ (Subtype.coe_prop _))) _

/-- For some `hJ : J ⊆ C` and `j : Set α`, where `hC : IsSetSemiring C`, this is
a `Finset (Set α)` such that `K j := hC.disjointOfUnion hJ` are disjoint
and `⋃₀ K j ⊆ j`, for `j ∈ J`.
Using these we write `⋃₀ J` as a disjoint union `⋃₀ J = ⋃₀ ⋃ x ∈ J, (K x)`.
See `MeasureTheory.IsSetSemiring.disjointOfUnion_props`. -/
/-
**MeasureTheory.IsSetSemiring.disjointOfUnion** 是 Mathlib 中的一个定义，位于命名空间 `Measure
Theory.IsSetSemiring`。
形式化陈述：disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (j : Set α) : 
Finset (Set α)
参数：hC : IsSetSemiring C；hJ : ↑J subseteq C；j : Set α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
For some `hJ : J ⊆ C` and `j : Set α`, where `hC : IsSetSemiring C`, this is
a `Finset (Set α)` such that `K j := hC.disjointOfUnion hJ` are disjoint
and `⋃₀ K j ⊆ j`, for `j ∈ J`.
Using these we write `⋃₀ J` as a disjoint union `⋃₀ J = ⋃₀ ⋃ x ∈ J, (K x)`.
See `MeasureTheory.IsSetSemiring.disjointOfUnion_props`.
-/
noncomputable def disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (j : Set α) :
    Finset (Set α) :=
  if hj : j ∈ J then (hC.exists_partition_disjointed hJ ⟨j, hj⟩).choose.parts else ∅
/-
**MeasureTheory.IsSetSemiring.disjointOfUnion_coe** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.IsSetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem disjointOfUnion_coe (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (j : J) :
    hC.disjointOfUnion hJ j = (hC.exists_partition_disjointed hJ j).choose.parts := by
  rw [disjointOfUnion, dif_pos j.2]
/-
**MeasureTheory.IsSetSemiring.pairwiseDisjoint_disjointOfUnion** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：pairwiseDisjoint_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J subseteq 
C) : PairwiseDisjoint J (hC.disjointOfUnion hJ)
参数：hC : IsSetSemiring C；hJ : ↑J subseteq C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pairwise.set_of_subtype`：∀ {α : Type u_1} (s : Set α) (r : α → α → Prop)
, (Pairwise fun x y => r ↑x ↑y) → s.Pairwise r
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.MeasureTheory.IsSetSemiring
.exists_partition_disjointed`：∀ {α : Type u_1} {C : Set (Set α)} {J : Finset (Se
t α)},   MeasureTheory.IsSetSemiring C → ↑J ⊆ C → ∀ (j : ↥J), ∃ P, ↑P.parts ⊆ C
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.MeasureTheory.IsSetSemiring
.disjointOfUnion_coe`：∀ {α : Type u_1} {C : Set (Set α)} {J : Finset (Set α)} (h
C : MeasureTheory.IsSetSemiring C) (hJ : ↑J ⊆ C) (j : ↥J),   hC.disjointOfUnion 
hJ…
· 使用定理 `Disjoint.ne`：Disjoint.ne (ha : a != ⊥) (hab : Disjoint a b) : a != b
· 使用定理 `Finpartition.ne_bot`：ne_bot {b : α} (hb : b in P.parts) : b != ⊥
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Finpartition.le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : OrderBot 
α] {a : α} (P : Finpartition a) {b : α}, b ∈ P.parts → b ≤ a
· 使用定理 `disjoint_disjointed`：disjoint_disjointed (f : ι -> α) : Pairwise (Disjoi
nt on disjointed f)
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma pairwiseDisjoint_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    PairwiseDisjoint J (hC.disjointOfUnion hJ) := by
  refine Pairwise.set_of_subtype _ _ fun j k hjk ↦ ?_
  simp_rw [Function.onFun, hC.disjointOfUnion_coe hJ, Finset.disjoint_iff_ne]
  exact fun s hs t ht ↦ Disjoint.ne (Finpartition.ne_bot _ hs) <|
    .mono (Finpartition.le _ hs) (Finpartition.le _ ht) <|
    disjoint_disjointed _ <| J.equivFin.injective.ne hjk
/-
**MeasureTheory.IsSetSemiring.disjointOfUnion_subset** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.IsSetSemiring`。
形式化陈述：disjointOfUnion_subset (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (hj : j
 in J) : (disjointOfUnion hC hJ j : Set (Set α)) subseteq C
参数：hC : IsSetSemiring C；hJ : ↑J subseteq C；hj : j in J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Finset.FinsetCoe.canLift`：∀ {α : Type u_1} (s : Finset α), CanLift α (↥s
) Subtype.val fun a => a ∈ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.MeasureTheory.IsSetSemiring
.exists_partition_disjointed`：∀ {α : Type u_1} {C : Set (Set α)} {J : Finset (Se
t α)},   MeasureTheory.IsSetSemiring C → ↑J ⊆ C → ∀ (j : ↥J), ∃ P, ↑P.parts ⊆ C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.MeasureTheory.IsSetSemiring
.disjointOfUnion_coe`：∀ {α : Type u_1} {C : Set (Set α)} {J : Finset (Set α)} (h
C : MeasureTheory.IsSetSemiring C) (hJ : ↑J ⊆ C) (j : ↥J),   hC.disjointOfUnion 
hJ…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma disjointOfUnion_subset (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) :
    (disjointOfUnion hC hJ j : Set (Set α)) ⊆ C := by
  lift j to J using hj
  rw [hC.disjointOfUnion_coe hJ]
  exact (hC.exists_partition_disjointed hJ j).choose_spec
/-
**MeasureTheory.IsSetSemiring.pairwiseDisjoint_disjointOfUnion_of_mem** 是 Mathli
b 中的一个引理，位于命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：pairwiseDisjoint_disjointOfUnion_of_mem (hC : IsSetSemiring C) (hJ : ↑J su
bseteq C) (hj : j in J) : PairwiseDisjoint (hC.disjointOfUnion hJ j : Set (Set α
)) id
参数：hC : IsSetSemiring C；hJ : ↑J subseteq C；hj : j in J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Finset.FinsetCoe.canLift`：∀ {α : Type u_1} (s : Finset α), CanLift α (↥s
) Subtype.val fun a => a ∈ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.MeasureTheory.IsSetSemiring
.exists_partition_disjointed`：∀ {α : Type u_1} {C : Set (Set α)} {J : Finset (Se
t α)},   MeasureTheory.IsSetSemiring C → ↑J ⊆ C → ∀ (j : ↥J), ∃ P, ↑P.parts ⊆ C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.MeasureTheory.IsSetSemiring
.disjointOfUnion_coe`：∀ {α : Type u_1} {C : Set (Set α)} {J : Finset (Set α)} (h
C : MeasureTheory.IsSetSemiring C) (hJ : ↑J ⊆ C) (j : ↥J),   hC.disjointOfUnion 
hJ…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.supIndep_iff_pairwiseDisjoint`：supIndep_iff_pairwiseDisjoint : s.
SupIndep f ↔ (s : Set ι).PairwiseDisjoint f
· 使用定理 `Finpartition.supIndep`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (self : Finpartition a), self.parts.SupIndep id
-/
lemma pairwiseDisjoint_disjointOfUnion_of_mem (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) :
    PairwiseDisjoint (hC.disjointOfUnion hJ j : Set (Set α)) id := by
  lift j to J using hj
  rw [disjointOfUnion_coe, ← supIndep_iff_pairwiseDisjoint]
  exact Finpartition.supIndep _
/-
**MeasureTheory.IsSetSemiring.pairwiseDisjoint_biUnion_disjointOfUnion** 是 Mathl
ib 中的一个引理，位于命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：pairwiseDisjoint_biUnion_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J s
ubseteq C) : PairwiseDisjoint (⋃ x in J, (hC.disjointOfUnion hJ x : Set (Set α))
) id
参数：hC : IsSetSemiring C；hJ : ↑J subseteq C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Set.PairwiseDisjoint.biUnion`：∀ {α : Type u_1} {ι : Type u_2} {ι' : Type
 u_3} [inst : CompleteLattice α] {s : Set ι'} {g : ι' → Set ι} {f : ι → α},   (s
.PairwiseDisjoint …
· 使用定理 `Pairwise.set_of_subtype`：∀ {α : Type u_1} (s : Set α) (r : α → α → Prop)
, (Pairwise fun x y => r ↑x ↑y) → s.Pairwise r
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.MeasureTheory.IsSetSemiring
.exists_partition_disjointed`：∀ {α : Type u_1} {C : Set (Set α)} {J : Finset (Se
t α)},   MeasureTheory.IsSetSemiring C → ↑J ⊆ C → ∀ (j : ↥J), ∃ P, ↑P.parts ⊆ C
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.MeasureTheory.IsSetSemiring
.disjointOfUnion_coe`：∀ {α : Type u_1} {C : Set (Set α)} {J : Finset (Set α)} (h
C : MeasureTheory.IsSetSemiring C) (hJ : ↑J ⊆ C) (j : ↥J),   hC.disjointOfUnion 
hJ…
· 使用定理 `Finpartition.sup_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Or
derBot α] {a : α} (self : Finpartition a), self.parts.sup id = a
· 使用引理 `Pairwise.comp_of_injective`：Pairwise.comp_of_injective (hr : Pairwise r)
 {f : β -> α} (hf : Injective f) : Pairwise (r on f)
· 使用定理 `disjoint_disjointed`：disjoint_disjointed (f : ι -> α) : Pairwise (Disjoi
nt on disjointed f)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用引理 `MeasureTheory.IsSetSemiring.pairwiseDisjoint_disjointOfUnion_of_mem`：pai
rwiseDisjoint_disjointOfUnion_of_mem (hC : IsSetSemiring C) (hJ : ↑J subseteq C)
 (hj : j in J) : PairwiseDisjoint (hC.disjointOfUnion hJ …
-/
lemma pairwiseDisjoint_biUnion_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    PairwiseDisjoint (⋃ x ∈ J, (hC.disjointOfUnion hJ x : Set (Set α))) id := by
  simp_rw [← SetLike.mem_coe]
  refine Set.PairwiseDisjoint.biUnion
    (Pairwise.set_of_subtype _ _ ?_)
    (fun _ ↦ hC.pairwiseDisjoint_disjointOfUnion_of_mem hJ)
  simp_rw [Function.onFun, disjointOfUnion_coe, SetLike.mem_coe, ← Finset.sup_eq_iSup,
    Finpartition.sup_parts]
  exact (disjoint_disjointed _).comp_of_injective J.equivFin.injective
/-
**MeasureTheory.IsSetSemiring.disjointOfUnion_subset_of_mem** 是 Mathlib 中的一个引理，位
于命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：disjointOfUnion_subset_of_mem (hC : IsSetSemiring C) (hJ : ↑J subseteq C) 
(hj : j in J) : ⋃₀ hC.disjointOfUnion hJ j subseteq j
参数：hC : IsSetSemiring C；hJ : ↑J subseteq C；hj : j in J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Finset.FinsetCoe.canLift`：∀ {α : Type u_1} (s : Finset α), CanLift α (↥s
) Subtype.val fun a => a ∈ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.MeasureTheory.IsSetSemiring
.exists_partition_disjointed`：∀ {α : Type u_1} {C : Set (Set α)} {J : Finset (Se
t α)},   MeasureTheory.IsSetSemiring C → ↑J ⊆ C → ∀ (j : ↥J), ∃ P, ↑P.parts ⊆ C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.MeasureTheory.IsSetSemiring
.disjointOfUnion_coe`：∀ {α : Type u_1} {C : Set (Set α)} {J : Finset (Set α)} (h
C : MeasureTheory.IsSetSemiring C) (hJ : ↑J ⊆ C) (j : ↥J),   hC.disjointOfUnion 
hJ…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_id_set_eq_sUnion`：sup_id_set_eq_sUnion (s : Finset (Set α)) :
 s.sup id = ⋃₀ ↑s
· 使用定理 `Finpartition.sup_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Or
derBot α] {a : α} (self : Finpartition a), self.parts.sup id = a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `disjointed_subset`：disjointed_subset [Preorder ι] [LocallyFiniteOrderBot
 ι] (f : ι -> Set α) (i : ι) : disjointed f i subseteq f i
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma disjointOfUnion_subset_of_mem (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) :
    ⋃₀ hC.disjointOfUnion hJ j ⊆ j := by
  lift j to J using hj
  grw [disjointOfUnion_coe, ← Finset.sup_id_set_eq_sUnion, Finpartition.sup_parts,
    disjointed_subset, Equiv.symm_apply_apply]
/-
**MeasureTheory.IsSetSemiring.subset_of_mem_disjointOfUnion** 是 Mathlib 中的一个引理，位
于命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：subset_of_mem_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J subseteq C) 
(hj : j in J) {x : Set α} (hx : x in (hC.disjointOfUnion hJ) j) : x subseteq j
参数：hC : IsSetSemiring C；hJ : ↑J subseteq C；hj : j in J；hx : x in (hC.disjointOfU
nion hJ) j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.sUnion_subset_iff`：sUnion_subset_iff {s : Set (Set α)} {t : Set α} :
 ⋃₀ s subseteq t ↔ forall t' in s, t' subseteq t
· 使用引理 `MeasureTheory.IsSetSemiring.disjointOfUnion_subset_of_mem`：disjointOfUni
on_subset_of_mem (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (hj : j in J) : ⋃₀ 
hC.disjointOfUnion hJ j subseteq j
-/
lemma subset_of_mem_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) {x : Set α}
    (hx : x ∈ (hC.disjointOfUnion hJ) j) : x ⊆ j :=
  sUnion_subset_iff.mp (hC.disjointOfUnion_subset_of_mem hJ hj) x hx
/-
**MeasureTheory.IsSetSemiring.empty_notMem_disjointOfUnion** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory.IsSetSemiring`。
形式化陈述：empty_notMem_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (
hj : j in J) : ∅ ∉ hC.disjointOfUnion hJ j
参数：hC : IsSetSemiring C；hJ : ↑J subseteq C；hj : j in J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Finset.FinsetCoe.canLift`：∀ {α : Type u_1} (s : Finset α), CanLift α (↥s
) Subtype.val fun a => a ∈ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.MeasureTheory.IsSetSemiring
.exists_partition_disjointed`：∀ {α : Type u_1} {C : Set (Set α)} {J : Finset (Se
t α)},   MeasureTheory.IsSetSemiring C → ↑J ⊆ C → ∀ (j : ↥J), ∃ P, ↑P.parts ⊆ C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.MeasureTheory.IsSetSemiring
.disjointOfUnion_coe`：∀ {α : Type u_1} {C : Set (Set α)} {J : Finset (Set α)} (h
C : MeasureTheory.IsSetSemiring C) (hJ : ↑J ⊆ C) (j : ↥J),   hC.disjointOfUnion 
hJ…
· 使用定理 `Finpartition.bot_notMem`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : O
rderBot α] {a : α} (self : Finpartition a), ⊥ ∉ self.parts
-/
lemma empty_notMem_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) :
    ∅ ∉ hC.disjointOfUnion hJ j := by
  lift j to J using hj
  rw [disjointOfUnion_coe]
  exact Finpartition.bot_notMem _
/-
**MeasureTheory.IsSetSemiring.sUnion_disjointOfUnion** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.IsSetSemiring`。
形式化陈述：sUnion_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J subseteq C) : ⋃₀ ⋃ 
x in J, (hC.disjointOfUnion hJ x : Set (Set α)) = ⋃₀ J
参数：hC : IsSetSemiring C；hJ : ↑J subseteq C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.sUnion_iUnion`：sUnion_iUnion (s : ι -> Set (Set α)) : ⋃₀ ⋃ i, s i = 
⋃ i, ⋃₀ s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.MeasureTheory.IsSetSemiring
.exists_partition_disjointed`：∀ {α : Type u_1} {C : Set (Set α)} {J : Finset (Se
t α)},   MeasureTheory.IsSetSemiring C → ↑J ⊆ C → ∀ (j : ↥J), ∃ P, ↑P.parts ⊆ C
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.MeasureTheory.IsSetSemiring
.disjointOfUnion_coe`：∀ {α : Type u_1} {C : Set (Set α)} {J : Finset (Set α)} (h
C : MeasureTheory.IsSetSemiring C) (hJ : ↑J ⊆ C) (j : ↥J),   hC.disjointOfUnion 
hJ…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finpartition.sup_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Or
derBot α] {a : α} (self : Finpartition a), self.parts.sup id = a
· 使用定理 `Function.Surjective.iSup_comp`：Function.Surjective.iSup_comp {f : ι -> ι
'} (hf : Surjective f) (g : ι' -> α) : ⨆ x, g (f x) = ⨆ y, g y
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `iSup_disjointed`：iSup_disjointed [PartialOrder ι] [LocallyFiniteOrderBot
 ι] (f : ι -> α) : ⨆ i, disjointed f i = ⨆ i, f i
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sUnion_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    ⋃₀ ⋃ x ∈ J, (hC.disjointOfUnion hJ x : Set (Set α)) = ⋃₀ J := by
  simp_rw [sUnion_iUnion, ← iSup_eq_iUnion, iSup_subtype', disjointOfUnion_coe,
    ← Finset.sup_id_set_eq_sUnion, Finpartition.sup_parts, J.equivFin.surjective.iSup_comp,
    iSup_disjointed, J.equivFin.symm.surjective.iSup_comp, iSup_subtype, Finset.sup_eq_iSup, id]
/-
**MeasureTheory.IsSetSemiring.disjointOfUnion_props** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.IsSetSemiring`。
形式化陈述：disjointOfUnion_props (hC : IsSetSemiring C) (h1 : ↑J subseteq C) : exists
 K : Set α -> Finset (Set α), PairwiseDisjoint J K ∧ (forall i in J, ↑(K i) subs
eteq C) ∧ PairwiseDisjoint (⋃ x in J, (K x : Set (Set α))) id ∧ (forall j in J, 
⋃₀ K j subseteq j) ∧ (forall j in J, ∅ ∉ K j) ∧ ⋃₀ J = ⋃₀ (⋃ x in J, (K x : Set 
(Set α)))
参数：hC : IsSetSemiring C；h1 : ↑J subseteq C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.IsSetSemiring.pairwiseDisjoint_disjointOfUnion`：pairwiseDi
sjoint_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J subseteq C) : PairwiseDis
joint J (hC.disjointOfUnion hJ)
· 使用引理 `MeasureTheory.IsSetSemiring.disjointOfUnion_subset`：disjointOfUnion_subs
et (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (hj : j in J) : (disjointOfUnion 
hC hJ j : Set (Set α)) subseteq C
· 使用引理 `MeasureTheory.IsSetSemiring.pairwiseDisjoint_biUnion_disjointOfUnion`：pa
irwiseDisjoint_biUnion_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J subseteq 
C) : PairwiseDisjoint (⋃ x in J, (hC.disjointOfUnion hJ x …
· 使用引理 `MeasureTheory.IsSetSemiring.disjointOfUnion_subset_of_mem`：disjointOfUni
on_subset_of_mem (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (hj : j in J) : ⋃₀ 
hC.disjointOfUnion hJ j subseteq j
· 使用引理 `MeasureTheory.IsSetSemiring.empty_notMem_disjointOfUnion`：empty_notMem_d
isjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (hj : j in J) : ∅ ∉ h
C.disjointOfUnion hJ j
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.IsSetSemiring.sUnion_disjointOfUnion`：sUnion_disjointOfUni
on (hC : IsSetSemiring C) (hJ : ↑J subseteq C) : ⋃₀ ⋃ x in J, (hC.disjointOfUnio
n hJ x : Set (Set α)) = ⋃₀ J
-/
theorem disjointOfUnion_props (hC : IsSetSemiring C) (h1 : ↑J ⊆ C) :
    ∃ K : Set α → Finset (Set α),
      PairwiseDisjoint J K
      ∧ (∀ i ∈ J, ↑(K i) ⊆ C)
      ∧ PairwiseDisjoint (⋃ x ∈ J, (K x : Set (Set α))) id
      ∧ (∀ j ∈ J, ⋃₀ K j ⊆ j)
      ∧ (∀ j ∈ J, ∅ ∉ K j)
      ∧ ⋃₀ J = ⋃₀ (⋃ x ∈ J, (K x : Set (Set α))) :=
  ⟨hC.disjointOfUnion h1,
   hC.pairwiseDisjoint_disjointOfUnion h1,
   fun _ ↦ hC.disjointOfUnion_subset h1,
   hC.pairwiseDisjoint_biUnion_disjointOfUnion h1,
   fun _ ↦ hC.disjointOfUnion_subset_of_mem h1,
   fun _ ↦ hC.empty_notMem_disjointOfUnion h1,
   (hC.sUnion_disjointOfUnion h1).symm⟩

end disjointOfUnion

/-
**MeasureTheory.IsSetSemiring._root_.Set.Ioc_mem_ofPred_Ioc_le** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory.IsSetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma _root_.Set.Ioc_mem_ofPred_Ioc_le [LinearOrder α] (u v : α) :
    Set.Ioc u v ∈ {s : Set α | ∃ u v, u ≤ v ∧ s = Set.Ioc u v} :=
  ⟨u, max u v, by grind, by grind⟩

/-- The set of open-closed intervals is a semi-ring of sets. -/
/-
**MeasureTheory.IsSetSemiring.Ioc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.IsSet
Semiring`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [Nonempty α], MeasureTheory.IsSetS
emiring {s | ∃ u v, u ≤ v ∧ s = Set.Ioc u v}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Ioc_inter_Ioc`：∀ {α : Type u_1} [inst : LinearOrder α] {a₁ a₂ b₁ b₂ 
: α},   Set.Ioc b₁ a₁ ∩ Set.Ioc b₂ a₂ = Set.Ioc (max b₁ b₂) (min a₁ a₂)
· 使用定理 `_private.Mathlib.MeasureTheory.SetSemiring.0.Set.Ioc_mem_ofPred_Ioc_le`：
∀ {α : Type u_1} [inst : LinearOrder α] (u v : α), Set.Ioc u v ∈ {s | ∃ u v, u ≤
 v ∧ s = Set.Ioc u v}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.sUnion_insert`：sUnion_insert (s : Set α) (T : Set (Set α)) : ⋃₀ inse
rt s T = s union ⋃₀ T
· 使用定理 `Set.sUnion_singleton`：sUnion_singleton (s : Set α) : ⋃₀ {s} = s

--- 原说明 ---
The set of open-closed intervals is a semi-ring of sets.
-/
protected lemma Ioc [LinearOrder α] [Nonempty α] :
    IsSetSemiring {s : Set α | ∃ u v, u ≤ v ∧ s = Set.Ioc u v} where
  empty_mem := by
    inhabit α
    exact ⟨default, default, le_rfl, by simp⟩
  inter_mem := by
    rintro s ⟨u, v, huv, rfl⟩ t ⟨u', v', hu'v', rfl⟩
    rw [Set.Ioc_inter_Ioc]
    apply Ioc_mem_ofPred_Ioc_le
  sdiff_eq_sUnion' := by
    rintro s ⟨u, v, huv, rfl⟩ t ⟨u', v', hu'v', rfl⟩
    rcases le_or_gt u' u with hu | hu
    · rcases Ioc_mem_ofPred_Ioc_le (max u v') v with ⟨u'', v'', h'', heq⟩
      exists {Set.Ioc u'' v''}
      grind [coe_singleton, pairwiseDisjoint_singleton]
    rcases le_or_gt v v' with hv | hv
    · rcases Ioc_mem_ofPred_Ioc_le u (min u' v) with ⟨u'', v'', h'', heq⟩
      exists {Set.Ioc u'' v''}
      grind [coe_singleton, pairwiseDisjoint_singleton]
    rw [show Set.Ioc u v \ Set.Ioc u' v' = Set.Ioc u u' ∪ Set.Ioc v' v by grind]
    refine ⟨{Set.Ioc u u', Set.Ioc v' v}, by grind, ?_, by simp⟩
    intro a ha b hb hab
    simp [Function.onFun]
    grind

end IsSetSemiring

end MeasureTheory

