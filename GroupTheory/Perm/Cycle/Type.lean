/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.GCDMonoid.Multiset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.List.Rotate
public import Mathlib.GroupTheory.Perm.Closure
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.Tactic.NormNum.GCD

/-!
# Cycle Types

In this file we define the cycle type of a permutation.

## Main definitions

- `Equiv.Perm.cycleType σ` where `σ` is a permutation of a `Fintype`
- `Equiv.Perm.partition σ` where `σ` is a permutation of a `Fintype`

## Main results

- `sum_cycleType` : The sum of `σ.cycleType` equals `σ.support.card`
- `lcm_cycleType` : The lcm of `σ.cycleType` equals `orderOf σ`
- `isConj_iff_cycleType_eq` : Two permutations are conjugate if and only if they have the same
  cycle type.
- `exists_prime_orderOf_dvd_card`: For every prime `p` dividing the order of a finite group `G`
  there exists an element of order `p` in `G`. This is known as Cauchy's theorem.
-/

@[expose] public section

open scoped Finset

namespace Equiv.Perm

open List (Vector)
open Equiv List Multiset

variable {α : Type*} [Fintype α]

section CycleType

variable [DecidableEq α]

/-- The cycle type of a permutation -/
/-
**Equiv.Perm.cycleType** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleType (σ : Perm α) : Multiset Nat
参数：σ : Perm α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cycle type of a permutation
-/
def cycleType (σ : Perm α) : Multiset ℕ :=
  σ.cycleFactorsFinset.1.map (Finset.card ∘ support)
/-
**Equiv.Perm.cycleType_def** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleType_def (σ : Perm α) : σ.cycleType = σ.cycleFactorsFinset.1.map (Fin
set.card ∘ support)
参数：σ : Perm α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cycleType_def (σ : Perm α) :
    σ.cycleType = σ.cycleFactorsFinset.1.map (Finset.card ∘ support) :=
  rfl
/-
**Equiv.Perm.cycleType_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleType_eq' {σ : Perm α} (s : Finset (Perm α)) (h1 : forall f : Perm α, 
f in s -> f.IsCycle) (h2 : (s : Set (Perm α)).Pairwise Disjoint) (h0 : s.noncomm
Prod id (h2.imp fun _ _ => Disjoint.commute) = σ) : σ.cycleType = s.1.map (Finse
t.card ∘ support)
参数：s : Finset (Perm α)；h1 : forall f : Perm α, f in s -> f.IsCycle；h2 : (s : Set
 (Perm α)).Pairwise Disjoint；h0 : s.noncommProd id (h2.imp fun _ _ => Disjoint.c
ommute) = σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.imp`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, s.P
airwise r → (∀ ⦃a b : α⦄, r a b → p a b) → s.Pairwise p
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleType_def`：cycleType_def (σ : Perm α) : σ.cycleType = σ.c
ycleFactorsFinset.1.map (Finset.card ∘ support)
· 使用定理 `Set.Pairwise.mono'`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, r
 ≤ p → s.Pairwise r → s.Pairwise p
· 使用定理 `Equiv.Perm.cycleFactorsFinset_eq_finset`：cycleFactorsFinset_eq_finset {σ
 : Perm α} {s : Finset (Perm α)} : σ.cycleFactorsFinset = s ↔ (forall f : Perm α
, f in s -> f.IsCycle) ∧ exis…
-/
theorem cycleType_eq' {σ : Perm α} (s : Finset (Perm α)) (h1 : ∀ f : Perm α, f ∈ s → f.IsCycle)
    (h2 : (s : Set (Perm α)).Pairwise Disjoint)
    (h0 : s.noncommProd id (h2.imp fun _ _ => Disjoint.commute) = σ) :
    σ.cycleType = s.1.map (Finset.card ∘ support) := by
  rw [cycleType_def]
  congr
  rw [cycleFactorsFinset_eq_finset]
  exact ⟨h1, h2, h0⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Equiv.Perm.cycleType_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleType_eq {σ : Perm α} (l : List (Perm α)) (h0 : l.prod = σ) (h1 : fora
ll σ : Perm α, σ in l -> σ.IsCycle) (h2 : l.Pairwise Disjoint) : σ.cycleType = l
.map (Finset.card ∘ support)
参数：l : List (Perm α)；h0 : l.prod = σ；h1 : forall σ : Perm α, σ in l -> σ.IsCycle
；h2 : l.Pairwise Disjoint。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.nodup_of_pairwise_disjoint_cycles`：nodup_of_pairwise_disjoint
_cycles {l : List (Perm β)} (h1 : forall f in l, IsCycle f) (h2 : l.Pairwise Dis
joint) : l.Nodup
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleType_eq'`：cycleType_eq' {σ : Perm α} (s : Finset (Perm α
)) (h1 : forall f : Perm α, f in s -> f.IsCycle) (h2 : (s : Set (Perm α)).Pairwi
se Disjoint) (…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.coe_toFinset`：coe_toFinset (l : List α) : (l.toFinset : Set α) = { 
a | a in l }
· 使用定理 `Equiv.Perm.Disjoint.stdSymm`：∀ {α : Type u_1}, Std.Symm Equiv.Perm.Disjo
int
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.Pairwise.imp`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, s.P
airwise r → (∀ ⦃a b : α⦄, r a b → p a b) → s.Pairwise p
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
· 使用定理 `Finset.noncommProd_congr`：noncommProd_congr {s₁ s₂ : Finset α} {f g : α 
-> β} (h₁ : s₁ = s₂) (h₂ : forall x in s₂, f x = g x) (comm) : noncommProd s₁ f 
comm = noncomm…
· 使用定理 `Finset.noncommProd_toFinset`：noncommProd_toFinset [DecidableEq α] (l : L
ist α) (f : α -> β) (comm) (hl : l.Nodup) : noncommProd l.toFinset f comm = (l.m
ap f).prod
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun'`：∀ {α : Type u_1}, (List.map fun a => a) = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.dedup_eq_self`：dedup_eq_self {l : List α} : dedup l = l ↔ Nodup l
-/
theorem cycleType_eq {σ : Perm α} (l : List (Perm α)) (h0 : l.prod = σ)
    (h1 : ∀ σ : Perm α, σ ∈ l → σ.IsCycle) (h2 : l.Pairwise Disjoint) :
    σ.cycleType = l.map (Finset.card ∘ support) := by
  have hl : l.Nodup := nodup_of_pairwise_disjoint_cycles h1 h2
  rw [cycleType_eq' l.toFinset]
  · simp [List.dedup_eq_self.mpr hl, Function.comp_def]
  · simpa using h1
  · simpa [hl] using h2
  · simp [hl, h0]

set_option backward.isDefEq.respectTransparency false in
/-
**Equiv.Perm.CycleType.count_def** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.CycleType
`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] {σ : Equiv.Pe
rm α} (n : ℕ),   Multiset.count n σ.cycleType = Fintype.card { c // (↑c).support
.card = n }
参数：n : ℕ；↑c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleType.eq_1`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 DecidableEq α] (σ : Equiv.Perm α),   σ.cycleType = Multiset.map (Finset.card ∘ 
Equiv.Perm.supp…
· 使用定理 `Multiset.count_eq_card_filter_eq`：count_eq_card_filter_eq [DecidableEq α
] (s : Multiset α) (a : α) : s.count a = card (s.filter (a = ·))
· 使用定理 `Fintype.subtype_card`：subtype_card {p : α -> Prop} (s : Finset α) (H : f
orall x : α, x in s ↔ p x) : @card { x // p x } (Fintype.subtype s H) = #s
· 使用定理 `Finset.univ_eq_attach`：Finset.univ_eq_attach {α : Type u} (s : Finset α)
 : (univ : Finset s) = s.attach
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `Subtype.map_injective`：map_injective {p : α -> Prop} {q : β -> Prop} {f 
: α -> β} (h : forall a, p a -> q (f a)) (hf : Injective f) : Injective (map f h
)
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用引理 `Finset.filter_attach'`：filter_attach' [DecidableEq α] (s : Finset α) (p 
: s -> Prop) [DecidablePred p] : s.attach.filter p = (s.filter fun x => exists h
, p ⟨x, h⟩)…
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.card_attach`：card_attach : #s.attach = #s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p
_1 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Multis
et α),       s =…
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.filter_map`：filter_map (f : β -> α) (s : Multiset β) : filter p
 (map f s) = map f (filter (p ∘ f) s)
· 使用定理 `Multiset.filter_congr`：filter_congr {p q : α -> Prop} [DecidablePred p] 
[DecidablePred q] {s : Multiset α} : (forall x in s, p x ↔ q x) -> filter p s = 
filter q s
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.mem_val`：mem_val {a : α} {s : Finset α} : (a in s.1) = (a in s)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem CycleType.count_def {σ : Perm α} (n : ℕ) :
    σ.cycleType.count n =
      Fintype.card {c : σ.cycleFactorsFinset // #(c : Perm α).support = n } := by
  -- work on the LHS
  rw [cycleType, Multiset.count_eq_card_filter_eq]
  -- rewrite the `Fintype.card` as a `Finset.card`
  rw [Fintype.subtype_card, Finset.univ_eq_attach, Finset.filter_attach',
    Finset.card_map, Finset.card_attach]
  simp only [Function.comp_apply, Finset.card, Finset.filter_val,
    Multiset.filter_map, Multiset.card_map]
  congr 1
  apply Multiset.filter_congr
  intro d h
  simp only [eq_comm, Finset.mem_val.mp h, exists_const]

@[simp]
/-
**Equiv.Perm.cycleType_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleType_eq_zero {σ : Perm α} : σ.cycleType = 0 ↔ σ = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cycleType_eq_zero {σ : Perm α} : σ.cycleType = 0 ↔ σ = 1 := by
  simp [cycleType_def, cycleFactorsFinset_eq_empty_iff]

@[simp]
/-
**Equiv.Perm.cycleType_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleType_one : (1 : Perm α).cycleType = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.cycleType_eq_zero`：cycleType_eq_zero {σ : Perm α} : σ.cycleTy
pe = 0 ↔ σ = 1
-/
theorem cycleType_one : (1 : Perm α).cycleType = 0 := cycleType_eq_zero.2 rfl
/-
**Equiv.Perm.card_cycleType_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：card_cycleType_eq_zero {σ : Perm α} : Multiset.card σ.cycleType = 0 ↔ σ = 
1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_eq_zero`：card_eq_zero {s : Multiset α} : card s = 0 ↔ s = 
0
· 使用定理 `Equiv.Perm.cycleType_eq_zero`：cycleType_eq_zero {σ : Perm α} : σ.cycleTy
pe = 0 ↔ σ = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem card_cycleType_eq_zero {σ : Perm α} : Multiset.card σ.cycleType = 0 ↔ σ = 1 := by
  rw [card_eq_zero, cycleType_eq_zero]
/-
**Equiv.Perm.card_cycleType_pos** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：card_cycleType_pos {σ : Perm α} : 0 < Multiset.card σ.cycleType ↔ σ != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Equiv.Perm.card_cycleType_eq_zero`：card_cycleType_eq_zero {σ : Perm α} :
 Multiset.card σ.cycleType = 0 ↔ σ = 1
-/
theorem card_cycleType_pos {σ : Perm α} : 0 < Multiset.card σ.cycleType ↔ σ ≠ 1 :=
  pos_iff_ne_zero.trans card_cycleType_eq_zero.not
/-
**Equiv.Perm.two_le_of_mem_cycleType** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：two_le_of_mem_cycleType {σ : Perm α} {n : Nat} (h : n in σ.cycleType) : 2 
<= n
参数：h : n in σ.cycleType。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.Perm.IsCycle.two_le_card_support`：∀ {α : Type u_2} {f : Equiv.Perm
 α} [inst : DecidableEq α] [inst_1 : Fintype α], f.IsCycle → 2 ≤ f.support.card
-/
theorem two_le_of_mem_cycleType {σ : Perm α} {n : ℕ} (h : n ∈ σ.cycleType) : 2 ≤ n := by
  simp only [cycleType_def, ← Finset.mem_def, Function.comp_apply, Multiset.mem_map,
    mem_cycleFactorsFinset_iff] at h
  obtain ⟨_, ⟨hc, -⟩, rfl⟩ := h
  exact hc.two_le_card_support
/-
**Equiv.Perm.one_lt_of_mem_cycleType** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：one_lt_of_mem_cycleType {σ : Perm α} {n : Nat} (h : n in σ.cycleType) : 1 
< n
参数：h : n in σ.cycleType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.two_le_of_mem_cycleType`：two_le_of_mem_cycleType {σ : Perm α}
 {n : Nat} (h : n in σ.cycleType) : 2 <= n
-/
theorem one_lt_of_mem_cycleType {σ : Perm α} {n : ℕ} (h : n ∈ σ.cycleType) : 1 < n :=
  two_le_of_mem_cycleType h
/-
**Equiv.Perm.IsCycle.cycleType** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] {σ : Equiv.Pe
rm α},   σ.IsCycle → σ.cycleType = {σ.support.card}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.cycleType_eq`：cycleType_eq {σ : Perm α} (l : List (Perm α)) (
h0 : l.prod = σ) (h1 : forall σ : Perm α, σ in l -> σ.IsCycle) (h2 : l.Pairwise 
Disjoint) : σ…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_singleton`：∀ {α : Type u_1} {a b : α}, a ∈ [b] ↔ a = b
· 使用定理 `List.pairwise_singleton`：∀ {α : Type u_1} (R : α → α → Prop) (a : α), Li
st.Pairwise R [a]
-/
theorem IsCycle.cycleType {σ : Perm α} (hσ : IsCycle σ) : σ.cycleType = {#σ.support} :=
  cycleType_eq [σ] (mul_one σ) (fun _τ hτ => (congr_arg IsCycle (List.mem_singleton.mp hτ)).mpr hσ)
    (List.pairwise_singleton Disjoint σ)
/-
**Equiv.Perm.card_cycleType_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：card_cycleType_eq_one {σ : Perm α} : Multiset.card σ.cycleType = 1 ↔ σ.IsC
ycle
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_eq_one`：card_eq_one {s : Multiset α} : card s = 1 ↔ exists
 a, s = {a}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem card_cycleType_eq_one {σ : Perm α} : Multiset.card σ.cycleType = 1 ↔ σ.IsCycle := by
  rw [card_eq_one]
  simp_rw [cycleType_def, Multiset.map_eq_singleton, ← Finset.singleton_val, Finset.val_inj,
    cycleFactorsFinset_eq_singleton_iff]
  grind
/-
**Equiv.Perm.Disjoint.cycleType_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Disjoi
nt`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] {σ τ : Equiv.
Perm α},   σ.Disjoint τ → (σ * τ).cycleType = σ.cycleType + τ.cycleType
参数：σ * τ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleType_def`：cycleType_def (σ : Perm α) : σ.cycleType = σ.c
ycleFactorsFinset.1.map (Finset.card ∘ support)
· 使用定理 `Equiv.Perm.Disjoint.cycleFactorsFinset_mul_eq_union`：∀ {α : Type u_2} [i
nst : DecidableEq α] [inst_1 : Fintype α] {f g : Equiv.Perm α},   f.Disjoint g →
 (f * g).cycleFactorsFinset = f.cycleFact…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `Finset.union_val`：union_val (s t : Finset α) : (s union t).1 = s.1 union
 t.1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.add_eq_union_iff_disjoint`：add_eq_union_iff_disjoint [Decidable
Eq α] {s t : Multiset α} : s + t = s union t ↔ Disjoint s t
· 使用定理 `Finset.disjoint_val`：disjoint_val : Disjoint s.1 t.1 ↔ Disjoint s t
· 使用定理 `Equiv.Perm.Disjoint.disjoint_cycleFactorsFinset`：∀ {α : Type u_2} [inst 
: DecidableEq α] [inst_1 : Fintype α] {f g : Equiv.Perm α},   f.Disjoint g → Dis
joint f.cycleFactorsFinset g.cycleFac…
-/
theorem Disjoint.cycleType_mul {σ τ : Perm α} (h : Disjoint σ τ) :
    (σ * τ).cycleType = σ.cycleType + τ.cycleType := by
  rw [cycleType_def, cycleType_def, cycleType_def, h.cycleFactorsFinset_mul_eq_union, ←
    Multiset.map_add, Finset.union_val, Multiset.add_eq_union_iff_disjoint.mpr _]
  exact Finset.disjoint_val.2 h.disjoint_cycleFactorsFinset

@[simp]
/-
**Equiv.Perm.cycleType_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleType_inv (σ : Perm α) : σ⁻¹.cycleType = σ.cycleType
参数：σ : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.cycle_induction_on`：cycle_induction_on [Finite β] (P : Perm β
 -> Prop) (σ : Perm β) (base_one : P 1) (base_cycles : forall σ : Perm β, σ.IsCy
cle -> P σ) (induct…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.IsCycle.cycleType`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : DecidableEq α] {σ : Equiv.Perm α},   σ.IsCycle → σ.cycleType = {σ.support.ca
rd}
· 使用定理 `Equiv.Perm.IsCycle.inv`：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsCycle →
 f⁻¹.IsCycle
· 使用定理 `Equiv.Perm.support_inv`：support_inv (σ : Perm α) : support σ⁻¹ = σ.suppo
rt
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.cycleType.congr_simp`：∀ {α : Type u_1} [inst : Fintype α] {in
st_1 : DecidableEq α} [inst_2 : DecidableEq α] (σ σ_1 : Equiv.Perm α),   σ = σ_1
 → σ.cycleType = σ_1.…
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Equiv.Perm.Disjoint.cycleType_mul`：∀ {α : Type u_1} [inst : Fintype α] [
inst_1 : DecidableEq α] {σ τ : Equiv.Perm α},   σ.Disjoint τ → (σ * τ).cycleType
 = σ.cycleType + τ.cycl…
· 使用定理 `Equiv.Perm.Disjoint.inv_right`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.
Disjoint g → f.Disjoint g⁻¹
· 使用定理 `Equiv.Perm.Disjoint.inv_left`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.D
isjoint g → f⁻¹.Disjoint g
· 使用定理 `Equiv.Perm.Disjoint.symm`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Disjo
int g → g.Disjoint f
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem cycleType_inv (σ : Perm α) : σ⁻¹.cycleType = σ.cycleType :=
  cycle_induction_on (P := fun τ : Perm α => τ⁻¹.cycleType = τ.cycleType) σ rfl
    (fun σ hσ => by simp only [hσ.cycleType, hσ.inv.cycleType, support_inv])
    fun σ τ hστ _ hσ hτ => by
      simp only [mul_inv_rev, hστ.cycleType_mul, hστ.symm.inv_left.inv_right.cycleType_mul, hσ, hτ,
        add_comm]

@[simp]
/-
**Equiv.Perm.cycleType_conj** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleType_conj {σ τ : Perm α} : (τ * σ * τ⁻¹).cycleType = σ.cycleType
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.cycle_induction_on`：cycle_induction_on [Finite β] (P : Perm β
 -> Prop) (σ : Perm β) (base_one : P 1) (base_cycles : forall σ : Perm β, σ.IsCy
cle -> P σ) (induct…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleType.congr_simp`：∀ {α : Type u_1} [inst : Fintype α] {in
st_1 : DecidableEq α} [inst_2 : DecidableEq α] (σ σ_1 : Equiv.Perm α),   σ = σ_1
 → σ.cycleType = σ_1.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `Equiv.Perm.cycleType_one`：cycleType_one : (1 : Perm α).cycleType = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.IsCycle.cycleType`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : DecidableEq α] {σ : Equiv.Perm α},   σ.IsCycle → σ.cycleType = {σ.support.ca
rd}
· 使用定理 `Equiv.Perm.IsCycle.conj`：∀ {α : Type u_2} {f g : Equiv.Perm α}, f.IsCycl
e → (g * f * g⁻¹).IsCycle
· 使用定理 `Equiv.Perm.card_support_conj`：card_support_conj : #(σ * τ * σ⁻¹).support
 = #τ.support
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `conj_mul`：conj_mul {a b c : α} : b * a * b⁻¹ * (b * c * b⁻¹) = b * (a * 
c) * b⁻¹
· 使用定理 `Equiv.Perm.Disjoint.cycleType_mul`：∀ {α : Type u_1} [inst : Fintype α] [
inst_1 : DecidableEq α] {σ τ : Equiv.Perm α},   σ.Disjoint τ → (σ * τ).cycleType
 = σ.cycleType + τ.cycl…
· 使用定理 `Equiv.Perm.Disjoint.conj`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Disjo
int g → ∀ (h : Equiv.Perm α), (h * f * h⁻¹).Disjoint (h * g * h⁻¹)
-/
theorem cycleType_conj {σ τ : Perm α} : (τ * σ * τ⁻¹).cycleType = σ.cycleType := by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => rw [hσ.cycleType, hσ.conj.cycleType, card_support_conj]
  | induction_disjoint σ π hd _ hσ hπ =>
    rw [← conj_mul, hd.cycleType_mul, (hd.conj _).cycleType_mul, hσ, hπ]
/-
**Equiv.Perm.sum_cycleType** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sum_cycleType (σ : Perm α) : σ.cycleType.sum = #σ.support
参数：σ : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.cycle_induction_on`：cycle_induction_on [Finite β] (P : Perm β
 -> Prop) (σ : Perm β) (base_one : P 1) (base_cycles : forall σ : Perm β, σ.IsCy
cle -> P σ) (induct…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleType_one`：cycleType_one : (1 : Perm α).cycleType = 0
· 使用定理 `Equiv.Perm.support_one`：support_one : (1 : Perm α).support = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.IsCycle.cycleType`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : DecidableEq α] {σ : Equiv.Perm α},   σ.IsCycle → σ.cycleType = {σ.support.ca
rd}
· 使用定理 `Multiset.sum_singleton`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M
), {a}.sum = a
· 使用定理 `Equiv.Perm.Disjoint.cycleType_mul`：∀ {α : Type u_1} [inst : Fintype α] [
inst_1 : DecidableEq α] {σ τ : Equiv.Perm α},   σ.Disjoint τ → (σ * τ).cycleType
 = σ.cycleType + τ.cycl…
· 使用定理 `Multiset.sum_add`：∀ {M : Type u_5} [inst : AddCommMonoid M] (s t : Multi
set M), (s + t).sum = s.sum + t.sum
· 使用定理 `Equiv.Perm.Disjoint.card_support_mul`：∀ {α : Type u_1} [inst : Decidable
Eq α] [inst_1 : Fintype α] {f g : Equiv.Perm α},   f.Disjoint g → (f * g).suppor
t.card = f.support.card + …
-/
theorem sum_cycleType (σ : Perm α) : σ.cycleType.sum = #σ.support := by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => rw [hσ.cycleType, Multiset.sum_singleton]
  | induction_disjoint σ τ hd _ hσ hτ => rw [hd.cycleType_mul, sum_add, hσ, hτ, hd.card_support_mul]
/-
**Equiv.Perm.sum_cycleType_le** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sum_cycleType_le (σ : Perm α) : σ.cycleType.sum <= Fintype.card α
参数：σ : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.sum_cycleType`：sum_cycleType (σ : Perm α) : σ.cycleType.sum =
 #σ.support
-/
theorem sum_cycleType_le (σ : Perm α) : σ.cycleType.sum ≤ Fintype.card α :=
  σ.sum_cycleType ▸ Finset.card_le_univ σ.support
/-
**Equiv.Perm.card_fixedPoints** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：card_fixedPoints (σ : Equiv.Perm α) : Fintype.card (Function.fixedPoints σ
) = Fintype.card α - σ.cycleType.sum
参数：σ : Equiv.Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.sum_cycleType`：sum_cycleType (σ : Perm α) : σ.cycleType.sum =
 #σ.support
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem card_fixedPoints (σ : Equiv.Perm α) :
    Fintype.card (Function.fixedPoints σ) = Fintype.card α - σ.cycleType.sum := by
  rw [Equiv.Perm.sum_cycleType, ← Finset.card_compl, Fintype.card_ofFinset]
  congr; aesop
/-
**Equiv.Perm.sign_of_cycleType'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_of_cycleType' (σ : Perm α) : sign σ = (σ.cycleType.map fun n => -(-1 
: Intˣ) ^ n).prod
参数：σ : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.cycle_induction_on`：cycle_induction_on [Finite β] (P : Perm β
 -> Prop) (σ : Perm β) (base_one : P 1) (base_cycles : forall σ : Perm β, σ.IsCy
cle -> P σ) (induct…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.sign_one`：sign_one : sign (1 : Perm α) = 1
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Equiv.Perm.cycleType_one`：cycleType_one : (1 : Perm α).cycleType = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.IsCycle.sign`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1
 : Fintype α] {f : Equiv.Perm α},   f.IsCycle → Equiv.Perm.sign f = -(-1) ^ f.su
pport.card
· 使用定理 `Equiv.Perm.IsCycle.cycleType`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : DecidableEq α] {σ : Equiv.Perm α},   σ.IsCycle → σ.cycleType = {σ.support.ca
rd}
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `Equiv.Perm.sign_mul`：sign_mul (f g : Perm α) : sign (f * g) = sign f * s
ign g
· 使用定理 `Equiv.Perm.Disjoint.cycleType_mul`：∀ {α : Type u_1} [inst : Fintype α] [
inst_1 : DecidableEq α] {σ τ : Equiv.Perm α},   σ.Disjoint τ → (σ * τ).cycleType
 = σ.cycleType + τ.cycl…
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `Multiset.prod_add`：prod_add (s t : Multiset M) : prod (s + t) = prod s *
 prod t
-/
theorem sign_of_cycleType' (σ : Perm α) :
    sign σ = (σ.cycleType.map fun n => -(-1 : ℤˣ) ^ n).prod := by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => simp [hσ.cycleType, hσ.sign]
  | induction_disjoint σ τ hd _ hσ hτ => simp [hσ, hτ, hd.cycleType_mul]
/-
**Equiv.Perm.sign_of_cycleType** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_of_cycleType (f : Perm α) : sign f = (-1 : Intˣ) ^ (f.cycleType.sum +
 Multiset.card f.cycleType)
参数：f : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.sign_of_cycleType'`：sign_of_cycleType' (σ : Perm α) : sign σ 
= (σ.cycleType.map fun n => -(-1 : Intˣ) ^ n).prod
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `Multiset.card_cons`：card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) 
= card s + 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sign_of_cycleType (f : Perm α) :
    sign f = (-1 : ℤˣ) ^ (f.cycleType.sum + Multiset.card f.cycleType) := by
  rw [sign_of_cycleType']
  induction f.cycleType using Multiset.induction_on with
  | empty => rfl
  | cons a s ihs =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, Multiset.card_cons, ihs]
    simp only [pow_add, pow_one, neg_mul, mul_neg, mul_assoc, mul_one]

@[simp]
/-
**Equiv.Perm.lcm_cycleType** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：lcm_cycleType (σ : Perm α) : σ.cycleType.lcm = orderOf σ
参数：σ : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.cycle_induction_on`：cycle_induction_on [Finite β] (P : Perm β
 -> Prop) (σ : Perm β) (base_one : P 1) (base_cycles : forall σ : Perm β, σ.IsCy
cle -> P σ) (induct…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleType_one`：cycleType_one : (1 : Perm α).cycleType = 0
· 使用定理 `Multiset.lcm_zero`：lcm_zero : (0 : Multiset α).lcm = 1
· 使用定理 `orderOf_one`：orderOf_one : orderOf (1 : G) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.IsCycle.cycleType`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : DecidableEq α] {σ : Equiv.Perm α},   σ.IsCycle → σ.cycleType = {σ.support.ca
rd}
· 使用定理 `Multiset.lcm_singleton`：lcm_singleton {a : α} : ({a} : Multiset α).lcm =
 normalize a
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Equiv.Perm.IsCycle.orderOf`：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : 
DecidableEq α] [inst_1 : Fintype α], f.IsCycle → orderOf f = f.support.card
· 使用定理 `Equiv.Perm.Disjoint.cycleType_mul`：∀ {α : Type u_1} [inst : Fintype α] [
inst_1 : DecidableEq α] {σ τ : Equiv.Perm α},   σ.Disjoint τ → (σ * τ).cycleType
 = σ.cycleType + τ.cycl…
· 使用定理 `Multiset.lcm_add`：lcm_add (s₁ s₂ : Multiset α) : (s₁ + s₂).lcm = GCDMono
id.lcm s₁.lcm s₂.lcm
· 使用定理 `Equiv.Perm.Disjoint.orderOf`：∀ {α : Type u} {σ τ : Equiv.Perm α}, σ.Disj
oint τ → orderOf (σ * τ) = (orderOf σ).lcm (orderOf τ)
-/
theorem lcm_cycleType (σ : Perm α) : σ.cycleType.lcm = orderOf σ := by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => simp [hσ.cycleType, hσ.orderOf]
  | induction_disjoint σ τ hd _ hσ hτ => simp [hd.cycleType_mul, hd.orderOf, lcm_eq_nat_lcm, hσ, hτ]
/-
**Equiv.Perm.dvd_of_mem_cycleType** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：dvd_of_mem_cycleType {σ : Perm α} {n : Nat} (h : n in σ.cycleType) : n ∣ o
rderOf σ
参数：h : n in σ.cycleType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.lcm_cycleType`：lcm_cycleType (σ : Perm α) : σ.cycleType.lcm =
 orderOf σ
· 使用定理 `Multiset.dvd_lcm`：dvd_lcm {s : Multiset α} {a : α} (h : a in s) : a ∣ s.
lcm
-/
theorem dvd_of_mem_cycleType {σ : Perm α} {n : ℕ} (h : n ∈ σ.cycleType) : n ∣ orderOf σ := by
  rw [← lcm_cycleType]
  exact dvd_lcm h
/-
**Equiv.Perm.orderOf_cycleOf_dvd_orderOf** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：orderOf_cycleOf_dvd_orderOf (f : Perm α) (x : α) : orderOf (cycleOf f x) ∣
 orderOf f
参数：f : Perm α；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.cycleOf_eq_one_iff`：cycleOf_eq_one_iff (f : Perm α) [Decidabl
eRel f.SameCycle] : cycleOf f x = 1 ↔ f x = x
· 使用定理 `orderOf_one`：orderOf_one : orderOf (1 : G) = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.dvd_of_mem_cycleType`：dvd_of_mem_cycleType {σ : Perm α} {n : 
Nat} (h : n in σ.cycleType) : n ∣ orderOf σ
· 使用定理 `Equiv.Perm.cycleType.eq_1`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 DecidableEq α] (σ : Equiv.Perm α),   σ.cycleType = Multiset.map (Finset.card ∘ 
Equiv.Perm.supp…
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Finset.mem_def`：mem_def {a : α} {s : Finset α} : a in s ↔ a in s.1
· 使用定理 `Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff`：cycleOf_mem_cycleFactorsF
inset_iff {f : Perm α} {x : α} : cycleOf f x in cycleFactorsFinset f ↔ x in f.su
pport
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Equiv.Perm.IsCycle.orderOf`：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : 
DecidableEq α] [inst_1 : Fintype α], f.IsCycle → orderOf f = f.support.card
· 使用定理 `Equiv.Perm.isCycle_cycleOf`：isCycle_cycleOf (f : Perm α) [DecidableRel f
.SameCycle] (hx : f x != x) : IsCycle (cycleOf f x)
-/
theorem orderOf_cycleOf_dvd_orderOf (f : Perm α) (x : α) : orderOf (cycleOf f x) ∣ orderOf f := by
  by_cases hx : f x = x
  · rw [← cycleOf_eq_one_iff] at hx
    simp [hx]
  · refine dvd_of_mem_cycleType ?_
    rw [cycleType, Multiset.mem_map]
    refine ⟨f.cycleOf x, ?_, ?_⟩
    · rwa [← Finset.mem_def, cycleOf_mem_cycleFactorsFinset_iff, mem_support]
    · simp [(isCycle_cycleOf _ hx).orderOf]
/-
**Equiv.Perm.two_dvd_card_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：two_dvd_card_support {σ : Perm α} (hσ : σ ^ 2 = 1) : 2 ∣ #σ.support
参数：hσ : σ ^ 2 = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.Perm.sum_cycleType`：sum_cycleType (σ : Perm α) : σ.cycleType.sum =
 #σ.support
· 使用引理 `Multiset.dvd_sum`：dvd_sum : (forall x in s, a ∣ x) -> a ∣ s.sum
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Equiv.Perm.dvd_of_mem_cycleType`：dvd_of_mem_cycleType {σ : Perm α} {n : 
Nat} (h : n in σ.cycleType) : n ∣ orderOf σ
· 使用定理 `orderOf_dvd_of_pow_eq_one`：orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : o
rderOf x ∣ n
· 使用定理 `Equiv.Perm.two_le_of_mem_cycleType`：two_le_of_mem_cycleType {σ : Perm α}
 {n : Nat} (h : n in σ.cycleType) : 2 <= n
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
-/
theorem two_dvd_card_support {σ : Perm α} (hσ : σ ^ 2 = 1) : 2 ∣ #σ.support :=
  (congr_arg (Dvd.dvd 2) σ.sum_cycleType).mp
    (Multiset.dvd_sum fun n hn => by
      rw [_root_.le_antisymm
          (Nat.le_of_dvd zero_lt_two <|
            (dvd_of_mem_cycleType hn).trans <| orderOf_dvd_of_pow_eq_one hσ)
          (two_le_of_mem_cycleType hn)])
/-
**Equiv.Perm.cycleType_prime_order** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleType_prime_order {σ : Perm α} (hσ : (orderOf σ).Prime) : exists n : N
at, σ.cycleType = Multiset.replicate (n + 1) (orderOf σ)
参数：hσ : (orderOf σ).Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.eq_replicate`：eq_replicate {a : α} {n} {s : Multiset α} : s = r
eplicate n a ↔ card s = n ∧ forall b in s, b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Equiv.Perm.card_cycleType_pos`：card_cycleType_pos {σ : Perm α} : 0 < Mul
tiset.card σ.cycleType ↔ σ != 1
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `orderOf_eq_one_iff`：orderOf_eq_one_iff : orderOf x = 1 ↔ x = 1
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Nat.Prime.eq_one_or_self_of_dvd`：∀ {p : ℕ}, Nat.Prime p → ∀ (m : ℕ), m ∣
 p → m = 1 ∨ m = p
· 使用定理 `Equiv.Perm.dvd_of_mem_cycleType`：dvd_of_mem_cycleType {σ : Perm α} {n : 
Nat} (h : n in σ.cycleType) : n ∣ orderOf σ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Equiv.Perm.one_lt_of_mem_cycleType`：one_lt_of_mem_cycleType {σ : Perm α}
 {n : Nat} (h : n in σ.cycleType) : 1 < n
-/
theorem cycleType_prime_order {σ : Perm α} (hσ : (orderOf σ).Prime) :
    ∃ n : ℕ, σ.cycleType = Multiset.replicate (n + 1) (orderOf σ) := by
  refine ⟨Multiset.card σ.cycleType - 1, eq_replicate.2 ⟨?_, fun n hn ↦ ?_⟩⟩
  · rw [tsub_add_cancel_of_le]
    rw [Nat.succ_le_iff, card_cycleType_pos, Ne, ← orderOf_eq_one_iff]
    exact hσ.ne_one
  · exact (hσ.eq_one_or_self_of_dvd n (dvd_of_mem_cycleType hn)).resolve_left
      (one_lt_of_mem_cycleType hn).ne'
/-
**Equiv.Perm.pow_prime_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：pow_prime_eq_one_iff {σ : Perm α} {p : Nat} [hp : Fact (Nat.Prime p)] : σ 
^ p = 1 ↔ forall c in σ.cycleType, c = p
参数：Nat.Prime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `orderOf_dvd_iff_pow_eq_one`：orderOf_dvd_iff_pow_eq_one {n : Nat} : order
Of x ∣ n ↔ x ^ n = 1
· 使用定理 `Equiv.Perm.lcm_cycleType`：lcm_cycleType (σ : Perm α) : σ.cycleType.lcm =
 orderOf σ
· 使用定理 `Multiset.lcm_dvd`：lcm_dvd {s : Multiset α} {a : α} : s.lcm ∣ a ↔ forall 
b in s, b ∣ a
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Nat.Prime.eq_one_or_self_of_dvd`：∀ {p : ℕ}, Nat.Prime p → ∀ (m : ℕ), m ∣
 p → m = 1 ∨ m = p
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
· 使用定理 `Nat.ne_of_lt'`：∀ {a b : ℕ}, a < b → b ≠ a
· 使用定理 `Equiv.Perm.one_lt_of_mem_cycleType`：one_lt_of_mem_cycleType {σ : Perm α}
 {n : Nat} (h : n in σ.cycleType) : 1 < n
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
-/
theorem pow_prime_eq_one_iff {σ : Perm α} {p : ℕ} [hp : Fact (Nat.Prime p)] :
    σ ^ p = 1 ↔ ∀ c ∈ σ.cycleType, c = p := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← lcm_cycleType, Multiset.lcm_dvd]
  apply forall_congr'
  exact fun c ↦ ⟨fun hc h ↦ Or.resolve_left (hp.elim.eq_one_or_self_of_dvd c (hc h))
       (Nat.ne_of_lt' (one_lt_of_mem_cycleType h)),
     fun hc h ↦ by rw [hc h]⟩
/-
**Equiv.Perm.cycleType_of_pow_prime_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm
`。
形式化陈述：cycleType_of_pow_prime_eq_one {σ : Perm α} {p : Nat} [Fact (Nat.Prime p)] 
(hσ : σ ^ p = 1) : σ.cycleType = Multiset.replicate σ.cycleType.card p
参数：Nat.Prime p；hσ : σ ^ p = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.eq_replicate`：eq_replicate {a : α} {n} {s : Multiset α} : s = r
eplicate n a ↔ card s = n ∧ forall b in s, b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.pow_prime_eq_one_iff`：pow_prime_eq_one_iff {σ : Perm α} {p : 
Nat} [hp : Fact (Nat.Prime p)] : σ ^ p = 1 ↔ forall c in σ.cycleType, c = p
-/
theorem cycleType_of_pow_prime_eq_one {σ : Perm α} {p : ℕ} [Fact (Nat.Prime p)] (hσ : σ ^ p = 1) :
    σ.cycleType = Multiset.replicate σ.cycleType.card p :=
  Multiset.eq_replicate.mpr ⟨rfl, pow_prime_eq_one_iff.mp hσ⟩
/-
**Equiv.Perm.isCycle_of_prime_order** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isCycle_of_prime_order {σ : Perm α} (h1 : (orderOf σ).Prime) (h2 : #σ.supp
ort < 2 * orderOf σ) : σ.IsCycle
参数：h1 : (orderOf σ).Prime；h2 : #σ.support < 2 * orderOf σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.cycleType_prime_order`：cycleType_prime_order {σ : Perm α} (hσ
 : (orderOf σ).Prime) : exists n : Nat, σ.cycleType = Multiset.replicate (n + 1)
 (orderOf σ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.card_cycleType_eq_one`：card_cycleType_eq_one {σ : Perm α} : M
ultiset.card σ.cycleType = 1 ↔ σ.IsCycle
· 使用定理 `Multiset.card_replicate`：∀ {α : Type u_1} (n : ℕ) (a : α), (Multiset.rep
licate n a).card = n
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Nat.succ_lt_succ_iff`：∀ {a b : ℕ}, a.succ < b.succ ↔ a < b
· 使用定理 `mul_lt_mul_iff_left₀`：mul_lt_mul_iff_left₀ [MulPosStrictMono α] [MulPosR
eflectLT α] (a0 : 0 < a) : b * a < c * a ↔ b < c where mp h
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用引理 `orderOf_pos`：orderOf_pos (x : G) : 0 < orderOf x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Nat.cast_id`：Nat.cast_id (n : Nat) : n.cast = n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Multiset.sum_replicate`：∀ {M : Type u_3} [inst : AddCommMonoid M] (n : ℕ
) (a : M), (Multiset.replicate n a).sum = n • a
· 使用定理 `Equiv.Perm.sum_cycleType`：sum_cycleType (σ : Perm α) : σ.cycleType.sum =
 #σ.support
-/
theorem isCycle_of_prime_order {σ : Perm α} (h1 : (orderOf σ).Prime)
    (h2 : #σ.support < 2 * orderOf σ) : σ.IsCycle := by
  obtain ⟨n, hn⟩ := cycleType_prime_order h1
  rw [← σ.sum_cycleType, hn, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id,
    mul_lt_mul_iff_left₀ (orderOf_pos σ), Nat.succ_lt_succ_iff, Nat.lt_succ_iff, Nat.le_zero] at h2
  rw [← card_cycleType_eq_one, hn, card_replicate, h2]
/-
**Equiv.Perm.cycleType_le_of_mem_cycleFactorsFinset** 是 Mathlib 中的一个定理，位于命名空间 `E
quiv.Perm`。
形式化陈述：cycleType_le_of_mem_cycleFactorsFinset {f g : Perm α} (hf : f in g.cycleFa
ctorsFinset) : f.cycleType <= g.cycleType
参数：hf : f in g.cycleFactorsFinset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_iff`：mem_cycleFactorsFinset_iff {f p :
 Perm α} : p in cycleFactorsFinset f ↔ p.IsCycle ∧ forall a in p.support, p a = 
f a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleType_def`：cycleType_def (σ : Perm α) : σ.cycleType = σ.c
ycleFactorsFinset.1.map (Finset.card ∘ support)
· 使用定理 `Equiv.Perm.IsCycle.cycleFactorsFinset_eq_singleton`：∀ {α : Type u_2} [in
st : DecidableEq α] [inst_1 : Fintype α] {f : Equiv.Perm α}, f.IsCycle → f.cycle
FactorsFinset = {f}
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Multiset.map_le_map`：map_le_map {f : α -> β} {s t : Multiset α} (h : s <
= t) : map f s <= map f t
-/
theorem cycleType_le_of_mem_cycleFactorsFinset {f g : Perm α} (hf : f ∈ g.cycleFactorsFinset) :
    f.cycleType ≤ g.cycleType := by
  have hf' := mem_cycleFactorsFinset_iff.1 hf
  rw [cycleType_def, cycleType_def, hf'.left.cycleFactorsFinset_eq_singleton]
  refine map_le_map ?_
  simpa only [Finset.singleton_val, singleton_le, Finset.mem_val] using hf
/-
**Equiv.Perm.Disjoint.cycleType_noncommProd** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Per
m.Disjoint`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] {ι : Type u_2
} {k : ι → Equiv.Perm α} {s : Finset ι}   (hs : (↑s).Pairwise fun i j => (k i).D
isjoint (k j))   (hs' : optParam ((↑s).Pairwise fun i j => Commute (k i) (k j)) 
⋯),   (s.noncommProd k hs').cycleType = ∑ i ∈ s, (k i).cycleType
参数：hs : (↑s).Pairwise fun i j => (k i).Disjoint (k j)；hs' : optParam ((↑s).Pairw
ise fun i j => Commute (k i) (k j)) ⋯；s.noncommProd k hs'；k i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleType_one`：cycleType_one : (1 : Perm α).cycleType = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.noncommProd_insert_of_notMem`：noncommProd_insert_of_notMem [Decid
ableEq α] (s : Finset α) (a : α) (f : α -> β) (comm) (ha : a ∉ s) : noncommProd 
(insert a s) f comm = f a…
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Equiv.Perm.Disjoint.cycleType_mul`：∀ {α : Type u_1} [inst : Fintype α] [
inst_1 : DecidableEq α] {σ τ : Equiv.Perm α},   σ.Disjoint τ → (σ * τ).cycleType
 = σ.cycleType + τ.cycl…
· 使用定理 `Equiv.Perm.disjoint_noncommProd_right`：disjoint_noncommProd_right {ι : T
ype*} {k : ι -> Perm α} {s : Finset ι} (hs : Set.Pairwise s fun i j => Commute (
k i) (k j)) (hg : forall i …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
-/
theorem Disjoint.cycleType_noncommProd {ι : Type*} {k : ι → Perm α} {s : Finset ι}
    (hs : Set.Pairwise s fun i j ↦ Disjoint (k i) (k j))
    (hs' : Set.Pairwise s fun i j ↦ Commute (k i) (k j) :=
      hs.imp (fun _ _ ↦ Perm.Disjoint.commute)) :
    (s.noncommProd k hs').cycleType = s.sum fun i ↦ (k i).cycleType := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hrec =>
    have hs' : (s : Set ι).Pairwise fun i j ↦ Disjoint (k i) (k j) :=
      hs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi, Finset.sum_insert hi]
    rw [Disjoint.cycleType_mul, hrec hs']
    apply disjoint_noncommProd_right
    intro j hj
    apply hs _ _ (ne_of_mem_of_not_mem hj hi).symm <;>
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hj, or_true, true_or]
/-
**Equiv.Perm.cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub** 是 Mathlib 中的一个定理，
位于命名空间 `Equiv.Perm`。
形式化陈述：cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub {f g : Perm α} (hf : f in 
g.cycleFactorsFinset) : (g * f⁻¹).cycleType = g.cycleType - f.cycleType
参数：hf : f in g.cycleFactorsFinset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_right_cancel`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] {
a b c : G}, a + b = c + b → a = c
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.Disjoint.cycleType_mul`：∀ {α : Type u_1} [inst : Fintype α] [
inst_1 : DecidableEq α] {σ τ : Equiv.Perm α},   σ.Disjoint τ → (σ * τ).cycleType
 = σ.cycleType + τ.cycl…
· 使用定理 `Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset`：disjoint_mul_inv_
of_mem_cycleFactorsFinset {f g : Perm α} (h : f in cycleFactorsFinset g) : Disjo
int (g * f⁻¹) f
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `Multiset.instExistsAddOfLE`：∀ {α : Type u_1}, ExistsAddOfLE (Multiset α)
· 使用定理 `Multiset.instOrderedSub`：∀ {α : Type u_1} [inst : DecidableEq α], Ordere
dSub (Multiset α)
· 使用定理 `Equiv.Perm.cycleType_le_of_mem_cycleFactorsFinset`：cycleType_le_of_mem_c
ycleFactorsFinset {f g : Perm α} (hf : f in g.cycleFactorsFinset) : f.cycleType 
<= g.cycleType
-/
theorem cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub
    {f g : Perm α} (hf : f ∈ g.cycleFactorsFinset) :
    (g * f⁻¹).cycleType = g.cycleType - f.cycleType :=
  add_right_cancel (b := f.cycleType) <| by
    rw [← (disjoint_mul_inv_of_mem_cycleFactorsFinset hf).cycleType_mul, inv_mul_cancel_right,
      tsub_add_cancel_of_le (cycleType_le_of_mem_cycleFactorsFinset hf)]
/-
**Equiv.Perm.isConj_of_cycleType_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isConj_of_cycleType_eq {σ τ : Perm α} (h : cycleType σ = cycleType τ) : Is
Conj σ τ
参数：h : cycleType σ = cycleType τ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.cycle_induction_on`：cycle_induction_on [Finite β] (P : Perm β
 -> Prop) (σ : Perm β) (base_one : P 1) (base_cycles : forall σ : Perm β, σ.IsCy
cle -> P σ) (induct…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleType_eq_zero`：cycleType_eq_zero {σ : Perm α} : σ.cycleTy
pe = 0 ↔ σ = 1
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Equiv.Perm.cycleType_one`：cycleType_one : (1 : Perm α).cycleType = 0
· 使用定理 `IsConj.refl`：IsConj.refl (a : α) : IsConj a a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.card_cycleType_eq_one`：card_cycleType_eq_one {σ : Perm α} : M
ultiset.card σ.cycleType = 1 ↔ σ.IsCycle
· 使用定理 `Equiv.Perm.IsCycle.isConj`：∀ {α : Type u_2} [inst : Fintype α] [inst_1 :
 DecidableEq α] {σ τ : Equiv.Perm α},   σ.IsCycle → τ.IsCycle → σ.support.card =
 τ.support.card…
· 使用定理 `Multiset.singleton_inj`：singleton_inj {a b : α} : ({a} : Multiset α) = {
b} ↔ a = b
· 使用定理 `Equiv.Perm.IsCycle.cycleType`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : DecidableEq α] {σ : Equiv.Perm α},   σ.IsCycle → σ.cycleType = {σ.support.ca
rd}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.Disjoint.cycleType_mul`：∀ {α : Type u_1} [inst : Fintype α] [
inst_1 : DecidableEq α] {σ τ : Equiv.Perm α},   σ.Disjoint τ → (σ * τ).cycleType
 = σ.cycleType + τ.cycl…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用引理 `IsConj.symm`：IsConj.symm (hσ : IsConj φ σ) : IsConj φ σ.symm
· 使用定理 `isConj_iff`：isConj_iff {a b : α} : IsConj a b ↔ exists c : α, c * a * c⁻
¹ = b
· 使用定理 `IsConj.trans`：∀ {α : Type u} [inst : Monoid α] {a b c : α}, IsConj a b →
 IsConj b c → IsConj a c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_iff`：mem_cycleFactorsFinset_iff {f p :
 Perm α} : p in cycleFactorsFinset f ↔ p.IsCycle ∧ forall a in p.support, p a = 
f a
· 使用定理 `Finset.mem_def`：mem_def {a : α} {s : Finset α} : a in s ↔ a in s.1
· 使用定理 `Equiv.Perm.Disjoint.isConj_mul`：∀ {α : Type u} [Finite α] {σ τ π ρ : Equ
iv.Perm α},   IsConj σ π → IsConj τ ρ → σ.Disjoint τ → π.Disjoint ρ → IsConj (σ 
* τ) (π * ρ)
· 使用定理 `Equiv.Perm.cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub`：cycleType_mu
l_inv_mem_cycleFactorsFinset_eq_sub {f g : Perm α} (hf : f in g.cycleFactorsFins
et) : (g * f⁻¹).cycleType = g.cycleType - f.cycl…
（共 35 条，此处仅展示前 30 条）
-/
theorem isConj_of_cycleType_eq {σ τ : Perm α} (h : cycleType σ = cycleType τ) : IsConj σ τ := by
  induction σ using cycle_induction_on generalizing τ with
  | base_one =>
    rw [cycleType_one, eq_comm, cycleType_eq_zero] at h
    rw [h]
  | base_cycles σ hσ =>
    have hτ := card_cycleType_eq_one.2 hσ
    rw [h, card_cycleType_eq_one] at hτ
    apply hσ.isConj hτ
    rwa [hσ.cycleType, hτ.cycleType, Multiset.singleton_inj] at h
  | induction_disjoint σ π hd hc hσ hπ =>
    rw [hd.cycleType_mul] at h
    have h' : #σ.support ∈ τ.cycleType := by
      simp [← h, hc.cycleType]
    obtain ⟨σ', hσ'l, hσ'⟩ := Multiset.mem_map.mp h'
    have key : IsConj (σ' * τ * σ'⁻¹) τ := (isConj_iff.2 ⟨σ', rfl⟩).symm
    refine IsConj.trans ?_ key
    rw [mul_assoc]
    have hs : σ.cycleType = σ'.cycleType := by
      rw [← Finset.mem_def, mem_cycleFactorsFinset_iff] at hσ'l
      rw [hc.cycleType, ← hσ', hσ'l.left.cycleType]; rfl
    refine hd.isConj_mul (hσ hs) (hπ ?_) ?_
    · rw [cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub, ← h, add_comm, hs,
        add_tsub_cancel_right]
      rwa [Finset.mem_def]
    · exact (disjoint_mul_inv_of_mem_cycleFactorsFinset hσ'l).symm
/-
**Equiv.Perm.isConj_iff_cycleType_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isConj_iff_cycleType_eq {σ τ : Perm α} : IsConj σ τ ↔ σ.cycleType = τ.cycl
eType
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isConj_iff`：isConj_iff {a b : α} : IsConj a b ↔ exists c : α, c * a * c⁻
¹ = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleType_conj`：cycleType_conj {σ τ : Perm α} : (τ * σ * τ⁻¹)
.cycleType = σ.cycleType
· 使用定理 `Equiv.Perm.isConj_of_cycleType_eq`：isConj_of_cycleType_eq {σ τ : Perm α}
 (h : cycleType σ = cycleType τ) : IsConj σ τ
-/
theorem isConj_iff_cycleType_eq {σ τ : Perm α} : IsConj σ τ ↔ σ.cycleType = τ.cycleType :=
  ⟨fun h => by
    obtain ⟨π, rfl⟩ := isConj_iff.1 h
    rw [cycleType_conj], isConj_of_cycleType_eq⟩

@[simp]
/-
**Equiv.Perm.cycleType_extendDomain** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleType_extendDomain {β : Type*} [Fintype β] [DecidableEq β] {p : β -> P
rop} [DecidablePred p] (f : α ≃ Subtype p) {g : Perm α} : cycleType (g.extendDom
ain f) = cycleType g
参数：f : α ≃ Subtype p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.cycle_induction_on`：cycle_induction_on [Finite β] (P : Perm β
 -> Prop) (σ : Perm β) (base_one : P 1) (base_cycles : forall σ : Perm β, σ.IsCy
cle -> P σ) (induct…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.extendDomain_one`：extendDomain_one : extendDomain 1 f = 1
· 使用定理 `Equiv.Perm.cycleType_one`：cycleType_one : (1 : Perm α).cycleType = 0
· 使用定理 `Equiv.Perm.IsCycle.cycleType`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : DecidableEq α] {σ : Equiv.Perm α},   σ.IsCycle → σ.cycleType = {σ.support.ca
rd}
· 使用定理 `Equiv.Perm.IsCycle.extendDomain`：∀ {α : Type u_2} {β : Type u_3} {g : Eq
uiv.Perm α} {p : β → Prop} [inst : DecidablePred p] (f : α ≃ Subtype p),   g.IsC
ycle → (g.extendDomai…
· 使用定理 `Equiv.Perm.card_support_extend_domain`：card_support_extend_domain (f : α
 ≃ Subtype p) {g : Perm α} : #(g.extendDomain f).support = #g.support
· 使用定理 `Equiv.Perm.Disjoint.cycleType_mul`：∀ {α : Type u_1} [inst : Fintype α] [
inst_1 : DecidableEq α] {σ τ : Equiv.Perm α},   σ.Disjoint τ → (σ * τ).cycleType
 = σ.cycleType + τ.cycl…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.extendDomain_mul`：extendDomain_mul (e e' : Perm α) : e.extend
Domain f * e'.extendDomain f = (e * e').extendDomain f
· 使用定理 `Equiv.Perm.Disjoint.extendDomain`：∀ {α : Type u} {β : Type v} {p : β → P
rop} [inst : DecidablePred p] (f : α ≃ Subtype p) {σ τ : Equiv.Perm α},   σ.Disj
oint τ → (σ.extendDoma…
-/
theorem cycleType_extendDomain {β : Type*} [Fintype β] [DecidableEq β] {p : β → Prop}
    [DecidablePred p] (f : α ≃ Subtype p) {g : Perm α} :
    cycleType (g.extendDomain f) = cycleType g := by
  induction g using cycle_induction_on with
  | base_one => rw [extendDomain_one, cycleType_one, cycleType_one]
  | base_cycles σ hσ =>
    rw [(hσ.extendDomain f).cycleType, hσ.cycleType, card_support_extend_domain]
  | induction_disjoint σ τ hd _ hσ hτ =>
    rw [hd.cycleType_mul, ← extendDomain_mul, (hd.extendDomain f).cycleType_mul, hσ, hτ]
/-
**Equiv.Perm.cycleType_ofSubtype** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleType_ofSubtype {p : α -> Prop} [DecidablePred p] [Fintype (Subtype p)
] {g : Perm (Subtype p)} : cycleType (ofSubtype g) = cycleType g
参数：Subtype p；Subtype p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.cycleType_extendDomain`：cycleType_extendDomain {β : Type*} [F
intype β] [DecidableEq β] {p : β -> Prop} [DecidablePred p] (f : α ≃ Subtype p) 
{g : Perm α} : cycleTyp…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem cycleType_ofSubtype {p : α → Prop} [DecidablePred p] [Fintype (Subtype p)]
    {g : Perm (Subtype p)} :
    cycleType (ofSubtype g) = cycleType g :=
  cycleType_extendDomain (Equiv.refl (Subtype p))
/-
**Equiv.Perm.mem_cycleType_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mem_cycleType_iff {n : Nat} {σ : Perm α} : n in cycleType σ ↔ exists c τ, 
σ = c * τ ∧ Disjoint c τ ∧ IsCycle c ∧ c.support.card = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `Multiset.mem_coe`：mem_coe {a : α} {l : List α} : a in (l : Multiset α) ↔
 a in l
· 使用定理 `Equiv.Perm.cycleType_eq`：cycleType_eq {σ : Perm α} (l : List (Perm α)) (
h0 : l.prod = σ) (h1 : forall σ : Perm α, σ in l -> σ.IsCycle) (h2 : l.Pairwise 
Disjoint) : σ…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `List.Perm.prod_eq'`：∀ {M : Type u_4} [inst : Monoid M] {l₁ l₂ : List M},
 l₁.Perm l₂ → List.Pairwise Commute l₁ → l₁.prod = l₂.prod
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `List.perm_cons_erase`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a :
 α} {l : List α}, a ∈ l → l.Perm (a :: l.erase a)
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
· 使用定理 `List.Perm.pairwise_iff`：∀ {α : Type u_1} {R : α → α → Prop},   (∀ {x y :
 α}, R x y → R y x) → ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → (List.Pairwise R l₁ ↔ Lis
t.Pairwise R…
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `Equiv.Perm.Disjoint.stdSymm`：∀ {α : Type u_1}, Std.Symm Equiv.Perm.Disjo
int
· 使用定理 `Equiv.Perm.disjoint_prod_right`：disjoint_prod_right (l : List (Perm α)) 
(h : forall g in l, Disjoint f g) : Disjoint f l.prod
· 使用定理 `List.rel_of_pairwise_cons`：∀ {α : Type u_1} {a : α} {l : List α} {R : α 
→ α → Prop}, List.Pairwise R (a :: l) → ∀ {a' : α}, a' ∈ l → R a a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.Disjoint.cycleType_mul`：∀ {α : Type u_1} [inst : Fintype α] [
inst_1 : DecidableEq α] {σ τ : Equiv.Perm α},   σ.Disjoint τ → (σ * τ).cycleType
 = σ.cycleType + τ.cycl…
· 使用定理 `Equiv.Perm.IsCycle.cycleType`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : DecidableEq α] {σ : Equiv.Perm α},   σ.IsCycle → σ.cycleType = {σ.support.ca
rd}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem mem_cycleType_iff {n : ℕ} {σ : Perm α} :
    n ∈ cycleType σ ↔ ∃ c τ, σ = c * τ ∧ Disjoint c τ ∧ IsCycle c ∧ c.support.card = n := by
  constructor
  · intro h
    obtain ⟨l, rfl, hlc, hld⟩ := truncCycleFactors σ
    rw [cycleType_eq _ rfl hlc hld, Multiset.mem_coe, List.mem_map] at h
    obtain ⟨c, cl, rfl⟩ := h
    rw [(List.perm_cons_erase cl).pairwise_iff symm] at hld
    refine ⟨c, (l.erase c).prod, ?_, ?_, hlc _ cl, rfl⟩
    · rw [← List.prod_cons, (List.perm_cons_erase cl).symm.prod_eq' (hld.imp Disjoint.commute)]
    · exact disjoint_prod_right _ fun g => List.rel_of_pairwise_cons hld
  · rintro ⟨c, t, rfl, hd, hc, rfl⟩
    simp [hd.cycleType_mul, hc.cycleType]
/-
**Equiv.Perm.le_card_support_of_mem_cycleType** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.P
erm`。
形式化陈述：le_card_support_of_mem_cycleType {n : Nat} {σ : Perm α} (h : n in cycleTyp
e σ) : n <= #σ.support
参数：h : n in cycleType σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Multiset.le_sum_of_mem`：∀ {α : Type u_2} [inst : AddCommMonoid α] {m : M
ultiset α} {a : α},   a ∈ m → ∀ [inst_1 : Preorder α] [CanonicallyOrderedAdd α],
 a ≤ m.sum
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Equiv.Perm.sum_cycleType`：sum_cycleType (σ : Perm α) : σ.cycleType.sum =
 #σ.support
-/
theorem le_card_support_of_mem_cycleType {n : ℕ} {σ : Perm α} (h : n ∈ cycleType σ) :
    n ≤ #σ.support :=
  (le_sum_of_mem h).trans (le_of_eq σ.sum_cycleType)
/-
**Equiv.Perm.cycleType_of_card_le_mem_cycleType_add_two** 是 Mathlib 中的一个定理，位于命名空
间 `Equiv.Perm`。
形式化陈述：cycleType_of_card_le_mem_cycleType_add_two {n : Nat} {g : Perm α} (hn2 : F
intype.card α < n + 2) (hng : n in g.cycleType) : g.cycleType = {n}
参数：hn2 : Fintype.card α < n + 2；hng : n in g.cycleType。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_cycleType_iff`：mem_cycleType_iff {n : Nat} {σ : Perm α} :
 n in cycleType σ ↔ exists c τ, σ = c * τ ∧ Disjoint c τ ∧ IsCycle c ∧ c.support
.card = n
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.Disjoint.card_support_mul`：∀ {α : Type u_1} [inst : Decidable
Eq α] [inst_1 : Fintype α] {f g : Equiv.Perm α},   f.Disjoint g → (f * g).suppor
t.card = f.support.card + …
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Equiv.Perm.two_le_card_support_of_ne_one`：two_le_card_support_of_ne_one 
{f : Perm α} (h : f != 1) : 2 <= #f.support
· 使用定理 `Equiv.Perm.Disjoint.cycleType_mul`：∀ {α : Type u_1} [inst : Fintype α] [
inst_1 : DecidableEq α] {σ τ : Equiv.Perm α},   σ.Disjoint τ → (σ * τ).cycleType
 = σ.cycleType + τ.cycl…
· 使用定理 `Equiv.Perm.IsCycle.cycleType`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : DecidableEq α] {σ : Equiv.Perm α},   σ.IsCycle → σ.cycleType = {σ.support.ca
rd}
· 使用定理 `Equiv.Perm.cycleType_one`：cycleType_one : (1 : Perm α).cycleType = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cycleType_of_card_le_mem_cycleType_add_two {n : ℕ} {g : Perm α}
    (hn2 : Fintype.card α < n + 2) (hng : n ∈ g.cycleType) : g.cycleType = {n} := by
  obtain ⟨c, g', rfl, hd, hc, rfl⟩ := mem_cycleType_iff.1 hng
  suffices g'1 : g' = 1 by
    rw [hd.cycleType_mul, hc.cycleType, g'1, cycleType_one, add_zero]
  contrapose! hn2 with g'1
  grw [← (c * g').support.card_le_univ, hd.card_support_mul, two_le_card_support_of_ne_one g'1]
/-
**Equiv.Perm.sign_of_cycleType_eq_replicate** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Per
m`。
形式化陈述：sign_of_cycleType_eq_replicate {σ : Perm α} {n : Nat} (hn : 0 < n) (hσ : σ
.cycleType = Multiset.replicate σ.cycleType.card n) : sign σ = if Odd n then 1 e
lse (-1) ^ ((Fintype.card α - Fintype.card (Function.fixedPoints σ)) / n)
参数：hn : 0 < n；hσ : σ.cycleType = Multiset.replicate σ.cycleType.card n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.sign_of_cycleType'`：sign_of_cycleType' (σ : Perm α) : sign σ 
= (σ.cycleType.map fun n => -(-1 : Intˣ) ^ n).prod
· 使用定理 `Multiset.map_replicate`：map_replicate (f : α -> β) (k : Nat) (a : α) : (
replicate k a).map f = replicate k (f a)
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.not_odd_iff_even`：∀ {n : ℕ}, ¬Odd n ↔ Even n
· 使用引理 `Even.neg_one_pow`：Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1
· 使用定理 `Equiv.Perm.card_fixedPoints`：card_fixedPoints (σ : Equiv.Perm α) : Finty
pe.card (Function.fixedPoints σ) = Fintype.card α - σ.cycleType.sum
· 使用定理 `Nat.sub_sub_self`：∀ {n m : ℕ}, m ≤ n → n - (n - m) = m
· 使用定理 `Equiv.Perm.sum_cycleType_le`：sum_cycleType_le (σ : Perm α) : σ.cycleType
.sum <= Fintype.card α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.sum_replicate`：∀ {M : Type u_3} [inst : AddCommMonoid M] (n : ℕ
) (a : M), (Multiset.replicate n a).sum = n • a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.card_replicate`：∀ {α : Type u_1} (n : ℕ) (a : α), (Multiset.rep
licate n a).card = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.mul_div_cancel`：∀ (m : ℕ) {n : ℕ}, 0 < n → m * n / n = m
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Odd.neg_one_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistrib
Neg α] {n : ℕ}, Odd n → (-1) ^ n = -1
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem sign_of_cycleType_eq_replicate {σ : Perm α} {n : ℕ} (hn : 0 < n)
    (hσ : σ.cycleType = Multiset.replicate σ.cycleType.card n) :
    sign σ = if Odd n then 1 else
      (-1) ^ ((Fintype.card α - Fintype.card (Function.fixedPoints σ)) / n) := by
  rw [sign_of_cycleType', hσ, Multiset.map_replicate, Multiset.prod_replicate]
  obtain h | h := Nat.even_or_odd n
  · rw [if_neg (Nat.not_odd_iff_even.mpr h), h.neg_one_pow, σ.card_fixedPoints,
      Nat.sub_sub_self σ.sum_cycleType_le,
      show σ.cycleType.sum = σ.cycleType.card * n by rw [hσ]; simp,
        Nat.mul_div_cancel _ hn]
  · rw [if_pos h, h.neg_one_pow, neg_neg, one_pow]
/-
**Equiv.Perm.sign_of_pow_two_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_of_pow_two_eq_one {σ : Perm α} (hσ : σ ^ 2 = 1) : sign σ = (-1) ^ ((F
intype.card α - Fintype.card (Function.fixedPoints σ)) / 2)
参数：hσ : σ ^ 2 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.sign_of_cycleType_eq_replicate`：sign_of_cycleType_eq_replicat
e {σ : Perm α} {n : Nat} (hn : 0 < n) (hσ : σ.cycleType = Multiset.replicate σ.c
ycleType.card n) : sign σ = if …
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Equiv.Perm.cycleType_of_pow_prime_eq_one`：cycleType_of_pow_prime_eq_one 
{σ : Perm α} {p : Nat} [Fact (Nat.Prime p)] (hσ : σ ^ p = 1) : σ.cycleType = Mul
tiset.replicate σ.cycleType.ca…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.not_odd_iff`：not_odd_iff : ¬Odd n ↔ n % 2 = 0
-/
theorem sign_of_pow_two_eq_one {σ : Perm α} (hσ : σ ^ 2 = 1) :
    sign σ = (-1) ^ ((Fintype.card α - Fintype.card (Function.fixedPoints σ)) / 2) := by
  rw [sign_of_cycleType_eq_replicate zero_lt_two (cycleType_of_pow_prime_eq_one hσ),
    if_neg (Nat.not_odd_iff.mpr rfl)]

end CycleType

/-
**Equiv.Perm.card_compl_support_modEq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：card_compl_support_modEq [DecidableEq α] {p n : Nat} [hp : Fact p.Prime] {
σ : Perm α} (hσ : σ ^ p ^ n = 1) : σ.supportᶜ.card ≡ Fintype.card α [MOD p]
参数：hσ : σ ^ p ^ n = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.modEq_iff_dvd'`：modEq_iff_dvd' (h : a <= b) : a ≡ b [MOD n] ↔ n ∣ b 
- a
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Equiv.Perm.sum_cycleType`：sum_cycleType (σ : Perm α) : σ.cycleType.sum =
 #σ.support
· 使用引理 `Multiset.dvd_sum`：dvd_sum : (forall x in s, a ∣ x) -> a ∣ s.sum
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_prime_pow`：dvd_prime_pow {p : Nat} (pp : Prime p) {m i : Nat} : 
i ∣ p ^ m ↔ exists k <= m, i = p ^ k
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `orderOf_dvd_of_pow_eq_one`：orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : o
rderOf x ∣ n
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.Perm.dvd_of_mem_cycleType`：dvd_of_mem_cycleType {σ : Perm α} {n : 
Nat} (h : n in σ.cycleType) : n ∣ orderOf σ
· 使用引理 `dvd_pow_self`：dvd_pow_self (a : α) {n : Nat} (hn : n != 0) : a ∣ a ^ n
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Equiv.Perm.one_lt_of_mem_cycleType`：one_lt_of_mem_cycleType {σ : Perm α}
 {n : Nat} (h : n in σ.cycleType) : 1 < n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
theorem card_compl_support_modEq [DecidableEq α] {p n : ℕ} [hp : Fact p.Prime] {σ : Perm α}
    (hσ : σ ^ p ^ n = 1) : σ.supportᶜ.card ≡ Fintype.card α [MOD p] := by
  rw [Nat.modEq_iff_dvd', ← Finset.card_compl, compl_compl, ← sum_cycleType]
  · refine Multiset.dvd_sum fun k hk => ?_
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hσ)
    obtain ⟨l, -, rfl⟩ := (Nat.dvd_prime_pow hp.out).mp
      ((congr_arg _ hm).mp (dvd_of_mem_cycleType hk))
    exact dvd_pow_self _ fun h => (one_lt_of_mem_cycleType hk).ne <| by rw [h, pow_zero]
  · exact Finset.card_le_univ _

set_option backward.isDefEq.respectTransparency false in
open Function in
/-- The number of fixed points of a `p ^ n`-th root of the identity function over a finite set
and the set's cardinality have the same residue modulo `p`, where `p` is a prime. -/
/-
**Equiv.Perm.card_fixedPoints_modEq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：card_fixedPoints_modEq [DecidableEq α] {f : Function.End α} {p n : Nat} [h
p : Fact p.Prime] (hf : f ^ p ^ n = 1) : Fintype.card α ≡ Fintype.card f.fixedPo
ints [MOD p]
参数：hf : f ^ p ^ n = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.leftInverse_iff_comp`：leftInverse_iff_comp {f : α -> β} {g : β 
-> α} : LeftInverse f g ↔ f ∘ g = id
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `pow_sub_mul_pow`：pow_sub_mul_pow (a : M) (h : m <= n) : a ^ (n - m) * a 
^ m = a ^ n
· 使用定理 `Nat.one_le_pow`：∀ (n m : ℕ), 0 < m → 1 ≤ m ^ n
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用引理 `pow_mul_pow_sub`：pow_mul_pow_sub (a : M) (h : m <= n) : a ^ m * a ^ (n -
 m) = a ^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFunLike.ext'_iff`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [i
 : DFunLike F α β] {f g : F}, f = g ↔ ⇑f = ⇑g
· 使用定理 `Equiv.Perm.coe_pow`：∀ {α : Type u_4} (f : Equiv.Perm α) (n : ℕ), ⇑(f ^ n
) = (⇑f)^[n]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hom_coe_pow`：∀ {M : Type u_4} {F : Type u_5} [inst : Monoid F] (c : F → 
M → M),   c 1 = id → (∀ (f g : F), c (f * g) = c f ∘ c g) → ∀ (f : F) (n : ℕ), c
 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.coe_compl`：coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用定理 `Equiv.Perm.card_compl_support_modEq`：card_compl_support_modEq [Decidable
Eq α] {p n : Nat} [hp : Fact p.Prime] {σ : Perm α} (hσ : σ ^ p ^ n = 1) : σ.supp
ortᶜ.card ≡ Fintype.card …

--- 原说明 ---
The number of fixed points of a `p ^ n`-th root of the identity function over a 
finite set
and the set's cardinality have the same residue modulo `p`, where `p` is a prime
.
-/
theorem card_fixedPoints_modEq [DecidableEq α] {f : Function.End α} {p n : ℕ}
    [hp : Fact p.Prime] (hf : f ^ p ^ n = 1) :
    Fintype.card α ≡ Fintype.card f.fixedPoints [MOD p] := by
  let σ : α ≃ α := ⟨f, f ^ (p ^ n - 1),
    leftInverse_iff_comp.mpr ((pow_sub_mul_pow f (Nat.one_le_pow n p hp.out.pos)).trans hf),
    leftInverse_iff_comp.mpr ((pow_mul_pow_sub f (Nat.one_le_pow n p hp.out.pos)).trans hf)⟩
  have hσ : σ ^ p ^ n = 1 := by
    rw [DFunLike.ext'_iff, coe_pow]
    exact (hom_coe_pow (fun g : Function.End α ↦ g) rfl (fun g h ↦ rfl) f (p ^ n)).symm.trans hf
  suffices Fintype.card f.fixedPoints = (support σ)ᶜ.card from
    this ▸ (card_compl_support_modEq hσ).symm
  suffices f.fixedPoints = (support σ)ᶜ by
    simp only [this]; apply Fintype.card_coe
  simp [σ, Set.ext_iff, IsFixedPt]
/-
**Equiv.Perm.exists_fixed_point_of_prime** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：exists_fixed_point_of_prime {p n : Nat} [hp : Fact p.Prime] (hα : ¬p ∣ Fin
type.card α) {σ : Perm α} (hσ : σ ^ p ^ n = 1) : exists a : α, σ a = a
参数：hα : ¬p ∣ Fintype.card α；hσ : σ ^ p ^ n = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用定理 `compl_eq_bot`：compl_eq_bot : xᶜ = ⊥ ↔ x = ⊤
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用定理 `Equiv.Perm.card_compl_support_modEq`：card_compl_support_modEq [Decidable
Eq α] {p n : Nat} [hp : Fact p.Prime] {σ : Perm α} (hσ : σ ^ p ^ n = 1) : σ.supp
ortᶜ.card ≡ Fintype.card …
-/
theorem exists_fixed_point_of_prime {p n : ℕ} [hp : Fact p.Prime] (hα : ¬p ∣ Fintype.card α)
    {σ : Perm α} (hσ : σ ^ p ^ n = 1) : ∃ a : α, σ a = a := by
  classical
    contrapose! hα
    simp_rw [← mem_support, ← Finset.eq_univ_iff_forall] at hα
    exact Nat.modEq_zero_iff_dvd.1 ((congr_arg _ (Finset.card_eq_zero.2 (compl_eq_bot.2 hα))).mp
      (card_compl_support_modEq hσ).symm)
/-
**Equiv.Perm.exists_fixed_point_of_prime'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`
。
形式化陈述：exists_fixed_point_of_prime' {p n : Nat} [hp : Fact p.Prime] (hα : p ∣ Fin
type.card α) {σ : Perm α} (hσ : σ ^ p ^ n = 1) {a : α} (ha : σ a = a) : exists b
 : α, σ b = b ∧ b != a
参数：hα : p ∣ Fintype.card α；hσ : σ ^ p ^ n = 1；ha : σ a = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_compl`：mem_compl : a in sᶜ ↔ a ∉ s
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `Finset.exists_mem_ne`：exists_mem_ne (hs : 1 < #s) (a : α) : exists b in 
s, b != a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用定理 `Equiv.Perm.card_compl_support_modEq`：card_compl_support_modEq [Decidable
Eq α] {p n : Nat} [hp : Fact p.Prime] {σ : Perm α} (hσ : σ ^ p ^ n = 1) : σ.supp
ortᶜ.card ≡ Fintype.card …
-/
theorem exists_fixed_point_of_prime' {p n : ℕ} [hp : Fact p.Prime] (hα : p ∣ Fintype.card α)
    {σ : Perm α} (hσ : σ ^ p ^ n = 1) {a : α} (ha : σ a = a) : ∃ b : α, σ b = b ∧ b ≠ a := by
  classical
    have h : ∀ b : α, b ∈ σ.supportᶜ ↔ σ b = b := fun b => by
      rw [Finset.mem_compl, mem_support, Classical.not_not]
    obtain ⟨b, hb1, hb2⟩ := Finset.exists_mem_ne (hp.out.one_lt.trans_le
      (Nat.le_of_dvd (Finset.card_pos.mpr ⟨a, (h a).mpr ha⟩) (Nat.modEq_zero_iff_dvd.mp
        ((card_compl_support_modEq hσ).trans (Nat.modEq_zero_iff_dvd.mpr hα))))) a
    exact ⟨b, (h b).mp hb1, hb2⟩
/-
**Equiv.Perm.isCycle_of_prime_order'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isCycle_of_prime_order' {σ : Perm α} (h1 : (orderOf σ).Prime) (h2 : Fintyp
e.card α < 2 * orderOf σ) : σ.IsCycle
参数：h1 : (orderOf σ).Prime；h2 : Fintype.card α < 2 * orderOf σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.isCycle_of_prime_order`：isCycle_of_prime_order {σ : Perm α} (
h1 : (orderOf σ).Prime) (h2 : #σ.support < 2 * orderOf σ) : σ.IsCycle
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
-/
theorem isCycle_of_prime_order' {σ : Perm α} (h1 : (orderOf σ).Prime)
    (h2 : Fintype.card α < 2 * orderOf σ) : σ.IsCycle := by
  classical exact isCycle_of_prime_order h1 (lt_of_le_of_lt σ.support.card_le_univ h2)
/-
**Equiv.Perm.isCycle_of_prime_order''** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isCycle_of_prime_order'' {σ : Perm α} (h1 : (Fintype.card α).Prime) (h2 : 
orderOf σ = Fintype.card α) : σ.IsCycle
参数：h1 : (Fintype.card α).Prime；h2 : orderOf σ = Fintype.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.isCycle_of_prime_order'`：isCycle_of_prime_order' {σ : Perm α}
 (h1 : (orderOf σ).Prime) (h2 : Fintype.card α < 2 * orderOf σ) : σ.IsCycle
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_lt_mul_iff_left₀`：mul_lt_mul_iff_left₀ [MulPosStrictMono α] [MulPosR
eflectLT α] (a0 : 0 < a) : b * a < c * a ↔ b < c where mp h
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用引理 `orderOf_pos`：orderOf_pos (x : G) : 0 < orderOf x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem isCycle_of_prime_order'' {σ : Perm α} (h1 : (Fintype.card α).Prime)
    (h2 : orderOf σ = Fintype.card α) : σ.IsCycle :=
  isCycle_of_prime_order' ((congr_arg Nat.Prime h2).mpr h1) <| by
    rw [← one_mul (Fintype.card α), ← h2, mul_lt_mul_iff_left₀ (orderOf_pos σ)]
    exact one_lt_two

section Cauchy

variable (G : Type*) [Group G] (n : ℕ)

/-- The type of vectors with terms from `G`, length `n`, and product equal to `1:G`. -/
/-
**Equiv.Perm.vectorsProdEqOne** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：vectorsProdEqOne : Set (List.Vector G n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of vectors with terms from `G`, length `n`, and product equal to `1:G`.
-/
def vectorsProdEqOne : Set (List.Vector G n) :=
  { v | v.toList.prod = 1 }

namespace VectorsProdEqOne

/-
**Equiv.Perm.VectorsProdEqOne.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Vect
orsProdEqOne`。
形式化陈述：mem_iff {n : Nat} (v : List.Vector G n) : v in vectorsProdEqOne G n ↔ v.to
List.prod = 1
参数：v : List.Vector G n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_iff {n : ℕ} (v : List.Vector G n) : v ∈ vectorsProdEqOne G n ↔ v.toList.prod = 1 :=
  Iff.rfl
/-
**Equiv.Perm.VectorsProdEqOne.zero_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Vect
orsProdEqOne`。
形式化陈述：zero_eq : vectorsProdEqOne G 0 = {Vector.nil}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem : s = {a} ↔
 a in s ∧ forall x in s, x = a
· 使用定理 `List.Vector.eq_nil`：∀ {α : Type u_1} (v : List.Vector α 0), v = List.Vec
tor.nil
-/
theorem zero_eq : vectorsProdEqOne G 0 = {Vector.nil} :=
  Set.eq_singleton_iff_unique_mem.mpr ⟨Eq.refl (1 : G), fun v _ => v.eq_nil⟩
/-
**Equiv.Perm.VectorsProdEqOne.one_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Vecto
rsProdEqOne`。
形式化陈述：one_eq : vectorsProdEqOne G 1 = {Vector.nil.cons 1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.Vector.toList_singleton`：toList_singleton (v : Vector α 1) : v.toLi
st = [v.head]
· 使用定理 `List.prod_singleton`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [S
td.LawfulRightIdentity (fun x1 x2 => x1 * x2) 1] {x : α},   [x].prod = x
· 使用定理 `Std.LawfulIdentity.toLawfulRightIdentity`：∀ {α : Sort u} {op : α → α → α
} {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulRightIdentity op 
o
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.Vector.head_cons`：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector
 α n), (a ::ᵥ v).head = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Vector.cons_head_tail`：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α 
n.succ), v.head ::ᵥ v.tail = v
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `List.Vector.eq_nil`：∀ {α : Type u_1} (v : List.Vector α 0), v = List.Vec
tor.nil
-/
theorem one_eq : vectorsProdEqOne G 1 = {Vector.nil.cons 1} := by
  simp_rw [Set.eq_singleton_iff_unique_mem, mem_iff, List.Vector.toList_singleton,
    List.prod_singleton, List.Vector.head_cons, true_and]
  exact fun v hv => v.cons_head_tail.symm.trans (congr_arg₂ Vector.cons hv v.tail.eq_nil)
/-
**Equiv.Perm.VectorsProdEqOne.zeroUnique** 是 Mathlib 中的一个实例，位于命名空间 `Equiv.Perm.V
ectorsProdEqOne`。
形式化陈述：zeroUnique : Unique (vectorsProdEqOne G 0)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance zeroUnique : Unique (vectorsProdEqOne G 0) := by
  rw [zero_eq]
  exact Set.uniqueSingleton Vector.nil
/-
**Equiv.Perm.VectorsProdEqOne.oneUnique** 是 Mathlib 中的一个实例，位于命名空间 `Equiv.Perm.Ve
ctorsProdEqOne`。
形式化陈述：oneUnique : Unique (vectorsProdEqOne G 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance oneUnique : Unique (vectorsProdEqOne G 1) := by
  rw [one_eq]
  exact Set.uniqueSingleton (Vector.nil.cons 1)

/-- Given a vector `v` of length `n`, make a vector of length `n + 1` whose product is `1`,
by appending the inverse of the product of `v`. -/
@[simps]
/-
**Equiv.Perm.VectorsProdEqOne.vectorEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm.
VectorsProdEqOne`。
形式化陈述：vectorEquiv : List.Vector G n ≃ vectorsProdEqOne G (n + 1) where toFun v
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a vector `v` of length `n`, make a vector of length `n + 1` whose product 
is `1`,
by appending the inverse of the product of `v`.
-/
def vectorEquiv : List.Vector G n ≃ vectorsProdEqOne G (n + 1) where
  toFun v := ⟨v.toList.prod⁻¹ ::ᵥ v, by
    rw [mem_iff, Vector.toList_cons, List.prod_cons, inv_mul_cancel]⟩
  invFun v := v.1.tail
  left_inv v := v.tail_cons v.toList.prod⁻¹
  right_inv v := Subtype.ext <|
    calc
      v.1.tail.toList.prod⁻¹ ::ᵥ v.1.tail = v.1.head ::ᵥ v.1.tail :=
        congr_arg (· ::ᵥ v.1.tail) <| Eq.symm <| eq_inv_of_mul_eq_one_left <| by
          rw [← List.prod_cons, ← Vector.toList_cons, v.1.cons_head_tail]
          exact v.2
      _ = v.1 := v.1.cons_head_tail

/-- Given a vector `v` of length `n` whose product is 1, make a vector of length `n - 1`,
by deleting the last entry of `v`. -/
/-
**Equiv.Perm.VectorsProdEqOne.equivVector** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm.
VectorsProdEqOne`。
形式化陈述：(G : Type u_2) → [inst : Group G] → (n : ℕ) → ↑(Equiv.Perm.vectorsProdEqOn
e G n) ≃ List.Vector G (n - 1)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a vector `v` of length `n` whose product is 1, make a vector of length `n 
- 1`,
by deleting the last entry of `v`.
-/
def equivVector : ∀ n, vectorsProdEqOne G n ≃ List.Vector G (n - 1)
  | 0 => (ofUnique (vectorsProdEqOne G 0) (vectorsProdEqOne G 1)).trans (vectorEquiv G 0).symm
  | (n + 1) => (vectorEquiv G n).symm
/-
**Equiv.Perm.VectorsProdEqOne.** 是 Mathlib 中的一个实例，位于命名空间 `Equiv.Perm.VectorsProd
EqOne`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fintype G] : Fintype (vectorsProdEqOne G n) :=
  Fintype.ofEquiv (List.Vector G (n - 1)) (equivVector G n).symm
/-
**Equiv.Perm.VectorsProdEqOne.card** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Vectors
ProdEqOne`。
形式化陈述：card [Fintype G] : Fintype.card (vectorsProdEqOne G n) = Fintype.card G ^ 
(n - 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `card_vector`：card_vector [Fintype α] (n : Nat) : Fintype.card (List.Vect
or α n) = Fintype.card α ^ n
-/
theorem card [Fintype G] : Fintype.card (vectorsProdEqOne G n) = Fintype.card G ^ (n - 1) :=
  (Fintype.card_congr (equivVector G n)).trans (card_vector (n - 1))

variable {G n} {g : G}
variable (v : vectorsProdEqOne G n) (j k : ℕ)

/-- Rotate a vector whose product is 1. -/
/-
**Equiv.Perm.VectorsProdEqOne.rotate** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm.Vecto
rsProdEqOne`。
形式化陈述：rotate : vectorsProdEqOne G n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Rotate a vector whose product is 1.
-/
def rotate : vectorsProdEqOne G n :=
  ⟨⟨_, (v.1.1.length_rotate k).trans v.1.2⟩, List.prod_rotate_eq_one_of_prod_eq_one v.2 k⟩
/-
**Equiv.Perm.VectorsProdEqOne.rotate_zero** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.
VectorsProdEqOne`。
形式化陈述：rotate_zero : rotate v 0 = v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `List.rotate_zero`：rotate_zero (l : List α) : l.rotate 0 = l
-/
theorem rotate_zero : rotate v 0 = v :=
  Subtype.ext (Subtype.ext v.1.1.rotate_zero)
/-
**Equiv.Perm.VectorsProdEqOne.rotate_rotate** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Per
m.VectorsProdEqOne`。
形式化陈述：rotate_rotate : rotate (rotate v j) k = rotate v (j + k)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `List.rotate_rotate`：rotate_rotate (l : List α) (n m : Nat) : (l.rotate n
).rotate m = l.rotate (n + m)
-/
theorem rotate_rotate : rotate (rotate v j) k = rotate v (j + k) :=
  Subtype.ext (Subtype.ext (v.1.1.rotate_rotate j k))
/-
**Equiv.Perm.VectorsProdEqOne.rotate_length** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Per
m.VectorsProdEqOne`。
形式化陈述：rotate_length : rotate v n = v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `List.rotate_length`：rotate_length (l : List α) : rotate l l.length = l
-/
theorem rotate_length : rotate v n = v :=
  Subtype.ext (Subtype.ext ((congr_arg _ v.1.2.symm).trans v.1.1.rotate_length))

end VectorsProdEqOne

set_option backward.isDefEq.respectTransparency false in
-- TODO: Make the `Finite` version of this theorem the default
/-- For every prime `p` dividing the order of a finite group `G` there exists an element of order
`p` in `G`. This is known as Cauchy's theorem. -/
/-
**Equiv.Perm._root_.exists_prime_orderOf_dvd_card** 是 Mathlib 中的一个定理，位于命名空间 `Equ
iv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For every prime `p` dividing the order of a finite group `G` there exists an ele
ment of order
`p` in `G`. This is known as Cauchy's theorem.
-/
theorem _root_.exists_prime_orderOf_dvd_card {G : Type*} [Group G] [Fintype G] (p : ℕ)
    [hp : Fact p.Prime] (hdvd : p ∣ Fintype.card G) : ∃ x : G, orderOf x = p := by
  have hp' : p - 1 ≠ 0 := mt tsub_eq_zero_iff_le.mp (not_le_of_gt hp.out.one_lt)
  have Scard :=
    calc
      p ∣ Fintype.card G ^ (p - 1) := hdvd.trans (dvd_pow (dvd_refl _) hp')
      _ = Fintype.card (vectorsProdEqOne G p) := (VectorsProdEqOne.card G p).symm
  let f : ℕ → vectorsProdEqOne G p → vectorsProdEqOne G p := fun k v =>
    VectorsProdEqOne.rotate v k
  have hf1 : ∀ v, f 0 v = v := VectorsProdEqOne.rotate_zero
  have hf2 : ∀ j k v, f k (f j v) = f (j + k) v := fun j k v =>
    VectorsProdEqOne.rotate_rotate v j k
  have hf3 : ∀ v, f p v = v := VectorsProdEqOne.rotate_length
  let σ :=
    Equiv.mk (f 1) (f (p - 1)) (fun s => by rw [hf2, add_tsub_cancel_of_le hp.out.one_lt.le, hf3])
      fun s => by rw [hf2, tsub_add_cancel_of_le hp.out.one_lt.le, hf3]
  have hσ : ∀ k v, (σ ^ k) v = f k v := fun k =>
    Nat.rec (fun v => (hf1 v).symm) (fun k hk v => by
      rw [pow_succ, Perm.mul_apply, hk (σ v), Nat.succ_eq_one_add, ← hf2 1 k]
      simp only [σ, coe_fn_mk]) k
  replace hσ : σ ^ p ^ 1 = 1 := Perm.ext fun v => by rw [pow_one, hσ, hf3, one_apply]
  let v₀ : vectorsProdEqOne G p :=
    ⟨List.Vector.replicate p 1, (List.prod_replicate p 1).trans (one_pow p)⟩
  have hv₀ : σ v₀ = v₀ := Subtype.ext (Subtype.ext (List.rotate_replicate (1 : G) p 1))
  obtain ⟨v, hv1, hv2⟩ := exists_fixed_point_of_prime' Scard hσ hv₀
  refine
    Exists.imp (fun g hg => orderOf_eq_prime ?_ fun hg' => hv2 ?_)
      (List.rotate_one_eq_self_iff_eq_replicate.mp (Subtype.ext_iff.mp (Subtype.ext_iff.mp hv1)))
  · rw [← List.prod_replicate, ← v.1.2, ← hg, show v.val.val.prod = 1 from v.2]
  · rw [Subtype.ext_iff, Subtype.ext_iff, hg, hg', v.1.2]
    simp only [v₀, List.Vector.replicate]

-- TODO: Make the `Finite` version of this theorem the default
/-- For every prime `p` dividing the order of a finite additive group `G` there exists an element of
order `p` in `G`. This is the additive version of Cauchy's theorem. -/
/-
**Equiv.Perm._root_.exists_prime_addOrderOf_dvd_card** 是 Mathlib 中的一个定理，位于命名空间 `
Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For every prime `p` dividing the order of a finite additive group `G` there exis
ts an element of
order `p` in `G`. This is the additive version of Cauchy's theorem.
-/
theorem _root_.exists_prime_addOrderOf_dvd_card {G : Type*} [AddGroup G] [Fintype G] (p : ℕ)
    [Fact p.Prime] (hdvd : p ∣ Fintype.card G) : ∃ x : G, addOrderOf x = p :=
  @exists_prime_orderOf_dvd_card (Multiplicative G) _ _ _ _ (by convert! hdvd)

attribute [to_additive existing] exists_prime_orderOf_dvd_card

-- TODO: Make the `Finite` version of this theorem the default
/-- For every prime `p` dividing the order of a finite group `G` there exists an element of order
`p` in `G`. This is known as Cauchy's theorem. -/
@[to_additive]
/-
**Equiv.Perm._root_.exists_prime_orderOf_dvd_card'** 是 Mathlib 中的一个定理，位于命名空间 `Eq
uiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For every prime `p` dividing the order of a finite group `G` there exists an ele
ment of order
`p` in `G`. This is known as Cauchy's theorem.
-/
theorem _root_.exists_prime_orderOf_dvd_card' {G : Type*} [Group G] [Finite G] (p : ℕ)
    [hp : Fact p.Prime] (hdvd : p ∣ Nat.card G) : ∃ x : G, orderOf x = p := by
  have := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card] at hdvd
  exact exists_prime_orderOf_dvd_card p hdvd

end Cauchy

/-
**Equiv.Perm.subgroup_eq_top_of_swap_mem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：subgroup_eq_top_of_swap_mem [DecidableEq α] {H : Subgroup (Perm α)} [d : D
ecidablePred (· in H)] {τ : Perm α} (h0 : (Fintype.card α).Prime) (h1 : Fintype.
card α ∣ Fintype.card H) (h2 : τ in H) (h3 : IsSwap τ) : H = ⊤
参数：Perm α；· in H；h0 : (Fintype.card α).Prime；h1 : Fintype.card α ∣ Fintype.card 
H；h2 : τ in H；h3 : IsSwap τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_prime_orderOf_dvd_card`：∀ {G : Type u_3} [inst : Group G] [inst_1
 : Fintype G] (p : ℕ) [hp : Fact (Nat.Prime p)],   p ∣ Fintype.card G → ∃ x, ord
erOf x = p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Subgroup.orderOf_coe`：orderOf_coe (a : H) : orderOf (a : G) = orderOf a
· 使用定理 `Equiv.Perm.isCycle_of_prime_order''`：isCycle_of_prime_order'' {σ : Perm 
α} (h1 : (Fintype.card α).Prime) (h2 : orderOf σ = Fintype.card α) : σ.IsCycle
· 使用定理 `Finset.eq_univ_of_card`：Finset.eq_univ_of_card [Fintype α] (s : Finset α
) (hs : #s = Fintype.card α) : s = univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.IsCycle.orderOf`：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : 
DecidableEq α] [inst_1 : Fintype α], f.IsCycle → orderOf f = f.support.card
· 使用定理 `Equiv.Perm.closure_prime_cycle_swap`：closure_prime_cycle_swap {σ τ : Per
m α} (h0 : (Fintype.card α).Prime) (h1 : IsCycle σ) (h2 : σ.support = Finset.uni
v) (h3 : IsSwap τ) : clos…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Subgroup.closure_le`：closure_le : closure k <= K ↔ k subseteq K
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
-/
theorem subgroup_eq_top_of_swap_mem [DecidableEq α] {H : Subgroup (Perm α)}
    [d : DecidablePred (· ∈ H)] {τ : Perm α} (h0 : (Fintype.card α).Prime)
    (h1 : Fintype.card α ∣ Fintype.card H) (h2 : τ ∈ H) (h3 : IsSwap τ) : H = ⊤ := by
  have : Fact (Fintype.card α).Prime := ⟨h0⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card (Fintype.card α) h1
  have hσ1 : orderOf (σ : Perm α) = Fintype.card α := (Subgroup.orderOf_coe σ).trans hσ
  have hσ2 : IsCycle ↑σ := isCycle_of_prime_order'' h0 hσ1
  have hσ3 : (σ : Perm α).support = ⊤ :=
    Finset.eq_univ_of_card (σ : Perm α).support (hσ2.orderOf.symm.trans hσ1)
  have hσ4 : Subgroup.closure {↑σ, τ} = ⊤ := closure_prime_cycle_swap h0 hσ2 hσ3 h3
  rw [eq_top_iff, ← hσ4, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨Subtype.mem σ, h2⟩

section Partition

variable [DecidableEq α]

/-- The partition corresponding to a permutation -/
/-
**Equiv.Perm.partition** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：partition (σ : Perm α) : (Fintype.card α).Partition where parts
参数：σ : Perm α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The partition corresponding to a permutation
-/
def partition (σ : Perm α) : (Fintype.card α).Partition where
  parts := σ.cycleType + Multiset.replicate (Fintype.card α - #σ.support) 1
  parts_pos {n hn} := by
    rcases mem_add.mp hn with hn | hn
    · exact zero_lt_one.trans (one_lt_of_mem_cycleType hn)
    · exact lt_of_lt_of_le zero_lt_one (ge_of_eq (Multiset.eq_of_mem_replicate hn))
  parts_sum := by
    rw [sum_add, sum_cycleType, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, mul_one,
      add_tsub_cancel_of_le σ.support.card_le_univ]
/-
**Equiv.Perm.parts_partition** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：parts_partition {σ : Perm α} : σ.partition.parts = σ.cycleType + Multiset.
replicate (Fintype.card α - #σ.support) 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem parts_partition {σ : Perm α} :
    σ.partition.parts = σ.cycleType + Multiset.replicate (Fintype.card α - #σ.support) 1 :=
  rfl
/-
**Equiv.Perm.filter_parts_partition_eq_cycleType** 是 Mathlib 中的一个定理，位于命名空间 `Equi
v.Perm`。
形式化陈述：filter_parts_partition_eq_cycleType {σ : Perm α} : ((partition σ).parts.fi
lter fun n => 2 <= n) = σ.cycleType
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.parts_partition`：parts_partition {σ : Perm α} : σ.partition.p
arts = σ.cycleType + Multiset.replicate (Fintype.card α - #σ.support) 1
· 使用定理 `Multiset.filter_add`：filter_add (s t : Multiset α) : filter p (s + t) = 
filter p s + filter p t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.filter_eq_self`：filter_eq_self {s} : filter p s = s ↔ forall a 
in s, p a
· 使用定理 `Equiv.Perm.two_le_of_mem_cycleType`：two_le_of_mem_cycleType {σ : Perm α}
 {n : Nat} (h : n in σ.cycleType) : 2 <= n
· 使用定理 `Multiset.filter_eq_nil`：filter_eq_nil {s} : filter p s = 0 ↔ forall a in
 s, ¬p a
· 使用定理 `Multiset.eq_of_mem_replicate`：eq_of_mem_replicate {a b : α} {n} : b in r
eplicate n a -> b = a
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem filter_parts_partition_eq_cycleType {σ : Perm α} :
    ((partition σ).parts.filter fun n => 2 ≤ n) = σ.cycleType := by
  rw [parts_partition, filter_add, Multiset.filter_eq_self.2 fun _ => two_le_of_mem_cycleType,
    Multiset.filter_eq_nil.2 fun a h => ?_, add_zero]
  rw [Multiset.eq_of_mem_replicate h]
  decide
/-
**Equiv.Perm.partition_eq_of_isConj** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：partition_eq_of_isConj {σ τ : Perm α} : IsConj σ τ ↔ σ.partition = τ.parti
tion
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.isConj_iff_cycleType_eq`：isConj_iff_cycleType_eq {σ τ : Perm 
α} : IsConj σ τ ↔ σ.cycleType = τ.cycleType
· 使用定理 `Nat.Partition.ext_iff`：∀ {n : ℕ} {x y : n.Partition}, x = y ↔ x.parts = 
y.parts
· 使用定理 `Equiv.Perm.parts_partition`：parts_partition {σ : Perm α} : σ.partition.p
arts = σ.cycleType + Multiset.replicate (Fintype.card α - #σ.support) 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.sum_cycleType`：sum_cycleType (σ : Perm α) : σ.cycleType.sum =
 #σ.support
· 使用定理 `Equiv.Perm.filter_parts_partition_eq_cycleType`：filter_parts_partition_e
q_cycleType {σ : Perm α} : ((partition σ).parts.filter fun n => 2 <= n) = σ.cycl
eType
-/
theorem partition_eq_of_isConj {σ τ : Perm α} : IsConj σ τ ↔ σ.partition = τ.partition := by
  rw [isConj_iff_cycleType_eq]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Nat.Partition.ext_iff, parts_partition, parts_partition, ← sum_cycleType, ← sum_cycleType,
      h]
  · rw [← filter_parts_partition_eq_cycleType, ← filter_parts_partition_eq_cycleType, h]

end Partition

section IsSwap

variable [DecidableEq α]

/-
**Equiv.Perm.isSwap_iff_cycleType** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isSwap_iff_cycleType {σ : Perm α} : σ.IsSwap ↔ σ.cycleType = {2}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.IsCycle.cycleType`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : DecidableEq α] {σ : Equiv.Perm α},   σ.IsCycle → σ.cycleType = {σ.support.ca
rd}
· 使用定理 `Equiv.Perm.IsSwap.isCycle`：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : D
ecidableEq α], f.IsSwap → f.IsCycle
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Multiset.sum_singleton`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M
), {a}.sum = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isSwap_iff_cycleType {σ : Perm α} : σ.IsSwap ↔ σ.cycleType = {2} := by
  constructor
  · intro h
    simpa [h.isCycle.cycleType, card_support_eq_two] using h
  · intro h
    simp [← card_support_eq_two, ← sum_cycleType, h]

omit [Fintype α] in variable [Finite α] in
/-
**Equiv.Perm.IsSwap.orderOf** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsSwap`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [Finite α] {σ : Equiv.Perm α}, σ.I
sSwap → orderOf σ = 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.lcm_cycleType`：lcm_cycleType (σ : Perm α) : σ.cycleType.lcm =
 orderOf σ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.isSwap_iff_cycleType`：isSwap_iff_cycleType {σ : Perm α} : σ.I
sSwap ↔ σ.cycleType = {2}
· 使用定理 `Multiset.lcm_singleton`：lcm_singleton {a : α} : ({a} : Multiset α).lcm =
 normalize a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
-/
theorem IsSwap.orderOf {σ : Equiv.Perm α} (h : σ.IsSwap) :
    orderOf σ = 2 := by
  have := Fintype.ofFinite α
  rw [← lcm_cycleType, isSwap_iff_cycleType.mp h, Multiset.lcm_singleton, normalize_eq]

end IsSwap

/-!
### 3-cycles
-/

/-- A three-cycle is a cycle of length 3. -/
/-
**Equiv.Perm.IsThreeCycle** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：IsThreeCycle [DecidableEq α] (σ : Perm α) : Prop
参数：σ : Perm α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A three-cycle is a cycle of length 3.
-/
def IsThreeCycle [DecidableEq α] (σ : Perm α) : Prop :=
  σ.cycleType = {3}

namespace IsThreeCycle

variable [DecidableEq α] {σ : Perm α}

/-
**Equiv.Perm.IsThreeCycle.cycleType** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsThre
eCycle`。
形式化陈述：cycleType (h : IsThreeCycle σ) : σ.cycleType = {3}
参数：h : IsThreeCycle σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cycleType (h : IsThreeCycle σ) : σ.cycleType = {3} :=
  h
/-
**Equiv.Perm.IsThreeCycle.ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsThreeCy
cle`。
形式化陈述：ne_one (h : IsThreeCycle σ) : σ != 1
参数：h : IsThreeCycle σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleType_one`：cycleType_one : (1 : Perm α).cycleType = 0
· 使用定理 `Equiv.Perm.IsThreeCycle.cycleType`：cycleType (h : IsThreeCycle σ) : σ.cy
cleType = {3}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ne_one (h : IsThreeCycle σ) : σ ≠ 1 := by
  rintro rfl
  simpa using h.cycleType
/-
**Equiv.Perm.IsThreeCycle.card_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsT
hreeCycle`。
形式化陈述：card_support (h : IsThreeCycle σ) : #σ.support = 3
参数：h : IsThreeCycle σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.sum_cycleType`：sum_cycleType (σ : Perm α) : σ.cycleType.sum =
 #σ.support
· 使用定理 `Equiv.Perm.IsThreeCycle.cycleType`：cycleType (h : IsThreeCycle σ) : σ.cy
cleType = {3}
· 使用定理 `Multiset.sum_singleton`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M
), {a}.sum = a
-/
theorem card_support (h : IsThreeCycle σ) : #σ.support = 3 := by
  rw [← sum_cycleType, h.cycleType, Multiset.sum_singleton]
/-
**Equiv.Perm.IsThreeCycle._root_.card_support_eq_three_iff** 是 Mathlib 中的一个定理，位于
命名空间 `Equiv.Perm.IsThreeCycle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.card_support_eq_three_iff : #σ.support = 3 ↔ σ.IsThreeCycle := by
  refine ⟨fun h => ?_, IsThreeCycle.card_support⟩
  by_cases h0 : σ.cycleType = 0
  · rw [← sum_cycleType, h0, sum_zero] at h
    exact (ne_of_lt zero_lt_three h).elim
  obtain ⟨n, hn⟩ := exists_mem_of_ne_zero h0
  by_cases h1 : σ.cycleType.erase n = 0
  · rw [← sum_cycleType, ← cons_erase hn, h1, cons_zero, Multiset.sum_singleton] at h
    rw [IsThreeCycle, ← cons_erase hn, h1, h, ← cons_zero]
  obtain ⟨m, hm⟩ := exists_mem_of_ne_zero h1
  rw [← sum_cycleType, ← cons_erase hn, ← cons_erase hm, Multiset.sum_cons, Multiset.sum_cons] at h
  have : ∀ {k}, 2 ≤ m → 2 ≤ n → n + (m + k) = 3 → False := by lia
  cases this (two_le_of_mem_cycleType (mem_of_mem_erase hm)) (two_le_of_mem_cycleType hn) h
/-
**Equiv.Perm.IsThreeCycle.isCycle** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsThreeC
ycle`。
形式化陈述：isCycle (h : IsThreeCycle σ) : IsCycle σ
参数：h : IsThreeCycle σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.card_cycleType_eq_one`：card_cycleType_eq_one {σ : Perm α} : M
ultiset.card σ.cycleType = 1 ↔ σ.IsCycle
· 使用定理 `Equiv.Perm.IsThreeCycle.cycleType`：cycleType (h : IsThreeCycle σ) : σ.cy
cleType = {3}
· 使用定理 `Multiset.card_singleton`：card_singleton (a : α) : card ({a} : Multiset α
) = 1
-/
theorem isCycle (h : IsThreeCycle σ) : IsCycle σ := by
  rw [← card_cycleType_eq_one, h.cycleType, card_singleton]
/-
**Equiv.Perm.IsThreeCycle.sign** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsThreeCycl
e`。
形式化陈述：sign (h : IsThreeCycle σ) : sign σ = 1
参数：h : IsThreeCycle σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.sign_of_cycleType`：sign_of_cycleType (f : Perm α) : sign f = 
(-1 : Intˣ) ^ (f.cycleType.sum + Multiset.card f.cycleType)
· 使用定理 `Equiv.Perm.IsThreeCycle.cycleType`：cycleType (h : IsThreeCycle σ) : σ.cy
cleType = {3}
-/
theorem sign (h : IsThreeCycle σ) : sign σ = 1 := by
  rw [Equiv.Perm.sign_of_cycleType, h.cycleType]
  rfl
/-
**Equiv.Perm.IsThreeCycle.inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsThreeCycle
`。
形式化陈述：inv {f : Perm α} (h : IsThreeCycle f) : IsThreeCycle f⁻¹
参数：h : IsThreeCycle f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.IsThreeCycle.eq_1`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : DecidableEq α] (σ : Equiv.Perm α), σ.IsThreeCycle = (σ.cycleType = {3})
· 使用定理 `Equiv.Perm.cycleType_inv`：cycleType_inv (σ : Perm α) : σ⁻¹.cycleType = σ
.cycleType
-/
theorem inv {f : Perm α} (h : IsThreeCycle f) : IsThreeCycle f⁻¹ := by
  rwa [IsThreeCycle, cycleType_inv]

@[simp]
/-
**Equiv.Perm.IsThreeCycle.inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsThreeC
ycle`。
形式化陈述：inv_iff {f : Perm α} : IsThreeCycle f⁻¹ ↔ IsThreeCycle f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Equiv.Perm.IsThreeCycle.inv`：inv {f : Perm α} (h : IsThreeCycle f) : IsT
hreeCycle f⁻¹
-/
theorem inv_iff {f : Perm α} : IsThreeCycle f⁻¹ ↔ IsThreeCycle f :=
  ⟨by
    rw [← inv_inv f]
    apply inv, inv⟩
/-
**Equiv.Perm.IsThreeCycle.orderOf** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsThreeC
ycle`。
形式化陈述：orderOf {g : Perm α} (ht : IsThreeCycle g) : orderOf g = 3
参数：ht : IsThreeCycle g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.lcm_cycleType`：lcm_cycleType (σ : Perm α) : σ.cycleType.lcm =
 orderOf σ
· 使用定理 `Equiv.Perm.IsThreeCycle.cycleType`：cycleType (h : IsThreeCycle σ) : σ.cy
cleType = {3}
· 使用定理 `Multiset.lcm_singleton`：lcm_singleton {a : α} : ({a} : Multiset α).lcm =
 normalize a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
-/
theorem orderOf {g : Perm α} (ht : IsThreeCycle g) : orderOf g = 3 := by
  rw [← lcm_cycleType, ht.cycleType, Multiset.lcm_singleton, normalize_eq]
/-
**Equiv.Perm.IsThreeCycle.isThreeCycle_sq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.
IsThreeCycle`。
形式化陈述：isThreeCycle_sq {g : Perm α} (ht : IsThreeCycle g) : IsThreeCycle (g * g)
参数：ht : IsThreeCycle g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `card_support_eq_three_iff`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 DecidableEq α] {σ : Equiv.Perm α}, σ.support.card = 3 ↔ σ.IsThreeCycle
· 使用定理 `Equiv.Perm.support_pow_coprime`：support_pow_coprime {σ : Perm α} {n : Na
t} (h : Nat.Coprime n (orderOf σ)) : (σ ^ n).support = σ.support
· 使用定理 `Equiv.Perm.IsThreeCycle.orderOf`：orderOf {g : Perm α} (ht : IsThreeCycle
 g) : orderOf g = 3
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_gcd`：∀ {x y nx ny z : ℕ},   Mathlib.Meta.Norm
Num.IsNat x nx →     Mathlib.Meta.NormNum.IsNat y ny → nx.gcd ny = z → Mathlib.M
eta.NormNum.IsNat (x…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.nat_gcd_helper_1'`：nat_gcd_helper_1' (x y a b : Nat
) (h : y * b = x * a + 1) : Nat.gcd x y = 1
· 使用定理 `Equiv.Perm.IsThreeCycle.card_support`：card_support (h : IsThreeCycle σ) 
: #σ.support = 3
-/
theorem isThreeCycle_sq {g : Perm α} (ht : IsThreeCycle g) : IsThreeCycle (g * g) := by
  rw [← pow_two, ← card_support_eq_three_iff, support_pow_coprime, ht.card_support]
  rw [ht.orderOf]
  norm_num

end IsThreeCycle

section

variable [DecidableEq α]

/-
**Equiv.Perm.isThreeCycle_swap_mul_swap_same** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Pe
rm`。
形式化陈述：isThreeCycle_swap_mul_swap_same {a b c : α} (ab : a != b) (ac : a != c) (b
c : b != c) : IsThreeCycle (swap a b * swap a c)
参数：ab : a != b；ac : a != c；bc : b != c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Equiv.Perm.support_mul_le`：support_mul_le (f g : Perm α) : (f * g).suppo
rt <= f.support ⊔ g.support
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.Perm.support_swap`：support_swap {x y : α} (h : x != y) : support (
swap x y) = {x, y}
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.union_insert`：union_insert (a : α) (s t : Finset α) : s union ins
ert a t = insert a (s union t)
· 使用定理 `Finset.insert_union`：insert_union (a : α) (s t : Finset α) : insert a s 
union t = insert a (s union t)
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `card_support_eq_three_iff`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 DecidableEq α] {σ : Equiv.Perm α}, σ.support.card = 3 ↔ σ.IsThreeCycle
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
-/
theorem isThreeCycle_swap_mul_swap_same {a b c : α} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
    IsThreeCycle (swap a b * swap a c) := by
  suffices h : support (swap a b * swap a c) = {a, b, c} by
    rw [← card_support_eq_three_iff, h]
    simp [ab, ac, bc]
  apply le_antisymm ((support_mul_le _ _).trans fun x => _) fun x hx => ?_
  · simp [ab, ac]
  · simp only [mem_support, coe_mul]
    grind
/-
**Equiv.Perm.IsThreeCycle.support_eq_iff_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `
Equiv.Perm.IsThreeCycle`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] {g : Equiv.Pe
rm α} {a : α},   g.IsThreeCycle → (g.support = {a, g a, g (g a)} ↔ a ∈ g.support
)
参数：g.support = {a, g a, g (g a)} ↔ a ∈ g.support。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Finset.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : 
insert a s subseteq t
· 使用定理 `Equiv.Perm.apply_mem_support`：apply_mem_support {x : α} : f x in f.suppo
rt ↔ x in f.support
· 使用定理 `Equiv.Perm.IsThreeCycle.card_support`：card_support (h : IsThreeCycle σ) 
: #σ.support = 3
· 使用定理 `Finset.card_insert_eq_ite`：card_insert_eq_ite : #(insert a s) = if a in 
s then #s else #s + 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Equiv.Perm.IsThreeCycle.orderOf`：orderOf {g : Perm α} (ht : IsThreeCycle
 g) : orderOf g = 3
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
-/
theorem IsThreeCycle.support_eq_iff_mem_support
    {g : Perm α} {a : α} (hg3 : g.IsThreeCycle) :
    g.support = {a, g a, g (g a)} ↔ a ∈ g.support := by
  constructor
  · intro hg; simp [hg]
  · intro ha
    symm
    apply Finset.eq_of_subset_of_card_le
    · apply Finset.insert_subset ha
      apply Finset.insert_subset
      · rwa [Perm.apply_mem_support]
      simpa only [Finset.singleton_subset_iff, Perm.apply_mem_support]
    · rw [hg3.card_support]
      simp only [mem_support, ne_eq] at ha
      rw [Finset.card_insert_eq_ite, if_neg]
      · rw [Finset.card_insert_eq_ite, if_neg]
        · simp
        · simpa using Ne.symm ha
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        contrapose ha
        rcases ha with ha | ha
        · exact ha.symm
        · suffices (g ^ 3) a = a by simpa [pow_succ, ← ha] using this
          simp [← hg3.orderOf]
/-
**Equiv.Perm.IsThreeCycle.nodup_iff_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv
.Perm.IsThreeCycle`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] {g : Equiv.Pe
rm α} {a : α},   g.IsThreeCycle → ([a, g a, g (g a)].Nodup ↔ a ∈ g.support)
参数：[a, g a, g (g a)].Nodup ↔ a ∈ g.support。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.IsThreeCycle.support_eq_iff_mem_support`：∀ {α : Type u_1} [in
st : Fintype α] [inst_1 : DecidableEq α] {g : Equiv.Perm α} {a : α},   g.IsThree
Cycle → (g.support = {a, g a, g (g a)} ↔…
· 使用定理 `Equiv.Perm.IsThreeCycle.card_support`：card_support (h : IsThreeCycle σ) 
: #σ.support = 3
-/
theorem IsThreeCycle.nodup_iff_mem_support {g : Perm α} {a : α} (hg3 : g.IsThreeCycle) :
    [a, g a, g (g a)].Nodup ↔ a ∈ g.support := by
  constructor
  · intro ha
    rw [mem_support]
    grind
  rw [← support_eq_iff_mem_support hg3]
  intro ha
  suffices g.support.card = 3 by grind
  exact hg3.card_support
/-
**Equiv.Perm.IsThreeCycle.eq_swap_mul_swap_iff_mem_support** 是 Mathlib 中的一个定理，位于
命名空间 `Equiv.Perm.IsThreeCycle`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] {g : Equiv.Pe
rm α} {a : α},   g.IsThreeCycle → (g = Equiv.swap a (g a) * Equiv.swap (g a) (g 
(g a)) ↔ a ∈ g.support)
参数：g = Equiv.swap a (g a) * Equiv.swap (g a) (g (g a)) ↔ a ∈ g.support。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Equiv.Perm.IsCycle.ne_one`：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsCycl
e → f ≠ 1
· 使用定理 `Equiv.Perm.IsThreeCycle.isCycle`：isCycle (h : IsThreeCycle σ) : IsCycle 
σ
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.swap_self`：swap_self (a : α) : swap a a = Equiv.refl _
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.IsThreeCycle.support_eq_iff_mem_support`：∀ {α : Type u_1} [in
st : Fintype α] [inst_1 : DecidableEq α] {g : Equiv.Perm α} {a : α},   g.IsThree
Cycle → (g.support = {a, g a, g (g a)} ↔…
· 使用定理 `Equiv.Perm.IsThreeCycle.nodup_iff_mem_support`：∀ {α : Type u_1} [inst : 
Fintype α] [inst_1 : DecidableEq α] {g : Equiv.Perm α} {a : α},   g.IsThreeCycle
 → ([a, g a, g (g a)].Nodup ↔ a ∈ g…
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `Equiv.Perm.IsThreeCycle.orderOf`：orderOf {g : Perm α} (ht : IsThreeCycle
 g) : orderOf g = 3
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
-/
theorem IsThreeCycle.eq_swap_mul_swap_iff_mem_support
    {g : Perm α} {a : α} (hg3 : g.IsThreeCycle) :
    g = (swap a (g a)) * (swap (g a) (g (g a))) ↔ a ∈ g.support := by
  constructor
  · intro hg
    rw [mem_support]
    intro hx
    apply hg3.isCycle.ne_one
    simpa [hx] using! hg
  intro ha
  have ha' := hg3.support_eq_iff_mem_support.mpr ha
  have ha'' := hg3.nodup_iff_mem_support.mpr ha
  ext x
  simp only [coe_mul, Function.comp_apply]
  by_cases h : x ∈ g.support
  · simp only [ha', Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | (rfl | rfl)
    · rw [swap_apply_of_ne_of_ne (x := x) (by grind) (by grind)]
      simp
    · rw [swap_apply_left, swap_apply_of_ne_of_ne (by grind) (by grind)]
    · simp only [swap_apply_right]
      suffices (g ^ 3) a = a by simpa
      simp [← hg3.orderOf]
  · rw [swap_apply_of_ne_of_ne (x := x) (by grind) (by grind)]
    rw [swap_apply_of_ne_of_ne (x := x) (by grind) (by grind)]
    simpa [notMem_support] using! h

open Subgroup
/-
**Equiv.Perm.swap_mul_swap_same_mem_closure_three_cycles** 是 Mathlib 中的一个定理，位于命名
空间 `Equiv.Perm`。
形式化陈述：swap_mul_swap_same_mem_closure_three_cycles {a b c : α} (ab : a != b) (ac 
: a != c) : swap a b * swap a c in closure { σ : Perm α | IsThreeCycle σ }
参数：ab : a != b；ac : a != c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.swap_mul_self`：∀ {α : Type u_4} [inst : DecidableEq α] (i j : α), 
Equiv.swap i j * Equiv.swap i j = 1
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
· 使用定理 `Equiv.Perm.isThreeCycle_swap_mul_swap_same`：isThreeCycle_swap_mul_swap_s
ame {a b c : α} (ab : a != b) (ac : a != c) (bc : b != c) : IsThreeCycle (swap a
 b * swap a c)
-/
theorem swap_mul_swap_same_mem_closure_three_cycles {a b c : α} (ab : a ≠ b) (ac : a ≠ c) :
    swap a b * swap a c ∈ closure { σ : Perm α | IsThreeCycle σ } := by
  by_cases bc : b = c
  · subst bc
    simp [one_mem]
  exact subset_closure (isThreeCycle_swap_mul_swap_same ab ac bc)
/-
**Equiv.Perm.IsSwap.mul_mem_closure_three_cycles** 是 Mathlib 中的一个定理，位于命名空间 `Equi
v.Perm.IsSwap`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] {σ τ : Equiv.
Perm α},   σ.IsSwap → τ.IsSwap → σ * τ ∈ Subgroup.closure {σ | σ.IsThreeCycle}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.swap_mul_swap_same_mem_closure_three_cycles`：swap_mul_swap_sa
me_mem_closure_three_cycles {a b c : α} (ab : a != b) (ac : a != c) : swap a b *
 swap a c in closure { σ : Perm α | IsThreeC…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.swap_comm`：swap_comm (a b : α) : swap a b = swap b a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Equiv.swap_mul_self_mul`：∀ {α : Type u_4} [inst : DecidableEq α] (i j : 
α) (σ : Equiv.Perm α), Equiv.swap i j * (Equiv.swap i j * σ) = σ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsSwap.mul_mem_closure_three_cycles {σ τ : Perm α} (hσ : IsSwap σ) (hτ : IsSwap τ) :
    σ * τ ∈ closure { σ : Perm α | IsThreeCycle σ } := by
  obtain ⟨a, b, ab, rfl⟩ := hσ
  obtain ⟨c, d, cd, rfl⟩ := hτ
  by_cases ac : a = c
  · subst ac
    exact swap_mul_swap_same_mem_closure_three_cycles ab cd
  have h' : swap a b * swap c d = swap a b * swap a c * (swap c a * swap c d) := by
    simp [swap_comm c a, mul_assoc]
  rw [h']
  exact
    mul_mem (swap_mul_swap_same_mem_closure_three_cycles ab ac)
      (swap_mul_swap_same_mem_closure_three_cycles (Ne.symm ac) cd)

end

section

variable [DecidableEq α]

/-
**Equiv.Perm.cycleType_swap_mul_swap_of_nodup** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.P
erm`。
形式化陈述：cycleType_swap_mul_swap_of_nodup {x y z t : α} (h : [x, y, z, t].Nodup) : 
(swap x y * swap z t).cycleType = {2, 2}
参数：h : [x, y, z, t].Nodup。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.Disjoint.cycleType_mul`：∀ {α : Type u_1} [inst : Fintype α] [
inst_1 : DecidableEq α] {σ τ : Equiv.Perm α},   σ.Disjoint τ → (σ * τ).cycleType
 = σ.cycleType + τ.cycl…
· 使用定理 `Equiv.Perm.disjoint_swap_swap`：disjoint_swap_swap {x y z t : α} (h : [x,
 y, z, t].Nodup) : Disjoint (swap x y) (swap z t)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.isSwap_iff_cycleType`：isSwap_iff_cycleType {σ : Perm α} : σ.I
sSwap ↔ σ.cycleType = {2}
· 使用定理 `Equiv.Perm.swap_isSwap_iff`：swap_isSwap_iff {a b : α} : (swap a b).IsSwa
p ↔ a != b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cycleType_swap_mul_swap_of_nodup {x y z t : α} (h : [x, y, z, t].Nodup) :
    (swap x y * swap z t).cycleType = {2, 2} := by
  rw [(disjoint_swap_swap h).cycleType_mul]
  rw [isSwap_iff_cycleType.mp ?_, isSwap_iff_cycleType.mp ?_]
  · simp
  · rw [swap_isSwap_iff]; grind
  · rw [swap_isSwap_iff]; grind

end

end Equiv.Perm

