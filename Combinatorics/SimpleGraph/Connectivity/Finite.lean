/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.Data.Set.Card

/-!
# Counting walks of a given length

## Main definitions
- `walkLengthTwoEquivCommonNeighbors`: bijective correspondence between walks of length two
from `u` to `v` and common neighbours of `u` and `v`. Note that `u` and `v` may be the same.
- `finsetWalkLength`: the `Finset` of length-`n` walks from `u` to `v`.
This is used to give `{p : G.walk u v | p.length = n}` a `Fintype` instance, and it
can also be useful as a recursive description of this set when `V` is finite.

TODO: should this be extended further?
-/

public section

assert_not_exists Field

open Finset Function

universe u v w

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

/-
**SimpleGraph.ConnectedComponent.card_le_card_of_le** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph.ConnectedComponent`。
形式化陈述：∀ {V : Type u} [Finite V] {G G' : SimpleGraph V},   G ≤ G' → Nat.card G'.C
onnectedComponent ≤ Nat.card G.ConnectedComponent
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.card_le_card_of_surjective`：card_le_card_of_surjective {α : Type u} 
{β : Type v} [Finite α] (f : α -> β) (hf : Surjective f) : Nat.card β <= Nat.car
d α
· 使用定理 `SimpleGraph.ConnectedComponent.instFinite`：∀ {V : Type u} {G : SimpleGra
ph V} [Finite V], Finite G.ConnectedComponent
· 使用定理 `SimpleGraph.ConnectedComponent.surjective_map_ofLE`：surjective_map_ofLE 
{G' : SimpleGraph V} (h : G <= G') : (map <| Hom.ofLE h).Surjective
-/
theorem ConnectedComponent.card_le_card_of_le [Finite V] {G G' : SimpleGraph V} (h : G ≤ G') :
    Nat.card G'.ConnectedComponent ≤ Nat.card G.ConnectedComponent :=
  Nat.card_le_card_of_surjective _ <| ConnectedComponent.surjective_map_ofLE h

section Fintype

variable [DecidableEq V] [Fintype V] [DecidableRel G.Adj]

/-
**SimpleGraph.reachable_iff_exists_finsetWalkLength_nonempty** 是 Mathlib 中的一个定理，
位于命名空间 `SimpleGraph`。
形式化陈述：reachable_iff_exists_finsetWalkLength_nonempty (u v : V) : G.Reachable u v
 ↔ exists n : Fin (Fintype.card V), (G.finsetWalkLength n u v).Nonempty
参数：u v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.elim_path`：∀ {V : Type u} {G : SimpleGraph V} {p :
 Prop} {u v : V}, G.Reachable u v → (∀ (a : G.Path u v), p) → p
· 使用定理 `SimpleGraph.Walk.IsPath.length_lt`：∀ {V : Type u} {G : SimpleGraph V} [i
nst : Fintype V] {u v : V} {p : G.Walk u v}, p.IsPath → p.length < Fintype.card 
V
· 使用定理 `SimpleGraph.Path.isPath`：∀ {V : Type u} {G : SimpleGraph V} {u v : V} (p
 : G.Path u v), (↑p).IsPath
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reachable_iff_exists_finsetWalkLength_nonempty (u v : V) :
    G.Reachable u v ↔ ∃ n : Fin (Fintype.card V), (G.finsetWalkLength n u v).Nonempty := by
  constructor
  · intro r
    refine r.elim_path fun p => ?_
    refine ⟨⟨_, p.isPath.length_lt⟩, p, ?_⟩
    simp [mem_finsetWalkLength_iff]
  · rintro ⟨_, p, _⟩
    exact ⟨p⟩
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidableRel G.Reachable := fun u v =>
  decidable_of_iff' _ (reachable_iff_exists_finsetWalkLength_nonempty G u v)
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Fintype G.ConnectedComponent :=
  fast_instance% @Quotient.fintype _ _ G.reachableSetoid (inferInstance : DecidableRel G.Reachable)
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Decidable G.Preconnected :=
  inferInstanceAs <| Decidable (∀ u v, G.Reachable u v)
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Decidable G.Connected :=
  decidable_of_iff (G.Preconnected ∧ (Finset.univ : Finset V).Nonempty) <| by
    rw [connected_iff, ← Finset.univ_nonempty_iff]
/-
**SimpleGraph.instDecidableMemSupp** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：instDecidableMemSupp (c : G.ConnectedComponent) (v : V) : Decidable (v in 
c.supp)
参数：c : G.ConnectedComponent；v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableMemSupp (c : G.ConnectedComponent) (v : V) : Decidable (v ∈ c.supp) :=
  c.recOn (fun w ↦ decidable_of_iff (G.Reachable v w) <| by simp)
    (fun _ _ _ _ ↦ Subsingleton.elim _ _)

set_option backward.isDefEq.respectTransparency.types false in
variable {G} in
/-
**SimpleGraph.disjiUnion_supp_toFinset_eq_supp_toFinset** 是 Mathlib 中的一个引理，位于命名空
间 `SimpleGraph`。
形式化陈述：disjiUnion_supp_toFinset_eq_supp_toFinset {G' : SimpleGraph V} (h : G <= G
') (c' : ConnectedComponent G') [Fintype c'.supp] [DecidablePred fun c : G.Conne
ctedComponent => c.supp subseteq c'.supp] : .disjiUnion {c : ConnectedComponent 
G | c.supp subseteq c'.supp} (fun c => c.supp.toFinset) (fun x _ y _ hxy => by s
impa using pairwise_disjoint_supp_connectedComponent _ hxy) = c'.supp.toFinset
参数：h : G <= G'；c' : ConnectedComponent G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.disjiUnion_eq_biUnion`：disjiUnion_eq_biUnion (s : Finset α) (f : 
α -> Finset β) (hf) : s.disjiUnion f hf = s.biUnion f
· 使用引理 `Finset.coe_biUnion`：coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Se
t α), t x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用引理 `SimpleGraph.ConnectedComponent.biUnion_supp_eq_supp`：biUnion_supp_eq_sup
p {G G' : SimpleGraph V} (h : G <= G') (c' : ConnectedComponent G') : ⋃ (c : Con
nectedComponent G) (_ : c.supp subseteq c…
-/
lemma disjiUnion_supp_toFinset_eq_supp_toFinset {G' : SimpleGraph V} (h : G ≤ G')
    (c' : ConnectedComponent G') [Fintype c'.supp]
    [DecidablePred fun c : G.ConnectedComponent ↦ c.supp ⊆ c'.supp] :
    .disjiUnion {c : ConnectedComponent G | c.supp ⊆ c'.supp} (fun c ↦ c.supp.toFinset)
      (fun x _ y _ hxy ↦ by simpa using pairwise_disjoint_supp_connectedComponent _ hxy) =
      c'.supp.toFinset :=
  Finset.coe_injective <| by simpa using ConnectedComponent.biUnion_supp_eq_supp h _

end Fintype

/-- The odd components are the connected components of odd cardinality. This definition excludes
infinite components. -/
/-
**SimpleGraph.oddComponents** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：oddComponents : Set G.ConnectedComponent
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The odd components are the connected components of odd cardinality. This definit
ion excludes
infinite components.
-/
abbrev oddComponents : Set G.ConnectedComponent := {c : G.ConnectedComponent | Odd c.supp.ncard}

set_option backward.isDefEq.respectTransparency.types false in
/-
**SimpleGraph.ConnectedComponent.odd_oddComponents_ncard_subset_supp** 是 Mathlib
 中的一个定理，位于命名空间 `SimpleGraph.ConnectedComponent`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) [Finite V] {G' : SimpleGraph V},   G ≤ 
G' → ∀ (c' : G'.ConnectedComponent), Odd {c | c ∈ G.oddComponents ∧ c.supp ⊆ c'.
supp}.ncard ↔ Odd c'.supp.ncard
参数：G : SimpleGraph V；c' : G'.ConnectedComponent。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.card_eq_card_toFinset`：card_eq_card_toFinset (s : Set α) [Fintype s]
 : Nat.card s = s.toFinset.card
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.disjiUnion_supp_toFinset_eq_supp_toFinset`：disjiUnion_supp_t
oFinset_eq_supp_toFinset {G' : SimpleGraph V} (h : G <= G') (c' : ConnectedCompo
nent G') [Fintype c'.supp] [DecidablePred f…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_disjiUnion`：card_disjiUnion (s : Finset ι) (t : ι -> Finset 
M) (h) : #(s.disjiUnion t h) = ∑ a in s, #(t a)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
· 使用引理 `Finset.odd_sum_iff_odd_card_odd`：odd_sum_iff_odd_card_odd {s : Finset ι}
 (f : ι -> Nat) : Odd (∑ i in s, f i) ↔ Odd #{x in s | Odd (f x)}
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Set.toFinset_ofPred`：toFinset_ofPred [Fintype α] (p : α -> Prop) [Decida
blePred p] [Fintype { x | p x }] : Set.toFinset {x | p x} = Finset.univ.filter p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ConnectedComponent.odd_oddComponents_ncard_subset_supp [Finite V] {G'}
    (h : G ≤ G') (c' : ConnectedComponent G') :
    Odd {c ∈ G.oddComponents | c.supp ⊆ c'.supp}.ncard ↔ Odd c'.supp.ncard := by
  simp_rw [← Nat.card_coe_set_eq]
  classical
  cases nonempty_fintype V
  rw [Nat.card_eq_card_toFinset c'.supp, ← disjiUnion_supp_toFinset_eq_supp_toFinset h]
  simp only [Finset.card_disjiUnion, Set.toFinset_card, Fintype.card_ofFinset]
  rw [Finset.odd_sum_iff_odd_card_odd, Nat.card_eq_fintype_card, Fintype.card_ofFinset]
  congr! 2
  ext c
  simp_rw [Set.toFinset_ofPred, mem_filter, ← Set.ncard_coe_finset, coe_filter,
    mem_supp_iff, mem_univ, true_and, supp, and_comm]
/-
**SimpleGraph.odd_ncard_oddComponents** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：odd_ncard_oddComponents [Finite V] : Odd G.oddComponents.ncard ↔ Odd (Nat.
card V)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `set_fintype_card_eq_univ_iff`：set_fintype_card_eq_univ_iff [Fintype α] (
s : Set α) [Fintype s] : Fintype.card s = Fintype.card α ↔ s = Set.univ
· 使用引理 `SimpleGraph.iUnion_connectedComponentSupp`：iUnion_connectedComponentSupp
 (G : SimpleGraph V) : ⋃ c : G.ConnectedComponent, c.supp = Set.univ
· 使用引理 `Set.toFinset_iUnion`：toFinset_iUnion [Fintype β] [DecidableEq α] (f : β 
-> Set α) [forall w, Fintype (f w)] : Set.toFinset (⋃ (x : β), f x) = Finset.biU
nion (Fin…
· 使用定理 `Finset.card_biUnion`：card_biUnion [DecidableEq M] {t : ι -> Finset M} (h
 : (s : Set ι).PairwiseDisjoint t) : #(s.biUnion t) = ∑ u in s, #(t u)
· 使用定理 `Set.disjoint_toFinset`：disjoint_toFinset [Fintype s] [Fintype t] : Disjo
int s.toFinset t.toFinset ↔ Disjoint s t
· 使用引理 `SimpleGraph.pairwise_disjoint_supp_connectedComponent`：pairwise_disjoint
_supp_connectedComponent (G : SimpleGraph V) : Pairwise fun c c' : ConnectedComp
onent G => Disjoint c.supp c'.supp
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.ncard_coe_finset`：∀ {α : Type u_1} (s : Finset α), (↑s).ncard = s.ca
rd
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Finset.odd_sum_iff_odd_card_odd`：odd_sum_iff_odd_card_odd {s : Finset ι}
 (f : ι -> Nat) : Odd (∑ i in s, f i) ↔ Odd #{x in s | Odd (f x)}
-/
lemma odd_ncard_oddComponents [Finite V] : Odd G.oddComponents.ncard ↔ Odd (Nat.card V) := by
  classical
  cases nonempty_fintype V
  rw [Nat.card_eq_fintype_card]
  simp only [← (set_fintype_card_eq_univ_iff _).mpr G.iUnion_connectedComponentSupp,
    ← Set.toFinset_card, Set.toFinset_iUnion ConnectedComponent.supp]
  rw [Finset.card_biUnion
    (fun x _ y _ hxy ↦ Set.disjoint_toFinset.mpr (pairwise_disjoint_supp_connectedComponent _ hxy))]
  simp_rw [← Set.ncard_eq_toFinset_card', ← Finset.coe_filter_univ, Set.ncard_coe_finset]
  exact (Finset.odd_sum_iff_odd_card_odd (fun x : G.ConnectedComponent ↦ x.supp.ncard)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-
**SimpleGraph.ncard_oddComponents_mono** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：ncard_oddComponents_mono [Finite V] {G' : SimpleGraph V} (h : G <= G') : G
'.oddComponents.ncard <= G.oddComponents.ncard
参数：h : G <= G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nonempty_of_ncard_ne_zero`：nonempty_of_ncard_ne_zero (hs : s.ncard !
= 0) : s.Nonempty
· 使用定理 `Nat.not_odd_zero`：¬Odd 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.ConnectedComponent.odd_oddComponents_ncard_subset_supp`：∀ {V
 : Type u} (G : SimpleGraph V) [Finite V] {G' : SimpleGraph V},   G ≤ G' → ∀ (c'
 : G'.ConnectedComponent), Odd {c | c ∈ G.oddComponents …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `Nat.card_le_card_of_injective`：card_le_card_of_injective {α : Type u} {β
 : Type v} [Finite β] (f : α -> β) (hf : Injective f) : Nat.card α <= Nat.card β
· 使用定理 `SimpleGraph.ConnectedComponent.instFinite`：∀ {V : Type u} {G : SimpleGra
ph V} [Finite V], Finite G.ConnectedComponent
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用引理 `SimpleGraph.ConnectedComponent.eq_of_common_vertex`：eq_of_common_vertex 
{v : V} {c c' : ConnectedComponent G} (hc : v in c.supp) (hc' : v in c'.supp) : 
c = c'
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `SimpleGraph.ConnectedComponent.nonempty_supp`：nonempty_supp (C : G.Conne
ctedComponent) : C.supp.Nonempty
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
-/
lemma ncard_oddComponents_mono [Finite V] {G' : SimpleGraph V} (h : G ≤ G') :
     G'.oddComponents.ncard ≤ G.oddComponents.ncard := by
  have aux (c : G'.ConnectedComponent) (hc : Odd c.supp.ncard) :
      {c' : G.ConnectedComponent | Odd c'.supp.ncard ∧ c'.supp ⊆ c.supp}.Nonempty := by
    refine Set.nonempty_of_ncard_ne_zero fun h' ↦ Nat.not_odd_zero ?_
    rw [← h']
    exact (c.odd_oddComponents_ncard_subset_supp _ h).2 hc
  let f : G'.oddComponents → G.oddComponents :=
    fun ⟨c, hc⟩ ↦ ⟨(aux c hc).choose, (aux c hc).choose_spec.1⟩
  refine Nat.card_le_card_of_injective f fun c c' fcc' ↦ ?_
  simp only [Subtype.mk.injEq, f] at fcc'
  exact Subtype.val_injective (ConnectedComponent.eq_of_common_vertex
    ((fcc' ▸ (aux c.1 c.2).choose_spec.2) (ConnectedComponent.nonempty_supp _).some_mem)
      ((aux c'.1 c'.2).choose_spec.2 (ConnectedComponent.nonempty_supp _).some_mem))

end SimpleGraph

