/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Tactic.Order
public import Mathlib.Topology.Order.IsLUB

/-!
# Monotone functions on an order topology

This file contains lemmas about limits and continuity for monotone / antitone functions on
linearly-ordered sets (with the order topology). For example, we prove that a monotone function
has left and right limits at any point (`Monotone.tendsto_nhdsLT`, `Monotone.tendsto_nhdsGT`).

-/

public section

open Set Filter TopologicalSpace Topology Function

open OrderDual (toDual ofDual)

variable {α β : Type*}

section LinearOrder

variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [LinearOrder β]
  {s : Set α} {x : α} {f : α → β}

/-
**MonotoneOn.insert_of_continuousWithinAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonotoneOn.insert_of_continuousWithinAt [TopologicalSpace β] [OrderClosedT
opology β] (hf : MonotoneOn f s) (hx : ClusterPt x (𝓟 s)) (h'x : ContinuousWithi
nAt f s x) : MonotoneOn f (insert x s)
参数：hf : MonotoneOn f s；hx : ClusterPt x (𝓟 s)；h'x : ContinuousWithinAt f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.monotoneOn_insert_iff`：monotoneOn_insert_iff {a : α} : MonotoneOn f 
(insert a s) ↔ (forall b in s, b <= a -> f b <= f a) ∧ (forall b in s, a <= b ->
 f a <= f b) ∧ …
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `ge_of_tendsto`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [
inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter β
} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `Ioi_mem_nhds`：Ioi_mem_nhds (h : a < b) : Ioi a in 𝓝 b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `Iio_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iio a ∈ nhds b
-/
lemma MonotoneOn.insert_of_continuousWithinAt [TopologicalSpace β] [OrderClosedTopology β]
    (hf : MonotoneOn f s) (hx : ClusterPt x (𝓟 s)) (h'x : ContinuousWithinAt f s x) :
    MonotoneOn f (insert x s) := by
  have : (𝓝[s] x).NeBot := hx
  apply monotoneOn_insert_iff.2 ⟨fun b hb hbx ↦ ?_, fun b hb hxb ↦ ?_, hf⟩
  · rcases hbx.eq_or_lt with rfl | hbx
    · exact le_rfl
    simp only [ContinuousWithinAt] at h'x
    apply ge_of_tendsto h'x
    have : s ∩ Ioi b ∈ 𝓝[s] x := inter_mem_nhdsWithin _ (Ioi_mem_nhds hbx)
    filter_upwards [this] with y hy using hf hb hy.1 (le_of_lt hy.2)
  · rcases hxb.eq_or_lt with rfl | hxb
    · exact le_rfl
    simp only [ContinuousWithinAt] at h'x
    apply le_of_tendsto h'x
    have : s ∩ Iio b ∈ 𝓝[s] x := inter_mem_nhdsWithin _ (Iio_mem_nhds hxb)
    filter_upwards [this] with y hy
    exact hf hy.1 hb (le_of_lt hy.2)

/-- If a function is monotone on a set in a second countable topological space, then there
are only countably many points that have several preimages. -/
/-
**MonotoneOn.countable_setOfPred_two_preimages** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonotoneOn.countable_setOfPred_two_preimages [SecondCountableTopology α] (
hf : MonotoneOn f s) : Set.Countable {c | exists x y, x in s ∧ y in s ∧ x < y ∧ 
f x = c ∧ f y = c}
参数：hf : MonotoneOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Set.PairwiseDisjoint.countable_of_Ioo`：Set.PairwiseDisjoint.countable_of
_Ioo [SecondCountableTopology α] {y : α -> α} {s : Set α} (h : PairwiseDisjoint 
s fun x => Ioo x (y x)) (h'…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.countable_of_injective_of_countable_image`：countable_of_injective_of
_countable_image {s : Set α} {f : α -> β} (hf : InjOn f s) (hs : (f '' s).Counta
ble) : s.Countable
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If a function is monotone on a set in a second countable topological space, then
 there
are only countably many points that have several preimages.
-/
lemma MonotoneOn.countable_setOfPred_two_preimages [SecondCountableTopology α]
    (hf : MonotoneOn f s) :
    Set.Countable {c | ∃ x y, x ∈ s ∧ y ∈ s ∧ x < y ∧ f x = c ∧ f y = c} := by
  nontriviality α
  let t := {c | ∃ x, ∃ y, x ∈ s ∧ y ∈ s ∧ x < y ∧ f x = c ∧ f y = c}
  have : ∀ c ∈ t, ∃ x, ∃ y, x ∈ s ∧ y ∈ s ∧ x < y ∧ f x = c ∧ f y = c := fun c hc ↦ hc
  choose! x y hxs hys hxy hfx hfy using this
  let u := x '' t
  suffices H : Set.Countable (x '' t) by
    have : Set.InjOn x t := by
      intro c hc d hd hcd
      have : f (x c) = f (x d) := by simp [hcd]
      rwa [hfx _ hc, hfx _ hd] at this
    exact countable_of_injective_of_countable_image this H
  apply Set.PairwiseDisjoint.countable_of_Ioo (y := fun a ↦ y (f a)); swap
  · rintro a ⟨c, hc, rfl⟩
    rw [hfx _ hc]
    exact hxy _ hc
  simp only [PairwiseDisjoint, Set.Pairwise, mem_image, onFun, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro c hc d hd hcd
  wlog H : c < d generalizing c d with h
  · apply (h d hd c hc hcd.symm ?_).symm
    have : c ≠ d := fun h ↦ hcd (congrArg x h)
    order
  simp only [disjoint_iff_forall_ne, mem_Ioo, ne_eq, and_imp]
  rintro a xca ayc b xda ayd rfl
  rw [hfx _ hc] at ayc
  have : x d ≤ y c := (xda.trans ayc).le
  have : f (x d) ≤ f (y c) := hf (hxs _ hd) (hys _ hc) this
  rw [hfx _ hd, hfy _ hc] at this
  exact not_le.2 H this

@[deprecated (since := "2026-07-09")] alias MonotoneOn.countable_setOf_two_preimages :=
  MonotoneOn.countable_setOfPred_two_preimages

/-- If a function is monotone in a second countable topological space, then there
are only countably many points that have several preimages. -/
/-
**Monotone.countable_setOfPred_two_preimages** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.countable_setOfPred_two_preimages [SecondCountableTopology α] (hf
 : Monotone f) : Set.Countable {c | exists x y, x < y ∧ f x = c ∧ f y = c}
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `MonotoneOn.countable_setOfPred_two_preimages`：MonotoneOn.countable_setOf
Pred_two_preimages [SecondCountableTopology α] (hf : MonotoneOn f s) : Set.Count
able {c | exists x y, x in s ∧ y i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `monotoneOn_univ`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β}, MonotoneOn f Set.univ ↔ Monotone f

--- 原说明 ---
If a function is monotone in a second countable topological space, then there
are only countably many points that have several preimages.
-/
lemma Monotone.countable_setOfPred_two_preimages [SecondCountableTopology α]
    (hf : Monotone f) :
    Set.Countable {c | ∃ x y, x < y ∧ f x = c ∧ f y = c} := by
  rw [← monotoneOn_univ] at hf
  simpa using hf.countable_setOfPred_two_preimages

@[deprecated (since := "2026-07-09")] alias Monotone.countable_setOf_two_preimages :=
  Monotone.countable_setOfPred_two_preimages

/-- If a function is antitone on a set in a second countable topological space, then there
are only countably many points that have several preimages. -/
/-
**AntitoneOn.countable_setOfPred_two_preimages** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AntitoneOn.countable_setOfPred_two_preimages [SecondCountableTopology α] (
hf : AntitoneOn f s) : Set.Countable {c | exists x y, x in s ∧ y in s ∧ x < y ∧ 
f x = c ∧ f y = c}
参数：hf : AntitoneOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonotoneOn.countable_setOfPred_two_preimages`：MonotoneOn.countable_setOf
Pred_two_preimages [SecondCountableTopology α] (hf : MonotoneOn f s) : Set.Count
able {c | exists x y, x in s ∧ y i…
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…

--- 原说明 ---
If a function is antitone on a set in a second countable topological space, then
 there
are only countably many points that have several preimages.
-/
lemma AntitoneOn.countable_setOfPred_two_preimages [SecondCountableTopology α]
    (hf : AntitoneOn f s) :
    Set.Countable {c | ∃ x y, x ∈ s ∧ y ∈ s ∧ x < y ∧ f x = c ∧ f y = c} :=
  (MonotoneOn.countable_setOfPred_two_preimages hf.dual_right :)

@[deprecated (since := "2026-07-09")] alias AntitoneOn.countable_setOf_two_preimages :=
  AntitoneOn.countable_setOfPred_two_preimages

/-- If a function is antitone in a second countable topological space, then there
are only countably many points that have several preimages. -/
/-
**Antitone.countable_setOfPred_two_preimages** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antitone.countable_setOfPred_two_preimages [SecondCountableTopology α] (hf
 : Antitone f) : Set.Countable {c | exists x y, x < y ∧ f x = c ∧ f y = c}
参数：hf : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Monotone.countable_setOfPred_two_preimages`：Monotone.countable_setOfPred
_two_preimages [SecondCountableTopology α] (hf : Monotone f) : Set.Countable {c 
| exists x y, x < y ∧ f x = c ∧ …
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)

--- 原说明 ---
If a function is antitone in a second countable topological space, then there
are only countably many points that have several preimages.
-/
lemma Antitone.countable_setOfPred_two_preimages [SecondCountableTopology α]
    (hf : Antitone f) :
    Set.Countable {c | ∃ x y, x < y ∧ f x = c ∧ f y = c} :=
  (Monotone.countable_setOfPred_two_preimages hf.dual_right :)

@[deprecated (since := "2026-07-09")] alias Antitone.countable_setOf_two_preimages :=
  Antitone.countable_setOfPred_two_preimages

section Continuity

variable [TopologicalSpace β] [OrderTopology β] [SecondCountableTopology β]

/-- In a second countable space, the set of points where a monotone function is not right-continuous
within a set is at most countable. Superseded by `MonotoneOn.countable_not_continuousWithinAt`
which gives the two-sided version. -/
/-
**MonotoneOn.countable_not_continuousWithinAt_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.countable_not_continuousWithinAt_Ioi (hf : MonotoneOn f s) : Se
t.Countable {x in s | ¬ContinuousWithinAt f (s inter Ioi x) x}
参数：hf : MonotoneOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `countable_image_lt_image_Ioi_within`：countable_image_lt_image_Ioi_within
 [LinearOrder β] [SecondCountableTopology α] (t : Set β) (f : β -> α) : Set.Coun
table {x in t | exists z,…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithin_inter`：nhdsWithin_inter (a : α) (s t : Set α) : 𝓝[s inter t] 
a = 𝓝[s] a ⊓ 𝓝[t] a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ioo_mem_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ioo b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
In a second countable space, the set of points where a monotone function is not 
right-continuous
within a set is at most countable. Superseded by `MonotoneOn.countable_not_conti
nuousWithinAt`
which gives the two-sided version.
-/
theorem MonotoneOn.countable_not_continuousWithinAt_Ioi (hf : MonotoneOn f s) :
    Set.Countable {x ∈ s | ¬ContinuousWithinAt f (s ∩ Ioi x) x} := by
  apply (countable_image_lt_image_Ioi_within s f).mono
  rintro x ⟨xs, hx : ¬ContinuousWithinAt f (s ∩ Ioi x) x⟩
  dsimp only [mem_ofPred_eq]
  contrapose! hx
  refine tendsto_order.2 ⟨fun m hm => ?_, fun u hu => ?_⟩
  · filter_upwards [@self_mem_nhdsWithin _ _ x (s ∩ Ioi x)] with y hy
    exact hm.trans_le (hf xs hy.1 (le_of_lt hy.2))
  rcases hx xs u hu with ⟨v, vs, xv, fvu⟩
  have : s ∩ Ioo x v ∈ 𝓝[s ∩ Ioi x] x := by simp [nhdsWithin_inter, mem_inf_of_left,
    self_mem_nhdsWithin, mem_inf_of_right, Ioo_mem_nhdsGT xv]
  filter_upwards [this] with y hy
  exact (hf hy.1 vs hy.2.2.le).trans_lt fvu

/-- In a second countable space, the set of points where a monotone function is not left-continuous
within a set is at most countable. Superseded by `MonotoneOn.countable_not_continuousWithinAt`
which gives the two-sided version. -/
/-
**MonotoneOn.countable_not_continuousWithinAt_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.countable_not_continuousWithinAt_Iio (hf : MonotoneOn f s) : Se
t.Countable {x in s | ¬ContinuousWithinAt f (s inter Iio x) x}
参数：hf : MonotoneOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.countable_not_continuousWithinAt_Ioi`：MonotoneOn.countable_no
t_continuousWithinAt_Ioi (hf : MonotoneOn f s) : Set.Countable {x in s | ¬Contin
uousWithinAt f (s inter Ioi x) x}
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instSecondCountableTopologyOrderDual`：∀ {α : Type u} [inst : Topological
Space α] [h : SecondCountableTopology α], SecondCountableTopology αᵒᵈ
· 使用定理 `MonotoneOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn (⇑OrderDua
l.toD…

--- 原说明 ---
In a second countable space, the set of points where a monotone function is not 
left-continuous
within a set is at most countable. Superseded by `MonotoneOn.countable_not_conti
nuousWithinAt`
which gives the two-sided version.
-/
theorem MonotoneOn.countable_not_continuousWithinAt_Iio (hf : MonotoneOn f s) :
    Set.Countable {x ∈ s | ¬ContinuousWithinAt f (s ∩ Iio x) x} :=
  hf.dual.countable_not_continuousWithinAt_Ioi

/-- In a second countable space, the set of points where a monotone function is not continuous
within a set is at most countable. -/
/-
**MonotoneOn.countable_not_continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.countable_not_continuousWithinAt (hf : MonotoneOn f s) : Set.Co
untable {x in s | ¬ContinuousWithinAt f s x}
参数：hf : MonotoneOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `Set.Countable.union`：∀ {α : Type u} {s t : Set α}, s.Countable → t.Count
able → (s ∪ t).Countable
· 使用定理 `MonotoneOn.countable_not_continuousWithinAt_Ioi`：MonotoneOn.countable_no
t_continuousWithinAt_Ioi (hf : MonotoneOn f s) : Set.Countable {x in s | ¬Contin
uousWithinAt f (s inter Ioi x) x}
· 使用定理 `MonotoneOn.countable_not_continuousWithinAt_Iio`：MonotoneOn.countable_no
t_continuousWithinAt_Iio (hf : MonotoneOn f s) : Set.Countable {x in s | ¬Contin
uousWithinAt f (s inter Iio x) x}
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousWithinAt_iff_continuous_left'_right'`：∀ {α : Type u_1} {β : Ty
pe u_2} [inst : TopologicalSpace α] [inst_1 : LinearOrder α] [inst_2 : Topologic
alSpace β]   {s : Set α} {a : α} {f …

--- 原说明 ---
In a second countable space, the set of points where a monotone function is not 
continuous
within a set is at most countable.
-/
theorem MonotoneOn.countable_not_continuousWithinAt (hf : MonotoneOn f s) :
    Set.Countable {x ∈ s | ¬ContinuousWithinAt f s x} := by
  apply (hf.countable_not_continuousWithinAt_Ioi.union hf.countable_not_continuousWithinAt_Iio).mono
  refine compl_subset_compl.1 ?_
  simp only [compl_union]
  rintro x ⟨hx, h'x⟩
  simp only [mem_compl_iff, mem_ofPred_eq, not_and, not_not] at hx h'x ⊢
  intro xs
  exact continuousWithinAt_iff_continuous_left'_right'.2 ⟨h'x xs, hx xs⟩

/-- In a second countable space, the set of points where a monotone function is not continuous
is at most countable. -/
/-
**Monotone.countable_not_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.countable_not_continuousAt (hf : Monotone f) : Set.Countable {x |
 ¬ContinuousAt f x}
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MonotoneOn.countable_not_continuousWithinAt`：MonotoneOn.countable_not_co
ntinuousWithinAt (hf : MonotoneOn f s) : Set.Countable {x in s | ¬ContinuousWith
inAt f s x}
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s

--- 原说明 ---
In a second countable space, the set of points where a monotone function is not 
continuous
is at most countable.
-/
theorem Monotone.countable_not_continuousAt (hf : Monotone f) :
    Set.Countable {x | ¬ContinuousAt f x} := by
  simpa [continuousWithinAt_univ] using (hf.monotoneOn univ).countable_not_continuousWithinAt

/-- In a second countable space, the set of points where an antitone function is not continuous
within a set is at most countable. -/
/-
**_root_.AntitoneOn.countable_not_continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：_root_.AntitoneOn.countable_not_continuousWithinAt {s : Set α} (hf : Antit
oneOn f s) : Set.Countable {x in s | ¬ContinuousWithinAt f s x}
参数：hf : AntitoneOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a second countable space, the set of points where an antitone function is not
 continuous
within a set is at most countable.
-/
theorem _root_.AntitoneOn.countable_not_continuousWithinAt
    {s : Set α} (hf : AntitoneOn f s) :
    Set.Countable {x ∈ s | ¬ContinuousWithinAt f s x} :=
  hf.dual_right.countable_not_continuousWithinAt

/-- In a second countable space, the set of points where an antitone function is not continuous
is at most countable. -/
/-
**Antitone.countable_not_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.countable_not_continuousAt (hf : Antitone f) : Set.Countable {x |
 ¬ContinuousAt f x}
参数：hf : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.countable_not_continuousAt`：Monotone.countable_not_continuousAt
 (hf : Monotone f) : Set.Countable {x | ¬ContinuousAt f x}
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instSecondCountableTopologyOrderDual`：∀ {α : Type u} [inst : Topological
Space α] [h : SecondCountableTopology α], SecondCountableTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)

--- 原说明 ---
In a second countable space, the set of points where an antitone function is not
 continuous
is at most countable.
-/
theorem Antitone.countable_not_continuousAt (hf : Antitone f) :
    Set.Countable {x | ¬ContinuousAt f x} :=
  hf.dual_right.countable_not_continuousAt

end Continuity

section OrdContinuous

variable [TopologicalSpace β] [OrderTopology β]

/-- A monotone left-continuous function is left-continuous in the order-theoretic sense. -/
@[to_dual
/-- A monotone right-continuous function is right-continuous in the order-theoretic sense. -/
]
/-
**Monotone.leftOrdContinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.leftOrdContinuous (hf : Monotone f) (cont : forall x, ContinuousW
ithinAt f (Iic x) x) : LeftOrdContinuous f
参数：hf : Monotone f；cont : forall x, ContinuousWithinAt f (Iic x) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.isLUB_of_tendsto`：IsLUB.isLUB_of_tendsto [Preorder γ] [Topological
Space γ] [OrderClosedTopology γ] {f : α -> γ} {s : Set α} {a : α} {b : γ} (hf : 
MonotoneOn f…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Monotone.leftOrdContinuous (hf : Monotone f)
    (cont : ∀ x, ContinuousWithinAt f (Iic x) x) : LeftOrdContinuous f :=
  fun s x hs hx ↦ IsLUB.isLUB_of_tendsto (hf.monotoneOn s) hx hs ((cont x).mono hx.1)

/-- A monotone continuous function is left-continuous in the order-theoretic sense. -/
@[to_dual
/-- A monotone continuous function is right-continuous in the order-theoretic sense. -/
]
/-
**Continuous.leftOrdContinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.leftOrdContinuous (cont : Continuous f) (hf : Monotone f) : Lef
tOrdContinuous f
参数：cont : Continuous f；hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.leftOrdContinuous`：Monotone.leftOrdContinuous (hf : Monotone f)
 (cont : forall x, ContinuousWithinAt f (Iic x) x) : LeftOrdContinuous f
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
-/
theorem Continuous.leftOrdContinuous (cont : Continuous f) (hf : Monotone f) :
    LeftOrdContinuous f :=
  hf.leftOrdContinuous fun _ ↦ cont.continuousWithinAt

end OrdContinuous

end LinearOrder

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderClosedTopology β]

/-- A monotone function continuous at the supremum of a nonempty set sends this supremum to
the supremum of the image of this set. -/
/-
**MonotoneOn.map_csSup_of_continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.map_csSup_of_continuousWithinAt {f : α -> β} {A : Set α} (Cf : 
ContinuousWithinAt f A (sSup A)) (Mf : MonotoneOn f A) (A_nonemp : A.Nonempty) (
A_bdd : BddAbove A
参数：Cf : ContinuousWithinAt f A (sSup A)；Mf : MonotoneOn f A；A_nonemp : A.Nonempt
y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLUB.csSup_eq`：IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup 
s = a
· 使用定理 `IsLUB.isLUB_of_tendsto`：IsLUB.isLUB_of_tendsto [Preorder γ] [Topological
Space γ] [OrderClosedTopology γ] {f : α -> γ} {s : Set α} {a : α} {b : γ} (hf : 
MonotoneOn f…
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty

--- 原说明 ---
A monotone function continuous at the supremum of a nonempty set sends this supr
emum to
the supremum of the image of this set.
-/
theorem MonotoneOn.map_csSup_of_continuousWithinAt {f : α → β} {A : Set α}
    (Cf : ContinuousWithinAt f A (sSup A))
    (Mf : MonotoneOn f A) (A_nonemp : A.Nonempty) (A_bdd : BddAbove A := by bddDefault) :
    f (sSup A) = sSup (f '' A) :=
  --This is a particular case of the more general `IsLUB.isLUB_of_tendsto`
  .symm <| ((isLUB_csSup A_nonemp A_bdd).isLUB_of_tendsto Mf A_nonemp <|
    Cf.mono_left fun ⦃_⦄ a ↦ a).csSup_eq (A_nonemp.image f)

/-- A monotone function continuous at the supremum of a nonempty set sends this supremum to
the supremum of the image of this set. -/
/-
**Monotone.map_csSup_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.map_csSup_of_continuousAt {f : α -> β} {A : Set α} (Cf : Continuo
usAt f (sSup A)) (Mf : Monotone f) (A_nonemp : A.Nonempty) (A_bdd : BddAbove A
参数：Cf : ContinuousAt f (sSup A)；Mf : Monotone f；A_nonemp : A.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.map_csSup_of_continuousWithinAt`：MonotoneOn.map_csSup_of_cont
inuousWithinAt {f : α -> β} {A : Set α} (Cf : ContinuousWithinAt f A (sSup A)) (
Mf : MonotoneOn f A) (A_nonemp :…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s

--- 原说明 ---
A monotone function continuous at the supremum of a nonempty set sends this supr
emum to
the supremum of the image of this set.
-/
theorem Monotone.map_csSup_of_continuousAt {f : α → β} {A : Set α}
    (Cf : ContinuousAt f (sSup A)) (Mf : Monotone f) (A_nonemp : A.Nonempty)
    (A_bdd : BddAbove A := by bddDefault) : f (sSup A) = sSup (f '' A) :=
  MonotoneOn.map_csSup_of_continuousWithinAt Cf.continuousWithinAt
    (Mf.monotoneOn _) A_nonemp A_bdd

/-- A monotone function continuous at the indexed supremum over a nonempty `Sort` sends this indexed
supremum to the indexed supremum of the composition. -/
/-
**Monotone.map_ciSup_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.map_ciSup_of_continuousAt {ι : Sort*} [Nonempty ι] {f : α -> β} {
g : ι -> α} (Cf : ContinuousAt f (iSup g)) (Mf : Monotone f) (bdd : BddAbove (ra
nge g)
参数：Cf : ContinuousAt f (iSup g)；Mf : Monotone f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Monotone.map_csSup_of_continuousAt`：Monotone.map_csSup_of_continuousAt {
f : α -> β} {A : Set α} (Cf : ContinuousAt f (sSup A)) (Mf : Monotone f) (A_none
mp : A.Nonempty) (A_bdd …
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)

--- 原说明 ---
A monotone function continuous at the indexed supremum over a nonempty `Sort` se
nds this indexed
supremum to the indexed supremum of the composition.
-/
theorem Monotone.map_ciSup_of_continuousAt {ι : Sort*} [Nonempty ι] {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iSup g)) (Mf : Monotone f)
    (bdd : BddAbove (range g) := by bddDefault) : f (⨆ i, g i) = ⨆ i, f (g i) := by
  rw [iSup, Monotone.map_csSup_of_continuousAt Cf Mf (range_nonempty g) bdd, ← range_comp, iSup,
    comp_def]

/-- A monotone function continuous at the infimum of a nonempty set sends this infimum to
the infimum of the image of this set. -/
/-
**MonotoneOn.map_csInf_of_continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.map_csInf_of_continuousWithinAt {f : α -> β} {A : Set α} (Cf : 
ContinuousWithinAt f A (sInf A)) (Mf : MonotoneOn f A) (A_nonemp : A.Nonempty) (
A_bdd : BddBelow A
参数：Cf : ContinuousWithinAt f A (sInf A)；Mf : MonotoneOn f A；A_nonemp : A.Nonempt
y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.map_csSup_of_continuousWithinAt`：MonotoneOn.map_csSup_of_cont
inuousWithinAt {f : α -> β} {A : Set α} (Cf : ContinuousWithinAt f A (sSup A)) (
Mf : MonotoneOn f A) (A_nonemp :…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `MonotoneOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn (⇑OrderDua
l.toD…

--- 原说明 ---
A monotone function continuous at the infimum of a nonempty set sends this infim
um to
the infimum of the image of this set.
-/
theorem MonotoneOn.map_csInf_of_continuousWithinAt {f : α → β} {A : Set α}
    (Cf : ContinuousWithinAt f A (sInf A))
    (Mf : MonotoneOn f A) (A_nonemp : A.Nonempty) (A_bdd : BddBelow A := by bddDefault) :
    f (sInf A) = sInf (f '' A) :=
  MonotoneOn.map_csSup_of_continuousWithinAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual A_nonemp A_bdd

/-- A monotone function continuous at the infimum of a nonempty set sends this infimum to
the infimum of the image of this set. -/
/-
**Monotone.map_csInf_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.map_csInf_of_continuousAt {f : α -> β} {A : Set α} (Cf : Continuo
usAt f (sInf A)) (Mf : Monotone f) (A_nonemp : A.Nonempty) (A_bdd : BddBelow A
参数：Cf : ContinuousAt f (sInf A)；Mf : Monotone f；A_nonemp : A.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_csSup_of_continuousAt`：Monotone.map_csSup_of_continuousAt {
f : α -> β} {A : Set α} (Cf : ContinuousAt f (sSup A)) (Mf : Monotone f) (A_none
mp : A.Nonempty) (A_bdd …
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…

--- 原说明 ---
A monotone function continuous at the infimum of a nonempty set sends this infim
um to
the infimum of the image of this set.
-/
theorem Monotone.map_csInf_of_continuousAt {f : α → β} {A : Set α} (Cf : ContinuousAt f (sInf A))
    (Mf : Monotone f) (A_nonemp : A.Nonempty) (A_bdd : BddBelow A := by bddDefault) :
    f (sInf A) = sInf (f '' A) :=
  Monotone.map_csSup_of_continuousAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual A_nonemp A_bdd

/-- A monotone function continuous at the indexed infimum over a nonempty `Sort` sends this indexed
infimum to the indexed infimum of the composition. -/
/-
**Monotone.map_ciInf_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.map_ciInf_of_continuousAt {ι : Sort*} [Nonempty ι] {f : α -> β} {
g : ι -> α} (Cf : ContinuousAt f (iInf g)) (Mf : Monotone f) (bdd : BddBelow (ra
nge g)
参数：Cf : ContinuousAt f (iInf g)；Mf : Monotone f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `Monotone.map_csInf_of_continuousAt`：Monotone.map_csInf_of_continuousAt {
f : α -> β} {A : Set α} (Cf : ContinuousAt f (sInf A)) (Mf : Monotone f) (A_none
mp : A.Nonempty) (A_bdd …
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)

--- 原说明 ---
A monotone function continuous at the indexed infimum over a nonempty `Sort` sen
ds this indexed
infimum to the indexed infimum of the composition.
-/
theorem Monotone.map_ciInf_of_continuousAt {ι : Sort*} [Nonempty ι] {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iInf g)) (Mf : Monotone f)
    (bdd : BddBelow (range g) := by bddDefault) : f (⨅ i, g i) = ⨅ i, f (g i) := by
  rw [iInf, Monotone.map_csInf_of_continuousAt Cf Mf (range_nonempty g) bdd, ← range_comp, iInf,
    comp_def]

/-- An antitone function continuous at the infimum of a nonempty set sends this infimum to
the supremum of the image of this set. -/
/-
**AntitoneOn.map_csInf_of_continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.map_csInf_of_continuousWithinAt {f : α -> β} {A : Set α} (Cf : 
ContinuousWithinAt f A (sInf A)) (Af : AntitoneOn f A) (A_nonemp : A.Nonempty) (
A_bdd : BddBelow A
参数：Cf : ContinuousWithinAt f A (sInf A)；Af : AntitoneOn f A；A_nonemp : A.Nonempt
y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.map_csInf_of_continuousWithinAt`：MonotoneOn.map_csInf_of_cont
inuousWithinAt {f : α -> β} {A : Set α} (Cf : ContinuousWithinAt f A (sInf A)) (
Mf : MonotoneOn f A) (A_nonemp :…
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…

--- 原说明 ---
An antitone function continuous at the infimum of a nonempty set sends this infi
mum to
the supremum of the image of this set.
-/
theorem AntitoneOn.map_csInf_of_continuousWithinAt {f : α → β} {A : Set α}
    (Cf : ContinuousWithinAt f A (sInf A))
    (Af : AntitoneOn f A) (A_nonemp : A.Nonempty) (A_bdd : BddBelow A := by bddDefault) :
    f (sInf A) = sSup (f '' A) :=
  MonotoneOn.map_csInf_of_continuousWithinAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

/-- An antitone function continuous at the infimum of a nonempty set sends this infimum to
the supremum of the image of this set. -/
/-
**Antitone.map_csInf_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.map_csInf_of_continuousAt {f : α -> β} {A : Set α} (Cf : Continuo
usAt f (sInf A)) (Af : Antitone f) (A_nonemp : A.Nonempty) (A_bdd : BddBelow A
参数：Cf : ContinuousAt f (sInf A)；Af : Antitone f；A_nonemp : A.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_csInf_of_continuousAt`：Monotone.map_csInf_of_continuousAt {
f : α -> β} {A : Set α} (Cf : ContinuousAt f (sInf A)) (Mf : Monotone f) (A_none
mp : A.Nonempty) (A_bdd …
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)

--- 原说明 ---
An antitone function continuous at the infimum of a nonempty set sends this infi
mum to
the supremum of the image of this set.
-/
theorem Antitone.map_csInf_of_continuousAt {f : α → β} {A : Set α} (Cf : ContinuousAt f (sInf A))
    (Af : Antitone f) (A_nonemp : A.Nonempty) (A_bdd : BddBelow A := by bddDefault) :
    f (sInf A) = sSup (f '' A) :=
  Monotone.map_csInf_of_continuousAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

/-- An antitone function continuous at the indexed infimum over a nonempty `Sort` sends this indexed
infimum to the indexed supremum of the composition. -/
/-
**Antitone.map_ciInf_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.map_ciInf_of_continuousAt {ι : Sort*} [Nonempty ι] {f : α -> β} {
g : ι -> α} (Cf : ContinuousAt f (iInf g)) (Af : Antitone f) (bdd : BddBelow (ra
nge g)
参数：Cf : ContinuousAt f (iInf g)；Af : Antitone f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `Antitone.map_csInf_of_continuousAt`：Antitone.map_csInf_of_continuousAt {
f : α -> β} {A : Set α} (Cf : ContinuousAt f (sInf A)) (Af : Antitone f) (A_none
mp : A.Nonempty) (A_bdd …
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)

--- 原说明 ---
An antitone function continuous at the indexed infimum over a nonempty `Sort` se
nds this indexed
infimum to the indexed supremum of the composition.
-/
theorem Antitone.map_ciInf_of_continuousAt {ι : Sort*} [Nonempty ι] {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iInf g)) (Af : Antitone f)
    (bdd : BddBelow (range g) := by bddDefault) : f (⨅ i, g i) = ⨆ i, f (g i) := by
  rw [iInf, Antitone.map_csInf_of_continuousAt Cf Af (range_nonempty g) bdd, ← range_comp, iSup,
    comp_def]

/-- An antitone function continuous at the supremum of a nonempty set sends this supremum to
the infimum of the image of this set. -/
/-
**AntitoneOn.map_csSup_of_continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.map_csSup_of_continuousWithinAt {f : α -> β} {A : Set α} (Cf : 
ContinuousWithinAt f A (sSup A)) (Af : AntitoneOn f A) (A_nonemp : A.Nonempty) (
A_bdd : BddAbove A
参数：Cf : ContinuousWithinAt f A (sSup A)；Af : AntitoneOn f A；A_nonemp : A.Nonempt
y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.map_csSup_of_continuousWithinAt`：MonotoneOn.map_csSup_of_cont
inuousWithinAt {f : α -> β} {A : Set α} (Cf : ContinuousWithinAt f A (sSup A)) (
Mf : MonotoneOn f A) (A_nonemp :…
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…

--- 原说明 ---
An antitone function continuous at the supremum of a nonempty set sends this sup
remum to
the infimum of the image of this set.
-/
theorem AntitoneOn.map_csSup_of_continuousWithinAt {f : α → β} {A : Set α}
    (Cf : ContinuousWithinAt f A (sSup A))
    (Af : AntitoneOn f A) (A_nonemp : A.Nonempty) (A_bdd : BddAbove A := by bddDefault) :
    f (sSup A) = sInf (f '' A) :=
  MonotoneOn.map_csSup_of_continuousWithinAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

/-- An antitone function continuous at the supremum of a nonempty set sends this supremum to
the infimum of the image of this set. -/
/-
**Antitone.map_csSup_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.map_csSup_of_continuousAt {f : α -> β} {A : Set α} (Cf : Continuo
usAt f (sSup A)) (Af : Antitone f) (A_nonemp : A.Nonempty) (A_bdd : BddAbove A
参数：Cf : ContinuousAt f (sSup A)；Af : Antitone f；A_nonemp : A.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_csSup_of_continuousAt`：Monotone.map_csSup_of_continuousAt {
f : α -> β} {A : Set α} (Cf : ContinuousAt f (sSup A)) (Mf : Monotone f) (A_none
mp : A.Nonempty) (A_bdd …
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)

--- 原说明 ---
An antitone function continuous at the supremum of a nonempty set sends this sup
remum to
the infimum of the image of this set.
-/
theorem Antitone.map_csSup_of_continuousAt {f : α → β} {A : Set α} (Cf : ContinuousAt f (sSup A))
    (Af : Antitone f) (A_nonemp : A.Nonempty) (A_bdd : BddAbove A := by bddDefault) :
    f (sSup A) = sInf (f '' A) :=
  Monotone.map_csSup_of_continuousAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

/-- An antitone function continuous at the indexed supremum over a nonempty `Sort` sends this
indexed supremum to the indexed infimum of the composition. -/
/-
**Antitone.map_ciSup_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.map_ciSup_of_continuousAt {ι : Sort*} [Nonempty ι] {f : α -> β} {
g : ι -> α} (Cf : ContinuousAt f (iSup g)) (Af : Antitone f) (bdd : BddAbove (ra
nge g)
参数：Cf : ContinuousAt f (iSup g)；Af : Antitone f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Antitone.map_csSup_of_continuousAt`：Antitone.map_csSup_of_continuousAt {
f : α -> β} {A : Set α} (Cf : ContinuousAt f (sSup A)) (Af : Antitone f) (A_none
mp : A.Nonempty) (A_bdd …
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)

--- 原说明 ---
An antitone function continuous at the indexed supremum over a nonempty `Sort` s
ends this
indexed supremum to the indexed infimum of the composition.
-/
theorem Antitone.map_ciSup_of_continuousAt {ι : Sort*} [Nonempty ι] {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iSup g)) (Af : Antitone f)
    (bdd : BddAbove (range g) := by bddDefault) : f (⨆ i, g i) = ⨅ i, f (g i) := by
  rw [iSup, Antitone.map_csSup_of_continuousAt Cf Af (range_nonempty g) bdd, ← range_comp, iInf,
    comp_def]

end ConditionallyCompleteLinearOrder

section CompleteLinearOrder

variable [CompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [CompleteLinearOrder β]
  [TopologicalSpace β] [OrderClosedTopology β]

/-
**sSup_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_mem_closure {s : Set α} (hs : s.Nonempty) : sSup s in closure s
参数：hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.mem_closure`：IsLUB.mem_closure {a : α} {s : Set α} (ha : IsLUB s a
) (hs : s.Nonempty) : a in closure s
· 使用定理 `isLUB_sSup`：isLUB_sSup (s : Set α) : IsLUB s (sSup s)
-/
theorem sSup_mem_closure {s : Set α} (hs : s.Nonempty) : sSup s ∈ closure s :=
  (isLUB_sSup s).mem_closure hs
/-
**sInf_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sInf_mem_closure {s : Set α} (hs : s.Nonempty) : sInf s in closure s
参数：hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.mem_closure`：IsGLB.mem_closure {a : α} {s : Set α} (ha : IsGLB s a
) (hs : s.Nonempty) : a in closure s
· 使用定理 `isGLB_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] (s : Set 
α), IsGLB s (sInf s)
-/
theorem sInf_mem_closure {s : Set α} (hs : s.Nonempty) : sInf s ∈ closure s :=
  (isGLB_sInf s).mem_closure hs
/-
**IsClosed.sSup_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.sSup_mem {s : Set α} (hs : s.Nonempty) (hc : IsClosed s) : sSup s
 in s
参数：hs : s.Nonempty；hc : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.mem_of_isClosed`：IsLUB.mem_of_isClosed {a : α} {s : Set α} (ha : I
sLUB s a) (hs : s.Nonempty) (sc : IsClosed s) : a in s
· 使用定理 `isLUB_sSup`：isLUB_sSup (s : Set α) : IsLUB s (sSup s)
-/
theorem IsClosed.sSup_mem {s : Set α} (hs : s.Nonempty) (hc : IsClosed s) : sSup s ∈ s :=
  (isLUB_sSup s).mem_of_isClosed hs hc
/-
**IsClosed.sInf_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.sInf_mem {s : Set α} (hs : s.Nonempty) (hc : IsClosed s) : sInf s
 in s
参数：hs : s.Nonempty；hc : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.mem_of_isClosed`：IsGLB.mem_of_isClosed {a : α} {s : Set α} (ha : I
sGLB s a) (hs : s.Nonempty) (sc : IsClosed s) : a in s
· 使用定理 `isGLB_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] (s : Set 
α), IsGLB s (sInf s)
-/
theorem IsClosed.sInf_mem {s : Set α} (hs : s.Nonempty) (hc : IsClosed s) : sInf s ∈ s :=
  (isGLB_sInf s).mem_of_isClosed hs hc

/-- A monotone function `f` sending `bot` to `bot` and continuous at the supremum of a set sends
this supremum to the supremum of the image of this set. -/
/-
**MonotoneOn.map_sSup_of_continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.map_sSup_of_continuousWithinAt {f : α -> β} {s : Set α} (Cf : C
ontinuousWithinAt f s (sSup s)) (Mf : MonotoneOn f s) (fbot : f ⊥ = ⊥) : f (sSup
 s) = sSup (f '' s)
参数：Cf : ContinuousWithinAt f s (sSup s)；Mf : MonotoneOn f s；fbot : f ⊥ = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_empty`：sSup_empty : sSup ∅ = (⊥ : α)
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MonotoneOn.map_csSup_of_continuousWithinAt`：MonotoneOn.map_csSup_of_cont
inuousWithinAt {f : α -> β} {A : Set α} (Cf : ContinuousWithinAt f A (sSup A)) (
Mf : MonotoneOn f A) (A_nonemp :…
· 使用定理 `OrderTop.bddAbove`：∀ {α : Type u_1} [inst : Preorder α] [OrderTop α] (s 
: Set α), BddAbove s

--- 原说明 ---
A monotone function `f` sending `bot` to `bot` and continuous at the supremum of
 a set sends
this supremum to the supremum of the image of this set.
-/
theorem MonotoneOn.map_sSup_of_continuousWithinAt {f : α → β} {s : Set α}
    (Cf : ContinuousWithinAt f s (sSup s))
    (Mf : MonotoneOn f s) (fbot : f ⊥ = ⊥) : f (sSup s) = sSup (f '' s) := by
  rcases s.eq_empty_or_nonempty with h | h
  · simp [h, fbot]
  · exact Mf.map_csSup_of_continuousWithinAt Cf h

/-- A monotone function `f` sending `bot` to `bot` and continuous at the supremum of a set sends
this supremum to the supremum of the image of this set. -/
/-
**Monotone.map_sSup_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.map_sSup_of_continuousAt {f : α -> β} {s : Set α} (Cf : Continuou
sAt f (sSup s)) (Mf : Monotone f) (fbot : f ⊥ = ⊥) : f (sSup s) = sSup (f '' s)
参数：Cf : ContinuousAt f (sSup s)；Mf : Monotone f；fbot : f ⊥ = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.map_sSup_of_continuousWithinAt`：MonotoneOn.map_sSup_of_contin
uousWithinAt {f : α -> β} {s : Set α} (Cf : ContinuousWithinAt f s (sSup s)) (Mf
 : MonotoneOn f s) (fbot : f ⊥ …
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s

--- 原说明 ---
A monotone function `f` sending `bot` to `bot` and continuous at the supremum of
 a set sends
this supremum to the supremum of the image of this set.
-/
theorem Monotone.map_sSup_of_continuousAt {f : α → β} {s : Set α} (Cf : ContinuousAt f (sSup s))
    (Mf : Monotone f) (fbot : f ⊥ = ⊥) : f (sSup s) = sSup (f '' s) :=
  MonotoneOn.map_sSup_of_continuousWithinAt Cf.continuousWithinAt (Mf.monotoneOn _) fbot

/-- If a monotone function sending `bot` to `bot` is continuous at the indexed supremum over
a `Sort`, then it sends this indexed supremum to the indexed supremum of the composition. -/
/-
**Monotone.map_iSup_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.map_iSup_of_continuousAt {ι : Sort*} {f : α -> β} {g : ι -> α} (C
f : ContinuousAt f (iSup g)) (Mf : Monotone f) (fbot : f ⊥ = ⊥) : f (⨆ i, g i) =
 ⨆ i, f (g i)
参数：Cf : ContinuousAt f (iSup g)；Mf : Monotone f；fbot : f ⊥ = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Monotone.map_sSup_of_continuousAt`：Monotone.map_sSup_of_continuousAt {f 
: α -> β} {s : Set α} (Cf : ContinuousAt f (sSup s)) (Mf : Monotone f) (fbot : f
 ⊥ = ⊥) : f (sSup s) = …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)

--- 原说明 ---
If a monotone function sending `bot` to `bot` is continuous at the indexed supre
mum over
a `Sort`, then it sends this indexed supremum to the indexed supremum of the com
position.
-/
theorem Monotone.map_iSup_of_continuousAt {ι : Sort*} {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iSup g)) (Mf : Monotone f) (fbot : f ⊥ = ⊥) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by
  rw [iSup, Mf.map_sSup_of_continuousAt Cf fbot, ← range_comp, iSup, comp_def]

/-- A monotone function `f` sending `top` to `top` and continuous at the infimum of a set sends
this infimum to the infimum of the image of this set. -/
/-
**MonotoneOn.map_sInf_of_continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.map_sInf_of_continuousWithinAt {f : α -> β} {s : Set α} (Cf : C
ontinuousWithinAt f s (sInf s)) (Mf : MonotoneOn f s) (ftop : f ⊤ = ⊤) : f (sInf
 s) = sInf (f '' s)
参数：Cf : ContinuousWithinAt f s (sInf s)；Mf : MonotoneOn f s；ftop : f ⊤ = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.map_sSup_of_continuousWithinAt`：MonotoneOn.map_sSup_of_contin
uousWithinAt {f : α -> β} {s : Set α} (Cf : ContinuousWithinAt f s (sSup s)) (Mf
 : MonotoneOn f s) (fbot : f ⊥ …
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `MonotoneOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn (⇑OrderDua
l.toD…

--- 原说明 ---
A monotone function `f` sending `top` to `top` and continuous at the infimum of 
a set sends
this infimum to the infimum of the image of this set.
-/
theorem MonotoneOn.map_sInf_of_continuousWithinAt {f : α → β} {s : Set α}
    (Cf : ContinuousWithinAt f s (sInf s)) (Mf : MonotoneOn f s) (ftop : f ⊤ = ⊤) :
    f (sInf s) = sInf (f '' s) :=
  MonotoneOn.map_sSup_of_continuousWithinAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual ftop

/-- A monotone function `f` sending `top` to `top` and continuous at the infimum of a set sends
this infimum to the infimum of the image of this set. -/
/-
**Monotone.map_sInf_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.map_sInf_of_continuousAt {f : α -> β} {s : Set α} (Cf : Continuou
sAt f (sInf s)) (Mf : Monotone f) (ftop : f ⊤ = ⊤) : f (sInf s) = sInf (f '' s)
参数：Cf : ContinuousAt f (sInf s)；Mf : Monotone f；ftop : f ⊤ = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_sSup_of_continuousAt`：Monotone.map_sSup_of_continuousAt {f 
: α -> β} {s : Set α} (Cf : ContinuousAt f (sSup s)) (Mf : Monotone f) (fbot : f
 ⊥ = ⊥) : f (sSup s) = …
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…

--- 原说明 ---
A monotone function `f` sending `top` to `top` and continuous at the infimum of 
a set sends
this infimum to the infimum of the image of this set.
-/
theorem Monotone.map_sInf_of_continuousAt {f : α → β} {s : Set α} (Cf : ContinuousAt f (sInf s))
    (Mf : Monotone f) (ftop : f ⊤ = ⊤) : f (sInf s) = sInf (f '' s) :=
  Monotone.map_sSup_of_continuousAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual ftop

/-- If a monotone function sending `top` to `top` is continuous at the indexed infimum over
a `Sort`, then it sends this indexed infimum to the indexed infimum of the composition. -/
/-
**Monotone.map_iInf_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.map_iInf_of_continuousAt {ι : Sort*} {f : α -> β} {g : ι -> α} (C
f : ContinuousAt f (iInf g)) (Mf : Monotone f) (ftop : f ⊤ = ⊤) : f (iInf g) = i
Inf (f ∘ g)
参数：Cf : ContinuousAt f (iInf g)；Mf : Monotone f；ftop : f ⊤ = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_iSup_of_continuousAt`：Monotone.map_iSup_of_continuousAt {ι 
: Sort*} {f : α -> β} {g : ι -> α} (Cf : ContinuousAt f (iSup g)) (Mf : Monotone
 f) (fbot : f ⊥ = ⊥) : …
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…

--- 原说明 ---
If a monotone function sending `top` to `top` is continuous at the indexed infim
um over
a `Sort`, then it sends this indexed infimum to the indexed infimum of the compo
sition.
-/
theorem Monotone.map_iInf_of_continuousAt {ι : Sort*} {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iInf g)) (Mf : Monotone f) (ftop : f ⊤ = ⊤) : f (iInf g) = iInf (f ∘ g) :=
  Monotone.map_iSup_of_continuousAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual ftop

/-- An antitone function `f` sending `bot` to `top` and continuous at the supremum of a set sends
this supremum to the infimum of the image of this set. -/
/-
**AntitoneOn.map_sSup_of_continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.map_sSup_of_continuousWithinAt {f : α -> β} {s : Set α} (Cf : C
ontinuousWithinAt f s (sSup s)) (Af : AntitoneOn f s) (fbot : f ⊥ = ⊤) : f (sSup
 s) = sInf (f '' s)
参数：Cf : ContinuousWithinAt f s (sSup s)；Af : AntitoneOn f s；fbot : f ⊥ = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.map_sSup_of_continuousWithinAt`：MonotoneOn.map_sSup_of_contin
uousWithinAt {f : α -> β} {s : Set α} (Cf : ContinuousWithinAt f s (sSup s)) (Mf
 : MonotoneOn f s) (fbot : f ⊥ …
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ

--- 原说明 ---
An antitone function `f` sending `bot` to `top` and continuous at the supremum o
f a set sends
this supremum to the infimum of the image of this set.
-/
theorem AntitoneOn.map_sSup_of_continuousWithinAt {f : α → β} {s : Set α}
    (Cf : ContinuousWithinAt f s (sSup s)) (Af : AntitoneOn f s) (fbot : f ⊥ = ⊤) :
    f (sSup s) = sInf (f '' s) :=
  MonotoneOn.map_sSup_of_continuousWithinAt
    (show ContinuousWithinAt (OrderDual.toDual ∘ f) s (sSup s) from Cf) Af fbot

/-- An antitone function `f` sending `bot` to `top` and continuous at the supremum of a set sends
this supremum to the infimum of the image of this set. -/
/-
**Antitone.map_sSup_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.map_sSup_of_continuousAt {f : α -> β} {s : Set α} (Cf : Continuou
sAt f (sSup s)) (Af : Antitone f) (fbot : f ⊥ = ⊤) : f (sSup s) = sInf (f '' s)
参数：Cf : ContinuousAt f (sSup s)；Af : Antitone f；fbot : f ⊥ = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_sSup_of_continuousAt`：Monotone.map_sSup_of_continuousAt {f 
: α -> β} {s : Set α} (Cf : ContinuousAt f (sSup s)) (Mf : Monotone f) (fbot : f
 ⊥ = ⊥) : f (sSup s) = …
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ

--- 原说明 ---
An antitone function `f` sending `bot` to `top` and continuous at the supremum o
f a set sends
this supremum to the infimum of the image of this set.
-/
theorem Antitone.map_sSup_of_continuousAt {f : α → β} {s : Set α} (Cf : ContinuousAt f (sSup s))
    (Af : Antitone f) (fbot : f ⊥ = ⊤) : f (sSup s) = sInf (f '' s) :=
  Monotone.map_sSup_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (sSup s) from Cf) Af
    fbot

/-- An antitone function sending `bot` to `top` is continuous at the indexed supremum over
a `Sort`, then it sends this indexed supremum to the indexed supremum of the composition. -/
/-
**Antitone.map_iSup_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.map_iSup_of_continuousAt {ι : Sort*} {f : α -> β} {g : ι -> α} (C
f : ContinuousAt f (iSup g)) (Af : Antitone f) (fbot : f ⊥ = ⊤) : f (⨆ i, g i) =
 ⨅ i, f (g i)
参数：Cf : ContinuousAt f (iSup g)；Af : Antitone f；fbot : f ⊥ = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_iSup_of_continuousAt`：Monotone.map_iSup_of_continuousAt {ι 
: Sort*} {f : α -> β} {g : ι -> α} (Cf : ContinuousAt f (iSup g)) (Mf : Monotone
 f) (fbot : f ⊥ = ⊥) : …
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ

--- 原说明 ---
An antitone function sending `bot` to `top` is continuous at the indexed supremu
m over
a `Sort`, then it sends this indexed supremum to the indexed supremum of the com
position.
-/
theorem Antitone.map_iSup_of_continuousAt {ι : Sort*} {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iSup g)) (Af : Antitone f) (fbot : f ⊥ = ⊤) :
    f (⨆ i, g i) = ⨅ i, f (g i) :=
  Monotone.map_iSup_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (iSup g) from Cf) Af
    fbot

/-- An antitone function `f` sending `top` to `bot` and continuous at the infimum of a set sends
this infimum to the supremum of the image of this set. -/
/-
**AntitoneOn.map_sInf_of_continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.map_sInf_of_continuousWithinAt {f : α -> β} {s : Set α} (Cf : C
ontinuousWithinAt f s (sInf s)) (Af : AntitoneOn f s) (ftop : f ⊤ = ⊥) : f (sInf
 s) = sSup (f '' s)
参数：Cf : ContinuousWithinAt f s (sInf s)；Af : AntitoneOn f s；ftop : f ⊤ = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.map_sInf_of_continuousWithinAt`：MonotoneOn.map_sInf_of_contin
uousWithinAt {f : α -> β} {s : Set α} (Cf : ContinuousWithinAt f s (sInf s)) (Mf
 : MonotoneOn f s) (ftop : f ⊤ …
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ

--- 原说明 ---
An antitone function `f` sending `top` to `bot` and continuous at the infimum of
 a set sends
this infimum to the supremum of the image of this set.
-/
theorem AntitoneOn.map_sInf_of_continuousWithinAt {f : α → β} {s : Set α}
    (Cf : ContinuousWithinAt f s (sInf s)) (Af : AntitoneOn f s) (ftop : f ⊤ = ⊥) :
    f (sInf s) = sSup (f '' s) :=
  MonotoneOn.map_sInf_of_continuousWithinAt
    (show ContinuousWithinAt (OrderDual.toDual ∘ f) s (sInf s) from Cf) Af ftop

/-- An antitone function `f` sending `top` to `bot` and continuous at the infimum of a set sends
this infimum to the supremum of the image of this set. -/
/-
**Antitone.map_sInf_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.map_sInf_of_continuousAt {f : α -> β} {s : Set α} (Cf : Continuou
sAt f (sInf s)) (Af : Antitone f) (ftop : f ⊤ = ⊥) : f (sInf s) = sSup (f '' s)
参数：Cf : ContinuousAt f (sInf s)；Af : Antitone f；ftop : f ⊤ = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_sInf_of_continuousAt`：Monotone.map_sInf_of_continuousAt {f 
: α -> β} {s : Set α} (Cf : ContinuousAt f (sInf s)) (Mf : Monotone f) (ftop : f
 ⊤ = ⊤) : f (sInf s) = …
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ

--- 原说明 ---
An antitone function `f` sending `top` to `bot` and continuous at the infimum of
 a set sends
this infimum to the supremum of the image of this set.
-/
theorem Antitone.map_sInf_of_continuousAt {f : α → β} {s : Set α} (Cf : ContinuousAt f (sInf s))
    (Af : Antitone f) (ftop : f ⊤ = ⊥) : f (sInf s) = sSup (f '' s) :=
  Monotone.map_sInf_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (sInf s) from Cf) Af
    ftop

/-- If an antitone function sending `top` to `bot` is continuous at the indexed infimum over
a `Sort`, then it sends this indexed infimum to the indexed supremum of the composition. -/
/-
**Antitone.map_iInf_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.map_iInf_of_continuousAt {ι : Sort*} {f : α -> β} {g : ι -> α} (C
f : ContinuousAt f (iInf g)) (Af : Antitone f) (ftop : f ⊤ = ⊥) : f (iInf g) = i
Sup (f ∘ g)
参数：Cf : ContinuousAt f (iInf g)；Af : Antitone f；ftop : f ⊤ = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_iInf_of_continuousAt`：Monotone.map_iInf_of_continuousAt {ι 
: Sort*} {f : α -> β} {g : ι -> α} (Cf : ContinuousAt f (iInf g)) (Mf : Monotone
 f) (ftop : f ⊤ = ⊤) : …
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ

--- 原说明 ---
If an antitone function sending `top` to `bot` is continuous at the indexed infi
mum over
a `Sort`, then it sends this indexed infimum to the indexed supremum of the comp
osition.
-/
theorem Antitone.map_iInf_of_continuousAt {ι : Sort*} {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iInf g)) (Af : Antitone f) (ftop : f ⊤ = ⊥) : f (iInf g) = iSup (f ∘ g) :=
  Monotone.map_iInf_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (iInf g) from Cf) Af
    ftop

end CompleteLinearOrder

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]

/-
**csSup_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_mem_closure {s : Set α} (hs : s.Nonempty) (B : BddAbove s) : sSup s 
in closure s
参数：hs : s.Nonempty；B : BddAbove s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.mem_closure`：IsLUB.mem_closure {a : α} {s : Set α} (ha : IsLUB s a
) (hs : s.Nonempty) : a in closure s
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
-/
theorem csSup_mem_closure {s : Set α} (hs : s.Nonempty) (B : BddAbove s) : sSup s ∈ closure s :=
  (isLUB_csSup hs B).mem_closure hs
/-
**csInf_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csInf_mem_closure {s : Set α} (hs : s.Nonempty) (B : BddBelow s) : sInf s 
in closure s
参数：hs : s.Nonempty；B : BddBelow s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.mem_closure`：IsGLB.mem_closure {a : α} {s : Set α} (ha : IsGLB s a
) (hs : s.Nonempty) : a in closure s
· 使用定理 `isGLB_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s
 : Set α},   s.Nonempty → autoParam (BddBelow s) isGLB_csInf._auto_1 → IsGLB s (
s…
-/
theorem csInf_mem_closure {s : Set α} (hs : s.Nonempty) (B : BddBelow s) : sInf s ∈ closure s :=
  (isGLB_csInf hs B).mem_closure hs
/-
**IsClosed.csSup_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.csSup_mem {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : Bd
dAbove s) : sSup s in s
参数：hc : IsClosed s；hs : s.Nonempty；B : BddAbove s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.mem_of_isClosed`：IsLUB.mem_of_isClosed {a : α} {s : Set α} (ha : I
sLUB s a) (hs : s.Nonempty) (sc : IsClosed s) : a in s
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
-/
theorem IsClosed.csSup_mem {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddAbove s) :
    sSup s ∈ s :=
  (isLUB_csSup hs B).mem_of_isClosed hs hc
/-
**IsClosed.csInf_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.csInf_mem {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : Bd
dBelow s) : sInf s in s
参数：hc : IsClosed s；hs : s.Nonempty；B : BddBelow s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.mem_of_isClosed`：IsGLB.mem_of_isClosed {a : α} {s : Set α} (ha : I
sGLB s a) (hs : s.Nonempty) (sc : IsClosed s) : a in s
· 使用定理 `isGLB_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s
 : Set α},   s.Nonempty → autoParam (BddBelow s) isGLB_csInf._auto_1 → IsGLB s (
s…
-/
theorem IsClosed.csInf_mem {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddBelow s) :
    sInf s ∈ s :=
  (isGLB_csInf hs B).mem_of_isClosed hs hc
/-
**IsClosed.isLeast_csInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.isLeast_csInf {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B 
: BddBelow s) : IsLeast s (sInf s)
参数：hc : IsClosed s；hs : s.Nonempty；B : BddBelow s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.csInf_mem`：IsClosed.csInf_mem {s : Set α} (hc : IsClosed s) (hs
 : s.Nonempty) (B : BddBelow s) : sInf s in s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isGLB_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s
 : Set α},   s.Nonempty → autoParam (BddBelow s) isGLB_csInf._auto_1 → IsGLB s (
s…
-/
theorem IsClosed.isLeast_csInf {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddBelow s) :
    IsLeast s (sInf s) :=
  ⟨hc.csInf_mem hs B, (isGLB_csInf hs B).1⟩
/-
**IsClosed.isGreatest_csSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.isGreatest_csSup {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) 
(B : BddAbove s) : IsGreatest s (sSup s)
参数：hc : IsClosed s；hs : s.Nonempty；B : BddAbove s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.isLeast_csInf`：IsClosed.isLeast_csInf {s : Set α} (hc : IsClose
d s) (hs : s.Nonempty) (B : BddBelow s) : IsLeast s (sInf s)
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem IsClosed.isGreatest_csSup {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddAbove s) :
    IsGreatest s (sSup s) :=
  IsClosed.isLeast_csInf (α := αᵒᵈ) hc hs B
/-
**MonotoneOn.tendsto_nhdsWithin_Ioo_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonotoneOn.tendsto_nhdsWithin_Ioo_left {α β : Type*} [LinearOrder α] [Topo
logicalSpace α] [OrderTopology α] [ConditionallyCompleteLinearOrder β] [Topologi
calSpace β] [OrderTopology β] {f : α -> β} {x y : α} (h_nonempty : (Ioo y x).Non
empty) (Mf : MonotoneOn f (Ioo y x)) (h_bdd : BddAbove (f '' Ioo y x)) : Tendsto
 f (𝓝[<] x) (𝓝 (sSup (f '' Ioo y x)))
参数：h_nonempty : (Ioo y x).Nonempty；Mf : MonotoneOn f (Ioo y x)；h_bdd : BddAbove 
(f '' Ioo y x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_lt_of_lt_csSup`：exists_lt_of_lt_csSup (hs : s.Nonempty) (hb : b <
 sSup s) : exists a in s, b < a
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Ioo_mem_nhdsLT`：Ioo_mem_nhdsLT (H : a < b) : Ioo a b in 𝓝[<] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
lemma MonotoneOn.tendsto_nhdsWithin_Ioo_left {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} {x y : α} (h_nonempty : (Ioo y x).Nonempty) (Mf : MonotoneOn f (Ioo y x))
    (h_bdd : BddAbove (f '' Ioo y x)) :
    Tendsto f (𝓝[<] x) (𝓝 (sSup (f '' Ioo y x))) := by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · obtain ⟨z, ⟨yz, zx⟩, lz⟩ : ∃ a : α, a ∈ Ioo y x ∧ l < f a := by
      simpa only [mem_image, exists_prop, exists_exists_and_eq_and] using
        exists_lt_of_lt_csSup (h_nonempty.image _) hl
    filter_upwards [Ioo_mem_nhdsLT zx] with w hw
    exact lz.trans_le <| Mf ⟨yz, zx⟩ ⟨yz.trans_le hw.1.le, hw.2⟩ hw.1.le
  · rcases h_nonempty with ⟨_, hy, hx⟩
    filter_upwards [Ioo_mem_nhdsLT (hy.trans hx)] with w hw
    exact (le_csSup h_bdd (mem_image_of_mem _ hw)).trans_lt hm
/-
**MonotoneOn.tendsto_nhdsWithin_Ioo_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonotoneOn.tendsto_nhdsWithin_Ioo_right {α β : Type*} [LinearOrder α] [Top
ologicalSpace α] [OrderTopology α] [ConditionallyCompleteLinearOrder β] [Topolog
icalSpace β] [OrderTopology β] {f : α -> β} {x y : α} (h_nonempty : (Ioo x y).No
nempty) (Mf : MonotoneOn f (Ioo x y)) (h_bdd : BddBelow (f '' Ioo x y)) : Tendst
o f (𝓝[>] x) (𝓝 (sInf (f '' Ioo x y)))
参数：h_nonempty : (Ioo x y).Nonempty；Mf : MonotoneOn f (Ioo x y)；h_bdd : BddBelow 
(f '' Ioo x y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Ioo_mem_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ioo b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_lt_of_csInf_lt`：∀ {α : Type u_1} [inst : ConditionallyCompleteLin
earOrder α] {s : Set α} {b : α},   s.Nonempty → sInf s < b → ∃ a ∈ s, a < b
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma MonotoneOn.tendsto_nhdsWithin_Ioo_right {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} {x y : α} (h_nonempty : (Ioo x y).Nonempty) (Mf : MonotoneOn f (Ioo x y))
    (h_bdd : BddBelow (f '' Ioo x y)) :
    Tendsto f (𝓝[>] x) (𝓝 (sInf (f '' Ioo x y))) := by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · rcases h_nonempty with ⟨p, hy, hx⟩
    filter_upwards [Ioo_mem_nhdsGT (hy.trans hx)] with w hw
    exact hl.trans_le <| csInf_le h_bdd (mem_image_of_mem _ hw)
  · obtain ⟨z, ⟨xz, zy⟩, zm⟩ : ∃ a : α, a ∈ Ioo x y ∧ f a < m := by
      simpa [mem_image, exists_prop, exists_exists_and_eq_and] using
        exists_lt_of_csInf_lt (h_nonempty.image _) hm
    filter_upwards [Ioo_mem_nhdsGT xz] with w hw
    exact (Mf ⟨hw.1, hw.2.trans zy⟩ ⟨xz, zy⟩ hw.2.le).trans_lt zm
/-
**MonotoneOn.tendsto_nhdsLT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonotoneOn.tendsto_nhdsLT {α β : Type*} [LinearOrder α] [TopologicalSpace 
α] [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [
OrderTopology β] {f : α -> β} {x : α} (Mf : MonotoneOn f (Iio x)) (h_bdd : BddAb
ove (f '' Iio x)) : Tendsto f (𝓝[<] x) (𝓝 (sSup (f '' Iio x)))
参数：Mf : MonotoneOn f (Iio x)；h_bdd : BddAbove (f '' Iio x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_empty`：nhdsWithin_empty (a : α) : 𝓝[∅] a = ⊥
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_lt_of_lt_csSup`：exists_lt_of_lt_csSup (hs : s.Nonempty) (hb : b <
 sSup s) : exists a in s, b < a
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Ioo_mem_nhdsLT`：Ioo_mem_nhdsLT (H : a < b) : Ioo a b in 𝓝[<] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
lemma MonotoneOn.tendsto_nhdsLT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α → β} {x : α}
    (Mf : MonotoneOn f (Iio x)) (h_bdd : BddAbove (f '' Iio x)) :
    Tendsto f (𝓝[<] x) (𝓝 (sSup (f '' Iio x))) := by
  rcases eq_empty_or_nonempty (Iio x) with (h | h); · simp [h]
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · obtain ⟨z, zx, lz⟩ : ∃ a : α, a < x ∧ l < f a := by
      simpa only [mem_image, exists_prop, exists_exists_and_eq_and] using!
        exists_lt_of_lt_csSup (h.image _) hl
    filter_upwards [Ioo_mem_nhdsLT zx] with y hy using lz.trans_le (Mf zx hy.2 hy.1.le)
  · refine mem_of_superset self_mem_nhdsWithin fun y hy => lt_of_le_of_lt ?_ hm
    exact le_csSup h_bdd (mem_image_of_mem _ hy)
/-
**MonotoneOn.tendsto_nhdsGT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonotoneOn.tendsto_nhdsGT {α β : Type*} [LinearOrder α] [TopologicalSpace 
α] [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [
OrderTopology β] {f : α -> β} {x : α} (Mf : MonotoneOn f (Ioi x)) (h_bdd : BddBe
low (f '' Ioi x)) : Tendsto f (𝓝[>] x) (𝓝 (sInf (f '' Ioi x)))
参数：Mf : MonotoneOn f (Ioi x)；h_bdd : BddBelow (f '' Ioi x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonotoneOn.tendsto_nhdsLT`：MonotoneOn.tendsto_nhdsLT {α β : Type*} [Line
arOrder α] [TopologicalSpace α] [OrderTopology α] [ConditionallyCompleteLinearOr
der β] [Topolog…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `MonotoneOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn (⇑OrderDua
l.toD…
-/
lemma MonotoneOn.tendsto_nhdsGT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α → β} {x : α}
    (Mf : MonotoneOn f (Ioi x)) (h_bdd : BddBelow (f '' Ioi x)) :
    Tendsto f (𝓝[>] x) (𝓝 (sInf (f '' Ioi x))) :=
  MonotoneOn.tendsto_nhdsLT (α := αᵒᵈ) (β := βᵒᵈ) Mf.dual h_bdd

/-- A monotone map has a limit to the left of any point `x`, equal to `sSup (f '' (Iio x))`. -/
/-
**Monotone.tendsto_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.tendsto_nhdsLT {α β : Type*} [LinearOrder α] [TopologicalSpace α]
 [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [Or
derTopology β] {f : α -> β} (Mf : Monotone f) (x : α) : Tendsto f (𝓝[<] x) (𝓝 (s
Sup (f '' Iio x)))
参数：Mf : Monotone f；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonotoneOn.tendsto_nhdsLT`：MonotoneOn.tendsto_nhdsLT {α β : Type*} [Line
arOrder α] [TopologicalSpace α] [OrderTopology α] [ConditionallyCompleteLinearOr
der β] [Topolog…
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
· 使用定理 `Monotone.map_bddAbove`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β},   Monotone f → ∀ {s : Set α}, BddAbove s → Bdd
Above (f ''…
· 使用定理 `bddAbove_Iio`：bddAbove_Iio : BddAbove (Iio a)

--- 原说明 ---
A monotone map has a limit to the left of any point `x`, equal to `sSup (f '' (I
io x))`.
-/
theorem Monotone.tendsto_nhdsLT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α → β}
    (Mf : Monotone f) (x : α) : Tendsto f (𝓝[<] x) (𝓝 (sSup (f '' Iio x))) :=
  MonotoneOn.tendsto_nhdsLT (Mf.monotoneOn _) (Mf.map_bddAbove bddAbove_Iio)

/-- A monotone map has a limit to the right of any point `x`, equal to `sInf (f '' (Ioi x))`. -/
/-
**Monotone.tendsto_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.tendsto_nhdsGT {α β : Type*} [LinearOrder α] [TopologicalSpace α]
 [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [Or
derTopology β] {f : α -> β} (Mf : Monotone f) (x : α) : Tendsto f (𝓝[>] x) (𝓝 (s
Inf (f '' Ioi x)))
参数：Mf : Monotone f；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_nhdsLT`：Monotone.tendsto_nhdsLT {α β : Type*} [LinearOr
der α] [TopologicalSpace α] [OrderTopology α] [ConditionallyCompleteLinearOrder 
β] [Topologic…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…

--- 原说明 ---
A monotone map has a limit to the right of any point `x`, equal to `sInf (f '' (
Ioi x))`.
-/
theorem Monotone.tendsto_nhdsGT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α → β}
    (Mf : Monotone f) (x : α) : Tendsto f (𝓝[>] x) (𝓝 (sInf (f '' Ioi x))) :=
  Monotone.tendsto_nhdsLT (α := αᵒᵈ) (β := βᵒᵈ) Mf.dual x
/-
**AntitoneOn.tendsto_nhdsWithin_Ioo_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AntitoneOn.tendsto_nhdsWithin_Ioo_left {α β : Type*} [LinearOrder α] [Topo
logicalSpace α] [OrderTopology α] [ConditionallyCompleteLinearOrder β] [Topologi
calSpace β] [OrderTopology β] {f : α -> β} {x y : α} (h_nonempty : (Ioo y x).Non
empty) (Af : AntitoneOn f (Ioo y x)) (h_bdd : BddBelow (f '' Ioo y x)) : Tendsto
 f (𝓝[<] x) (𝓝 (sInf (f '' Ioo y x)))
参数：h_nonempty : (Ioo y x).Nonempty；Af : AntitoneOn f (Ioo y x)；h_bdd : BddBelow 
(f '' Ioo y x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonotoneOn.tendsto_nhdsWithin_Ioo_left`：MonotoneOn.tendsto_nhdsWithin_Io
o_left {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [Con
ditionallyCompleteLinearOrde…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…
-/
lemma AntitoneOn.tendsto_nhdsWithin_Ioo_left {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} {x y : α} (h_nonempty : (Ioo y x).Nonempty) (Af : AntitoneOn f (Ioo y x))
    (h_bdd : BddBelow (f '' Ioo y x)) :
    Tendsto f (𝓝[<] x) (𝓝 (sInf (f '' Ioo y x))) :=
  MonotoneOn.tendsto_nhdsWithin_Ioo_left h_nonempty Af.dual_right h_bdd
/-
**AntitoneOn.tendsto_nhdsWithin_Ioo_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AntitoneOn.tendsto_nhdsWithin_Ioo_right {α β : Type*} [LinearOrder α] [Top
ologicalSpace α] [OrderTopology α] [ConditionallyCompleteLinearOrder β] [Topolog
icalSpace β] [OrderTopology β] {f : α -> β} {x y : α} (h_nonempty : (Ioo x y).No
nempty) (Af : AntitoneOn f (Ioo x y)) (h_bdd : BddAbove (f '' Ioo x y)) : Tendst
o f (𝓝[>] x) (𝓝 (sSup (f '' Ioo x y)))
参数：h_nonempty : (Ioo x y).Nonempty；Af : AntitoneOn f (Ioo x y)；h_bdd : BddAbove 
(f '' Ioo x y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonotoneOn.tendsto_nhdsWithin_Ioo_right`：MonotoneOn.tendsto_nhdsWithin_I
oo_right {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [C
onditionallyCompleteLinearOrd…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…
-/
lemma AntitoneOn.tendsto_nhdsWithin_Ioo_right {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} {x y : α} (h_nonempty : (Ioo x y).Nonempty) (Af : AntitoneOn f (Ioo x y))
    (h_bdd : BddAbove (f '' Ioo x y)) :
    Tendsto f (𝓝[>] x) (𝓝 (sSup (f '' Ioo x y))) :=
  MonotoneOn.tendsto_nhdsWithin_Ioo_right h_nonempty Af.dual_right h_bdd
/-
**AntitoneOn.tendsto_nhdsLT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AntitoneOn.tendsto_nhdsLT {α β : Type*} [LinearOrder α] [TopologicalSpace 
α] [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [
OrderTopology β] {f : α -> β} {x : α} (Af : AntitoneOn f (Iio x)) (h_bdd : BddBe
low (f '' Iio x)) : Tendsto f (𝓝[<] x) (𝓝 (sInf (f '' Iio x)))
参数：Af : AntitoneOn f (Iio x)；h_bdd : BddBelow (f '' Iio x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonotoneOn.tendsto_nhdsLT`：MonotoneOn.tendsto_nhdsLT {α β : Type*} [Line
arOrder α] [TopologicalSpace α] [OrderTopology α] [ConditionallyCompleteLinearOr
der β] [Topolog…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…
-/
lemma AntitoneOn.tendsto_nhdsLT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α → β} {x : α}
    (Af : AntitoneOn f (Iio x)) (h_bdd : BddBelow (f '' Iio x)) :
    Tendsto f (𝓝[<] x) (𝓝 (sInf (f '' Iio x))) :=
  MonotoneOn.tendsto_nhdsLT Af.dual_right h_bdd
/-
**AntitoneOn.tendsto_nhdsGT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AntitoneOn.tendsto_nhdsGT {α β : Type*} [LinearOrder α] [TopologicalSpace 
α] [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [
OrderTopology β] {f : α -> β} {x : α} (Af : AntitoneOn f (Ioi x)) (h_bdd : BddAb
ove (f '' Ioi x)) : Tendsto f (𝓝[>] x) (𝓝 (sSup (f '' Ioi x)))
参数：Af : AntitoneOn f (Ioi x)；h_bdd : BddAbove (f '' Ioi x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonotoneOn.tendsto_nhdsGT`：MonotoneOn.tendsto_nhdsGT {α β : Type*} [Line
arOrder α] [TopologicalSpace α] [OrderTopology α] [ConditionallyCompleteLinearOr
der β] [Topolog…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…
-/
lemma AntitoneOn.tendsto_nhdsGT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α → β} {x : α}
    (Af : AntitoneOn f (Ioi x)) (h_bdd : BddAbove (f '' Ioi x)) :
    Tendsto f (𝓝[>] x) (𝓝 (sSup (f '' Ioi x))) :=
  MonotoneOn.tendsto_nhdsGT Af.dual_right h_bdd

/-- An antitone map has a limit to the left of any point `x`, equal to `sInf (f '' (Iio x))`. -/
/-
**Antitone.tendsto_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.tendsto_nhdsLT {α β : Type*} [LinearOrder α] [TopologicalSpace α]
 [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [Or
derTopology β] {f : α -> β} (Af : Antitone f) (x : α) : Tendsto f (𝓝[<] x) (𝓝 (s
Inf (f '' Iio x)))
参数：Af : Antitone f；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_nhdsLT`：Monotone.tendsto_nhdsLT {α β : Type*} [LinearOr
der α] [TopologicalSpace α] [OrderTopology α] [ConditionallyCompleteLinearOrder 
β] [Topologic…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)

--- 原说明 ---
An antitone map has a limit to the left of any point `x`, equal to `sInf (f '' (
Iio x))`.
-/
theorem Antitone.tendsto_nhdsLT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α → β}
    (Af : Antitone f) (x : α) : Tendsto f (𝓝[<] x) (𝓝 (sInf (f '' Iio x))) :=
  Monotone.tendsto_nhdsLT Af.dual_right x

/-- An antitone map has a limit to the right of any point `x`, equal to `sSup (f '' (Ioi x))`. -/
/-
**Antitone.tendsto_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.tendsto_nhdsGT {α β : Type*} [LinearOrder α] [TopologicalSpace α]
 [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [Or
derTopology β] {f : α -> β} (Af : Antitone f) (x : α) : Tendsto f (𝓝[>] x) (𝓝 (s
Sup (f '' Ioi x)))
参数：Af : Antitone f；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_nhdsGT`：Monotone.tendsto_nhdsGT {α β : Type*} [LinearOr
der α] [TopologicalSpace α] [OrderTopology α] [ConditionallyCompleteLinearOrder 
β] [Topologic…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)

--- 原说明 ---
An antitone map has a limit to the right of any point `x`, equal to `sSup (f '' 
(Ioi x))`.
-/
theorem Antitone.tendsto_nhdsGT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α → β}
    (Af : Antitone f) (x : α) : Tendsto f (𝓝[>] x) (𝓝 (sSup (f '' Ioi x))) :=
  Monotone.tendsto_nhdsGT Af.dual_right x

end ConditionallyCompleteLinearOrder

